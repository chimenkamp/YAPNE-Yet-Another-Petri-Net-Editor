import { Transition, PetriNet, Place, Arc } from '../petri-net-simulator.js';
import { solveExpressionWithWebPPL } from './probabilistic-execution.js';
import { parse } from './guard-language/guard-parser.js';
import { evaluatePrecondition as evalPre, evaluatePostcondition as evalPost, checkConstraint, constraintToString, getWrittenVariables } from './guard-language/guard-evaluator.js';

/**
 * Represents a data variable in a Data Petri Net
 */
class DataVariable {
  /**
   * Create a new data variable
   * @param {string} id - Unique identifier for the variable
   * @param {string} name - Human-readable name of the variable
   * @param {string} type - Data type ('int'|'integer'|'bool'|'boolean'|'real')
   * @param {*} initialValue - Initial value of the variable
   * @param {string} description - Optional description of the variable
   */
  constructor(id, name, type, initialValue = null, description = "") {
    this.id = id;
    this.name = name;
    this.type = DataVariable.normalizeType(type);
    this.currentValue = initialValue;
    this.description = description;
  }

  /**
   * Normalize type aliases to canonical forms
   * @param {string} type - Raw type string
   * @returns {string} Normalized type: 'int', 'bool', or 'real'
   */
  static normalizeType(type) {
    const t = (type || 'real').toLowerCase();
    if (t === 'int' || t === 'integer') return 'int';
    if (t === 'bool' || t === 'boolean') return 'bool';
    if (t === 'real' || t === 'float' || t === 'number') return 'real';
    // Legacy: treat 'string' as 'int' (integer encoding)
    if (t === 'string') return 'int';
    return 'real';
  }

  /**
   * Get the current value with proper type conversion
   * @returns {*} The current value with the correct type
   */
  getValue() {
    if (this.currentValue === null) return null;

    switch (this.type) {
      case 'int':
        return Math.floor(Number(this.currentValue));
      case 'bool':
        return Boolean(this.currentValue);
      case 'real':
      default:
        return Number(this.currentValue);
    }
  }

  /**
   * Set the current value with type validation
   * @param {*} value - The new value
   * @returns {boolean} Whether the value was set successfully
   */
  setValue(value) {
    try {
      switch (this.type) {
        case 'int': {
          const intValue = Number(value);
          if (isNaN(intValue)) {
            throw new Error('Not a valid integer');
          }
          this.currentValue = Math.floor(intValue);
          break;
        }
        case 'bool':
          this.currentValue = Boolean(value);
          break;
        case 'real':
        default: {
          const realValue = Number(value);
          if (isNaN(realValue)) {
            throw new Error('Not a valid real number');
          }
          this.currentValue = realValue;
          break;
        }
      }
      return true;
    } catch (error) {
      console.error(`Error setting value for variable ${this.name}:`, error);
      return false;
    }
  }

  /**
   * Reset the variable to its initial value
   */
  reset() {
    this.currentValue = this.initialValue;
  }
}

/**
 * Extends the Transition class to support data-aware preconditions and postconditions
 */
class DataAwareTransition extends Transition {
  /**
   * Create a new data-aware transition
   * @param {string} id - Unique identifier for the transition
   * @param {Object} position - {x, y} position of the transition
   * @param {string} label - Label of the transition
   * @param {number} priority - Priority for conflict resolution
   * @param {number} delay - Execution delay in milliseconds
   * @param {string} precondition - Guard condition as a JavaScript expression
   * @param {string} postcondition - Data manipulation as a JavaScript expression
   * @param {boolean} silent - Whether this is a silent (tau) transition
   */
  constructor(id, position, label = "", priority = 1, delay = 0, precondition = "", postcondition = "", silent = false) {
    super(id, position, label, priority, delay, silent);
    this.precondition = precondition;
    this.postcondition = postcondition;
  }

  /**
   * Evaluate the precondition guard with the current data valuation
   * @param {Object} valuation - Map of variable names to current values
   * @returns {boolean} Whether the precondition is satisfied
   */
  evaluatePrecondition(valuation) {
    if (!this.precondition || this.precondition.trim() === "") {
      return true; // No precondition means it's always satisfied
    }

    try {
      const { ast } = parse(this.precondition, { isPostcondition: false });
      return evalPre(ast, valuation);
    } catch (error) {
      console.error(`Error evaluating precondition for transition ${this.id}:`, error);
      console.error(`Precondition: ${this.precondition}`);
      console.error(`Valuation:`, valuation);
      return false; // On error, disable the transition for safety
    }
  }

  /**
   * Evaluate the postcondition and compute the new data valuation (ASYNC)
   * @param {Object} valuation - Map of variable names to current values
   * @returns {Promise<Object>} New valuation after applying the postcondition
   */
  async evaluatePostcondition(valuation) {
    if (!this.postcondition || this.postcondition.trim() === "") {
      return valuation; // No postcondition means no changes
    }
  
    try {
      const newValuation = { ...valuation };
      const { ast } = parse(this.postcondition, { isPostcondition: true });
      const { assignments, constraints } = evalPost(ast, valuation);

      // Apply direct assignments
      for (const [varName, value] of assignments) {
        if (varName in valuation) {
          newValuation[varName] = value;
        }
      }

      // Handle constraint-based assignments via WebPPL solver
      if (constraints.length > 0) {
        const primedVars = getWrittenVariables(ast);
        
        for (const variableName of primedVars) {
          if (!(variableName in valuation)) continue;
          // Skip if already handled by direct assignment
          if (assignments.has(variableName)) continue;

          const currentValue = valuation[variableName];

          // For boolean variables, try both values directly
          if (typeof currentValue === 'boolean') {
            const trueOk = constraints.every(c => checkConstraint(c, valuation, { ...newValuation, [variableName]: true }));
            const falseOk = constraints.every(c => checkConstraint(c, valuation, { ...newValuation, [variableName]: false }));
            if (trueOk) { newValuation[variableName] = true; continue; }
            if (falseOk) { newValuation[variableName] = false; continue; }
            continue;
          }

          // For numeric variables, use WebPPL solver
          if (typeof currentValue === 'number') {
            try {
              const combinedConstraint = constraints.map(c => constraintToString(c)).join(' && ');
              let variableType = 'int';
              if (window.petriApp && window.petriApp.api && window.petriApp.api.petriNet && window.petriApp.api.petriNet.dataVariables) {
                for (const [, variable] of window.petriApp.api.petriNet.dataVariables) {
                  if (variable.name === variableName) {
                    variableType = variable.type;
                    break;
                  }
                }
              }
              
              const result = await solveExpressionWithWebPPL(
                combinedConstraint, 
                newValuation, 
                variableType === 'real' ? 'float' : 'int'
              );
              
              if (result && result.success && result.newValues && result.newValues[variableName] !== undefined) {
                if (variableType === 'int') {
                  newValuation[variableName] = Math.floor(Number(result.newValues[variableName]));
                } else {
                  newValuation[variableName] = Number(result.newValues[variableName]);
                }
              }
            } catch (error) {
              console.error('[DPN] Error using WebPPL solver:', error);
            }
          }
        }
      }
      
      return newValuation;
    } catch (error) {
      console.error(`Error evaluating postcondition for transition ${this.id}:`, error);
      console.error(`Postcondition: ${this.postcondition}`);
      console.error(`Valuation:`, valuation);
      return valuation; // On error, keep the original valuation
    }
  }
  
}

/**
 * Extends the PetriNet class to support data variables and data-aware transitions
 */
class DataPetriNet extends PetriNet {
  /**
   * Create a new Data Petri Net
   * @param {string} id - Unique identifier for the net
   * @param {string} name - Name of the net
   * @param {string} description - Description of the net
   */
  constructor(id, name = "New Data Petri Net", description = "") {
    super(id, name, description);
    this.dataVariables = new Map(); // Map of data variable ID -> DataVariable object
  }

  /**
   * Add a data variable to the net
   * @param {DataVariable} variable - The data variable to add
   */
  addDataVariable(variable) {
    this.dataVariables.set(variable.id, variable);
  }

  /**
   * Get a data variable by ID
   * @param {string} id - ID of the variable to get
   * @returns {DataVariable|undefined} The data variable, if found
   */
  getDataVariable(id) {
    return this.dataVariables.get(id);
  }

  /**
   * Remove a data variable by ID
   * @param {string} id - ID of the variable to remove
   * @returns {boolean} Whether the variable was removed
   */
  removeDataVariable(id) {
    return this.dataVariables.delete(id);
  }

  /**
   * Get the current data valuation (map of variable names to values)
   * @returns {Object} The current data valuation
   */
  getDataValuation() {
    const valuation = {};
    for (const [, variable] of this.dataVariables) {
      valuation[variable.name] = variable.getValue();
    }
    return valuation;
  }

  /**
   * Update the current data valuation
   * @param {Object} valuation - Map of variable names to new values
   */
  setDataValuation(valuation) {
    for (const [name, value] of Object.entries(valuation)) {
      for (const [, variable] of this.dataVariables) {
        if (variable.name === name) {
          variable.setValue(value);
          break;
        }
      }
    }
  }

  /**
   * Override the parent updateEnabledTransitions method to check data preconditions
   */
  updateEnabledTransitions() {
    super.updateEnabledTransitions();

    const valuation = this.getDataValuation();

    for (const [id, transition] of this.transitions) {
      if (transition.isEnabled) {
        if (typeof transition.evaluatePrecondition === 'function') {
          transition.isEnabled = transition.evaluatePrecondition(valuation);
        }
      }
    }
  }

  /**
   * Override the parent isTransitionEnabled method to check data preconditions
   * @param {string} transitionId - ID of the transition to check
   * @returns {boolean} Whether the transition is enabled
   */
  isTransitionEnabled(transitionId) {
    const isEnabledByTokens = super.isTransitionEnabled(transitionId);

    if (!isEnabledByTokens) return false;

    const transition = this.transitions.get(transitionId);
    if (!transition) return false;

    if (typeof transition.evaluatePrecondition === 'function') {
      const valuation = this.getDataValuation();
      return transition.evaluatePrecondition(valuation);
    }

    return true;
  }

  /**
   * Override the parent fireTransition method to handle data updates (ASYNC)
   * @param {string} transitionId - ID of the transition to fire
   * @returns {Promise<boolean>} Whether the transition fired successfully
   */
  async fireTransition(transitionId) {
    if (!this.isTransitionEnabled(transitionId)) {
      return false;
    }

    const transition = this.transitions.get(transitionId);
    if (!transition) return false;

    const valuation = this.getDataValuation();

    // Handle token movement first
    const incomingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outgoingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.source === transitionId);

    for (const arc of incomingArcs) {
      const place = this.places.get(arc.source);
      if (!place) continue;

      if (arc.type === "regular") {
        place.removeTokens(arc.weight);
      } else if (arc.type === "reset") {
        place.tokens = 0;
      }
    }

    for (const arc of outgoingArcs) {
      const place = this.places.get(arc.target);
      if (!place) continue;

      place.addTokens(arc.weight);
    }

    // Handle data updates (this is now async)
    if (typeof transition.evaluatePostcondition === 'function') {
      try {
        const newValuation = await transition.evaluatePostcondition(valuation);
        this.setDataValuation(newValuation);
      } catch (error) {
        console.error('Error evaluating postcondition:', error);
        // Continue with execution even if postcondition fails
      }
    }

    return true;
  }

  /**
   * Detect if two transitions are in structural conflict (share input places)
   * @param {string} trans1Id - First transition ID
   * @param {string} trans2Id - Second transition ID
   * @returns {boolean} - True if transitions are in conflict
   */
  areTransitionsInConflict(trans1Id, trans2Id) {
    const incomingArcs1 = Array.from(this.arcs.values())
      .filter(arc => arc.target === trans1Id && arc.type === "regular");
    const incomingArcs2 = Array.from(this.arcs.values())
      .filter(arc => arc.target === trans2Id && arc.type === "regular");

    // Check if they share any input places
    const inputPlaces1 = new Set(incomingArcs1.map(arc => arc.source));
    const inputPlaces2 = new Set(incomingArcs2.map(arc => arc.source));

    for (const placeId of inputPlaces1) {
      if (inputPlaces2.has(placeId)) {
        // Check if there are enough tokens to fire both
        const place = this.places.get(placeId);
        if (!place) continue;

        // Calculate total token requirement
        const weight1 = incomingArcs1.find(arc => arc.source === placeId)?.weight || 0;
        const weight2 = incomingArcs2.find(arc => arc.source === placeId)?.weight || 0;

        if (place.tokens < weight1 + weight2) {
          return true; // Conflict: not enough tokens for both
        }
      }
    }

    return false;
  }

  /**
   * Resolve conflicts by selecting a subset of transitions that can fire together
   * Randomly selects among transitions with equal priority and weight
   * @param {Array<string>} enabledTransitionIds - Array of enabled transition IDs
   * @returns {Array<string>} - Array of non-conflicting transition IDs to fire
   */
  resolveConflicts(enabledTransitionIds) {
    if (enabledTransitionIds.length <= 1) {
      return enabledTransitionIds;
    }

    // Group transitions by their input places to identify conflict sets
    const conflictGroups = new Map(); // placeId -> array of transition IDs

    for (const transId of enabledTransitionIds) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === transId && arc.type === "regular");

      for (const arc of incomingArcs) {
        if (!conflictGroups.has(arc.source)) {
          conflictGroups.set(arc.source, []);
        }
        conflictGroups.get(arc.source).push({
          transitionId: transId,
          weight: arc.weight
        });
      }
    }

    // Find transitions that are actually in conflict
    const toFire = new Set(enabledTransitionIds);

    for (const [placeId, transitions] of conflictGroups) {
      if (transitions.length <= 1) continue;

      const place = this.places.get(placeId);
      if (!place) continue;

      // Calculate total token requirement
      const totalRequired = transitions.reduce((sum, t) => sum + t.weight, 0);

      // If there's a conflict (not enough tokens for all)
      if (place.tokens < totalRequired) {
        // Group by priority and weight
        const transitionDetails = transitions.map(t => {
          const transition = this.transitions.get(t.transitionId);
          return {
            id: t.transitionId,
            priority: transition?.priority || 1,
            weight: t.weight
          };
        });

        // Sort by priority (higher first), then randomly shuffle within same priority
        transitionDetails.sort((a, b) => {
          if (b.priority !== a.priority) {
            return b.priority - a.priority;
          }
          // Same priority - randomize
          return Math.random() - 0.5;
        });

        // Select transitions until we run out of tokens
        let availableTokens = place.tokens;
        const selected = [];

        for (const trans of transitionDetails) {
          const arcWeight = transitions.find(t => t.transitionId === trans.id)?.weight || 0;
          if (availableTokens >= arcWeight && toFire.has(trans.id)) {
            selected.push(trans.id);
            availableTokens -= arcWeight;
          } else {
            toFire.delete(trans.id);
          }
        }
      }
    }

    return Array.from(toFire);
  }

  /**
   * Fire multiple transitions simultaneously in one atomic step (synchronous step semantics)
   * All transitions that are enabled at the start of the step will fire together
   * @param {Array<string>} transitionIds - Array of transition IDs to fire
   * @returns {Promise<boolean>} - True if at least one transition was successfully fired
   */
  async fireTransitionsSynchronously(transitionIds) {
    // Filter to only enabled transitions
    const enabledTransitions = transitionIds.filter(id => this.isTransitionEnabled(id));
    
    if (enabledTransitions.length === 0) {
      return false;
    }

    // Resolve conflicts - randomly select among transitions with same priority/weight
    const transitionsToFire = this.resolveConflicts(enabledTransitions);

    if (transitionsToFire.length === 0) {
      return false;
    }

    const valuation = this.getDataValuation();

    // Phase 1: Collect all arc operations (token consumption and production)
    const tokenDeltas = new Map(); // placeId -> delta (positive for production, negative for consumption)

    for (const transitionId of transitionsToFire) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === transitionId);
      const outgoingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.source === transitionId);

      // Handle incoming arcs (token consumption)
      for (const arc of incomingArcs) {
        const place = this.places.get(arc.source);
        if (!place) continue;

        if (arc.type === "regular") {
          const currentDelta = tokenDeltas.get(arc.source) || 0;
          tokenDeltas.set(arc.source, currentDelta - arc.weight);
        } else if (arc.type === "reset") {
          // Reset arcs set tokens to 0 (overrides any delta)
          tokenDeltas.set(arc.source, -place.tokens);
        }
      }

      // Handle outgoing arcs (token production)
      for (const arc of outgoingArcs) {
        const place = this.places.get(arc.target);
        if (!place) continue;

        const currentDelta = tokenDeltas.get(arc.target) || 0;
        tokenDeltas.set(arc.target, currentDelta + arc.weight);
      }
    }

    // Phase 2: Apply all token changes atomically
    for (const [placeId, delta] of tokenDeltas) {
      const place = this.places.get(placeId);
      if (!place) continue;

      place.tokens += delta;
      // Ensure tokens don't go negative (safety check)
      if (place.tokens < 0) place.tokens = 0;
      // Ensure we don't exceed capacity
      if (place.capacity !== null && place.tokens > place.capacity) {
        place.tokens = place.capacity;
      }
    }

    // Phase 3: Handle data updates for all fired transitions
    // Note: For synchronous semantics, we need to decide how to handle multiple postconditions
    // Option 1: Apply them sequentially in the order of transition IDs
    // Option 2: Compose them somehow
    // We'll use Option 1 for now
    for (const transitionId of transitionsToFire) {
      const transition = this.transitions.get(transitionId);
      if (!transition) continue;

      if (typeof transition.evaluatePostcondition === 'function') {
        try {
          const newValuation = await transition.evaluatePostcondition(this.getDataValuation());
          this.setDataValuation(newValuation);
        } catch (error) {
          console.error(`Error evaluating postcondition for transition ${transitionId}:`, error);
          // Continue with execution even if postcondition fails
        }
      }
    }

    return true;
  }

  /**
   * Convert the Data Petri Net to a JSON string
   * @returns {string} JSON representation of the net
   */
  toJSON() {
    return JSON.stringify({
      id: this.id,
      name: this.name,
      description: this.description,
      places: Array.from(this.places.values()),
      transitions: Array.from(this.transitions.values()),
      arcs: Array.from(this.arcs.values()),
      dataVariables: Array.from(this.dataVariables.values())
    });
  }

  /**
   * Create a Data Petri Net from a JSON string
   * @param {string} json - JSON representation of the net
   * @returns {DataPetriNet} The reconstructed Data Petri Net
   */
  static fromJSON(json) {
    const data = JSON.parse(json);
    const net = new DataPetriNet(data.id, data.name, data.description);

    data.places.forEach((placeData) => {
      const place = new Place(
        placeData.id,
        placeData.position,
        placeData.label,
        placeData.tokens,
        placeData.capacity,
        placeData.finalMarking || null
      );
      net.places.set(place.id, place);
    });

    data.transitions.forEach((transitionData) => {
      // Only create DataAwareTransition if it has precondition or postcondition
      const hasPrecondition = transitionData.precondition && transitionData.precondition.trim() !== "";
      const hasPostcondition = transitionData.postcondition && transitionData.postcondition.trim() !== "";
      
      // Detect silent transition: explicit silent flag or null/empty label
      const isSilent = transitionData.silent || !transitionData.label || transitionData.label.trim() === '';
      
      let transition;
      if (hasPrecondition || hasPostcondition) {
        transition = new DataAwareTransition(
          transitionData.id,
          transitionData.position,
          transitionData.label || '',
          transitionData.priority,
          transitionData.delay,
          transitionData.precondition || "",
          transitionData.postcondition || "",
          isSilent
        );
      } else {
        // Create regular transition if no pre/post conditions
        transition = new Transition(
          transitionData.id,
          transitionData.position,
          transitionData.label || '',
          transitionData.priority,
          transitionData.delay,
          isSilent
        );
      }
      net.transitions.set(transition.id, transition);
    });

    data.arcs.forEach((arcData) => {
      const arc = new Arc(
        arcData.id,
        arcData.source,
        arcData.target,
        arcData.weight,
        arcData.type,
        arcData.points,
        arcData.label
      );
      net.arcs.set(arc.id, arc);
    });

    if (data.dataVariables) {
      data.dataVariables.forEach((variableData) => {
        const variable = new DataVariable(
          variableData.id,
          variableData.name,
          variableData.type, // normalizeType is called in the constructor
          variableData.currentValue,
          variableData.description
        );
        net.dataVariables.set(variable.id, variable);
      });
    }

    return net;
  }

/**
   * Export the Data Petri Net to PNML format
   * @returns {string} PNML representation of the net
   */
  /**
   * Escapes XML special characters to prevent breaking XML structure
   * @param {string} str - The string to escape
   * @returns {string} The escaped string
   * @private
   */
  escapeXML(str) {
    if (str == null) return '';
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&apos;');
  }

  toPNML() {
    let pnml = `<?xml version="1.0" encoding="UTF-8"?>
<pnml>
   <net id="${this.escapeXML(this.id)}" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
      <name>
         <text>${this.escapeXML(this.name)}</text>
      </name>
      <source>
         <text>Generated by YAPNE - Yet Another Petri Net Editor</text>
      </source>
      <page id="n0">`;

    // Export places
    for (const [id, place] of this.places) {
      pnml += `
         <place id="${this.escapeXML(id)}">
            <name>
               <text>${this.escapeXML(place.label)}</text>
            </name>`;
      
      if (place.tokens > 0) {
        pnml += `
            <initialMarking>
               <text>${place.tokens}</text>
            </initialMarking>`;
      }
      
      if (place.capacity && place.capacity > 0) {
        pnml += `
            <capacity>
               <text>${place.capacity}</text>
            </capacity>`;
      }
      
      pnml += `
         </place>`;
    }

    // Export transitions
    for (const [id, transition] of this.transitions) {
      // Build guard attribute
      let guardAttr = '';
      if (transition.precondition || transition.postcondition) {
        const parts = [];
        if (transition.precondition && transition.precondition.trim()) {
          parts.push(`pre: ${this.escapeXML(transition.precondition.trim())}`);
        }
        if (transition.postcondition && transition.postcondition.trim()) {
          parts.push(`post: ${this.escapeXML(transition.postcondition.trim())}`);
        }
        if (parts.length > 0) {
          guardAttr = ` guard="${parts.join(' | ')}"`;
        }
      }

      pnml += `
         <transition${guardAttr} id="${this.escapeXML(id)}">
            <name>
               <text>${this.escapeXML(transition.label)}</text>
            </name>`;

      // Add writeVariable elements for variables modified in postcondition
      if (transition.postcondition && transition.postcondition.trim()) {
        const modifiedVars = this.extractModifiedVariables(transition.postcondition);
        for (const varName of modifiedVars) {
          pnml += `
            <writeVariable>${this.escapeXML(varName)}</writeVariable>`;
        }
      }
      
      // Add silent transition attribute in toolspecific section
      if (transition.silent) {
        pnml += `
            <toolspecific tool="YAPNE" version="1.0">
               <silent>true</silent>
            </toolspecific>`;
      }

      pnml += `
         </transition>`;
    }

    // Export arcs
    for (const [id, arc] of this.arcs) {
      pnml += `
         <arc id="${this.escapeXML(id)}" source="${this.escapeXML(arc.source)}" target="${this.escapeXML(arc.target)}">
            <arctype>
               <text>${this.escapeXML(arc.type || 'normal')}</text>
            </arctype>`;
      
      if (arc.weight > 1) {
        pnml += `
            <inscription>
               <text>${this.escapeXML(arc.weight)}</text>
            </inscription>`;
      }
      
      pnml += `
         </arc>`;
    }

    pnml += `
      </page>`;

    // Export variables section
    if (this.dataVariables.size > 0) {
      pnml += `
      <variables>`;
      
      for (const [id, variable] of this.dataVariables) {
        // Determine min/max values based on type
        let minValue = '0';
        let maxValue = '100000';
        let javaType = 'java.lang.Double';
        
        switch (variable.type) {
          case 'int':
            javaType = 'java.lang.Integer';
            break;
          case 'real':
            javaType = 'java.lang.Double';
            maxValue = '100000.0';
            break;
          case 'bool':
            javaType = 'java.lang.Boolean';
            maxValue = '100000';
            break;
        }

        pnml += `
         <variable maxValue="${this.escapeXML(maxValue)}" minValue="${this.escapeXML(minValue)}" type="${this.escapeXML(javaType)}">
            <name>${this.escapeXML(variable.name)}</name>
         </variable>`;
      }
      
      pnml += `
      </variables>`;
    }

    pnml += `
   </net>
</pnml>`;

    return pnml;
  }

  /**
   * Extract variable names that are modified in a postcondition expression
   * @param {string} postcondition - The postcondition expression
   * @returns {Array<string>} Array of variable names that are modified
   * @private
   */
  extractModifiedVariables(postcondition) {
    try {
      const { ast } = parse(postcondition, { isPostcondition: true });
      return Array.from(getWrittenVariables(ast));
    } catch {
      // Fallback to regex if parsing fails
      const modifiedVars = new Set();
      const primeMatches = postcondition.match(/([a-zA-Z_][a-zA-Z0-9_]*)'/g);
      if (primeMatches) {
        primeMatches.forEach(match => modifiedVars.add(match.slice(0, -1)));
      }
      return Array.from(modifiedVars);
    }
  }
}

export { DataVariable, DataAwareTransition, DataPetriNet };