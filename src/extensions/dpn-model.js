import { Transition, PetriNet, Place, Arc } from '../petri-net-simulator.js';
import { parse } from './guard-language/guard-parser.js';
import { evaluatePrecondition as evalPre, evaluatePostcondition as evalPost, checkConstraint, getWrittenVariables, getPostconditionUpdates, EvaluationDomainError } from './guard-language/guard-evaluator.js';
import { addSuccessor, equalValuations, getObservedSuccessors, isDataValue, selectSuccessor, validateDiscoveryContract, validateFinalMarkings } from './discovery-contract.js';
import { assessGuardCompatibility, hasQuantifier } from './guard-language/guard-compatibility.js';

/** A valid guard requires an execution method unavailable in native simulation. */
export class UnsupportedNativeGuardError extends Error {}

/**
 * Represents a data variable in a Data Petri Net
 */
class DataVariable {
  /**
   * Create a new data variable
   * @param {string} id - Unique identifier for the variable
   * @param {string} name - Human-readable name of the variable
   * @param {string} type - Data type ('int'|'integer'|'bool'|'boolean'|'real'|'data')
   * @param {*} initialValue - Initial value of the variable
   * @param {string} description - Optional description of the variable
   */
  constructor(id, name, type, initialValue = undefined, description = "") {
    this.id = id;
    this.name = name;
    this.type = DataVariable.normalizeType(type);
    this.initialValue = initialValue === undefined && this.type !== 'data' ? null : initialValue;
    this.currentValue = this.initialValue;
    this.description = description;
  }

  /**
   * Normalize type aliases to canonical forms
   * @param {string} type - Raw type string
   * @returns {string} Normalized type: 'int', 'bool', 'real', or 'data'
   */
  static normalizeType(type) {
    const t = (type || 'real').toLowerCase();
    if (t === 'data') return 'data';
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
    if (this.type === 'data') return this.currentValue;
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
        case 'data':
          if (value !== undefined && !isDataValue(value)) throw new Error('Not a finite JSON scalar');
          this.currentValue = value;
          break;
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

  /** Preserve an absent initial state separately from a later current value.
   * @returns {Object} JSON-serializable variable state.
   */
  toJSON() {
    return { ...this, initialValuePresent: this.initialValue !== undefined };
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

  /** Return all distinct native successors permitted by this transition.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @returns {import('./discovery-contract.js').Valuation[]}
   */
  getSuccessorValuations(valuation) {
    const contract = this.discoveryContract;
    const successors = contract ? getObservedSuccessors(contract, valuation) : [];
    if (!contract || contract.generalized) {
      const candidate = this.getDeterministicSuccessor(valuation);
      if (candidate !== null) addSuccessor(successors, candidate);
    }
    return successors;
  }

  /** Evaluate the symbolic branch using simultaneous assignments and its full predicate.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @returns {import('./discovery-contract.js').Valuation | null}
   */
  getDeterministicSuccessor(valuation) {
    try {
      const pre = parse(this.precondition || '', { isPostcondition: false }).ast;
      const post = parse(this.postcondition || '', { isPostcondition: true }).ast;
      if (hasQuantifier(pre) || hasQuantifier(post)) {
        throw new UnsupportedNativeGuardError('Quantified guards cannot be executed in native simulation.');
      }
      if (!evalPre(pre, valuation)) return null;
      const updates = getPostconditionUpdates(post);
      if ([...getWrittenVariables(post)].some(name => !updates.assignments.has(name))) {
        throw new UnsupportedNativeGuardError('Native simulation requires deterministic assignments for every written variable; this postcondition requires constraint sampling.');
      }
      const { assignments } = evalPost(post, valuation);
      if (this.discoveryContract && [...assignments.values()].some(value => typeof value !== 'number' || !Number.isFinite(value))) return null;
      const candidate = { ...valuation, ...Object.fromEntries(assignments) };
      return post === null || checkConstraint(post, valuation, candidate) ? candidate : null;
    } catch (error) {
      if (error instanceof EvaluationDomainError) return null;
      throw error;
    }
  }

  /** Check whether at least one complete data successor is available.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @returns {boolean}
   */
  evaluatePrecondition(valuation) {
    return this.getSuccessorValuations(valuation).length > 0;
  }

  /** Select one valid successor without mutating the current data state.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @param {() => number} random
   * @returns {Promise<import('./discovery-contract.js').Valuation>}
   */
  async evaluatePostcondition(valuation, random = Math.random) {
    return selectSuccessor(this.getSuccessorValuations(valuation), random);
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
  constructor(id, name = "New Data Petri Net", description = "", options = {}) {
    super(id, name, description, options);
    this.dataVariables = new Map(); // Map of data variable ID -> DataVariable object
    /** @type {Record<string, number>[]} */
    this.finalMarkings = [];
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
   * @param {boolean} useSourceNames - Use original Discovery labels for exported events.
   * @returns {Object} The current data valuation
   */
  getDataValuation(useSourceNames = false) {
    return Object.fromEntries([...this.dataVariables.values()]
      .filter(variable => variable.getValue() !== undefined)
      .map(variable => [useSourceNames ? variable.sourceName || variable.name : variable.name, variable.getValue()]));
  }

  /** Validate a candidate without changing any variable.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @returns {void}
   */
  validateDataValuation(valuation) {
    const variables = new Map([...this.dataVariables.values()].map(variable => [variable.name, variable]));
    for (const [name, value] of Object.entries(valuation)) {
      const variable = variables.get(name);
      if (!variable) throw new Error(`Undeclared data variable '${name}'.`);
      const valid = variable.type === 'data' ? isDataValue(value) : value === null ||
        (variable.type === 'bool' ? typeof value === 'boolean' :
          typeof value === 'number' && Number.isFinite(value) && (variable.type !== 'int' || Number.isInteger(value)));
      if (!valid) throw new Error(`Value for '${name}' does not satisfy its ${variable.type} type.`);
    }
  }

  /** Apply a validated state; replacement also preserves absent Discovery values.
   * @param {import('./discovery-contract.js').Valuation} valuation
   * @param {boolean} replace
   * @returns {void}
   */
  setDataValuation(valuation, replace = false) {
    this.validateDataValuation(valuation);
    for (const variable of this.dataVariables.values()) {
      if (Object.hasOwn(valuation, variable.name)) {
        variable.currentValue = valuation[variable.name];
      } else if (replace && variable.type === 'data') {
        variable.currentValue = undefined;
      }
    }
  }

  /** Keep unsupported native guards visible for editing and formal analysis.
   * @returns {void}
   */
  updateEnabledTransitions() {
    for (const [id, transition] of this.transitions) {
      transition.nativeExecutionError = null;
      try {
        transition.isEnabled = this.isTransitionEnabled(id);
      } catch (error) {
        if (!(error instanceof UnsupportedNativeGuardError)) throw error;
        transition.isEnabled = false;
        transition.nativeExecutionError = error.message;
      }
    }
  }

  /** Reject unsupported native models before simulation can report a false deadlock.
   * @returns {void}
   */
  assertNativeExecutionSupported() {
    const profile = assessGuardCompatibility(this).simulation;
    if (!profile.supported) throw new UnsupportedNativeGuardError(profile.reasons.join('\n'));
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
   * @param {() => number} random - Configured source for native successor choices.
   * @returns {Promise<boolean>} Whether the transition fired successfully
   */
  async fireTransition(transitionId, random = Math.random) {
    if (!this.isTransitionEnabled(transitionId)) return false;
    const transition = this.transitions.get(transitionId);
    const valuation = this.getDataValuation();
    const nextValuation = typeof transition.evaluatePostcondition === 'function'
      ? await transition.evaluatePostcondition(valuation, random) : valuation;
    this.validateDataValuation(nextValuation);
    if (!equalValuations(valuation, this.getDataValuation())) return false;
    if (!super.fireTransition(transitionId)) return false;
    this.setDataValuation(nextValuation, true);
    return true;
  }

  areTransitionsInConflict(trans1Id, trans2Id) {
    return super.areTransitionsInConflict(trans1Id, trans2Id);
  }

  resolveConflicts(enabledTransitionIds) {
    return super.resolveConflicts(enabledTransitionIds);
  }

  /**
   * Fire multiple transitions simultaneously in one atomic step (synchronous step semantics)
   * All transitions that are enabled at the start of the step will fire together
   * @param {Array<string>} transitionIds - Array of transition IDs to fire
   * @param {() => number} random - Configured source for native successor choices.
   * @returns {Promise<boolean>} - True if at least one transition was successfully fired
   */
  async fireTransitionsSynchronously(transitionIds, random = Math.random) {
    const transitionsToFire = this.planSynchronousTransitions(transitionIds);
    if (transitionsToFire.length === 0) return false;
    if (transitionsToFire.length > 1 && transitionsToFire.some(id => this.transitions.get(id).discoveryContract)) {
      throw new Error('Discovery contracts use interleaving execution; fire one transition at a time.');
    }
    const initialValuation = this.getDataValuation();
    let valuation = initialValuation;
    for (const id of transitionsToFire) {
      const transition = this.transitions.get(id);
      if (typeof transition.evaluatePostcondition === 'function') {
        valuation = await transition.evaluatePostcondition(valuation, random);
        this.validateDataValuation(valuation);
      }
    }
    if (!equalValuations(initialValuation, this.getDataValuation())) return false;
    if (!super.fireTransitionsSynchronously(transitionsToFire)) return false;
    this.setDataValuation(valuation, true);
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
      arcSemantics: this.getArcSemantics(),
      finalMarkings: this.finalMarkings,
      discoveryMetadata: this.discoveryMetadata,
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
    const net = new DataPetriNet(data.id, data.name, data.description, {
      arcSemantics: data.arcSemantics
    });

    net.finalMarkings = data.finalMarkings || [];
    net.discoveryMetadata = data.discoveryMetadata;

    data.places.forEach((placeData) => {
      const place = new Place(
        placeData.id,
        placeData.position,
        placeData.label,
        placeData.tokens,
        placeData.capacity,
        placeData.finalMarking ?? null
      );
      net.places.set(place.id, place);
    });
    validateFinalMarkings(net.finalMarkings, new Set(net.places.keys()));

    data.transitions.forEach((transitionData) => {
      // Only create DataAwareTransition if it has precondition or postcondition
      const hasPrecondition = transitionData.precondition && transitionData.precondition.trim() !== "";
      const hasPostcondition = transitionData.postcondition && transitionData.postcondition.trim() !== "";
      
      // Detect silent transition: explicit silent flag or null/empty label
      const isSilent = transitionData.silent || !transitionData.label || transitionData.label.trim() === '';
      
      let transition;
      if (hasPrecondition || hasPostcondition || transitionData.discoveryContract) {
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
      if (transitionData.discoveryContract) {
        validateDiscoveryContract(transitionData.discoveryContract);
        transition.discoveryContract = transitionData.discoveryContract;
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
          variableData.initialValuePresent === false ? undefined :
            Object.hasOwn(variableData, 'initialValue') ? variableData.initialValue : variableData.currentValue,
          variableData.description
        );
        if (Object.hasOwn(variableData, 'currentValue')) variable.currentValue = variableData.currentValue;
        variable.sourceName = variableData.sourceName;
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
      <toolspecific tool="YAPNE" version="2">
         <model-json>${this.escapeXML(this.toJSON())}</model-json>
      </toolspecific>
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
          case 'data':
            javaType = 'java.lang.Object';
            break;
          case 'bool':
            javaType = 'java.lang.Boolean';
            maxValue = '100000';
            break;
        }

        const bounds = variable.type === 'data' ? '' : ` maxValue="${this.escapeXML(maxValue)}" minValue="${this.escapeXML(minValue)}"`;
        pnml += `
         <variable${bounds} type="${this.escapeXML(javaType)}">
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
