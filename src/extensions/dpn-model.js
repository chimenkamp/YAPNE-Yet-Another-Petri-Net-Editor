
/**
 * Represents a data variable in a Data Petri Net
 */
class DataVariable {
    /**
     * Create a new data variable
     * @param {string} id - Unique identifier for the variable
     * @param {string} name - Human-readable name of the variable
     * @param {string} type - Data type ('number', 'string', 'boolean')
     * @param {*} initialValue - Initial value of the variable
     * @param {string} description - Optional description of the variable
     */
    constructor(id, name, type, initialValue = null, description = "") {
      this.id = id;
      this.name = name;
      this.type = type;
      this.currentValue = initialValue;
      this.description = description;
    }
  
    /**
     * Get the current value with proper type conversion
     * @returns {*} The current value with the correct type
     */
    getValue() {
      if (this.currentValue === null) return null;
      
      // Ensure the value has the correct type
      switch (this.type) {
        case 'number':
          return Number(this.currentValue);
        case 'boolean':
          return Boolean(this.currentValue);
        case 'string':
        default:
          return String(this.currentValue);
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
          case 'number':
            this.currentValue = Number(value);
            break;
          case 'boolean':
            this.currentValue = Boolean(value);
            break;
          case 'string':
          default:
            this.currentValue = String(value);
            break;
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
     */
    constructor(id, position, label = "", priority = 1, delay = 0, precondition = "", postcondition = "") {
      super(id, position, label, priority, delay);
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
        // Create a sandbox function to evaluate the expression safely
        const variableNames = Object.keys(valuation);
        const variableValues = variableNames.map(name => valuation[name]);
        const functionBody = `return ${this.precondition};`;
        const evaluator = new Function(...variableNames, functionBody);
        
        // Execute the precondition with the current valuation
        return Boolean(evaluator(...variableValues));
      } catch (error) {
        console.error(`Error evaluating precondition for transition ${this.id}:`, error);
        console.error(`Precondition: ${this.precondition}`);
        console.error(`Valuation:`, valuation);
        return false; // On error, disable the transition for safety
      }
    }
  
    /**
     * Evaluate the postcondition and compute the new data valuation
     * @param {Object} valuation - Map of variable names to current values
     * @returns {Object} New valuation after applying the postcondition
     */
    evaluatePostcondition(valuation) {
      if (!this.postcondition || this.postcondition.trim() === "") {
        return valuation; // No postcondition means no changes
      }
  
      try {
        // Create copies of values to avoid modifying the original valuation
        const newValuation = { ...valuation };
        
        // Handle primed variables (V')
        // This approach evaluates each assignment in the postcondition
        const assignments = this.postcondition.split(';');
        
        for (const assignment of assignments) {
          if (!assignment.trim()) continue;
          
          // Parse the assignment (format: "x' = expression")
          const match = assignment.trim().match(/([a-zA-Z_][a-zA-Z0-9_]*)'s*=s*(.+)/);
          if (!match) continue;
          
          const [, variableName, expression] = match;
          
          // Skip if variable doesn't exist in the valuation
          if (!(variableName in valuation)) continue;
          
          // Create function to evaluate the right-hand expression
          const expressionFunction = this.createExpressionEvaluator(expression, Object.keys(valuation));
          
          // Execute the expression with current valuation
          const newValue = expressionFunction(...Object.values(valuation));
          
          // Update the new valuation
          newValuation[variableName] = newValue;
        }
        
        return newValuation;
      } catch (error) {
        console.error(`Error evaluating postcondition for transition ${this.id}:`, error);
        console.error(`Postcondition: ${this.postcondition}`);
        console.error(`Valuation:`, valuation);
        return valuation; // On error, keep the original valuation
      }
    }
  
    /**
     * Create a function to evaluate an expression
     * @param {string} expression - The expression to evaluate
     * @param {Array<string>} variables - Array of variable names
     * @returns {Function} A function that evaluates the expression
     * @private
     */
    createExpressionEvaluator(expression, variables) {
      // Replace any primed variables in the expression with non-primed versions
      let processedExpression = expression;
      variables.forEach(name => {
        const regex = new RegExp(`${name}'`, 'g');
        processedExpression = processedExpression.replace(regex, name);
      });
      
      // Create and return the evaluator function
      return new Function(...variables, `return (${processedExpression});`);
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
      // First perform the standard token-based enabling check
      super.updateEnabledTransitions();
      
      // Then further restrict based on data preconditions
      const valuation = this.getDataValuation();
      
      for (const [id, transition] of this.transitions) {
        if (transition.isEnabled) {
          // If the transition has a precondition method, evaluate it
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
      // First check token-based enabling
      const isEnabledByTokens = super.isTransitionEnabled(transitionId);
      
      if (!isEnabledByTokens) return false;
      
      // Then check data precondition
      const transition = this.transitions.get(transitionId);
      if (!transition) return false;
      
      // If this is a data-aware transition, evaluate its precondition
      if (typeof transition.evaluatePrecondition === 'function') {
        const valuation = this.getDataValuation();
        return transition.evaluatePrecondition(valuation);
      }
      
      return true;
    }
  
    /**
     * Override the parent fireTransition method to handle data updates
     * @param {string} transitionId - ID of the transition to fire
     * @returns {boolean} Whether the transition fired successfully
     */
    fireTransition(transitionId) {
      if (!this.isTransitionEnabled(transitionId)) {
        return false;
      }
  
      const transition = this.transitions.get(transitionId);
      if (!transition) return false;
  
      // Step 1: Get the current data valuation before firing
      const valuation = this.getDataValuation();
  
      // Step 2: Collect incoming and outgoing arcs
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === transitionId);
      const outgoingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.source === transitionId);
  
      // Step 3: Remove tokens from input places
      for (const arc of incomingArcs) {
        const place = this.places.get(arc.source);
        if (!place) continue;
  
        if (arc.type === "regular") {
          place.removeTokens(arc.weight);
        } else if (arc.type === "reset") {
          place.tokens = 0;
        }
        // Inhibitor and read arcs don't remove tokens
      }
  
      // Step 4: Add tokens to output places
      for (const arc of outgoingArcs) {
        const place = this.places.get(arc.target);
        if (!place) continue;
  
        place.addTokens(arc.weight);
      }
  
      // Step 5: Update data variables based on postcondition (if it's a data-aware transition)
      if (typeof transition.evaluatePostcondition === 'function') {
        const newValuation = transition.evaluatePostcondition(valuation);
        this.setDataValuation(newValuation);
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
  
      // Recreate places
      data.places.forEach((placeData) => {
        const place = new Place(
          placeData.id,
          placeData.position,
          placeData.label,
          placeData.tokens,
          placeData.capacity
        );
        net.places.set(place.id, place);
      });
  
      // Recreate transitions
      data.transitions.forEach((transitionData) => {
        const transition = new DataAwareTransition(
          transitionData.id,
          transitionData.position,
          transitionData.label,
          transitionData.priority,
          transitionData.delay,
          transitionData.precondition || "",
          transitionData.postcondition || ""
        );
        net.transitions.set(transition.id, transition);
      });
  
      // Recreate arcs
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
  
      // Recreate data variables
      if (data.dataVariables) {
        data.dataVariables.forEach((variableData) => {
          const variable = new DataVariable(
            variableData.id,
            variableData.name,
            variableData.type,
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
    toPNML() {
      let pnml = `<?xml version="1.0" encoding="UTF-8"?>
  <pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
    <net id="${this.id}" type="http://www.pnml.org/version-2009/grammar/ptnet">
      <name>
        <text>${this.name}</text>
      </name>
      <description>
        <text>${this.description}</text>
      </description>`;
  
      // Places
      for (const [id, place] of this.places) {
        pnml += `
      <place id="${id}">
        <name>
          <text>${place.label}</text>
        </name>
        <initialMarking>
          <text>${place.tokens}</text>
        </initialMarking>
        <graphics>
          <position x="${place.position.x}" y="${place.position.y}"/>
        </graphics>
      </place>`;
      }
  
      // Transitions
      for (const [id, transition] of this.transitions) {
        pnml += `
      <transition id="${id}">
        <name>
          <text>${transition.label}</text>
        </name>
        <graphics>
          <position x="${transition.position.x}" y="${transition.position.y}"/>
        </graphics>`;
        
        // Add data-related attributes for data-aware transitions
        if (transition.precondition || transition.postcondition) {
          pnml += `
        <dataGuard>
          <text>${transition.precondition || ""}</text>
        </dataGuard>
        <dataUpdate>
          <text>${transition.postcondition || ""}</text>
        </dataUpdate>`;
        }
        
        pnml += `
      </transition>`;
      }
  
      // Arcs
      for (const [id, arc] of this.arcs) {
        pnml += `
      <arc id="${id}" source="${arc.source}" target="${arc.target}">
        <inscription>
          <text>${arc.weight}</text>
        </inscription>`;
  
        if (arc.type !== "regular") {
          pnml += `
        <arctype>
          <text>${arc.type}</text>
        </arctype>`;
        }
  
        if (arc.points.length > 0) {
          pnml += `
        <graphics>`;
          for (const point of arc.points) {
            pnml += `
          <position x="${point.x}" y="${point.y}"/>`;
          }
          pnml += `
        </graphics>`;
        }
  
        pnml += `
      </arc>`;
      }
  
      // Data variables
      pnml += `
      <dataVariables>`;
      for (const [id, variable] of this.dataVariables) {
        pnml += `
        <variable id="${id}">
          <name>
            <text>${variable.name}</text>
          </name>
          <type>
            <text>${variable.type}</text>
          </type>
          <initialValue>
            <text>${variable.currentValue !== null ? variable.currentValue : ""}</text>
          </initialValue>
          <description>
            <text>${variable.description}</text>
          </description>
        </variable>`;
      }
      pnml += `
      </dataVariables>`;
  
      pnml += `
    </net>
  </pnml>`;
  
      return pnml;
    }
  }