class DataPetriNetAPI extends PetriNetAPI {
  /**
   * Create a new Data Petri Net API
   * @param {string} id - Unique identifier for the net
   * @param {string} name - Name of the net
   * @param {string} description - Description of the net
   */
  constructor(id, name, description) {
    super(id, name, description);

    this.petriNet = new DataPetriNet(
      id || this.generateUUID(),
      name || "New Data Petri Net",
      description || ""
    );
  }

  /**
   * Create a new data-aware transition
   * @param {number} x - X coordinate position
   * @param {number} y - Y coordinate position
   * @param {string} label - Label for the transition
   * @param {string} precondition - Guard condition as a JavaScript expression
   * @param {string} postcondition - Data manipulation as a JavaScript expression
   * @returns {string} ID of the created transition
   */
  createDataTransition(x, y, label, precondition = "", postcondition = "") {
    const id = this.generateUUID();
    const transition = new DataAwareTransition(
      id,
      { x, y },
      label || `T${this.petriNet.transitions.size + 1}`,
      1, // default priority
      0, // default delay
      precondition,
      postcondition
    );
    this.petriNet.addTransition(transition);
    if (this.editor) this.editor.render();
    return id;
  }

  /**
   * Create a new data variable
   * @param {string} name - Name of the variable
   * @param {string} type - Data type ('int', 'float', 'string', 'boolean')
   * @param {*} initialValue - Initial value
   * @param {string} description - Optional description
   * @returns {string} ID of the created variable
   */
  createDataVariable(name, type, initialValue = null, description = "") {
    const id = this.generateUUID();
    const variable = new DataVariable(id, name, type, initialValue, description);
    this.petriNet.addDataVariable(variable);
    return id;
  }

  /**
   * Get a data variable by ID
   * @param {string} id - ID of the variable
   * @returns {DataVariable|undefined} The data variable, if found
   */
  getDataVariable(id) {
    return this.petriNet.getDataVariable(id);
  }

  /**
   * Remove a data variable
   * @param {string} id - ID of the variable to remove
   * @returns {boolean} Whether the variable was removed
   */
  removeDataVariable(id) {
    return this.petriNet.removeDataVariable(id);
  }

  /**
   * Get all data variables
   * @returns {Map<string, DataVariable>} Map of variable IDs to DataVariable objects
   */
  getDataVariables() {
    return this.petriNet.dataVariables;
  }

  /**
   * Update a data variable value
   * @param {string} id - ID of the variable
   * @param {*} value - New value
   * @returns {boolean} Whether the update was successful
   */
  updateDataVariableValue(id, value) {
    const variable = this.petriNet.getDataVariable(id);
    if (!variable) return false;

    const success = variable.setValue(value);

    // Update enabled transitions
    this.petriNet.updateEnabledTransitions();

    // Render if editor is available
    if (this.editor) this.editor.render();

    return success;
  }

  /**
   * Set precondition for a transition
   * @param {string} transitionId - ID of the transition
   * @param {string} precondition - Guard condition as a JavaScript expression
   * @returns {boolean} Whether the update was successful
   */
  setTransitionPrecondition(transitionId, precondition) {
    const transition = this.petriNet.transitions.get(transitionId);
    if (!transition || typeof transition.evaluatePrecondition !== 'function') return false;

    transition.precondition = precondition;

    // Update enabled transitions
    this.petriNet.updateEnabledTransitions();

    // Render if editor is available
    if (this.editor) this.editor.render();

    return true;
  }

  /**
   * Set postcondition for a transition
   * @param {string} transitionId - ID of the transition
   * @param {string} postcondition - Data manipulation as a JavaScript expression
   * @returns {boolean} Whether the update was successful
   */
  setTransitionPostcondition(transitionId, postcondition) {
    const transition = this.petriNet.transitions.get(transitionId);
    if (!transition || typeof transition.evaluatePostcondition !== 'function') return false;

    transition.postcondition = postcondition;

    // Render if editor is available
    if (this.editor) this.editor.render();

    return true;
  }

  /**
   * Get the current data valuation
   * @returns {Object} Map of variable names to current values
   */
  getDataValuation() {
    return this.petriNet.getDataValuation();
  }

  /**
   * Reset all data variables to their initial values
   */
  resetDataVariables() {
    for (const [, variable] of this.petriNet.dataVariables) {
      if (typeof variable.reset === 'function') {
        variable.reset();
      }
    }

    // Update enabled transitions
    this.petriNet.updateEnabledTransitions();

    // Render if editor is available
    if (this.editor) this.editor.render();
  }

  /**
   * Fire a transition (ASYNC)
   * @param {string} id - ID of the transition to fire
   * @returns {Promise<boolean>} Whether the transition fired successfully
   */
  async fireTransition(id) {
    const success = await this.petriNet.fireTransition(id);
    if (success && this.editor) this.editor.render();
    return success;
  }

  /**
   * Auto-fire enabled transitions with a maximum number of steps (ASYNC)
   * @param {number} maxSteps - Maximum number of steps to execute
   * @returns {Promise<number>} Number of steps executed
   */
  async autoFireEnabledTransitions(maxSteps = 10) {
    let steps = 0;
    let firedAny = false;

    do {
      firedAny = false;

      // Update enabled transitions
      this.petriNet.updateEnabledTransitions();
      const enabledTransitions = [];

      for (const [id, transition] of this.petriNet.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }

      // Sort by priority
      enabledTransitions.sort((a, b) => {
        const transA = this.petriNet.transitions.get(a);
        const transB = this.petriNet.transitions.get(b);
        return (transB?.priority || 0) - (transA?.priority || 0);
      });

      // Fire the highest priority transition
      if (enabledTransitions.length > 0) {
        firedAny = await this.petriNet.fireTransition(enabledTransitions[0]);
        if (firedAny) steps++;
      }
    } while (firedAny && steps < maxSteps);

    if (this.editor) this.editor.render();
    return steps;
  }

  /**
   * Override the parent method to ensure we create a DataPetriNet
   */
  static importFromJSON(json) {
    try {
      const petriNet = DataPetriNet.fromJSON(json);
      const api = new DataPetriNetAPI();
      api.petriNet = petriNet;
      return api;
    } catch (error) {
      console.error("Error importing Data Petri Net from JSON:", error);
      return null;
    }
  }

  /**
   * Export data variables to JSON
   * @returns {string} JSON representation of data variables
   */
  exportDataVariablesToJSON() {
    return JSON.stringify(Array.from(this.petriNet.dataVariables.values()));
  }

  /**
   * Import data variables from JSON
   * @param {string} json - JSON representation of data variables
   * @returns {boolean} Whether the import was successful
   */
  importDataVariablesFromJSON(json) {
    try {
      const variables = JSON.parse(json);

      // Clear existing variables
      this.petriNet.dataVariables.clear();

      // Add new variables
      for (const varData of variables) {
        // Handle legacy 'number' type by converting to 'int'
        let variableType = varData.type;
        if (variableType === 'number') {
          variableType = 'int';
        }
        
        const variable = new DataVariable(
          varData.id || this.generateUUID(),
          varData.name,
          variableType,
          varData.currentValue,
          varData.description || ""
        );
        this.petriNet.addDataVariable(variable);
      }

      // Update enabled transitions
      this.petriNet.updateEnabledTransitions();

      // Render if editor is available
      if (this.editor) this.editor.render();

      return true;
    } catch (error) {
      console.error("Error importing data variables:", error);
      return false;
    }
  }

  /**
   * Validate a precondition expression
   * @param {string} expression - Precondition expression to validate
   * @param {Array<string>} variableNames - Available variable names
   * @returns {Object} Validation result {valid: boolean, error: string}
   */
  validatePrecondition(expression, variableNames = []) {
    if (!expression.trim()) {
      return { valid: true, error: null }; // Empty expression is valid
    }

    try {
      // Create dummy valuation
      const dummyValuation = {};
      variableNames.forEach(name => {
        dummyValuation[name] = 0; // Use 0 as a safe default for validation
      });

      // Create evaluator function
      const functionBody = `return ${expression};`;
      const evaluator = new Function(...variableNames, functionBody);

      // Test evaluation
      evaluator(...variableNames.map(name => dummyValuation[name]));

      return { valid: true, error: null };
    } catch (error) {
      return {
        valid: false,
        error: `Invalid expression: ${error.message}`
      };
    }
  }

  /**
   * Validate a postcondition expression
   * @param {string} expression - Postcondition expression to validate
   * @param {Array<string>} variableNames - Available variable names
   * @returns {Object} Validation result {valid: boolean, error: string}
   */
  validatePostcondition(expression, variableNames = []) {
    if (!expression.trim()) {
      return { valid: true, error: null }; // Empty expression is valid
    }
  
    // Split into statements
    const statements = expression.split(';');
    
    for (const statement of statements) {
      if (!statement.trim()) continue;
      
      // Check for assignment pattern
      const assignMatch = statement.trim().match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)/);
      
      if (assignMatch) {
        // Direct assignment validation
        const [, variableName, rightHandSide] = assignMatch;
        
        // Check if variable exists
        if (!variableNames.includes(variableName)) {
          return {
            valid: false,
            error: `Unknown variable: ${variableName}`
          };
        }
        
        // Validate right-hand side expression
        try {
          // Create dummy valuation
          const dummyValuation = {};
          variableNames.forEach(name => {
            dummyValuation[name] = 0; // Use 0 as a safe default for validation
          });
          
          // Process expression (remove primes)
          let processedExpression = rightHandSide;
          variableNames.forEach(name => {
            const regex = new RegExp(`${name}'`, 'g');
            processedExpression = processedExpression.replace(regex, name);
          });
          
          // Create and test evaluator
          const evaluator = new Function(...variableNames, `return (${processedExpression});`);
          evaluator(...variableNames.map(name => dummyValuation[name]));
        } catch (error) {
          return { 
            valid: false, 
            error: `Invalid expression in "${statement}": ${error.message}` 
          };
        }
      } else {
        // Check for constraint pattern
        const primedVarsUsed = variableNames.filter(name => 
          statement.match(new RegExp(`${name}'`, 'g'))
        );
        
        if (primedVarsUsed.length === 0) {
          return {
            valid: false,
            error: `Statement "${statement}" is not a valid assignment or constraint. It should either be an assignment (x' = expr) or a constraint involving primed variables (x' > 0).`
          };
        }
        
        // Validate constraint expression
        try {
          // Create dummy valuation
          const dummyValuation = {};
          variableNames.forEach(name => {
            dummyValuation[name] = 0; // Use 0 as a safe default for validation
          });
          
          const dummyTestValuation = { ...dummyValuation };
          
          // Process expression for validation
          let processedExpression = statement;
          variableNames.forEach(name => {
            const regex = new RegExp(`${name}'`, 'g');
            processedExpression = processedExpression.replace(regex, `dummyTestValuation["${name}"]`);
          });
          
          // Create and test evaluator
          const evaluator = new Function(
            ...variableNames,
            'dummyTestValuation',
            `return (${processedExpression});`
          );
          
          evaluator(...variableNames.map(name => dummyValuation[name]), dummyTestValuation);
        } catch (error) {
          return {
            valid: false,
            error: `Invalid constraint in "${statement}": ${error.message}`
          };
        }
      }
    }
    
    return { valid: true, error: null };
  }

  /**
   * Get simplified help/docs for data expressions
   * @returns {Object} Documentation for preconditions and postconditions
   */
  getDataExpressionHelp() {
    return {
      precondition: `
  Precondition (Guard) Help:
  - JavaScript expression that evaluates to true/false
  - Determines when a transition is enabled
  - Example: x > 5 && y === "ready"
  - Available variables: ${Array.from(this.petriNet.dataVariables.values()).map(v => v.name).join(', ')}
      `,
      postcondition: `
  Postcondition (Data Update) Help:
  - Defines how variables change when transition fires
  - Two supported formats:
    1. Direct assignment: variable' = expression;
       Example: x' = x + 1; y' = "done";
    
    2. Constraint-based random assignment: expression containing variable';
       Example: x' > 0 && x' < x*2;
       (generates a random value satisfying the constraints)
       
  - Use semicolons to separate multiple assignments/constraints
  - Direct assignments have priority over constraints
  - Available variables: ${Array.from(this.petriNet.dataVariables.values()).map(v => v.name).join(', ')}
  
  Data Types:
  - int: Whole numbers (42, -7, 0)
  - float: Decimal numbers (3.14, -2.5, 1.0)
  - string: Text values ("hello", "processing")
  - boolean: true or false values
      `
    };
  }
  
}