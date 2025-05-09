

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
   * @param {string} type - Data type ('number', 'string', 'boolean')
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


    this.petriNet.updateEnabledTransitions();


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


    this.petriNet.updateEnabledTransitions();


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


    this.petriNet.updateEnabledTransitions();


    if (this.editor) this.editor.render();
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


      this.petriNet.dataVariables.clear();


      for (const varData of variables) {
        const variable = new DataVariable(
          varData.id || this.generateUUID(),
          varData.name,
          varData.type,
          varData.currentValue,
          varData.description || ""
        );
        this.petriNet.addDataVariable(variable);
      }


      this.petriNet.updateEnabledTransitions();


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

      const dummyValuation = {};
      variableNames.forEach(name => {
        dummyValuation[name] = 0; // Use 0 as a safe default for validation
      });


      const functionBody = `return ${expression};`;
      const evaluator = new Function(...variableNames, functionBody);


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
  

    const statements = expression.split(';');
    
    for (const statement of statements) {
      if (!statement.trim()) continue;
      

      const assignMatch = statement.trim().match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)/);
      
      if (assignMatch) {

        const [, variableName, rightHandSide] = assignMatch;
        

        if (!variableNames.includes(variableName)) {
          return {
            valid: false,
            error: `Unknown variable: ${variableName}`
          };
        }
        

        try {

          const dummyValuation = {};
          variableNames.forEach(name => {
            dummyValuation[name] = 0; // Use 0 as a safe default for validation
          });
          

          let processedExpression = rightHandSide;
          variableNames.forEach(name => {
            const regex = new RegExp(`${name}'`, 'g');
            processedExpression = processedExpression.replace(regex, name);
          });
          

          const evaluator = new Function(...variableNames, `return (${processedExpression});`);
          

          evaluator(...variableNames.map(name => dummyValuation[name]));
        } catch (error) {
          return { 
            valid: false, 
            error: `Invalid expression in "${statement}": ${error.message}` 
          };
        }
      } else {

        

        const primedVarsUsed = variableNames.filter(name => 
          statement.match(new RegExp(`${name}'`, 'g'))
        );
        
        if (primedVarsUsed.length === 0) {
          return {
            valid: false,
            error: `Statement "${statement}" is not a valid assignment or constraint. It should either be an assignment (x' = expr) or a constraint involving primed variables (x' > 0).`
          };
        }
        

        try {

          const dummyValuation = {};
          variableNames.forEach(name => {
            dummyValuation[name] = 0; // Use 0 as a safe default for validation
          });
          

          const dummyTestValuation = { ...dummyValuation };
          

          let processedExpression = statement;
          variableNames.forEach(name => {
            const regex = new RegExp(`${name}'`, 'g');
            processedExpression = processedExpression.replace(regex, `dummyTestValuation["${name}"]`);
          });
          

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
      `
    };
  }
  
}