
import { PetriNetAPI, Place, Transition, Arc } from '../petri-net-simulator.js';
import { DataPetriNet, DataAwareTransition, DataVariable } from './dpn-model.js';
import { validatePrecondition, validatePostcondition } from './guard-language/guard-validator.js';

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
   * @param {string} type - Data type ('int'|'integer'|'bool'|'boolean'|'real')
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

      // Update enabled transitions for the current marking
      this.petriNet.updateEnabledTransitions();
      const enabledTransitions = [];

      for (const [id, transition] of this.petriNet.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }

      // Fire all enabled transitions simultaneously (synchronous step semantics)
      if (enabledTransitions.length > 0) {
        firedAny = await this.petriNet.fireTransitionsSynchronously(enabledTransitions);
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
        const variable = new DataVariable(
          varData.id || this.generateUUID(),
          varData.name,
          varData.type, // normalizeType is called in the constructor
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
   * @returns {Object} Validation result {valid: boolean, error: string|null, pos: number|null}
   */
  validatePrecondition(expression, variableNames = []) {
    if (!expression.trim()) {
      return { valid: true, error: null, pos: null };
    }
    return validatePrecondition(expression, variableNames);
  }

  /**
   * Validate a postcondition expression
   * @param {string} expression - Postcondition expression to validate
   * @param {Array<string>} variableNames - Available variable names
   * @returns {Object} Validation result {valid: boolean, error: string|null, pos: number|null}
   */
  validatePostcondition(expression, variableNames = []) {
    if (!expression.trim()) {
      return { valid: true, error: null, pos: null };
    }
    return validatePostcondition(expression, variableNames);
  }

  /**
   * Get simplified help/docs for data expressions
   * @returns {Object} Documentation for preconditions and postconditions
   */
  getDataExpressionHelp() {
    return {
      precondition: `
  Precondition (Guard) Help:
  - Guard expression that evaluates to true/false
  - Determines when a transition is enabled
  - Two forms supported:
    1. Infix: x > 5 and y = 1
    2. SMT prefix: (and (> x 5) (= y 1))
  - Operators: =, distinct, <, <=, >, >=, +, -, *, /
  - Logical: and, or, not, => (implies)
  - No primed variables (x') allowed in preconditions
  - Available variables: ${Array.from(this.petriNet.dataVariables.values()).map(v => v.name).join(', ')}
      `,
      postcondition: `
  Postcondition (Data Update) Help:
  - Defines how variables change when transition fires
  - Use primed variables (x') for next-state values
  - Two supported formats:
    1. Direct assignment: x' = x + 1 and y' = 0
    2. Constraint-based: x' > 0 and x' < x * 2
       (generates a value satisfying the constraints)
  - Use 'and' to combine multiple assignments/constraints
  - Direct assignments have priority over constraints
  - Available variables: ${Array.from(this.petriNet.dataVariables.values()).map(v => v.name).join(', ')}
  
  Data Types:
  - int / integer: Whole numbers (42, -7, 0)
  - real: Decimal numbers (3.14, -2.5, 1.0)
  - bool / boolean: true or false values
      `
    };
  }
  
}

export { DataPetriNetAPI };