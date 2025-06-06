
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

      const variableNames = Object.keys(valuation);
      const variableValues = variableNames.map(name => valuation[name]);
      const functionBody = `return ${this.precondition};`;
      const evaluator = new Function(...variableNames, functionBody);


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
    
      const newValuation = { ...valuation };
      

      const statements = this.postcondition.split(';');
      

      for (const statement of statements) {
        if (!statement.trim()) continue;
        

        const assignMatch = statement.trim().match(/([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)/);
        if (!assignMatch) continue; // Skip non-assignments for now
        
        const [, variableName, expression] = assignMatch;
        if (!(variableName in valuation)) continue;
        

        const expressionFunction = this.createExpressionEvaluator(expression, Object.keys(valuation));
        newValuation[variableName] = expressionFunction(...Object.values(valuation));
      }
      

      const constraintStatements = statements.filter(stmt => {
        if (!stmt.trim()) return false;

        return !stmt.trim().match(/^[a-zA-Z_][a-zA-Z0-9_]*'\s*=/) && 
               stmt.trim().match(/[a-zA-Z_][a-zA-Z0-9_]*'/);
      });

      if (constraintStatements.length > 0) {

        const primedVars = new Set();
        for (const stmt of constraintStatements) {
          this.detectPrimedVariables(stmt).forEach(v => primedVars.add(v));
        }
        

        for (const variableName of primedVars) {
          if (!(variableName in valuation)) continue;
          

          if (statements.some(stmt => 
            stmt.trim().match(new RegExp(`^${variableName}'\s*=`)))) {
            continue;
          }
          

          newValuation[variableName] = this.findValueSatisfyingConstraints(
            variableName,
            constraintStatements,
            valuation,
            newValuation
          );
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
  
  /**
   * Helper method to detect primed variables in an expression
   * @param {string} expression - The expression to analyze
   * @returns {Array<string>} Array of variable names (without primes)
   */
  detectPrimedVariables(expression) {
    const primeRegex = /([a-zA-Z_][a-zA-Z0-9_]*)'/g;
    const matches = expression.match(primeRegex) || [];
    

    return matches.map(match => match.slice(0, -1));
  }
  
  /**
   * Check if a specific value satisfies all constraint statements
   * @param {*} value - The value to check
   * @param {string} variableName - The variable name
   * @param {Array<string>} constraintStatements - Array of constraint expressions
   * @param {Object} originalValuation - Original variable values
   * @param {Object} currentValuation - Current working variable values
   * @returns {boolean} Whether the value satisfies all constraints
   */
  checkValueAgainstConstraints(value, variableName, constraintStatements, originalValuation, currentValuation) {

    const testValuation = { ...currentValuation };
    testValuation[variableName] = value;
    

    for (const statement of constraintStatements) {

      const constraintFunction = this.createConstraintEvaluator(
        statement,
        Object.keys(originalValuation),
        testValuation
      );
      

      try {

        if (!constraintFunction(...Object.values(originalValuation), testValuation)) {
          return false;
        }
      } catch (error) {
        console.error(`Error evaluating constraint: ${statement}`, error);
        return false;
      }
    }
    

    return true;
  }

  /**
* Create a function to evaluate a constraint with primed variables
* @param {string} constraintExpression - The constraint expression
* @param {Array<string>} variableNames - Array of variable names
* @param {Object} testValuation - The test valuation object containing potential new values
* @returns {Function} A function that evaluates the constraint
*/
createConstraintEvaluator(constraintExpression, variableNames, testValuation) {

  let processedExpression = constraintExpression.trim();

  const functionBody = `
    try {

      ${variableNames.map(name => `const ${name}_prime = testValuation["${name}"];`).join('\n      ')}
      

      const result = (${processedExpression.replace(
        new RegExp(`(^|[^\\w])([a-zA-Z_][a-zA-Z0-9_]*)'`, 'g'), 
        (match, prefix, varName) => {

          if (variableNames.includes(varName)) {
            return `${prefix}${varName}_prime`;
          }
          return match;
        }
      )});
      
      return !!result;
    } catch (e) {
      console.error("Error in constraint evaluation:", e);
      return false;
    }
  `;
  

  return new Function(...variableNames, 'testValuation', functionBody);
}


  /**
   * Find a value that satisfies all constraint statements for a variable
   * @param {string} variableName - The variable name to generate a value for
   * @param {Array<string>} constraintStatements - Array of constraint expressions
   * @param {Object} originalValuation - Original variable values
   * @param {Object} currentValuation - Current working variable values
   * @returns {*} A value that satisfies all constraints
   */
  findValueSatisfyingConstraints(variableName, constraintStatements, originalValuation, currentValuation) {

    const currentValue = originalValuation[variableName];
    console.log("Call me maybe")

    if (typeof currentValue === 'boolean') {

      if (this.checkValueAgainstConstraints(true, variableName, constraintStatements, originalValuation, currentValuation)) {
        return true;
      }
      if (this.checkValueAgainstConstraints(false, variableName, constraintStatements, originalValuation, currentValuation)) {
        return false;
      }
      return currentValue; // Fallback to current value
    }
    console.log(variableName, constraintStatements, originalValuation, currentValuation);
    if (typeof currentValue === 'number') {
      // Create the solver
      const solver = new ExpressionSolver(currentValuation);

      const expr = "x' > x + 5; x' < x + 100";

      const newValues = solver.solve(constraintStatements.join("; "));

      console.log(`Random Valid Value: ${newValues[variableName]}`);

      return newValues[variableName];

    } else if (typeof currentValue === 'string') {

      console.warn(`Constraint-based sampling for string variables is not yet implemented`);
    }
    

    return currentValue;
  }
  /**
   * Create a function to evaluate an expression
   * @param {string} expression - The expression to evaluate
   * @param {Array<string>} variables - Array of variable names
   * @returns {Function} A function that evaluates the expression
   * @private
   */
  createExpressionEvaluator(expression, variables) {

    let processedExpression = expression;
    variables.forEach(name => {
      const regex = new RegExp(`${name}'`, 'g');
      processedExpression = processedExpression.replace(regex, name);
    });


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


    const valuation = this.getDataValuation();


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


    for (const [id, transition] of this.transitions) {
      pnml += `
      <transition id="${id}">
        <name>
          <text>${transition.label}</text>
        </name>
        <graphics>
          <position x="${transition.position.x}" y="${transition.position.y}"/>
        </graphics>`;


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