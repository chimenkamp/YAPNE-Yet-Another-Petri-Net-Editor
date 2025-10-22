import { Transition, PetriNet, Place, Arc } from '../petri-net-simulator.js';

/**
 * Represents a data variable in a Data Petri Net
 */
class DataVariable {
  /**
   * Create a new data variable
   * @param {string} id - Unique identifier for the variable
   * @param {string} name - Human-readable name of the variable
   * @param {string} type - Data type ('int', 'float', 'string', 'boolean')
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
      case 'int':
        return Math.floor(Number(this.currentValue));
      case 'float':
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
        case 'int':
          const intValue = Number(value);
          if (isNaN(intValue)) {
            throw new Error('Not a valid integer');
          }
          this.currentValue = Math.floor(intValue);
          break;
        case 'float':
          const floatValue = Number(value);
          if (isNaN(floatValue)) {
            throw new Error('Not a valid float');
          }
          this.currentValue = floatValue;
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
      const statements = this.postcondition.split(';');
      
      // First pass: Handle direct assignments
      for (const statement of statements) {
        if (!statement.trim()) continue;
        
        const assignMatch = statement.trim().match(/([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)/);
        if (!assignMatch) continue; // Skip non-assignments for now
        
        const [, variableName, expression] = assignMatch;
        if (!(variableName in valuation)) continue;
        
        const expressionFunction = this.createExpressionEvaluator(expression, Object.keys(valuation));
        newValuation[variableName] = expressionFunction(...Object.values(valuation));
      }
      
      // Second pass: Handle constraint-based assignments
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
          
          // Skip if already handled by direct assignment
          if (statements.some(stmt => 
            stmt.trim().match(new RegExp(`^${variableName}'\s*=`)))) {
            continue;
          }
          
          // Use constraint-based assignment with proper type
          newValuation[variableName] = await this.findValueSatisfyingConstraints(
            variableName,
            constraintStatements,
            valuation,
            newValuation
          );
          console.log(`Found value for ${variableName}: ${newValuation[variableName]}`);
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
        ${variableNames.map(name => `const ${name}_prime = testValuation["${name}"];`).join('\n        ')}
        
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
 * Find a value that satisfies all constraint statements for a variable (ASYNC)
 * @param {string} variableName - The variable name to generate a value for
 * @param {Array<string>} constraintStatements - Array of constraint expressions
 * @param {Object} originalValuation - Original variable values
 * @param {Object} currentValuation - Current working variable values
 * @returns {Promise<*>} A value that satisfies all constraints
 */
async findValueSatisfyingConstraints(variableName, constraintStatements, originalValuation, currentValuation) {
  const currentValue = originalValuation[variableName];
  console.log("Finding value for constraints", variableName, constraintStatements);

  if (typeof currentValue === 'boolean') {
    if (this.checkValueAgainstConstraints(true, variableName, constraintStatements, originalValuation, currentValuation)) {
      return true;
    }
    if (this.checkValueAgainstConstraints(false, variableName, constraintStatements, originalValuation, currentValuation)) {
      return false;
    }
    return currentValue; // Fallback to current value
  }

  if (typeof currentValue === 'number') {
    try {
      // Use 'auto' mode to let Z3 auto-detect types based on actual values
      // This is more robust than trying to manually determine types
      console.log('Combined constraints:', constraintStatements.join(' && '));
      console.log('Using auto type detection');
      
      // Call the async solveExpression function with auto type detection
      const result = await window.solveExpression(
        constraintStatements.join(' && '), 
        currentValuation, 
        'auto'  // Use auto mode for robust type detection
      );
      console.log('Z3 solver result:', result);
      if (result && result.newValues && result.newValues[variableName] !== undefined) {
        console.log(`Z3 solver found value for ${variableName}: ${result.newValues[variableName]}`);
        
        // Get the actual variable type from the data petri net for proper conversion
        let variableType = 'int'; // default fallback
        
        if (window.petriApp && window.petriApp.api && window.petriApp.api.petriNet && window.petriApp.api.petriNet.dataVariables) {
          for (const [id, variable] of window.petriApp.api.petriNet.dataVariables) {
            if (variable.name === variableName) {
              variableType = variable.type;
              // Handle legacy 'number' type
              if (variableType === 'number') {
                variableType = 'int';
              }
              break;
            }
          }
        }
        
        // Ensure the result matches the expected type
        if (variableType === 'int') {
          return Math.floor(Number(result.newValues[variableName]));
        } else if (variableType === 'float') {
          return Number(result.newValues[variableName]);
        } else if (variableType === 'boolean') {
          return Boolean(result.newValues[variableName]);
        } else {
          // For other types, return as-is
          return result.newValues[variableName];
        }
      }
    } catch (error) {
      console.error('Error using Z3 solver:', error);
    }
    
    // Fallback to current value if Z3 solver fails
    return currentValue;
  } else if (typeof currentValue === 'string') {
    // For string variables, try using Z3 with auto detection
    try {
      console.log('String variable, using Z3 with auto detection');
      const result = await window.solveExpression(
        constraintStatements.join(' && '), 
        currentValuation, 
        'auto'
      );
      
      if (result && result.newValues && result.newValues[variableName] !== undefined) {
        console.log(`Z3 solver found value for string ${variableName}: ${result.newValues[variableName]}`);
        return String(result.newValues[variableName]);
      }
    } catch (error) {
      console.error('Error using Z3 solver for string:', error);
    }
    
    // Fallback for strings - return current value
    return currentValue;
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
        // Handle legacy 'number' type by converting to 'int'
        let variableType = variableData.type;
        if (variableType === 'number') {
          variableType = 'int';
        }
        
        const variable = new DataVariable(
          variableData.id,
          variableData.name,
          variableType,
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
<pnml>
   <net id="${this.id}" type="http://www.pnml.org/version-2009/grammar/pnmlcoremodel">
      <name>
         <text>${this.name}</text>
      </name>
      <source>
         <text>Generated by YAPNE - Yet Another Petri Net Editor</text>
      </source>
      <page id="n0">`;

    // Export places
    for (const [id, place] of this.places) {
      pnml += `
         <place id="${id}">
            <name>
               <text>${place.label}</text>
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
          parts.push(`pre: ${transition.precondition.trim()}`);
        }
        if (transition.postcondition && transition.postcondition.trim()) {
          parts.push(`post: ${transition.postcondition.trim()}`);
        }
        if (parts.length > 0) {
          guardAttr = ` guard="${parts.join(' | ')}"`;
        }
      }

      pnml += `
         <transition${guardAttr} id="${id}">
            <name>
               <text>${transition.label}</text>
            </name>`;

      // Add writeVariable elements for variables modified in postcondition
      if (transition.postcondition && transition.postcondition.trim()) {
        const modifiedVars = this.extractModifiedVariables(transition.postcondition);
        for (const varName of modifiedVars) {
          pnml += `
            <writeVariable>${varName}</writeVariable>`;
        }
      }

      pnml += `
         </transition>`;
    }

    // Export arcs
    for (const [id, arc] of this.arcs) {
      pnml += `
         <arc id="${id}" source="${arc.source}" target="${arc.target}">
            <arctype>
               <text>${arc.type || 'normal'}</text>
            </arctype>`;
      
      if (arc.weight > 1) {
        pnml += `
            <inscription>
               <text>${arc.weight}</text>
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
          case 'float':
            javaType = 'java.lang.Double';
            maxValue = '100000.0';
            break;
          case 'boolean':
            javaType = 'java.lang.Boolean';
            maxValue = '100000';
            break;
          case 'string':
            javaType = 'java.lang.String';
            break;
        }

        pnml += `
         <variable maxValue="${maxValue}" minValue="${minValue}" type="${javaType}">
            <name>${variable.name}</name>
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
    const modifiedVars = new Set();
    
    // Split by semicolon to handle multiple statements
    const statements = postcondition.split(';');
    
    for (const statement of statements) {
      if (!statement.trim()) continue;
      
      // Look for assignment patterns: variableName' = ...
      const assignMatch = statement.trim().match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\s*=/);
      if (assignMatch) {
        modifiedVars.add(assignMatch[1]);
      } else {
        // Look for constraint patterns: expressions containing variableName'
        const primeMatches = statement.match(/([a-zA-Z_][a-zA-Z0-9_]*)'/g);
        if (primeMatches) {
          primeMatches.forEach(match => {
            modifiedVars.add(match.slice(0, -1)); // Remove the prime
          });
        }
      }
    }
    
    return Array.from(modifiedVars);
  }
}

export { DataVariable, DataAwareTransition, DataPetriNet };