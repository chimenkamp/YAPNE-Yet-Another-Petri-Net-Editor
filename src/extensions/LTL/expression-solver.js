/**
 * Expression Solver for Data Petri Net Constraints
 * 
 * This class handles constraint-based random value generation for 
 * data variables in postconditions using primed variable notation.
 */
/**
 * Z3-Enhanced Expression Solver for Data Petri Net Constraints
 * 
 * This class handles constraint-based random value generation for 
 * data variables in postconditions using primed variable notation
 * and leverages Z3 for powerful constraint solving.
 */
class LTLExpressionSolver {
    constructor(currentValuation) {
        this.currentValuation = { ...currentValuation };
        this.constraints = [];
        this.primedVariables = new Set();
        this.randomSeed = Math.random();
        this.smtSolver = new SMTSolver();
    }

    /**
     * Solve constraints and generate new values for primed variables
     * @param {string} constraintExpression - The constraint expression to solve
     * @returns {Object} New valuation with solved variable values
     */
    async solve(constraintExpression) {
        try {
            // Parse the constraint expression
            this.parseConstraints(constraintExpression);
            
            // Use Z3 to solve constraints if we have primed variables
            if (this.primedVariables.size > 0) {
                const z3Result = await this._solveWithZ3(constraintExpression);
                if (z3Result) {
                    return z3Result;
                }
            }
            
            // Fallback to original approach for simple cases
            const newValuation = { ...this.currentValuation };
            
            for (const variable of this.primedVariables) {
                if (this.currentValuation.hasOwnProperty(variable)) {
                    newValuation[variable] = this.generateValueForVariable(variable);
                }
            }
            
            return newValuation;
        } catch (error) {
            console.error("Error solving constraints:", error);
            return this.currentValuation;
        }
    }

    /**
     * Solve constraints using Z3 SMT solver
     * @param {string} constraintExpression - The constraint expression
     * @returns {Promise<Object|null>} - New valuation or null if unsatisfiable
     * @private
     */
    async _solveWithZ3(constraintExpression) {
        try {
            // Convert primed variable notation to Z3 format
            const z3Formula = this._convertToZ3Format(constraintExpression);
            
            // Use Z3 to solve
            const solution = await this.smtSolver.solve(z3Formula);
            
            if (solution) {
                // Map Z3 solution back to our variable space
                return this._mapZ3SolutionToValuation(solution);
            }
            
            return null;
        } catch (error) {
            console.error("Z3 solving failed:", error);
            return null;
        }
    }

    /**
     * Convert constraint expression with primed variables to Z3 format
     * @param {string} expression - Original constraint expression
     * @returns {string} - Z3-compatible formula
     * @private
     */
    _convertToZ3Format(expression) {
        let z3Formula = expression;
        
        // Add current variable values as constraints
        const currentConstraints = [];
        for (const [varName, value] of Object.entries(this.currentValuation)) {
            currentConstraints.push(`${varName}_old == ${this._valueToZ3(value)}`);
        }
        
        // Replace primed variables with new variable names
        for (const varName of this.primedVariables) {
            const regex = new RegExp(`\\b${varName}'`, 'g');
            z3Formula = z3Formula.replace(regex, `${varName}_new`);
        }
        
        // Replace unprimed variables with old variable names
        for (const varName of Object.keys(this.currentValuation)) {
            if (!this.primedVariables.has(varName)) {
                const regex = new RegExp(`\\b${varName}\\b`, 'g');
                z3Formula = z3Formula.replace(regex, `${varName}_old`);
            }
        }
        
        // Combine current state constraints with new constraints
        const allConstraints = [...currentConstraints];
        
        // Split by semicolon and add each constraint
        const statements = z3Formula.split(';').map(s => s.trim()).filter(s => s.length > 0);
        allConstraints.push(...statements);
        
        // Add reasonable bounds for numeric variables to ensure finite solutions
        for (const varName of this.primedVariables) {
            const currentValue = this.currentValuation[varName];
            if (typeof currentValue === 'number') {
                const lowerBound = currentValue - 1000;
                const upperBound = currentValue + 1000;
                allConstraints.push(`${varName}_new >= ${lowerBound}`);
                allConstraints.push(`${varName}_new <= ${upperBound}`);
            }
        }
        
        return allConstraints.join(' && ');
    }

    /**
     * Convert a value to Z3 representation
     * @param {*} value - The value to convert
     * @returns {string} - Z3 representation
     * @private
     */
    _valueToZ3(value) {
        if (typeof value === 'number') {
            return value.toString();
        } else if (typeof value === 'boolean') {
            return value ? 'true' : 'false';
        } else if (typeof value === 'string') {
            return `"${value}"`;
        }
        return '0'; // Default fallback
    }

    /**
     * Map Z3 solution back to our valuation format
     * @param {Object} z3Solution - Solution from Z3
     * @returns {Object} - New valuation
     * @private
     */
    _mapZ3SolutionToValuation(z3Solution) {
        const newValuation = { ...this.currentValuation };
        
        // Extract new values for primed variables
        for (const varName of this.primedVariables) {
            const newVarName = `${varName}_new`;
            if (z3Solution.hasOwnProperty(newVarName)) {
                newValuation[varName] = z3Solution[newVarName];
            }
        }
        
        return newValuation;
    }

    /**
     * Parse constraint expressions and extract primed variables
     * @param {string} expression - The constraint expression
     */
    parseConstraints(expression) {
        this.constraints = [];
        this.primedVariables.clear();
        
        // Split by semicolons and process each constraint
        const statements = expression.split(';').map(s => s.trim()).filter(s => s.length > 0);
        
        for (const statement of statements) {
            // Extract primed variables (variables with ' suffix)
            const primedMatches = statement.match(/([a-zA-Z_][a-zA-Z0-9_]*)'/g);
            if (primedMatches) {
                primedMatches.forEach(match => {
                    const varName = match.slice(0, -1); // Remove the '
                    this.primedVariables.add(varName);
                });
            }
            
            // Store the constraint
            if (primedMatches && primedMatches.length > 0) {
                this.constraints.push({
                    expression: statement,
                    primedVars: primedMatches.map(m => m.slice(0, -1))
                });
            }
        }
    }

    /**
     * Generate a value for a specific variable that satisfies all constraints
     * (Fallback method when Z3 is not available or fails)
     * @param {string} variableName - The variable to generate a value for
     * @returns {*} A generated value that satisfies the constraints
     */
    generateValueForVariable(variableName) {
        const currentValue = this.currentValuation[variableName];
        const varType = typeof currentValue;
        
        // Get constraints that involve this variable
        const relevantConstraints = this.constraints.filter(c => 
            c.primedVars.includes(variableName));
        
        if (relevantConstraints.length === 0) {
            // No constraints, return current value
            return currentValue;
        }
        
        switch (varType) {
            case 'number':
                return this.generateNumericValue(variableName, relevantConstraints);
            case 'boolean':
                return this.generateBooleanValue(variableName, relevantConstraints);
            case 'string':
                return this.generateStringValue(variableName, relevantConstraints);
            default:
                return currentValue;
        }
    }

    /**
     * Generate a numeric value that satisfies constraints
     * @param {string} variableName - The variable name
     * @param {Array} constraints - Relevant constraints
     * @returns {number} Generated numeric value
     */
    generateNumericValue(variableName, constraints) {
        const currentValue = this.currentValuation[variableName];
        let minValue = Number.NEGATIVE_INFINITY;
        let maxValue = Number.POSITIVE_INFINITY;
        let excludedValues = new Set();
        
        // Analyze constraints to determine bounds
        for (const constraint of constraints) {
            const bounds = this.analyzeNumericConstraint(variableName, constraint.expression);
            
            if (bounds.min !== undefined) {
                minValue = Math.max(minValue, bounds.min);
            }
            if (bounds.max !== undefined) {
                maxValue = Math.min(maxValue, bounds.max);
            }
            if (bounds.excluded) {
                bounds.excluded.forEach(val => excludedValues.add(val));
            }
        }
        
        // If no meaningful bounds found, use range around current value
        if (minValue === Number.NEGATIVE_INFINITY) {
            minValue = currentValue - 100;
        }
        if (maxValue === Number.POSITIVE_INFINITY) {
            maxValue = currentValue + 100;
        }
        
        // Ensure min <= max
        if (minValue > maxValue) {
            console.warn(`Inconsistent constraints for ${variableName}: min=${minValue}, max=${maxValue}`);
            return currentValue;
        }
        
        // Generate a value in the valid range
        let attempts = 0;
        const maxAttempts = 1000;
        
        while (attempts < maxAttempts) {
            let candidate;
            
            if (Number.isInteger(currentValue)) {
                // Generate integer
                candidate = Math.floor(minValue + Math.random() * (maxValue - minValue + 1));
            } else {
                // Generate float
                candidate = minValue + Math.random() * (maxValue - minValue);
            }
            
            // Check if candidate is excluded
            if (!excludedValues.has(candidate)) {
                // Verify the candidate satisfies all constraints
                if (this.verifyNumericValue(variableName, candidate, constraints)) {
                    return candidate;
                }
            }
            
            attempts++;
        }
        
        console.warn(`Could not find valid value for ${variableName} after ${maxAttempts} attempts`);
        return currentValue;
    }

    /**
     * Analyze a numeric constraint to extract bounds
     * @param {string} variableName - The variable name
     * @param {string} expression - The constraint expression
     * @returns {Object} Bounds information {min, max, excluded}
     */
    analyzeNumericConstraint(variableName, expression) {
        const bounds = {};
        
        // Handle different comparison patterns
        const patterns = [
            { regex: new RegExp(`${variableName}'\\s*>\\s*([^\\s&|]+)`), type: 'gt' },
            { regex: new RegExp(`${variableName}'\\s*>=\\s*([^\\s&|]+)`), type: 'gte' },
            { regex: new RegExp(`${variableName}'\\s*<\\s*([^\\s&|]+)`), type: 'lt' },
            { regex: new RegExp(`${variableName}'\\s*<=\\s*([^\\s&|]+)`), type: 'lte' },
            { regex: new RegExp(`${variableName}'\\s*==\\s*([^\\s&|]+)`), type: 'eq' },
            { regex: new RegExp(`${variableName}'\\s*!=\\s*([^\\s&|]+)`), type: 'neq' },
            { regex: new RegExp(`([^\\s&|]+)\\s*<\\s*${variableName}'`), type: 'gt' },
            { regex: new RegExp(`([^\\s&|]+)\\s*<=\\s*${variableName}'`), type: 'gte' },
            { regex: new RegExp(`([^\\s&|]+)\\s*>\\s*${variableName}'`), type: 'lt' },
            { regex: new RegExp(`([^\\s&|]+)\\s*>=\\s*${variableName}'`), type: 'lte' }
        ];
        
        for (const pattern of patterns) {
            const match = expression.match(pattern.regex);
            if (match) {
                const valueExpr = match[1];
                const numValue = this.evaluateExpression(valueExpr);
                
                if (typeof numValue === 'number' && !isNaN(numValue)) {
                    switch (pattern.type) {
                        case 'gt':
                            bounds.min = numValue + (Number.isInteger(numValue) ? 1 : 1e-10);
                            break;
                        case 'gte':
                            bounds.min = numValue;
                            break;
                        case 'lt':
                            bounds.max = numValue - (Number.isInteger(numValue) ? 1 : 1e-10);
                            break;
                        case 'lte':
                            bounds.max = numValue;
                            break;
                        case 'eq':
                            bounds.min = bounds.max = numValue;
                            break;
                        case 'neq':
                            if (!bounds.excluded) bounds.excluded = [];
                            bounds.excluded.push(numValue);
                            break;
                    }
                }
            }
        }
        
        return bounds;
    }

    /**
     * Verify that a numeric value satisfies all constraints
     * @param {string} variableName - The variable name
     * @param {number} value - The value to test
     * @param {Array} constraints - The constraints to check
     * @returns {boolean} Whether the value satisfies all constraints
     */
    verifyNumericValue(variableName, value, constraints) {
        for (const constraint of constraints) {
            if (!this.testConstraint(variableName, value, constraint.expression)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Test a specific constraint with a value
     * @param {string} variableName - The variable name
     * @param {*} value - The value to test
     * @param {string} expression - The constraint expression
     * @returns {boolean} Whether the constraint is satisfied
     */
    testConstraint(variableName, value, expression) {
        try {
            // Create a test valuation
            const testValuation = { ...this.currentValuation };
            testValuation[variableName] = value;
            
            // Replace primed variables in the expression
            let testExpression = expression;
            for (const varName of Object.keys(testValuation)) {
                const regex = new RegExp(`${varName}'`, 'g');
                testExpression = testExpression.replace(regex, testValuation[varName]);
            }
            
            // Replace unprimed variables
            for (const varName of Object.keys(this.currentValuation)) {
                const regex = new RegExp(`\\b${varName}\\b`, 'g');
                testExpression = testExpression.replace(regex, this.currentValuation[varName]);
            }
            
            // Evaluate the expression
            return this.evaluateExpression(testExpression);
        } catch (error) {
            console.error(`Error testing constraint ${expression}:`, error);
            return false;
        }
    }

    /**
     * Generate a boolean value that satisfies constraints
     * @param {string} variableName - The variable name
     * @param {Array} constraints - Relevant constraints
     * @returns {boolean} Generated boolean value
     */
    generateBooleanValue(variableName, constraints) {
        // Try both true and false, return the first that satisfies all constraints
        if (this.verifyBooleanValue(variableName, true, constraints)) {
            return true;
        }
        if (this.verifyBooleanValue(variableName, false, constraints)) {
            return false;
        }
        
        // If neither works, return current value
        return this.currentValuation[variableName];
    }

    /**
     * Verify that a boolean value satisfies constraints
     * @param {string} variableName - The variable name
     * @param {boolean} value - The value to test
     * @param {Array} constraints - The constraints to check
     * @returns {boolean} Whether the value satisfies all constraints
     */
    verifyBooleanValue(variableName, value, constraints) {
        for (const constraint of constraints) {
            if (!this.testConstraint(variableName, value, constraint.expression)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Generate a string value that satisfies constraints
     * @param {string} variableName - The variable name
     * @param {Array} constraints - Relevant constraints
     * @returns {string} Generated string value
     */
    generateStringValue(variableName, constraints) {
        const currentValue = this.currentValuation[variableName];
        
        // For strings, we'll try some common values and the current value
        const candidates = [
            currentValue,
            "",
            "true",
            "false",
            "done",
            "pending",
            "active",
            "completed",
            "error",
            "success"
        ];
        
        for (const candidate of candidates) {
            if (this.verifyStringValue(variableName, candidate, constraints)) {
                return candidate;
            }
        }
        
        // If no predefined value works, return current value
        return currentValue;
    }

    /**
     * Verify that a string value satisfies constraints
     * @param {string} variableName - The variable name
     * @param {string} value - The value to test
     * @param {Array} constraints - The constraints to check
     * @returns {boolean} Whether the value satisfies all constraints
     */
    verifyStringValue(variableName, value, constraints) {
        for (const constraint of constraints) {
            if (!this.testConstraint(variableName, value, constraint.expression)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Evaluate a mathematical/logical expression
     * @param {string} expression - The expression to evaluate
     * @returns {*} The result of the expression
     */
    evaluateExpression(expression) {
        try {
            // Clean up the expression
            const cleanExpr = expression.toString().trim();
            
            // Handle simple numeric values
            if (/^-?\d+(\.\d+)?$/.test(cleanExpr)) {
                return parseFloat(cleanExpr);
            }
            
            // Handle boolean values
            if (cleanExpr === 'true') return true;
            if (cleanExpr === 'false') return false;
            
            // Handle string literals
            if (/^".*"$/.test(cleanExpr)) {
                return cleanExpr.slice(1, -1);
            }
            
            // For complex expressions, use Function constructor (be careful with security)
            // This is a simplified approach - in production, you'd want a proper expression parser
            const safeExpr = cleanExpr.replace(/[^0-9+\-*/.()<>=!&| ]/g, '');
            if (safeExpr !== cleanExpr) {
                console.warn(`Expression sanitized: ${cleanExpr} -> ${safeExpr}`);
            }
            
            return Function(`"use strict"; return (${safeExpr})`)();
        } catch (error) {
            console.error(`Error evaluating expression "${expression}":`, error);
            return false;
        }
    }

    /**
     * Get a random number in range [min, max]
     * @param {number} min - Minimum value
     * @param {number} max - Maximum value
     * @returns {number} Random number in range
     */
    randomInRange(min, max) {
        return min + Math.random() * (max - min);
    }

    /**
     * Get a random integer in range [min, max]
     * @param {number} min - Minimum value
     * @param {number} max - Maximum value
     * @returns {number} Random integer in range
     */
    randomIntInRange(min, max) {
        return Math.floor(min + Math.random() * (max - min + 1));
    }
}

// Export for use in other modules
if (typeof module !== 'undefined' && module.exports) {
    module.exports = LTLExpressionSolver;
} else {
    window.LTLExpressionSolver = LTLExpressionSolver;
}
// Export for use in other modules
if (typeof module !== 'undefined' && module.exports) {
    module.exports = LTLExpressionSolver;
} else {
    window.LTLExpressionSolver = LTLExpressionSolver;
}