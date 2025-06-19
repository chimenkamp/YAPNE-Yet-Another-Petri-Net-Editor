/**
 * Z3-based SMT Solver for Data Petri Net Constraints - FIXED VERSION
 * Corrected Z3 WASM API usage
 */
class SMTSolver {
    constructor() {
        this.z3 = null;
        this.initialized = false;
        this.initPromise = null;
    }

    /**
     * Initialize Z3 if not already initialized
     * @returns {Promise<void>}
     */
    async ensureInitialized() {
        if (this.initialized) return;
        
        if (this.initPromise) {
            await this.initPromise;
            return;
        }

        this.initPromise = initZ3().then((z3) => {
            this.z3 = z3;
            this.initialized = true;
            console.log('Z3 API functions available:', Object.keys(z3).filter(k => k.startsWith('_Z3_')).length);
        }).catch((error) => {
            console.error('Failed to initialize Z3:', error);
            this.initialized = false;
            throw error;
        });

        await this.initPromise;
    }

    /**
     * Main public method. Checks if a given formula string is satisfiable.
     * @param {string} formulaString - The logical formula to check.
     * @returns {boolean} - True if the formula is satisfiable, false otherwise.
     */
    async isSatisfiable(formulaString) {
        try {
            await this.ensureInitialized();
            
            const trimmed = (formulaString || '').trim();
            if (trimmed === '' || trimmed === 'true') return true;
            if (trimmed === 'false') return false;

            return this._checkSatisfiabilityWithZ3(trimmed);
        } catch (error) {
            console.error(`Z3 SMT Solver Error: ${error.message} in formula "${formulaString}"`);
            // Treat errors as unsatisfiable to preserve soundness
            return false;
        }
    }

    /**
     * Check satisfiability using Z3
     * @param {string} formula - The formula to check
     * @returns {boolean} - Satisfiability result
     * @private
     */
    _checkSatisfiabilityWithZ3(formula) {
        const ctx = this.z3._Z3_mk_context();
        const solver = this.z3._Z3_mk_solver(ctx);
        this.z3._Z3_solver_inc_ref(ctx, solver);

        try {
            // Parse variables from the formula
            const variables = this._extractVariables(formula);
            const z3Vars = new Map();
            
            // Create Z3 variables
            for (const varName of variables) {
                const symbol = this._mkStringSymbol(ctx, varName);
                let sort;
                
                // Determine variable type based on context
                if (this._isIntegerVariable(varName, formula)) {
                    sort = this.z3._Z3_mk_int_sort(ctx);
                } else if (this._isBooleanVariable(varName, formula)) {
                    sort = this.z3._Z3_mk_bool_sort(ctx);
                } else {
                    // Default to real for numeric operations
                    sort = this.z3._Z3_mk_real_sort(ctx);
                }
                
                const z3Var = this.z3._Z3_mk_const(ctx, symbol, sort);
                z3Vars.set(varName, { var: z3Var, sort: sort });
            }

            // Convert formula to Z3 constraints
            const z3Constraint = this._parseFormulaToZ3(ctx, formula, z3Vars);
            
            if (z3Constraint) {
                this.z3._Z3_solver_assert(ctx, solver, z3Constraint);
            }

            // Check satisfiability
            const result = this.z3._Z3_solver_check(ctx, solver);
            
            // Result: 1 = SAT, -1 = UNSAT, 0 = UNKNOWN
            return result === 1;

        } finally {
            // Cleanup
            this.z3._Z3_solver_dec_ref(ctx, solver);
            this.z3._Z3_del_context(ctx);
        }
    }

    /**
     * Helper to create string symbol with proper memory management
     * @param {number} ctx - Z3 context
     * @param {string} str - String value
     * @returns {number} - Z3 symbol
     * @private
     */
    _mkStringSymbol(ctx, str) {
        // Allocate string in WASM memory
        const strPtr = this.z3.allocateUTF8(str);
        try {
            return this.z3._Z3_mk_string_symbol(ctx, strPtr);
        } finally {
            this.z3._free(strPtr);
        }
    }

    /**
     * Helper to create integer value
     * @param {number} ctx - Z3 context
     * @param {number} value - Integer value
     * @returns {number} - Z3 AST
     * @private
     */
    _mkInt(ctx, value) {
        return this.z3._Z3_mk_int(ctx, value, this.z3._Z3_mk_int_sort(ctx));
    }

    /**
     * Helper to create real value from float
     * @param {number} ctx - Z3 context
     * @param {number} value - Float value
     * @returns {number} - Z3 AST
     * @private
     */
    _mkReal(ctx, value) {
        // Convert float to rational representation
        const numerator = Math.round(value * 1000000);
        const denominator = 1000000;
        const numStr = this.z3.allocateUTF8(numerator.toString());
        const denStr = this.z3.allocateUTF8(denominator.toString());
        
        try {
            const numAST = this.z3._Z3_mk_numeral(ctx, numStr, this.z3._Z3_mk_int_sort(ctx));
            const denAST = this.z3._Z3_mk_numeral(ctx, denStr, this.z3._Z3_mk_int_sort(ctx));
            return this.z3._Z3_mk_div(ctx, numAST, denAST);
        } finally {
            this.z3._free(numStr);
            this.z3._free(denStr);
        }
    }

    /**
     * Helper to create array in WASM memory
     * @param {Array} jsArray - JavaScript array of pointers
     * @returns {number} - Pointer to WASM array
     * @private
     */
    _createWasmArray(jsArray) {
        const arrayPtr = this.z3._malloc(jsArray.length * 4); // 4 bytes per pointer
        for (let i = 0; i < jsArray.length; i++) {
            this.z3.HEAP32[(arrayPtr >> 2) + i] = jsArray[i];
        }
        return arrayPtr;
    }

    /**
     * Extract variable names from formula
     * @param {string} formula - The formula
     * @returns {Set<string>} - Set of variable names
     * @private
     */
    _extractVariables(formula) {
        const variables = new Set();
        const varRegex = /\b([a-zA-Z_][a-zA-Z0-9_]*)\b/g;
        let match;
        
        while ((match = varRegex.exec(formula)) !== null) {
            const varName = match[1];
            // Skip boolean constants and operators
            if (!['true', 'false', 'and', 'or', 'not'].includes(varName.toLowerCase())) {
                variables.add(varName);
            }
        }
        
        return variables;
    }

    /**
     * Check if a variable should be treated as integer
     * @param {string} varName - Variable name
     * @param {string} formula - The formula context
     * @returns {boolean}
     * @private
     */
    _isIntegerVariable(varName, formula) {
        const intPatterns = [
            new RegExp(`${varName}\\s*%`, 'g'), // modulo operation
            new RegExp(`${varName}\\s*==\\s*\\d+(?!\\.)`), // equality with integer
        ];
        
        return intPatterns.some(pattern => pattern.test(formula));
    }

    /**
     * Check if a variable should be treated as boolean
     * @param {string} varName - Variable name
     * @param {string} formula - The formula context
     * @returns {boolean}
     * @private
     */
    _isBooleanVariable(varName, formula) {
        const boolPatterns = [
            new RegExp(`${varName}\\s*==\\s*(true|false)\\b`, 'g'),
            new RegExp(`\\b(not|!)\\s*${varName}\\b`, 'g'),
        ];
        
        return boolPatterns.some(pattern => pattern.test(formula));
    }

    /**
     * Parse formula string to Z3 constraint
     * @param {number} ctx - Z3 context
     * @param {string} formula - Formula string
     * @param {Map} z3Vars - Map of variable names to Z3 variables
     * @returns {number|null} - Z3 AST or null
     * @private
     */
    _parseFormulaToZ3(ctx, formula, z3Vars) {
        try {
            // Tokenize and parse the formula
            const tokens = this._tokenizeFormula(formula);
            const ast = this._parseTokensToAST(tokens);
            
            // Convert AST to Z3
            return this._astToZ3(ctx, ast, z3Vars);
        } catch (error) {
            console.error('Error parsing formula to Z3:', error);
            return null;
        }
    }

    /**
     * Tokenize formula
     * @param {string} formula - Formula string
     * @returns {Array} - Array of tokens
     * @private
     */
    _tokenizeFormula(formula) {
        const tokenRegex = /(\(|\)|&&|\|\||==|!=|<=|>=|<|>|\+|-|\*|\/|%|\b(?:and|or|not|true|false)\b|\b[a-zA-Z_][a-zA-Z0-9_]*\b|\d+(?:\.\d+)?)/g;
        const tokens = [];
        let match;

        while ((match = tokenRegex.exec(formula)) !== null) {
            tokens.push(match[1]);
        }

        return tokens;
    }

    /**
     * Parse tokens to AST
     * @param {Array} tokens - Token array
     * @returns {Object} - AST node
     * @private
     */
    _parseTokensToAST(tokens) {
        let pos = 0;

        const parseExpression = () => {
            return parseOr();
        };

        const parseOr = () => {
            let left = parseAnd();
            while (pos < tokens.length && (tokens[pos] === '||' || tokens[pos] === 'or')) {
                const op = tokens[pos++];
                const right = parseAnd();
                left = { type: 'binary', op: 'or', left, right };
            }
            return left;
        };

        const parseAnd = () => {
            let left = parseComparison();
            while (pos < tokens.length && (tokens[pos] === '&&' || tokens[pos] === 'and')) {
                const op = tokens[pos++];
                const right = parseComparison();
                left = { type: 'binary', op: 'and', left, right };
            }
            return left;
        };

        const parseComparison = () => {
            let left = parseArithmetic();
            if (pos < tokens.length && ['==', '!=', '<', '>', '<=', '>='].includes(tokens[pos])) {
                const op = tokens[pos++];
                const right = parseArithmetic();
                return { type: 'comparison', op, left, right };
            }
            return left;
        };

        const parseArithmetic = () => {
            let left = parseTerm();
            while (pos < tokens.length && ['+', '-'].includes(tokens[pos])) {
                const op = tokens[pos++];
                const right = parseTerm();
                left = { type: 'arithmetic', op, left, right };
            }
            return left;
        };

        const parseTerm = () => {
            let left = parseUnary();
            while (pos < tokens.length && ['*', '/', '%'].includes(tokens[pos])) {
                const op = tokens[pos++];
                const right = parseUnary();
                left = { type: 'arithmetic', op, left, right };
            }
            return left;
        };

        const parseUnary = () => {
            if (pos < tokens.length && (tokens[pos] === 'not' || tokens[pos] === '!')) {
                const op = tokens[pos++];
                const operand = parseUnary();
                return { type: 'unary', op: 'not', operand };
            }
            return parsePrimary();
        };

        const parsePrimary = () => {
            if (pos >= tokens.length) {
                throw new Error('Unexpected end of expression');
            }

            const token = tokens[pos++];

            if (token === '(') {
                const expr = parseExpression();
                if (pos >= tokens.length || tokens[pos++] !== ')') {
                    throw new Error('Missing closing parenthesis');
                }
                return expr;
            }

            if (token === 'true' || token === 'false') {
                return { type: 'boolean', value: token === 'true' };
            }

            if (/^\d+(\.\d+)?$/.test(token)) {
                return { type: 'number', value: parseFloat(token) };
            }

            if (/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(token)) {
                return { type: 'variable', name: token };
            }

            throw new Error(`Unexpected token: ${token}`);
        };

        return parseExpression();
    }

    /**
     * Convert AST to Z3 constraint
     * @param {number} ctx - Z3 context
     * @param {Object} ast - AST node
     * @param {Map} z3Vars - Z3 variables map
     * @returns {number} - Z3 AST
     * @private
     */
    _astToZ3(ctx, ast, z3Vars) {
        switch (ast.type) {
            case 'boolean':
                return ast.value ? this.z3._Z3_mk_true(ctx) : this.z3._Z3_mk_false(ctx);

            case 'number':
                if (Number.isInteger(ast.value)) {
                    return this._mkInt(ctx, ast.value);
                } else {
                    return this._mkReal(ctx, ast.value);
                }

            case 'variable':
                if (z3Vars.has(ast.name)) {
                    return z3Vars.get(ast.name).var;
                }
                throw new Error(`Unknown variable: ${ast.name}`);

            case 'binary':
                const left = this._astToZ3(ctx, ast.left, z3Vars);
                const right = this._astToZ3(ctx, ast.right, z3Vars);
                
                switch (ast.op) {
                    case 'and': {
                        const argsPtr = this._createWasmArray([left, right]);
                        try {
                            return this.z3._Z3_mk_and(ctx, 2, argsPtr);
                        } finally {
                            this.z3._free(argsPtr);
                        }
                    }
                    case 'or': {
                        const argsPtr = this._createWasmArray([left, right]);
                        try {
                            return this.z3._Z3_mk_or(ctx, 2, argsPtr);
                        } finally {
                            this.z3._free(argsPtr);
                        }
                    }
                }
                break;

            case 'comparison':
                const leftComp = this._astToZ3(ctx, ast.left, z3Vars);
                const rightComp = this._astToZ3(ctx, ast.right, z3Vars);
                
                switch (ast.op) {
                    case '==':
                        return this.z3._Z3_mk_eq(ctx, leftComp, rightComp);
                    case '!=':
                        return this.z3._Z3_mk_not(ctx, this.z3._Z3_mk_eq(ctx, leftComp, rightComp));
                    case '<':
                        return this.z3._Z3_mk_lt(ctx, leftComp, rightComp);
                    case '<=':
                        return this.z3._Z3_mk_le(ctx, leftComp, rightComp);
                    case '>':
                        return this.z3._Z3_mk_gt(ctx, leftComp, rightComp);
                    case '>=':
                        return this.z3._Z3_mk_ge(ctx, leftComp, rightComp);
                }
                break;

            case 'arithmetic':
                const leftArith = this._astToZ3(ctx, ast.left, z3Vars);
                const rightArith = this._astToZ3(ctx, ast.right, z3Vars);
                
                switch (ast.op) {
                    case '+': {
                        const argsPtr = this._createWasmArray([leftArith, rightArith]);
                        try {
                            return this.z3._Z3_mk_add(ctx, 2, argsPtr);
                        } finally {
                            this.z3._free(argsPtr);
                        }
                    }
                    case '-': {
                        const argsPtr = this._createWasmArray([leftArith, rightArith]);
                        try {
                            return this.z3._Z3_mk_sub(ctx, 2, argsPtr);
                        } finally {
                            this.z3._free(argsPtr);
                        }
                    }
                    case '*': {
                        const argsPtr = this._createWasmArray([leftArith, rightArith]);
                        try {
                            return this.z3._Z3_mk_mul(ctx, 2, argsPtr);
                        } finally {
                            this.z3._free(argsPtr);
                        }
                    }
                    case '/':
                        return this.z3._Z3_mk_div(ctx, leftArith, rightArith);
                    case '%':
                        return this.z3._Z3_mk_mod(ctx, leftArith, rightArith);
                }
                break;

            case 'unary':
                if (ast.op === 'not') {
                    const operand = this._astToZ3(ctx, ast.operand, z3Vars);
                    return this.z3._Z3_mk_not(ctx, operand);
                }
                break;
        }

        throw new Error(`Unsupported AST node type: ${ast.type}`);
    }

    /**
     * Solve constraints and return a model
     * @param {string} formulaString - The constraint formula
     * @returns {Object|null} - Variable assignments or null if unsatisfiable
     */
    async solve(formulaString) {
        try {
            await this.ensureInitialized();
            
            const trimmed = (formulaString || '').trim();
            if (trimmed === '' || trimmed === 'true') return {};
            if (trimmed === 'false') return null;

            return this._solveWithZ3(trimmed);
        } catch (error) {
            console.error(`Z3 Solve Error: ${error.message}`);
            return null;
        }
    }

    /**
     * Solve constraints using Z3 and extract model
     * @param {string} formula - The formula to solve
     * @returns {Object|null} - Variable assignments
     * @private
     */
    _solveWithZ3(formula) {
        const ctx = this.z3._Z3_mk_context();
        const solver = this.z3._Z3_mk_solver(ctx);
        this.z3._Z3_solver_inc_ref(ctx, solver);

        try {
            const variables = this._extractVariables(formula);
            const z3Vars = new Map();
            
            // Create Z3 variables
            for (const varName of variables) {
                const symbol = this._mkStringSymbol(ctx, varName);
                let sort;
                
                if (this._isIntegerVariable(varName, formula)) {
                    sort = this.z3._Z3_mk_int_sort(ctx);
                } else if (this._isBooleanVariable(varName, formula)) {
                    sort = this.z3._Z3_mk_bool_sort(ctx);
                } else {
                    sort = this.z3._Z3_mk_real_sort(ctx);
                }
                
                const z3Var = this.z3._Z3_mk_const(ctx, symbol, sort);
                z3Vars.set(varName, { var: z3Var, sort: sort });
            }

            // Convert formula to Z3 constraints
            const z3Constraint = this._parseFormulaToZ3(ctx, formula, z3Vars);
            
            if (z3Constraint) {
                this.z3._Z3_solver_assert(ctx, solver, z3Constraint);
            }

            // Check satisfiability
            const result = this.z3._Z3_solver_check(ctx, solver);
            
            if (result === 1) { // SAT
                const model = this.z3._Z3_solver_get_model(ctx, solver);
                this.z3._Z3_model_inc_ref(ctx, model);
                
                try {
                    const assignments = {};
                    
                    // Extract values for each variable
                    for (const [varName, {var: z3Var, sort}] of z3Vars) {
                        let valuePtr = this.z3._malloc(4); // Allocate space for pointer
                        const evalResult = this.z3._Z3_model_eval(ctx, model, z3Var, false, valuePtr);
                        
                        if (evalResult) {
                            const actualValuePtr = this.z3.HEAP32[valuePtr >> 2];
                            assignments[varName] = this._extractValueFromZ3(ctx, actualValuePtr, sort);
                        }
                        
                        this.z3._free(valuePtr);
                    }
                    
                    return assignments;
                } finally {
                    this.z3._Z3_model_dec_ref(ctx, model);
                }
            }
            
            return null; // UNSAT
            
        } finally {
            this.z3._Z3_solver_dec_ref(ctx, solver);
            this.z3._Z3_del_context(ctx);
        }
    }

    /**
     * Extract value from Z3 AST
     * @param {number} ctx - Z3 context
     * @param {number} ast - Z3 AST
     * @param {number} sort - Z3 sort
     * @returns {*} - Extracted value
     * @private
     */
    _extractValueFromZ3(ctx, ast, sort) {
        const sortKind = this.z3._Z3_get_sort_kind(ctx, sort);
        
        // Z3 sort kind constants
        const Z3_BOOL_SORT = 1;
        const Z3_INT_SORT = 2;
        const Z3_REAL_SORT = 3;
        
        if (sortKind === Z3_INT_SORT) {
            let intPtr = this.z3._malloc(4);
            try {
                const success = this.z3._Z3_get_numeral_int(ctx, ast, intPtr);
                if (success) {
                    return this.z3.HEAP32[intPtr >> 2];
                }
            } finally {
                this.z3._free(intPtr);
            }
        } else if (sortKind === Z3_REAL_SORT) {
            return this.z3._Z3_get_numeral_double(ctx, ast);
        } else if (sortKind === Z3_BOOL_SORT) {
            if (this.z3._Z3_is_true(ctx, ast)) return true;
            if (this.z3._Z3_is_false(ctx, ast)) return false;
        }
        
        // Fallback: try to get as string and parse
        const strPtr = this.z3._Z3_ast_to_string(ctx, ast);
        const str = this.z3.UTF8ToString(strPtr);
        
        if (str === 'true') return true;
        if (str === 'false') return false;
        
        const num = parseFloat(str);
        return isNaN(num) ? str : num;
    }
}

// Global instance for backward compatibility
window.SMTSolver = SMTSolver;