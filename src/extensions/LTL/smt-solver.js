
class SMTSolver {
    constructor() {
        this.MIN_VALUE = Number.NEGATIVE_INFINITY;
        this.MAX_VALUE = Number.POSITIVE_INFINITY;
    }

    /**
     * Main public method. Checks if a given formula string is satisfiable.
     * @param {string} formulaString - The logical formula to check.
     * @returns {boolean} - True if the formula is satisfiable, false otherwise.
     */
    isSatisfiable(formulaString) {
        const trimmed = (formulaString || '').trim();
        if (trimmed === '' || trimmed === 'true') return true;
        if (trimmed === 'false') return false;

        try {
            const tokens = this._tokenize(trimmed);
            if (tokens.length === 0) return true;
            const ast = this._parse(tokens);
            const dnf = this._toDNF(ast);
            for (const clause of dnf) {
                if (this._checkClause(clause)) {
                    return true;
                }
            }
            return false;
        } catch (error) {
            console.error(`SMT Solver Error: ${error.message} in formula \"${formulaString}\"`);
            // Treat errors as unsatisfiable to preserve soundness
            return false;
        }
    }
    /**
     * Checks if a single conjunctive clause is satisfiable.
     * @private
     */
    _checkClause(clause) {
        let context = {};
        let changed = true;
        const clauseSize = clause.length;

        for (let i = 0; i < clauseSize * 2 && changed; i++) {
            changed = false;
            for (const constraint of clause) {
                if (this._propagateConstraint(constraint, context)) {
                    changed = true;
                }
            }
        }
        
        for (const varName in context) {
            const varInfo = context[varName];
            if (varInfo.min > varInfo.max) return false;
            if (varInfo.eq !== undefined) {
                if (varInfo.eq < varInfo.min || varInfo.eq > varInfo.max) return false;
                if (varInfo.not_eq.has(varInfo.eq)) return false;
            }
        }
        return true;
    }

    /**
     * Updates the context with a single constraint.
     * @private
     */
    _propagateConstraint(constraint, context) {
        const { op, left, right } = constraint;
        if (left.type !== 'VAR') return false;

        const varName = left.name;
        if (!context[varName]) {
            context[varName] = { min: this.MIN_VALUE, max: this.MAX_VALUE, eq: undefined, not_eq: new Set() };
        }
        const varInfo = context[varName];
        const oldInfoJSON = JSON.stringify({ ...varInfo, not_eq: [...varInfo.not_eq]});

        const value = this._evaluateExpression(right, context);
        if (value === undefined) return false;

        switch (op) {
            case '==':
                varInfo.eq = varInfo.eq !== undefined ? (varInfo.eq === value ? value : NaN) : value;
                varInfo.min = Math.max(varInfo.min, value);
                varInfo.max = Math.min(varInfo.max, value);
                break;
            case '!=':
                varInfo.not_eq.add(value);
                break;
            case '>':
                varInfo.min = Math.max(varInfo.min, value + (Number.isInteger(value) ? 1 : 1e-10));
                break;
            case '>=':
                varInfo.min = Math.max(varInfo.min, value);
                break;
            case '<':
                varInfo.max = Math.min(varInfo.max, value - (Number.isInteger(value) ? 1 : 1e-10));
                break;
            case '<=':
                varInfo.max = Math.min(varInfo.max, value);
                break;
        }
        
        if (isNaN(varInfo.eq) || varInfo.min > varInfo.max) {
            varInfo.min = 1;
            varInfo.max = 0;
        }

        const newInfoJSON = JSON.stringify({ ...varInfo, not_eq: [...varInfo.not_eq]});
        return oldInfoJSON !== newInfoJSON;
    }

    /**
     * Recursively evaluates an expression AST node within a given context.
     * @private
     */
    _evaluateExpression(node, context) {
        if (node.type === 'NUM' || node.type === 'BOOL' || node.type === 'STR') return node.value;
        if (node.type === 'VAR') return context[node.name]?.eq;
        if (node.type === 'BINARY') {
            const leftVal = this._evaluateExpression(node.left, context);
            const rightVal = this._evaluateExpression(node.right, context);
            if (leftVal === undefined || rightVal === undefined) return undefined;
            
            switch (node.op) {
                case '+': return leftVal + rightVal;
                case '-': return leftVal - rightVal;
                case '*': return leftVal * rightVal;
                case '/': return leftVal / rightVal;
            }
        }
        return undefined;
    }

    // --- PARSER AND DNF CONVERSION SUBSYSTEM ---

    _tokenize(str) {
        const rules = [
            [/^\s+/, null],
            [/^\(/, 'LPAREN'],
            [/^\)/, 'RPAREN'],
            [/^"([^"]*)"/, 'STR'],
            [/^true\b|^false\b/, 'BOOL'],
            [/^-?\d+(\.\d+)?/, 'NUM'],
            [/^[a-zA-Z_]\w*/, 'VAR'],
            [/^(==|!=|<=|>=|<|>)/, 'REL_OP'],
            [/^(&&|\|\|)/, 'LOGIC_OP'],
            [/^(\+|-)/, 'ADD_OP'],
            [/^(\*|\/)/, 'MUL_OP'],
        ];
        let tokens = [];
        let s = str;
        while (s.length > 0) {
            let matched = false;
            for (const [regex, type] of rules) {
                const match = s.match(regex);
                if (match) {
                    if (type) tokens.push({ type, value: match[0] });
                    s = s.substring(match[0].length);
                    matched = true;
                    break;
                }
            }
            if (!matched) throw new Error(`Tokenizer error: Unexpected token at start of: ${s}`);
        }
        return tokens;
    }

    _parse(tokens) {
        this.tokens = tokens;
        this.pos = 0;
        const ast = this._parseLogicalOr();
        if (this.pos < this.tokens.length) throw new Error(`Parser error: Unexpected token ${this._peek().value}`);
        return ast;
    }

    _peek() { return this.tokens[this.pos]; }
    _consume() { return this.tokens[this.pos++]; }

    _parseLogicalOr() {
        let left = this._parseLogicalAnd();
        while (this._peek() && this._peek().value === '||') {
            const opToken = this._consume();
            const right = this._parseLogicalAnd();
            left = { op: 'OR', left, right };
        }
        return left;
    }

    _parseLogicalAnd() {
        let left = this._parseComparison();
        while (this._peek() && this._peek().value === '&&') {
            const opToken = this._consume();
            const right = this._parseComparison();
            left = { op: 'AND', left, right };
        }
        return left;
    }

    _parseComparison() {
        let left = this._parseAddition();
        if (this._peek() && this._peek().type === 'REL_OP') {
            const opToken = this._consume();
            const right = this._parseAddition();
            return { op: opToken.value, left, right };
        }
        return left;
    }
    
    _parseAddition() {
        let left = this._parseMultiplication();
        while (this._peek() && this._peek().type === 'ADD_OP') {
            const opToken = this._consume();
            const right = this._parseMultiplication();
            left = { type: 'BINARY', op: opToken.value, left, right };
        }
        return left;
    }

    _parseMultiplication() {
        let left = this._parsePrimary();
        while (this._peek() && this._peek().type === 'MUL_OP') {
            const opToken = this._consume();
            const right = this._parsePrimary();
            left = { type: 'BINARY', op: opToken.value, left, right };
        }
        return left;
    }

    _parsePrimary() {
        const token = this._peek();
        if (token.type === 'NUM') return this._consume(), { type: 'NUM', value: parseFloat(token.value) };
        if (token.type === 'STR') return this._consume(), { type: 'STR', value: token.value.slice(1, -1) };
        if (token.type === 'BOOL') return this._consume(), { type: 'BOOL', value: token.value === 'true' };
        if (token.type === 'VAR') return this._consume(), { type: 'VAR', name: token.value };
        if (token.type === 'LPAREN') {
            this._consume();
            const expr = this._parseLogicalOr();
            if (this._peek()?.type !== 'RPAREN') throw new Error("Parser error: Missing ')'");
            this._consume();
            return expr;
        }
        throw new Error(`Parser error: Unexpected token ${token.value}`);
    }

    _toDNF(ast) {
        if (!ast.op || ['==', '!=', '<', '>', '<=', '>='].includes(ast.op)) return [[ast]];
        if (ast.op === 'OR') return [...this._toDNF(ast.left), ...this._toDNF(ast.right)];
        if (ast.op === 'AND') {
            const leftDNF = this._toDNF(ast.left);
            const rightDNF = this._toDNF(ast.right);
            const result = [];
            for (const lClause of leftDNF) {
                for (const rClause of rightDNF) {
                    result.push([...lClause, ...rClause]);
                }
            }
            return result;
        }
        return [[ast]]; // Should not be reached for logical ops
    }
}