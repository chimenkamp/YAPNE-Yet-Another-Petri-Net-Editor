/**
 * z3-solver.js
 *
 * An SMT solver implementation for the LTL model checker using Z3.js.
 * This version is designed to receive a pre-initialized Z3 instance.
 */
class Z3Solver {
    /**
     * @param {Z3.Context} z3Instance - The initialized Z3 context from Z3.init().
     */
    constructor(z3Instance) {
        if (!z3Instance || typeof z3Instance.Solver !== 'function') {
            throw new Error("Invalid Z3 instance provided to Z3Solver constructor.");
        }
        this.z3 = z3Instance;
    }

    /**
     * Main public method. Checks if a given formula string is satisfiable.
     * @param {string} formulaString - The logical formula to check.
     * @returns {Promise<boolean>} - True if the formula is satisfiable, false otherwise.
     */
    async isSatisfiable(formulaString) {
        const trimmed = (formulaString || '').trim();
        if (trimmed === '' || trimmed.toLowerCase() === 'true') return true;
        if (trimmed.toLowerCase() === 'false') return false;

        try {
            const solver = new this.z3.Solver();
            const z3Expr = this.parseFormulaToZ3(trimmed);
            solver.add(z3Expr);
            const result = await solver.check();
            return result === 'sat';
        } catch (error) {
            console.error(`Z3 Solver Error: ${error.message} in formula "${formulaString}"`);
            return false; // Fail safely
        }
    }

    /**
     * Parses a formula string into a Z3 expression object.
     * @param {string} text - The formula string.
     * @returns {Z3.Expr} A Z3 expression.
     */
    parseFormulaToZ3(text) {
        const tokens = text.match(/([a-zA-Z_]\w*\'?|<=|>=|==|!=|<|>|&&|\|\||\d+|\(|\)|\+|-|\*|\/)/g) || [];
        let pos = 0;

        const parseLogicOr = () => {
            let left = parseLogicAnd();
            while (pos < tokens.length && tokens[pos] === '||') {
                pos++;
                const right = parseLogicAnd();
                left = this.z3.Or(left, right);
            }
            return left;
        };

        const parseLogicAnd = () => {
            let left = parseComparison();
            while (pos < tokens.length && tokens[pos] === '&&') {
                pos++;
                const right = parseComparison();
                left = this.z3.And(left, right);
            }
            return left;
        };
        
        const parseComparison = () => {
            const left = parseExpr();
            if (pos < tokens.length && ['<', '>', '<=', '>=', '==', '!='].includes(tokens[pos])) {
                const op = tokens[pos++];
                const right = parseExpr();
                switch (op) {
                    case '<':  return this.z3.LT(left, right);
                    case '>':  return this.z3.GT(left, right);
                    case '<=': return this.z3.LE(left, right);
                    case '>=': return this.z3.GE(left, right);
                    case '==': return this.z3.Eq(left, right);
                    case '!=': return this.z3.Distinct(left, right);
                }
            }
            return left;
        };

        const parseExpr = () => {
            let left = parseTerm();
            while (pos < tokens.length && (tokens[pos] === '+' || tokens[pos] === '-')) {
                const op = tokens[pos++];
                const right = parseTerm();
                if (op === '+') left = this.z3.Add(left, right);
                else left = this.z3.Sub(left, right);
            }
            return left;
        };

        const parseTerm = () => {
            let left = parseFactor();
            while (pos < tokens.length && (tokens[pos] === '*' || tokens[pos] === '/')) {
                const op = tokens[pos++];
                const right = parseFactor();
                if (op === '*') left = this.z3.Mul(left, right);
                else left = this.z3.Div(left, right);
            }
            return left;
        };

        const parseFactor = () => {
            const token = tokens[pos++];
            if (token === '(') {
                const result = parseLogicOr();
                if (tokens[pos++] !== ')') throw new Error("Mismatched parentheses in formula.");
                return result;
            } else if (!isNaN(token)) {
                // Assuming integer variables for Petri net data. Change if you use floating point.
                return this.z3.IntVal(parseInt(token, 10));
            } else {
                return this.z3.Int(token);
            }
        };

        return parseLogicOr();
    }
}