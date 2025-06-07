/**
 * LTL Integration Layer
 * 
 * This module integrates the new LTL verification system with the existing
 * LTL infrastructure (LTLReader, LTLSyntaxModel, LTLEvaluator, etc.)
 */

/**
 * Enhanced LTL Reader that uses the existing infrastructure
 */
class IntegratedLTLReader {
    constructor() {
        this.syntaxBuilder = null;
    }

    /**
     * Read and parse an LTL expression using the existing infrastructure
     * @param {string} input - The LTL formula string
     * @returns {Object} Parsed LTL AST
     */
    readExpression(input) {
        try {
            // Check if the readExpression function from LTLReader.js is available
            if (typeof readExpression === 'function') {
                return readExpression(input);
            } else {
                // Fallback to manual parsing
                return this.parseManually(input);
            }
        } catch (error) {
            console.error('Error reading LTL expression:', error);
            throw new Error(`Failed to parse LTL expression: ${error.message}`);
        }
    }

    /**
     * Manual parsing fallback
     * @param {string} input - The LTL formula string
     * @returns {Object} Parsed LTL AST
     */
    parseManually(input) {
        const parser = new ManualLTLParser();
        return parser.parse(input);
    }

    /**
     * Link references in the AST
     * @param {Object} ast - The AST to link
     * @param {Map} context - Variable context
     */
    linkReferences(ast, context = new Map()) {
        if (typeof link === 'function') {
            link(ast, context);
        } else {
            // Manual linking
            this.performManualLinking(ast, context);
        }
    }

    /**
     * Perform manual linking of references
     * @param {Object} ast - The AST node
     * @param {Map} context - Variable context
     */
    performManualLinking(ast, context) {
        if (!ast) return;

        if (ast.type === 'LTLReference' && ast.name) {
            if (context.has(ast.name)) {
                ast.setExpression(context.get(ast.name));
            }
        }

        // Recursively link child nodes
        if (ast.left) this.performManualLinking(ast.left, context);
        if (ast.right) this.performManualLinking(ast.right, context);
        if (ast.expression) this.performManualLinking(ast.expression, context);
        if (ast.operand) this.performManualLinking(ast.operand, context);
    }
}

/**
 * Manual LTL Parser for cases where the existing infrastructure isn't available
 */
class ManualLTLParser {
    constructor() {
        this.tokens = [];
        this.position = 0;
    }

    /**
     * Parse an LTL formula
     * @param {string} input - The formula string
     * @returns {Object} LTL AST
     */
    parse(input) {
        this.tokens = this.tokenize(input);
        this.position = 0;
        return this.parseFormula();
    }

    /**
     * Tokenize the input
     * @param {string} input - The input string
     * @returns {Array} Array of tokens
     */
    tokenize(input) {
        const tokenRegex = /(\|[^|]*\||"[^"]*"|G|F|X|U|W|R|M|eventually|globally|next|until|weak-until|weak-release|strong-release|&&|and|\|\||or|!|not|~|->|implies|<->|iff|\(|\)|true|false|[a-zA-Z_][a-zA-Z0-9_]*)/g;
        const tokens = [];
        let match;

        while ((match = tokenRegex.exec(input)) !== null) {
            const value = match[1];
            tokens.push({
                type: this.getTokenType(value),
                value: value,
                position: match.index
            });
        }

        return tokens;
    }

    /**
     * Get the type of a token
     * @param {string} value - Token value
     * @returns {string} Token type
     */
    getTokenType(value) {
        const temporalOps = ['F', 'G', 'X', 'U', 'W', 'R', 'M', 'eventually', 'globally', 'next', 'until', 'weak-until', 'weak-release', 'strong-release'];
        const logicalOps = ['&&', 'and', '||', 'or', '!', 'not', '~', '->', 'implies', '<->', 'iff'];

        if (value === '(' || value === ')') return 'PAREN';
        if (temporalOps.includes(value)) return 'TEMPORAL';
        if (logicalOps.includes(value)) return 'LOGICAL';
        if (value === 'true' || value === 'false') return 'LITERAL';
        if (value.startsWith('|') && value.endsWith('|')) return 'ATOM';
        if (value.startsWith('"') && value.endsWith('"')) return 'ATOM';
        if (/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(value)) return 'IDENTIFIER';

        return 'UNKNOWN';
    }

    /**
     * Parse the main formula
     * @returns {Object} AST node
     */
    parseFormula() {
        return this.parseImplication();
    }

    /**
     * Parse implication
     * @returns {Object} AST node
     */
    parseImplication() {
        let left = this.parseOr();

        while (this.peek() && (this.peek().value === '->' || this.peek().value === 'implies')) {
            const op = this.consume().value;
            const right = this.parseOr();
            left = this.createNode('LTLImplication', op, null, left, right);
        }

        return left;
    }

    /**
     * Parse OR operations
     * @returns {Object} AST node
     */
    parseOr() {
        let left = this.parseAnd();

        while (this.peek() && (this.peek().value === '||' || this.peek().value === 'or')) {
            const op = this.consume().value;
            const right = this.parseAnd();
            left = this.createNode('LTLDisjunction', op, null, left, right);
        }

        return left;
    }

    /**
     * Parse AND operations
     * @returns {Object} AST node
     */
    parseAnd() {
        let left = this.parseUntil();

        while (this.peek() && (this.peek().value === '&&' || this.peek().value === 'and')) {
            const op = this.consume().value;
            const right = this.parseUntil();
            left = this.createNode('LTLConjunction', op, null, left, right);
        }

        return left;
    }

    /**
     * Parse temporal binary operations
     * @returns {Object} AST node
     */
    parseUntil() {
        let left = this.parseUnary();

        while (this.peek() && ['U', 'W', 'R', 'M', 'until', 'weak-until', 'weak-release', 'strong-release'].includes(this.peek().value)) {
            const op = this.consume().value;
            const right = this.parseUnary();

            let type;
            switch (op) {
                case 'U':
                case 'until':
                    type = 'LTLStrongUntil';
                    break;
                case 'W':
                case 'weak-until':
                    type = 'LTLWeakUntil';
                    break;
                case 'R':
                case 'weak-release':
                    type = 'LTLWeakRelease';
                    break;
                case 'M':
                case 'strong-release':
                    type = 'LTLStrongRelease';
                    break;
            }

            left = this.createNode(type, op, null, left, right);
        }

        return left;
    }

    /**
     * Parse unary operations
     * @returns {Object} AST node
     */
    parseUnary() {
        const token = this.peek();

        if (token && ['F', 'G', 'X', 'eventually', 'globally', 'next'].includes(token.value)) {
            const op = this.consume().value;
            const operand = this.parseUnary();

            let type;
            switch (op) {
                case 'F':
                case 'eventually':
                    type = 'LTLEventually';
                    break;
                case 'G':
                case 'globally':
                    type = 'LTLGlobally';
                    break;
                case 'X':
                case 'next':
                    type = 'LTLNext';
                    break;
            }

            return this.createNode(type, op, operand);
        }

        if (token && (token.value === '!' || token.value === 'not' || token.value === '~')) {
            const op = this.consume().value;
            const operand = this.parseUnary();
            return this.createNode('LTLNegation', op, operand);
        }

        return this.parseAtom();
    }

    /**
     * Parse atomic formulas
     * @returns {Object} AST node
     */
    parseAtom() {
        const token = this.peek();

        if (!token) {
            throw new Error('Unexpected end of formula');
        }

        if (token.value === '(') {
            this.consume('(');
            const expr = this.parseFormula();
            this.consume(')');
            return expr;
        }

        if (token.type === 'LITERAL') {
            const value = this.consume().value;
            return this.createNode(value === 'true' ? 'LTLTrue' : 'LTLFalse');
        }

        if (token.type === 'ATOM') {
            const atomValue = this.consume().value;
            let content, delimiter;

            if (atomValue.startsWith('|') && atomValue.endsWith('|')) {
                content = atomValue.slice(1, -1);
                delimiter = '|';
            } else if (atomValue.startsWith('"') && atomValue.endsWith('"')) {
                content = atomValue.slice(1, -1);
                delimiter = '"';
            } else {
                content = atomValue;
                delimiter = '';
            }

            return this.createNode('LTLAtom', null, null, null, null, content, delimiter);
        }

        if (token.type === 'IDENTIFIER') {
            const name = this.consume().value;
            return this.createNode('LTLReference', null, null, null, null, name);
        }

        throw new Error(`Unexpected token: ${token.value}`);
    }

    /**
     * Create an AST node
     * @param {string} type - Node type
     * @param {string} operator - Operator (optional)
     * @param {Object} expression - Expression (optional)
     * @param {Object} left - Left child (optional)
     * @param {Object} right - Right child (optional)
     * @param {string} value - Value (optional)
     * @param {string} delimiter - Delimiter (optional)
     * @returns {Object} AST node
     */
    createNode(type, operator = null, expression = null, left = null, right = null, value = null, delimiter = null) {
        const node = { type };

        if (operator !== null) node.operator = operator;
        if (expression !== null) node.expression = expression;
        if (left !== null) node.left = left;
        if (right !== null) node.right = right;
        if (value !== null) node.value = value;
        if (delimiter !== null) node.delimiter = delimiter;

        // Add accept method for visitor pattern
        node.accept = function(visitor, input) {
            const methodName = `visit${type.replace('LTL', '')}`;
            if (typeof visitor[methodName] === 'function') {
                return visitor[methodName](this, input);
            } else {
                return visitor.visitSyntaxTreeElement(this, input);
            }
        };

        // Special methods for reference nodes
        if (type === 'LTLReference') {
            node.name = value;
            node.setExpression = function(expr) {
                this.expression = expr;
            };
        }

        return node;
    }

    /**
     * Peek at current token
     * @returns {Object} Current token
     */
    peek() {
        return this.position < this.tokens.length ? this.tokens[this.position] : null;
    }

    /**
     * Consume current token
     * @param {string} expected - Expected token value (optional)
     * @returns {Object} Consumed token
     */
    consume(expected = null) {
        const token = this.tokens[this.position];

        if (!token) {
            throw new Error('Unexpected end of formula');
        }

        if (expected && token.value !== expected) {
            throw new Error(`Expected '${expected}' but got '${token.value}'`);
        }

        this.position++;
        return token;
    }
}

/**
 * Data-aware LTL Evaluator that extends the existing LTLEvaluator
 */
class DataAwareLTLEvaluator {
    constructor(atomEvaluator) {
        this.atomEvaluator = atomEvaluator;
    }

    /**
     * Evaluate an LTL formula in a given state
     * @param {Object} formula - The LTL AST
     * @param {Object} state - The current state {marking, valuation}
     * @returns {boolean} Evaluation result
     */
    async evaluate(formula, state) {
        if (!formula) return true;

        switch (formula.type) {
            case 'LTLTrue':
                return true;

            case 'LTLFalse':
                return false;

            case 'LTLAtom':
                return this.evaluateAtom(formula, state);

            case 'LTLReference':
                if (formula.expression) {
                    return this.evaluate(formula.expression, state);
                } else {
                    // Treat as place reference
                    return (state.marking[formula.name] || 0) > 0;
                }

            case 'LTLNegation':
                return !(await this.evaluate(formula.expression, state));

            case 'LTLConjunction':
                return (await this.evaluate(formula.left, state)) && 
                       (await this.evaluate(formula.right, state));

            case 'LTLDisjunction':
                return (await this.evaluate(formula.left, state)) || 
                       (await this.evaluate(formula.right, state));

            case 'LTLImplication':
                const left = await this.evaluate(formula.left, state);
                const right = await this.evaluate(formula.right, state);
                return !left || right;

            case 'LTLEquivalence':
                const leftEq = await this.evaluate(formula.left, state);
                const rightEq = await this.evaluate(formula.right, state);
                return leftEq === rightEq;

            case 'LTLExclusiveDisjunction':
                const leftXor = await this.evaluate(formula.left, state);
                const rightXor = await this.evaluate(formula.right, state);
                return leftXor !== rightXor;

            // Temporal operators should not be evaluated directly in a single state
            case 'LTLEventually':
            case 'LTLGlobally':
            case 'LTLNext':
            case 'LTLStrongUntil':
            case 'LTLWeakUntil':
            case 'LTLWeakRelease':
            case 'LTLStrongRelease':
                console.warn(`Temporal operator ${formula.type} cannot be evaluated in a single state`);
                return false;

            default:
                console.warn(`Unknown formula type: ${formula.type}`);
                return false;
        }
    }

    /**
     * Evaluate an atom in the current state
     * @param {Object} atom - The atom to evaluate
     * @param {Object} state - The current state
     * @returns {boolean} Evaluation result
     */
    evaluateAtom(atom, state) {
        const content = atom.value;

        // Check if it's a data constraint
        const constraintMatch = content.match(/^([a-zA-Z_][a-zA-Z0-9_]*)\s*([<>=!]+)\s*(.+)$/);

        if (constraintMatch) {
            const [, variable, operator, valueStr] = constraintMatch;
            const currentValue = state.valuation[variable];

            if (currentValue === undefined) {
                console.warn(`Variable ${variable} not found in valuation`);
                return false;
            }

            // Parse target value
            let targetValue;
            if (/^".*"$/.test(valueStr.trim())) {
                targetValue = valueStr.trim().slice(1, -1); // Remove quotes
            } else if (!isNaN(valueStr.trim())) {
                targetValue = parseFloat(valueStr.trim());
            } else {
                targetValue = valueStr.trim();
            }

            return this.evaluateConstraint(currentValue, operator, targetValue);
        } else {
            // Simple variable or place reference
            if (state.valuation.hasOwnProperty(content)) {
                return Boolean(state.valuation[content]);
            } else if (state.marking.hasOwnProperty(content)) {
                return (state.marking[content] || 0) > 0;
            }
            return false;
        }
    }

    /**
     * Evaluate a constraint
     * @param {*} value - Current value
     * @param {string} operator - Comparison operator
     * @param {*} target - Target value
     * @returns {boolean} Constraint result
     */
    evaluateConstraint(value, operator, target) {
        const numValue = typeof value === 'number' ? value : parseFloat(value);
        const numTarget = typeof target === 'number' ? target : parseFloat(target);

        if (!isNaN(numValue) && !isNaN(numTarget)) {
            switch (operator.trim()) {
                case '>': return numValue > numTarget;
                case '<': return numValue < numTarget;
                case '>=': return numValue >= numTarget;
                case '<=': return numValue <= numTarget;
                case '==': case '=': return Math.abs(numValue - numTarget) < 1e-10;
                case '!=': return Math.abs(numValue - numTarget) >= 1e-10;
                default: return false;
            }
        } else {
            switch (operator.trim()) {
                case '==': case '=': return value == target;
                case '!=': return value != target;
                default: return false;
            }
        }
    }
}

/**
 * Enhanced LTL to LTL3BA converter that integrates with existing infrastructure
 */
class EnhancedLTLConverterForLTL3BA {
    constructor() {
        this.name2atom = new Map();
        this.atom2name = new Map();
        this.atomCounter = 0;
    }

    /**
     * Transform LTL AST to LTL3BA format
     * @param {Object} ltlSyntax - The LTL AST
     * @returns {Object} Conversion result
     */
    transform(ltlSyntax) {
        // Check if the existing transformer is available
        if (typeof transformToLTL3BA === 'function') {
            return transformToLTL3BA(ltlSyntax);
        } else {
            // Use our own transformer
            return {
                expression: this.convertNode(ltlSyntax),
                name2atom: this.name2atom
            };
        }
    }

    /**
     * Convert an AST node to LTL3BA format
     * @param {Object} node - The AST node
     * @returns {string} LTL3BA expression
     */
    convertNode(node) {
        if (!node) return 'true';

        switch (node.type) {
            case 'LTLTrue':
                return 'true';

            case 'LTLFalse':
                return 'false';

            case 'LTLAtom':
                return this.convertAtom(node);

            case 'LTLReference':
                if (node.expression) {
                    return this.convertNode(node.expression);
                } else {
                    return this.convertAtom({ type: 'LTLAtom', value: node.name, delimiter: '' });
                }

            case 'LTLNegation':
                return `(!${this.convertNode(node.expression)})`;

            case 'LTLNext':
                return `(X ${this.convertNode(node.expression)})`;

            case 'LTLEventually':
                return `(<> ${this.convertNode(node.expression)})`;

            case 'LTLGlobally':
                return `([] ${this.convertNode(node.expression)})`;

            case 'LTLConjunction':
                return `(${this.convertNode(node.left)} && ${this.convertNode(node.right)})`;

            case 'LTLDisjunction':
                return `(${this.convertNode(node.left)} || ${this.convertNode(node.right)})`;

            case 'LTLExclusiveDisjunction':
                // XOR is not supported by LTL3BA, use encoding: (!a && b) || (a && !b)
                return `((!${this.convertNode(node.left)} && ${this.convertNode(node.right)}) || (${this.convertNode(node.left)} && !${this.convertNode(node.right)}))`;

            case 'LTLImplication':
                return `(${this.convertNode(node.left)} -> ${this.convertNode(node.right)})`;

            case 'LTLEquivalence':
                return `(${this.convertNode(node.left)} <-> ${this.convertNode(node.right)})`;

            case 'LTLStrongUntil':
                return `(${this.convertNode(node.left)} U ${this.convertNode(node.right)})`;

            case 'LTLWeakUntil':
                // W is not supported by LTL3BA, use encoding: []a || (a U b)
                return `(([] ${this.convertNode(node.left)}) || (${this.convertNode(node.left)} U ${this.convertNode(node.right)}))`;

            case 'LTLStrongRelease':
                // M is not supported by LTL3BA, use encoding: b U (a && b)
                return `(${this.convertNode(node.right)} U (${this.convertNode(node.left)} && ${this.convertNode(node.right)}))`;

            case 'LTLWeakRelease':
                return `(${this.convertNode(node.left)} R ${this.convertNode(node.right)})`;

            default:
                console.warn(`Unknown node type for LTL3BA conversion: ${node.type}`);
                return 'true';
        }
    }

    /**
     * Convert an atom to LTL3BA format
     * @param {Object} atom - The atom node
     * @returns {string} Atom name for LTL3BA
     */
    convertAtom(atom) {
        let name = this.atom2name.get(atom);
        if (name === undefined) {
            name = `atom${this.atomCounter++}`;
            this.name2atom.set(name, atom);
            this.atom2name.set(atom, name);
        }
        return name;
    }
}

/**
 * Integration manager that coordinates all components
 */
class LTLIntegrationManager {
    constructor() {
        this.reader = new IntegratedLTLReader();
        this.evaluator = null;
        this.converter = new EnhancedLTLConverterForLTL3BA();
    }

    /**
     * Initialize the integration manager
     * @param {Object} options - Configuration options
     */
    initialize(options = {}) {
        // Set up evaluator with atom evaluator
        const atomEvaluator = options.atomEvaluator || this.defaultAtomEvaluator;
        this.evaluator = new DataAwareLTLEvaluator(atomEvaluator);
    }

    /**
     * Default atom evaluator
     * @param {string} atomValue - The atom value
     * @param {Object} input - Input context
     * @returns {boolean} Evaluation result
     */
    defaultAtomEvaluator(atomValue, input) {
        if (input && input.marking && input.marking[atomValue] !== undefined) {
            return input.marking[atomValue] > 0;
        }
        if (input && input.valuation && input.valuation[atomValue] !== undefined) {
            return Boolean(input.valuation[atomValue]);
        }
        return false;
    }

    /**
     * Parse an LTL formula
     * @param {string} formula - The formula string
     * @returns {Object} Parsed AST
     */
    parseFormula(formula) {
        return this.reader.readExpression(formula);
    }

    /**
     * Evaluate a formula in a state
     * @param {Object} ast - The formula AST
     * @param {Object} state - The state
     * @returns {boolean} Evaluation result
     */
    async evaluateFormula(ast, state) {
        if (!this.evaluator) {
            this.initialize();
        }
        return this.evaluator.evaluate(ast, state);
    }

    /**
     * Convert formula to LTL3BA format
     * @param {Object} ast - The formula AST
     * @returns {Object} Conversion result
     */
    convertToLTL3BA(ast) {
        return this.converter.transform(ast);
    }

    /**
     * Get available atoms from a Data Petri Net
     * @param {Object} petriNet - The Petri net
     * @returns {Array} Available atom names
     */
    getAvailableAtoms(petriNet) {
        const atoms = [];

        // Add place names
        if (petriNet.places) {
            for (const [id, place] of petriNet.places) {
                atoms.push(place.label);
            }
        }

        // Add data variable names
        if (petriNet.dataVariables) {
            for (const [id, variable] of petriNet.dataVariables) {
                atoms.push(variable.name);
            }
        }

        return atoms;
    }

    /**
     * Create a state object from Petri net state
     * @param {Object} petriNet - The Petri net
     * @returns {Object} State object
     */
    createStateFromPetriNet(petriNet) {
        const marking = {};
        const valuation = {};

        // Extract marking
        if (petriNet.places) {
            for (const [id, place] of petriNet.places) {
                marking[place.label] = place.tokens || 0;
            }
        }

        // Extract data valuation
        if (petriNet.dataVariables) {
            for (const [id, variable] of petriNet.dataVariables) {
                valuation[variable.name] = variable.getValue ? variable.getValue() : (variable.value || 0);
            }
        }

        return { marking, valuation };
    }
}

// Export the integration manager
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        LTLIntegrationManager,
        IntegratedLTLReader,
        DataAwareLTLEvaluator,
        EnhancedLTLConverterForLTL3BA,
        ManualLTLParser
    };
} else {
    window.LTLIntegrationManager = LTLIntegrationManager;
    window.IntegratedLTLReader = IntegratedLTLReader;
    window.DataAwareLTLEvaluator = DataAwareLTLEvaluator;
    window.EnhancedLTLConverterForLTL3BA = EnhancedLTLConverterForLTL3BA;
    window.ManualLTLParser = ManualLTLParser;
}