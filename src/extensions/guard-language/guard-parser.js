/**
 * Guard Language Parser
 * Parses tokenized guard expressions into an AST.
 * Supports both SMT-LIB2 prefix form and restricted infix form.
 * The two forms may not be mixed within a single expression.
 */

import { tokenize, TokenType, LexerError } from './guard-lexer.js';

// ─── AST Node Types ───────────────────────────────────────────────────────

/** AST node types */
export const NodeType = Object.freeze({
  LITERAL:    'Literal',      // { sort: 'Int'|'Real'|'Bool', value }
  VAR:        'Var',          // { name, primed: boolean }
  BINOP:      'BinOp',        // { op, left, right }
  UNARYOP:    'UnaryOp',      // { op, operand }
  CALL:       'Call',         // { op, args: [] }  — SMT multi-arg ops
  QUANTIFIER: 'Quantifier',   // { kind: 'exists'|'forall', bindings: [{name,sort}], body }
  LET_EXPR:   'Let',          // { bindings: [{name,expr}], body }
});

/** Create a literal node */
export function litNode(sort, value) {
  return { type: NodeType.LITERAL, sort, value };
}

/** Create a variable reference node */
export function varNode(name, primed = false) {
  return { type: NodeType.VAR, name, primed };
}

/** Create a binary operation node */
export function binopNode(op, left, right) {
  return { type: NodeType.BINOP, op, left, right };
}

/** Create a unary operation node */
export function unaryNode(op, operand) {
  return { type: NodeType.UNARYOP, op, operand };
}

/** Create a multi-argument call node (SMT ops like and, or, +, -, etc.) */
export function callNode(op, args) {
  return { type: NodeType.CALL, op, args };
}

/** Create a quantifier node */
export function quantifierNode(kind, bindings, body) {
  return { type: NodeType.QUANTIFIER, kind, bindings, body };
}

/** Create a let expression node */
export function letNode(bindings, body) {
  return { type: NodeType.LET_EXPR, bindings, body };
}

// ─── Parse Error ──────────────────────────────────────────────────────────

export class ParseError extends Error {
  /**
   * @param {string} message
   * @param {number} pos - 0-based character offset in the input
   */
  constructor(message, pos) {
    super(message);
    this.name = 'ParseError';
    this.pos = pos;
  }
}

// ─── SMT Operators with Arity Constraints ─────────────────────────────────

/**
 * Arity map for SMT operators: [minArgs, maxArgs].
 * null for maxArgs means unbounded.
 */
const SMT_ARITY = new Map([
  ['and',      [1, null]],
  ['or',       [1, null]],
  ['not',      [1, null]],   // not: ≥1 (spec says ≥1)
  ['+',        [1, null]],
  ['-',        [1, null]],
  ['*',        [2, null]],
  ['/',        [2, null]],
  ['=>',       [2, null]],
  ['=',        [2, null]],
  ['distinct', [2, null]],
  ['<',        [2, null]],
  ['<=',       [2, null]],
  ['>',        [2, null]],
  ['>=',       [2, null]],
  ['ite',      [3, 3]],
]);

/** Set of all valid SMT operator names */
const SMT_OPS = new Set(SMT_ARITY.keys());
// Add quantifiers and let (handled separately)
SMT_OPS.add('exists');
SMT_OPS.add('forall');
SMT_OPS.add('let');

// ─── Parser Class ─────────────────────────────────────────────────────────

class Parser {
  /**
   * @param {import('./guard-lexer.js').Token[]} tokens
   * @param {boolean} isPostcondition - Whether primed variables are allowed
   */
  constructor(tokens, isPostcondition) {
    this.tokens = tokens;
    this.pos = 0;
    this.isPostcondition = isPostcondition;
  }

  /** Current token */
  peek() {
    return this.tokens[this.pos];
  }

  /** Consume and return current token */
  advance() {
    const tok = this.tokens[this.pos];
    this.pos++;
    return tok;
  }

  /** Expect a specific token type, consume and return it, or throw */
  expect(type) {
    const tok = this.peek();
    if (tok.type !== type) {
      throw new ParseError(
        `Expected ${type} but got ${tok.type} ('${tok.value}')`,
        tok.pos
      );
    }
    return this.advance();
  }

  /** Check if current token is of a given type */
  check(type) {
    return this.peek().type === type;
  }

  /** Check if current token matches a type and value */
  checkValue(type, value) {
    const tok = this.peek();
    return tok.type === type && tok.value === value;
  }

  // ─── Top-level dispatch ───────────────────────────────────────────────

  /**
   * Parse the full expression.
   * If the first non-whitespace token is '(', parse as SMT prefix form.
   * Otherwise, parse as infix form.
   */
  parseExpression() {
    if (this.check(TokenType.EOF)) {
      return null; // empty expression
    }

    let ast;
    if (this.check(TokenType.LPAREN)) {
      ast = this.parseSmt();
    } else {
      ast = this.parseDisjunction();
    }

    // Must consume all tokens
    if (!this.check(TokenType.EOF)) {
      const tok = this.peek();
      throw new ParseError(
        `Unexpected token '${tok.value}' after end of expression`,
        tok.pos
      );
    }

    return ast;
  }

  // ─── SMT-LIB2 Prefix Parser ──────────────────────────────────────────

  /**
   * Parse an SMT s-expression: (op arg1 arg2 ...) | ident | number | bool_lit
   */
  parseSmt() {
    const tok = this.peek();

    if (tok.type === TokenType.LPAREN) {
      return this.parseSmtApplication();
    }
    if (tok.type === TokenType.IDENT) {
      return this.parseSmtAtom();
    }
    if (tok.type === TokenType.INTEGER || tok.type === TokenType.REAL) {
      return this.parseSmtNumber();
    }
    if (tok.type === TokenType.BOOL_LIT) {
      return this.parseSmtBoolLit();
    }
    // Allow + or - as prefix for numbers inside SMT forms
    if (tok.type === TokenType.PLUS || tok.type === TokenType.MINUS) {
      return this.parseSmtNumber();
    }

    throw new ParseError(
      `Unexpected token '${tok.value}' in SMT expression`,
      tok.pos
    );
  }

  /** Parse (op args...) in SMT prefix form */
  parseSmtApplication() {
    const lp = this.expect(TokenType.LPAREN);

    const opTok = this.peek();

    // Determine the operator
    let op;
    if (opTok.type === TokenType.AND)      op = 'and';
    else if (opTok.type === TokenType.OR)   op = 'or';
    else if (opTok.type === TokenType.NOT)  op = 'not';
    else if (opTok.type === TokenType.IMPLIES) op = '=>';
    else if (opTok.type === TokenType.ITE)  op = 'ite';
    else if (opTok.type === TokenType.DISTINCT) op = 'distinct';
    else if (opTok.type === TokenType.EXISTS) op = 'exists';
    else if (opTok.type === TokenType.FORALL) op = 'forall';
    else if (opTok.type === TokenType.LET)  op = 'let';
    else if (opTok.type === TokenType.EQ)   op = '=';
    else if (opTok.type === TokenType.LT)   op = '<';
    else if (opTok.type === TokenType.LE)   op = '<=';
    else if (opTok.type === TokenType.GT)   op = '>';
    else if (opTok.type === TokenType.GE)   op = '>=';
    else if (opTok.type === TokenType.PLUS) op = '+';
    else if (opTok.type === TokenType.MINUS) op = '-';
    else if (opTok.type === TokenType.STAR) op = '*';
    else if (opTok.type === TokenType.SLASH) op = '/';
    else {
      // Reject uninterpreted function symbols: (f ...) where f is an ident
      // Also reject (number) forms like (10)
      throw new ParseError(
        `Invalid SMT operator '${opTok.value}'. Only built-in operators are allowed (and, or, not, =>, ite, distinct, =, <, <=, >, >=, +, -, *, /, exists, forall, let).`,
        opTok.pos
      );
    }
    this.advance(); // consume operator

    // Handle quantifiers
    if (op === 'exists' || op === 'forall') {
      return this.parseSmtQuantifier(op, lp.pos);
    }

    // Handle let
    if (op === 'let') {
      return this.parseSmtLet(lp.pos);
    }

    // Parse arguments
    const args = [];
    while (!this.check(TokenType.RPAREN) && !this.check(TokenType.EOF)) {
      args.push(this.parseSmt());
    }
    this.expect(TokenType.RPAREN);

    // Validate arity
    const arity = SMT_ARITY.get(op);
    if (arity) {
      const [minArgs, maxArgs] = arity;
      if (args.length < minArgs) {
        throw new ParseError(
          `Operator '${op}' requires at least ${minArgs} argument(s), got ${args.length}`,
          lp.pos
        );
      }
      if (maxArgs !== null && args.length > maxArgs) {
        throw new ParseError(
          `Operator '${op}' accepts at most ${maxArgs} argument(s), got ${args.length}`,
          lp.pos
        );
      }
    }

    return callNode(op, args);
  }

  /** Parse (exists ((v1 Sort1) ...) body) */
  parseSmtQuantifier(kind, startPos) {
    this.expect(TokenType.LPAREN); // opening of bindings list

    const bindings = [];
    while (this.check(TokenType.LPAREN)) {
      this.advance(); // (
      const nameTok = this.expect(TokenType.IDENT);
      const sortTok = this.expect(TokenType.IDENT);
      bindings.push({ name: nameTok.value, sort: sortTok.value });
      this.expect(TokenType.RPAREN); // )
    }
    this.expect(TokenType.RPAREN); // close bindings list

    if (bindings.length === 0) {
      throw new ParseError(
        `Quantifier '${kind}' requires at least one binding`,
        startPos
      );
    }

    const body = this.parseSmt();
    this.expect(TokenType.RPAREN); // close quantifier

    return quantifierNode(kind, bindings, body);
  }

  /** Parse (let ((v1 expr1) ...) body) */
  parseSmtLet(startPos) {
    this.expect(TokenType.LPAREN); // opening of bindings list

    const bindings = [];
    while (this.check(TokenType.LPAREN)) {
      this.advance(); // (
      const nameTok = this.expect(TokenType.IDENT);
      const expr = this.parseSmt();
      bindings.push({ name: nameTok.value, expr });
      this.expect(TokenType.RPAREN); // )
    }
    this.expect(TokenType.RPAREN); // close bindings list

    if (bindings.length === 0) {
      throw new ParseError(`'let' requires at least one binding`, startPos);
    }

    const body = this.parseSmt();
    this.expect(TokenType.RPAREN); // close let

    return letNode(bindings, body);
  }

  /** Parse an identifier atom, possibly with prime */
  parseSmtAtom() {
    const tok = this.advance();
    // Check for prime
    if (this.check(TokenType.PRIME)) {
      if (!this.isPostcondition) {
        throw new ParseError(
          `Primed variable '${tok.value}'' is not allowed in preconditions`,
          tok.pos
        );
      }
      this.advance(); // consume '
      return varNode(tok.value, true);
    }
    return varNode(tok.value, false);
  }

  /** Parse a number in SMT context */
  parseSmtNumber() {
    const tok = this.peek();
    // Handle signed numbers
    if (tok.type === TokenType.PLUS || tok.type === TokenType.MINUS) {
      const sign = this.advance();
      const numTok = this.peek();
      if (numTok.type === TokenType.INTEGER || numTok.type === TokenType.REAL) {
        this.advance();
        const value = sign.value + numTok.value;
        return litNode(numTok.type === TokenType.REAL ? 'Real' : 'Int',
          numTok.type === TokenType.REAL ? parseFloat(value) : parseInt(value, 10));
      }
      throw new ParseError(`Expected number after '${sign.value}'`, sign.pos);
    }

    const numTok = this.advance();
    if (numTok.type === TokenType.REAL) {
      return litNode('Real', parseFloat(numTok.value));
    }
    return litNode('Int', parseInt(numTok.value, 10));
  }

  /** Parse a boolean literal in SMT context */
  parseSmtBoolLit() {
    const tok = this.advance();
    return litNode('Bool', tok.value === 'true');
  }

  // ─── Infix Parser (Recursive Descent) ─────────────────────────────────

  /**
   * disj ::= conj ( ('or' | '||') conj )*
   */
  parseDisjunction() {
    let left = this.parseConjunction();

    while (this.check(TokenType.OR)) {
      this.advance();
      const right = this.parseConjunction();
      left = binopNode('or', left, right);
    }

    return left;
  }

  /**
   * conj ::= neg ( ('and' | '&&') neg )*
   */
  parseConjunction() {
    let left = this.parseNegation();

    while (this.check(TokenType.AND)) {
      this.advance();
      const right = this.parseNegation();
      left = binopNode('and', left, right);
    }

    return left;
  }

  /**
   * neg ::= ('not' neg) | cmp
   */
  parseNegation() {
    if (this.check(TokenType.NOT)) {
      const tok = this.advance();
      const operand = this.parseNegation();
      return unaryNode('not', operand);
    }
    return this.parseComparison();
  }

  /**
   * cmp ::= arith ( rel_op arith )?
   */
  parseComparison() {
    const left = this.parseArithmetic();

    const tok = this.peek();
    if (tok.type === TokenType.EQ ||
        tok.type === TokenType.DISTINCT ||
        tok.type === TokenType.LT ||
        tok.type === TokenType.LE ||
        tok.type === TokenType.GT ||
        tok.type === TokenType.GE) {
      const opTok = this.advance();
      const right = this.parseArithmetic();
      const op = opTok.type === TokenType.DISTINCT ? 'distinct' : opTok.value;
      return binopNode(op, left, right);
    }

    return left;
  }

  /**
   * arith ::= term ( ('+' | '-') term )*
   */
  parseArithmetic() {
    let left = this.parseTerm();

    while (this.check(TokenType.PLUS) || this.check(TokenType.MINUS)) {
      const opTok = this.advance();
      const right = this.parseTerm();
      left = binopNode(opTok.value, left, right);
    }

    return left;
  }

  /**
   * term ::= factor ( ('*' | '/') factor )*
   */
  parseTerm() {
    let left = this.parseFactor();

    while (this.check(TokenType.STAR) || this.check(TokenType.SLASH)) {
      const opTok = this.advance();
      const right = this.parseFactor();
      left = binopNode(opTok.value, left, right);
    }

    return left;
  }

  /**
   * factor ::= '(' infix_expr ')' | var_ref | number | bool_lit
   */
  parseFactor() {
    const tok = this.peek();

    // Parenthesized expression
    if (tok.type === TokenType.LPAREN) {
      this.advance(); // (
      const inner = this.parseDisjunction();
      this.expect(TokenType.RPAREN);
      return inner;
    }

    // Number literals
    if (tok.type === TokenType.INTEGER || tok.type === TokenType.REAL) {
      this.advance();
      if (tok.type === TokenType.REAL) {
        return litNode('Real', parseFloat(tok.value));
      }
      return litNode('Int', parseInt(tok.value, 10));
    }

    // Boolean literals
    if (tok.type === TokenType.BOOL_LIT) {
      this.advance();
      return litNode('Bool', tok.value === 'true');
    }

    // Identifier (possibly primed)
    if (tok.type === TokenType.IDENT) {
      this.advance();
      if (this.check(TokenType.PRIME)) {
        if (!this.isPostcondition) {
          throw new ParseError(
            `Primed variable '${tok.value}'' is not allowed in preconditions`,
            tok.pos
          );
        }
        this.advance(); // consume '
        return varNode(tok.value, true);
      }
      return varNode(tok.value, false);
    }

    // Unary minus in factor position (e.g., -x, -5)
    if (tok.type === TokenType.MINUS) {
      this.advance();
      const operand = this.parseFactor();
      // Optimize: if operand is a literal number, negate it directly
      if (operand.type === NodeType.LITERAL && (operand.sort === 'Int' || operand.sort === 'Real')) {
        operand.value = -operand.value;
        return operand;
      }
      return unaryNode('-', operand);
    }

    // Unary plus (discard)
    if (tok.type === TokenType.PLUS) {
      this.advance();
      return this.parseFactor();
    }

    throw new ParseError(
      `Unexpected token '${tok.value}' — expected variable, number, boolean, or '('`,
      tok.pos
    );
  }
}

// ─── Public API ───────────────────────────────────────────────────────────

/**
 * Parse a guard expression string into an AST.
 *
 * @param {string} input - The expression string
 * @param {Object} [options]
 * @param {boolean} [options.isPostcondition=false] - Whether primed variables are allowed
 * @returns {{ ast: Object|null, tokens: import('./guard-lexer.js').Token[] }}
 * @throws {ParseError|LexerError} On syntax or lexical errors
 */
export function parse(input, options = {}) {
  const isPostcondition = options.isPostcondition || false;
  const trimmed = (input || '').trim();

  if (!trimmed) {
    return { ast: null, tokens: [] };
  }

  const tokens = tokenize(trimmed);
  const parser = new Parser(tokens, isPostcondition);
  const ast = parser.parseExpression();

  return { ast, tokens };
}

export { LexerError };
