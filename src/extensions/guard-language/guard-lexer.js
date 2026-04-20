/**
 * Guard Language Lexer
 * Tokenizes guard expressions (preconditions/postconditions) for Data Petri Nets.
 * Supports both SMT-LIB2 prefix form and restricted infix form.
 */

/** Token types */
export const TokenType = Object.freeze({
  // Literals
  INTEGER:    'INTEGER',
  REAL:       'REAL',
  BOOL_LIT:   'BOOL_LIT',
  IDENT:      'IDENT',

  // Keywords (logical)
  AND:        'AND',
  OR:         'OR',
  NOT:        'NOT',
  IMPLIES:    'IMPLIES',     // =>
  ITE:        'ITE',
  DISTINCT:   'DISTINCT',
  EXISTS:     'EXISTS',
  FORALL:     'FORALL',
  LET:        'LET',

  // Comparison operators
  EQ:         'EQ',          // =
  LT:         'LT',          // <
  LE:         'LE',          // <=
  GT:         'GT',          // >
  GE:         'GE',          // >=

  // Arithmetic operators
  PLUS:       'PLUS',        // +
  MINUS:      'MINUS',       // -
  STAR:       'STAR',        // *
  SLASH:      'SLASH',       // /

  // Delimiters
  LPAREN:     'LPAREN',      // (
  RPAREN:     'RPAREN',      // )

  // Prime
  PRIME:      'PRIME',       // '

  // End
  EOF:        'EOF',
});

/** Reserved suffixes that must not be used as base variable names */
const RESERVED_SUFFIXES = ['_r', '_w', '_prime'];

/** Keyword map (case-insensitive) */
const KEYWORDS = new Map([
  ['and',      TokenType.AND],
  ['or',       TokenType.OR],
  ['not',      TokenType.NOT],
  ['true',     TokenType.BOOL_LIT],
  ['false',    TokenType.BOOL_LIT],
  ['ite',      TokenType.ITE],
  ['distinct', TokenType.DISTINCT],
  ['exists',   TokenType.EXISTS],
  ['forall',   TokenType.FORALL],
  ['let',      TokenType.LET],
]);

/**
 * A single token produced by the lexer
 */
export class Token {
  /**
   * @param {string} type - TokenType value
   * @param {string} value - Raw string value
   * @param {number} pos - 0-based character offset in the input
   */
  constructor(type, value, pos) {
    this.type = type;
    this.value = value;
    this.pos = pos;
  }
}

/**
 * Lexer error with position information
 */
export class LexerError extends Error {
  /**
   * @param {string} message - Error description
   * @param {number} pos - 0-based character offset where the error occurred
   */
  constructor(message, pos) {
    super(message);
    this.name = 'LexerError';
    this.pos = pos;
  }
}

/**
 * Tokenize a guard expression string.
 *
 * @param {string} input - The expression to tokenize
 * @returns {Token[]} Array of tokens (always ends with EOF)
 * @throws {LexerError} On unrecognized characters or reserved names
 */
export function tokenize(input) {
  const tokens = [];
  let i = 0;
  const len = input.length;

  while (i < len) {
    const ch = input[i];

    // Skip whitespace
    if (/\s/.test(ch)) {
      i++;
      continue;
    }

    // Single-character tokens
    if (ch === '(') { tokens.push(new Token(TokenType.LPAREN, '(', i)); i++; continue; }
    if (ch === ')') { tokens.push(new Token(TokenType.RPAREN, ')', i)); i++; continue; }
    if (ch === '*') { tokens.push(new Token(TokenType.STAR, '*', i)); i++; continue; }
    if (ch === '/') { tokens.push(new Token(TokenType.SLASH, '/', i)); i++; continue; }
    if (ch === "'") { tokens.push(new Token(TokenType.PRIME, "'", i)); i++; continue; }

    // => (implies)
    if (ch === '=' && i + 1 < len && input[i + 1] === '>') {
      tokens.push(new Token(TokenType.IMPLIES, '=>', i));
      i += 2;
      continue;
    }

    // == normalized to = (EQ)
    if (ch === '=' && i + 1 < len && input[i + 1] === '=') {
      tokens.push(new Token(TokenType.EQ, '=', i));
      i += 2;
      continue;
    }

    // = (EQ)
    if (ch === '=') {
      tokens.push(new Token(TokenType.EQ, '=', i));
      i++;
      continue;
    }

    // != normalized to DISTINCT
    if (ch === '!' && i + 1 < len && input[i + 1] === '=') {
      tokens.push(new Token(TokenType.DISTINCT, 'distinct', i));
      i += 2;
      continue;
    }

    // <= (LE)
    if (ch === '<' && i + 1 < len && input[i + 1] === '=') {
      tokens.push(new Token(TokenType.LE, '<=', i));
      i += 2;
      continue;
    }

    // < (LT)
    if (ch === '<') {
      tokens.push(new Token(TokenType.LT, '<', i));
      i++;
      continue;
    }

    // >= (GE) — but not => (already handled above)
    if (ch === '>' && i + 1 < len && input[i + 1] === '=') {
      tokens.push(new Token(TokenType.GE, '>=', i));
      i += 2;
      continue;
    }

    // > (GT)
    if (ch === '>') {
      tokens.push(new Token(TokenType.GT, '>', i));
      i++;
      continue;
    }

    // && normalized to AND
    if (ch === '&' && i + 1 < len && input[i + 1] === '&') {
      tokens.push(new Token(TokenType.AND, 'and', i));
      i += 2;
      continue;
    }

    // || normalized to OR
    if (ch === '|' && i + 1 < len && input[i + 1] === '|') {
      tokens.push(new Token(TokenType.OR, 'or', i));
      i += 2;
      continue;
    }

    // + / - : could be operator or part of a number
    if (ch === '+' || ch === '-') {
      // Check if this is a sign for a number (not preceded by a value token)
      const prevToken = tokens.length > 0 ? tokens[tokens.length - 1] : null;
      const isSign = !prevToken ||
        prevToken.type === TokenType.LPAREN ||
        prevToken.type === TokenType.EQ ||
        prevToken.type === TokenType.LT ||
        prevToken.type === TokenType.LE ||
        prevToken.type === TokenType.GT ||
        prevToken.type === TokenType.GE ||
        prevToken.type === TokenType.DISTINCT ||
        prevToken.type === TokenType.PLUS ||
        prevToken.type === TokenType.MINUS ||
        prevToken.type === TokenType.STAR ||
        prevToken.type === TokenType.SLASH ||
        prevToken.type === TokenType.AND ||
        prevToken.type === TokenType.OR ||
        prevToken.type === TokenType.NOT ||
        prevToken.type === TokenType.IMPLIES ||
        prevToken.type === TokenType.ITE;

      if (isSign && i + 1 < len && /\d/.test(input[i + 1])) {
        // Signed number
        const start = i;
        i++; // skip sign
        const numToken = readNumber(input, i, start);
        tokens.push(numToken);
        i = start + numToken.value.length;
        continue;
      }

      // Otherwise it's an operator
      if (ch === '+') {
        tokens.push(new Token(TokenType.PLUS, '+', i));
      } else {
        tokens.push(new Token(TokenType.MINUS, '-', i));
      }
      i++;
      continue;
    }

    // Numbers
    if (/\d/.test(ch)) {
      const numToken = readNumber(input, i, i);
      tokens.push(numToken);
      i += numToken.value.length;
      continue;
    }

    // Identifiers and keywords
    if (/[a-zA-Z_]/.test(ch)) {
      const start = i;
      while (i < len && /[a-zA-Z0-9_]/.test(input[i])) {
        i++;
      }
      const word = input.slice(start, i);
      const lower = word.toLowerCase();

      // Check for reserved suffixes on base variable names
      for (const suffix of RESERVED_SUFFIXES) {
        if (lower.endsWith(suffix) && lower !== suffix) {
          throw new LexerError(
            `Identifier "${word}" uses reserved suffix "${suffix}". ` +
            `Names ending in _r, _w, or _prime are reserved for internal use.`,
            start
          );
        }
      }

      // Check for keyword
      const kwType = KEYWORDS.get(lower);
      if (kwType) {
        if (kwType === TokenType.BOOL_LIT) {
          tokens.push(new Token(TokenType.BOOL_LIT, lower, start));
        } else {
          tokens.push(new Token(kwType, lower, start));
        }
      } else {
        tokens.push(new Token(TokenType.IDENT, word, start));
      }
      continue;
    }

    throw new LexerError(`Unexpected character '${ch}'`, i);
  }

  tokens.push(new Token(TokenType.EOF, '', len));
  return tokens;
}

/**
 * Read a number (integer or real) starting at position `i` in `input`.
 * @param {string} input
 * @param {number} i - Position of first digit
 * @param {number} tokenStart - Position of the token start (may include sign)
 * @returns {Token}
 */
function readNumber(input, i, tokenStart) {
  let end = i;
  const len = input.length;

  while (end < len && /\d/.test(input[end])) {
    end++;
  }

  // Check for decimal point
  if (end < len && input[end] === '.' && end + 1 < len && /\d/.test(input[end + 1])) {
    end++; // skip '.'
    while (end < len && /\d/.test(input[end])) {
      end++;
    }
    const value = input.slice(tokenStart, end);
    return new Token(TokenType.REAL, value, tokenStart);
  }

  const value = input.slice(tokenStart, end);
  return new Token(TokenType.INTEGER, value, tokenStart);
}
