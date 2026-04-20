import { DataPetriNet, DataAwareTransition, DataVariable } from './dpn-model.js';
import { Place, Transition, Arc } from '../petri-net-simulator.js';


/**
 * Translate Python source code into a YAPNE-compatible Data Petri Net.
 *
 * The translation preserves recall of 1: every feasible execution trace of
 * the input Python program corresponds to a firing sequence of the produced
 * DPN. At generalization 0 precision is also 1, i.e. every firing sequence
 * of the DPN matches some Python trace. Raising generalization progressively
 * drops postconditions (variable effects) and then preconditions (branch
 * guards), trading precision for a simpler model while preserving recall.
 *
 * Guard and postcondition syntax follows the restricted infix form of the
 * YAPNE DPN grammar: operators `and`, `or`, `not`, `=`, `==`, `!=`, `<`,
 * `<=`, `>`, `>=`, `+`, `-`, `*`, `/`, with primed identifiers (`v'`) for
 * writes in postconditions and assignments separated by `;`.
 */
class PythonToDPN {
  /**
   * Create a new translator.
   *
   * @param {{generalization?: number, depth?: number, name?: string}} [options]
   *   - generalization: number in [0, 1] controlling how aggressively guards
   *     and effects are dropped. Values >= 0.4 drop postconditions; values
   *     >= 0.8 additionally drop preconditions. Default 0 (exact translation).
   *   - depth: maximum function-call inlining depth. 0 keeps every call as a
   *     single opaque transition; n > 0 inlines up to n nested call levels.
   *     Default 1.
   *   - name: display name for the produced DataPetriNet. Default 'Python Program'.
   */
  constructor(options = {}) {
    this.generalization = options.generalization ?? 0;
    this.depth = options.depth ?? 1;
    this.name = options.name ?? 'Python Program';
  }

  /**
   * Convert a Python source string into a Data Petri Net.
   *
   * @param {string} code - Raw Python source code.
   * @returns {DataPetriNet} A populated DataPetriNet instance. Call `.toJSON()`
   *   on the result to persist it or import it into YAPNE.
   */
  convert(code) {
    this._dpn = new DataPetriNet(this._uuid(), this.name, 'Generated from Python source');
    this._variables = new Map();
    this._functions = new Map();
    this._loopStack = [];
    this._callDepth = 0;
    this._gridX = 0;
    this._gridY = 0;

    const topLevel = [];
    for (const stmt of this._parseProgram(code)) {
      if (stmt.kind === 'def') {
        this._functions.set(stmt.name, stmt);
      } else {
        topLevel.push(stmt);
      }
    }

    const start = this._addPlace('start', 1);
    const exit = this._buildBlock(topLevel, start);
    if (exit !== null) {
      this._dpn.getPlace(exit).finalMarking = 1;
    }

    for (const [name, type] of this._variables) {
      this._dpn.addDataVariable(
        new DataVariable(this._uuid(), name, type, this._defaultValue(type))
      );
    }
    return this._dpn;
  }

  /**
   * Parse a full Python program into a list of top-level statement ASTs.
   *
   * @param {string} code - Raw Python source.
   * @returns {Array<Object>} Parsed statement nodes.
   */
  _parseProgram(code) {
    const lines = [];
    for (const raw of code.split('\n')) {
      const stripped = this._stripComment(raw);
      if (stripped.trim() === '') continue;
      const indent = stripped.length - stripped.trimStart().length;
      lines.push({ indent: indent, text: stripped.trim() });
    }
    return this._parseBlock(lines, 0, 0).stmts;
  }

  /**
   * Remove a trailing line comment from a Python source line, ignoring `#`
   * characters that occur inside string literals.
   *
   * @param {string} line - A single line of Python source.
   * @returns {string} The line without its trailing comment.
   */
  _stripComment(line) {
    let inStr = null;
    for (let i = 0; i < line.length; i++) {
      const c = line[i];
      if (inStr) {
        if (c === inStr && line[i - 1] !== '\\') inStr = null;
      } else if (c === '"' || c === "'") {
        inStr = c;
      } else if (c === '#') {
        return line.substring(0, i);
      }
    }
    return line;
  }

  /**
   * Parse a contiguous block of statements at indentation >= `indent`.
   *
   * @param {Array<{indent: number, text: string}>} lines - Pre-tokenized lines.
   * @param {number} start - Starting line index.
   * @param {number} indent - Required minimum indentation for the block.
   * @returns {{stmts: Array<Object>, nextIdx: number}} Parsed statements and
   *   the index of the first line not belonging to the block.
   */
  _parseBlock(lines, start, indent) {
    const stmts = [];
    let i = start;
    while (i < lines.length && lines[i].indent >= indent) {
      if (lines[i].indent > indent) {
        i++;
        continue;
      }
      const { stmt, nextIdx } = this._parseStatement(lines, i);
      if (stmt) stmts.push(stmt);
      i = nextIdx;
    }
    return { stmts: stmts, nextIdx: i };
  }

  /**
   * Parse a single statement starting at line index `idx`.
   *
   * @param {Array<{indent: number, text: string}>} lines - Pre-tokenized lines.
   * @param {number} idx - Line index of the statement's first line.
   * @returns {{stmt: Object|null, nextIdx: number}} Parsed AST node (or null
   *   for an unrecognized line) and the index of the next unparsed line.
   */
  _parseStatement(lines, idx) {
    const text = lines[idx].text;

    if (text.startsWith('if ') && text.endsWith(':')) {
      return this._parseIfChain(lines, idx);
    }
    if (text.startsWith('while ') && text.endsWith(':')) {
      const cond = text.slice(6, -1).trim();
      const child = this._childIndent(lines, idx);
      const body = this._parseBlock(lines, idx + 1, child);
      return { stmt: { kind: 'while', cond: cond, body: body.stmts }, nextIdx: body.nextIdx };
    }
    if (text.startsWith('for ')) {
      const m = text.match(/^for\s+([A-Za-z_]\w*)\s+in\s+(.+):$/);
      if (m) {
        const child = this._childIndent(lines, idx);
        const body = this._parseBlock(lines, idx + 1, child);
        return {
          stmt: { kind: 'for', variable: m[1], iterable: m[2].trim(), body: body.stmts },
          nextIdx: body.nextIdx
        };
      }
    }
    if (text.startsWith('def ')) {
      const m = text.match(/^def\s+([A-Za-z_]\w*)\s*\(([^)]*)\)\s*:$/);
      if (m) {
        const child = this._childIndent(lines, idx);
        const body = this._parseBlock(lines, idx + 1, child);
        const params = m[2].split(',').map(p => p.trim()).filter(p => p.length > 0);
        return {
          stmt: { kind: 'def', name: m[1], params: params, body: body.stmts },
          nextIdx: body.nextIdx
        };
      }
    }
    if (text === 'return' || text.startsWith('return ')) {
      const expr = text === 'return' ? null : text.slice(7).trim();
      return { stmt: { kind: 'return', expr: expr }, nextIdx: idx + 1 };
    }
    if (text === 'pass')     return { stmt: { kind: 'pass' },     nextIdx: idx + 1 };
    if (text === 'break')    return { stmt: { kind: 'break' },    nextIdx: idx + 1 };
    if (text === 'continue') return { stmt: { kind: 'continue' }, nextIdx: idx + 1 };

    const aug = text.match(/^([A-Za-z_]\w*)\s*(\+=|-=|\*=|\/=)\s*(.+)$/);
    if (aug) {
      return {
        stmt: { kind: 'assign', variable: aug[1], op: aug[2], expr: aug[3].trim() },
        nextIdx: idx + 1
      };
    }

    const assign = text.match(/^([A-Za-z_]\w*)\s*=(?!=)\s*(.+)$/);
    if (assign) {
      return {
        stmt: { kind: 'assign', variable: assign[1], op: '=', expr: assign[2].trim() },
        nextIdx: idx + 1
      };
    }

    const call = this._matchPureCall(text);
    if (call) {
      return { stmt: { kind: 'call', name: call.name, args: call.args }, nextIdx: idx + 1 };
    }

    return { stmt: { kind: 'expr', text: text }, nextIdx: idx + 1 };
  }

  /**
   * Parse an if/elif+/else chain into a right-nested if AST.
   *
   * @param {Array<{indent: number, text: string}>} lines - Pre-tokenized lines.
   * @param {number} idx - Line index of the `if` header.
   * @returns {{stmt: Object, nextIdx: number}} The nested if AST and the next index.
   */
  _parseIfChain(lines, idx) {
    const own = lines[idx].indent;
    const branches = [];

    const firstCond = lines[idx].text.slice(3, -1).trim();
    const firstChild = this._childIndent(lines, idx);
    const firstBody = this._parseBlock(lines, idx + 1, firstChild);
    branches.push({ cond: firstCond, body: firstBody.stmts });
    let i = firstBody.nextIdx;

    while (i < lines.length && lines[i].indent === own) {
      const t = lines[i].text;
      if (t.startsWith('elif ') && t.endsWith(':')) {
        const c = t.slice(5, -1).trim();
        const ci = this._childIndent(lines, i);
        const b = this._parseBlock(lines, i + 1, ci);
        branches.push({ cond: c, body: b.stmts });
        i = b.nextIdx;
      } else if (t === 'else:') {
        const ci = this._childIndent(lines, i);
        const b = this._parseBlock(lines, i + 1, ci);
        branches.push({ cond: null, body: b.stmts });
        i = b.nextIdx;
        break;
      } else {
        break;
      }
    }

    let elseBody = [];
    if (branches[branches.length - 1].cond === null) {
      elseBody = branches.pop().body;
    }
    let result = elseBody;
    for (let k = branches.length - 1; k >= 0; k--) {
      result = [{
        kind: 'if',
        cond: branches[k].cond,
        thenBody: branches[k].body,
        elseBody: result
      }];
    }
    return { stmt: result[0], nextIdx: i };
  }

  /**
   * Determine the indentation level of the block following a header line.
   *
   * @param {Array<{indent: number, text: string}>} lines - Pre-tokenized lines.
   * @param {number} idx - Index of the header line (e.g. an `if x:` line).
   * @returns {number} Indentation of the child block, or the header's indent + 4
   *   when the child block is empty.
   */
  _childIndent(lines, idx) {
    if (idx + 1 < lines.length && lines[idx + 1].indent > lines[idx].indent) {
      return lines[idx + 1].indent;
    }
    return lines[idx].indent + 4;
  }

  /**
   * Match a statement that is exactly a single function call with balanced parentheses.
   *
   * @param {string} text - The trimmed statement line.
   * @returns {{name: string, args: string}|null} Name and raw argument string,
   *   or null if the line is not a pure call.
   */
  _matchPureCall(text) {
    const head = text.match(/^([A-Za-z_]\w*)\s*\(/);
    if (!head) return null;
    let depth = 1;
    let i = head[0].length;
    while (i < text.length && depth > 0) {
      const c = text[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      i++;
    }
    if (depth !== 0 || i !== text.length) return null;
    return { name: head[1], args: text.substring(head[0].length, i - 1) };
  }

  /**
   * Build the DPN sub-graph for a sequence of statements.
   *
   * @param {Array<Object>} stmts - Statement AST nodes.
   * @param {string} entry - Id of the place where control enters the block.
   * @returns {string|null} Id of the exit place, or null when control does
   *   not fall through (after a return, break, or continue).
   */
  _buildBlock(stmts, entry) {
    let cur = entry;
    for (const s of stmts) {
      if (cur === null) break;
      cur = this._buildStmt(s, cur);
    }
    return cur;
  }

  /**
   * Dispatch to the builder for a single statement.
   *
   * @param {Object} stmt - Statement AST node.
   * @param {string} entry - Entry place id.
   * @returns {string|null} Exit place id, or null for non-falling-through statements.
   */
  _buildStmt(stmt, entry) {
    switch (stmt.kind) {
      case 'assign':   return this._buildAssign(stmt, entry);
      case 'if':       return this._buildIf(stmt, entry);
      case 'while':    return this._buildWhile(stmt, entry);
      case 'for':      return this._buildFor(stmt, entry);
      case 'call':     return this._buildCall(stmt, entry);
      case 'return':   return this._buildReturn(stmt, entry);
      case 'pass':     return entry;
      case 'break':    return this._buildJump(entry, 'break');
      case 'continue': return this._buildJump(entry, 'continue');
      case 'expr':     return this._buildOpaque(stmt.text, entry);
      default:         return entry;
    }
  }

  /**
   * Emit a transition encoding a Python assignment `x = rhs` or augmented form.
   *
   * @param {{variable: string, op: string, expr: string}} stmt - Assignment AST.
   * @param {string} entry - Entry place id.
   * @returns {string} Exit place id.
   */
  _buildAssign(stmt, entry) {
    this._ensureVariable(stmt.variable, this._inferType(stmt.expr));
    const rhs = this._translateExpr(stmt.expr);
    let post = null;
    if (this._isSupported(rhs)) {
      const body = stmt.op === '='
        ? rhs
        : `${stmt.variable} ${stmt.op[0]} (${rhs})`;
      post = `${stmt.variable}' = ${body}`;
    }
    const label = `${stmt.variable} ${stmt.op} ${stmt.expr}`;
    const next = this._addPlace('');
    const t = this._addTransition(label, null, this._generalizePost(post), false);
    this._addArc(entry, t);
    this._addArc(t, next);
    return next;
  }

  /**
   * Emit the branching structure for a Python if/else statement.
   *
   * @param {{cond: string, thenBody: Array<Object>, elseBody: Array<Object>}} stmt - If AST.
   * @param {string} entry - Entry place id.
   * @returns {string} Id of the merge place where both branches rejoin.
   */
  _buildIf(stmt, entry) {
    const cond = this._translateExpr(stmt.cond);
    const pre = this._isSupported(cond) ? cond : null;
    const negPre = pre === null ? null : `not (${pre})`;
    const merge = this._addPlace('');

    const thenEntry = this._addPlace('');
    const tThen = this._addTransition('[then]', this._generalizePre(pre), null, true);
    this._addArc(entry, tThen);
    this._addArc(tThen, thenEntry);
    const thenExit = this._buildBlock(stmt.thenBody, thenEntry);
    if (thenExit !== null) {
      const tj = this._addTransition('', null, null, true);
      this._addArc(thenExit, tj);
      this._addArc(tj, merge);
    }

    const elseEntry = this._addPlace('');
    const tElse = this._addTransition('[else]', this._generalizePre(negPre), null, true);
    this._addArc(entry, tElse);
    this._addArc(tElse, elseEntry);
    const elseExit = this._buildBlock(stmt.elseBody, elseEntry);
    if (elseExit !== null) {
      const tj = this._addTransition('', null, null, true);
      this._addArc(elseExit, tj);
      this._addArc(tj, merge);
    }

    return merge;
  }

  /**
   * Emit a loop structure for a Python while statement. The entry place
   * doubles as the loop header so continue-edges can reuse it.
   *
   * @param {{cond: string, body: Array<Object>}} stmt - While AST.
   * @param {string} entry - Entry place id, reused as the loop header.
   * @returns {string} Id of the loop's exit place.
   */
  _buildWhile(stmt, entry) {
    const cond = this._translateExpr(stmt.cond);
    const pre = this._isSupported(cond) ? cond : null;
    const negPre = pre === null ? null : `not (${pre})`;

    const bodyEntry = this._addPlace('');
    const exitPlace = this._addPlace('');

    const tEnter = this._addTransition('[while-enter]', this._generalizePre(pre), null, true);
    this._addArc(entry, tEnter);
    this._addArc(tEnter, bodyEntry);

    const tExit = this._addTransition('[while-exit]', this._generalizePre(negPre), null, true);
    this._addArc(entry, tExit);
    this._addArc(tExit, exitPlace);

    this._loopStack.push({ back: entry, exit: exitPlace });
    const bodyExit = this._buildBlock(stmt.body, bodyEntry);
    this._loopStack.pop();

    if (bodyExit !== null) {
      const tBack = this._addTransition('', null, null, true);
      this._addArc(bodyExit, tBack);
      this._addArc(tBack, entry);
    }
    return exitPlace;
  }

  /**
   * Emit a loop for `for v in range(...)`. Other iterables collapse to an
   * opaque transition.
   *
   * @param {{variable: string, iterable: string, body: Array<Object>}} stmt - For AST.
   * @param {string} entry - Entry place id.
   * @returns {string} Exit place id after the loop.
   */
  _buildFor(stmt, entry) {
    const m = stmt.iterable.match(
      /^range\s*\(\s*([^,)]+)(?:\s*,\s*([^,)]+))?(?:\s*,\s*([^)]+))?\s*\)$/
    );
    if (m) {
      const startExpr = m[2] ? m[1].trim() : '0';
      const endExpr = m[2] ? m[2].trim() : m[1].trim();
      const stepExpr = m[3] ? m[3].trim() : '1';
      this._ensureVariable(stmt.variable, 'int');
      const init = { kind: 'assign', variable: stmt.variable, op: '=', expr: startExpr };
      const inc = {
        kind: 'assign',
        variable: stmt.variable,
        op: '=',
        expr: `${stmt.variable} + ${stepExpr}`
      };
      const whileStmt = {
        kind: 'while',
        cond: `${stmt.variable} < ${endExpr}`,
        body: stmt.body.concat([inc])
      };
      const afterInit = this._buildAssign(init, entry);
      return this._buildWhile(whileStmt, afterInit);
    }
    return this._buildOpaque(`for ${stmt.variable} in ${stmt.iterable}`, entry);
  }

  /**
   * Emit a function call, either inlining the body (when the function is
   * known and current depth permits) or as a single opaque transition.
   *
   * @param {{name: string, args: string}} stmt - Call AST.
   * @param {string} entry - Entry place id.
   * @returns {string} Exit place id after the call.
   */
  _buildCall(stmt, entry) {
    const fn = this._functions.get(stmt.name);
    if (fn && this._callDepth < this.depth) {
      let cur = entry;
      if (fn.params.length > 0) {
        const args = this._splitArgs(stmt.args);
        const clauses = [];
        for (let i = 0; i < Math.min(fn.params.length, args.length); i++) {
          const p = fn.params[i];
          const a = args[i];
          this._ensureVariable(p, this._inferType(a));
          const rhs = this._translateExpr(a);
          if (this._isSupported(rhs)) clauses.push(`${p}' = ${rhs}`);
        }
        if (clauses.length > 0) {
          const bind = this._addTransition(
            `[call ${stmt.name}]`,
            null,
            this._generalizePost(clauses.join('; ')),
            true
          );
          const after = this._addPlace('');
          this._addArc(cur, bind);
          this._addArc(bind, after);
          cur = after;
        }
      }
      this._callDepth++;
      const exit = this._buildBlock(fn.body, cur);
      this._callDepth--;
      return exit === null ? this._addPlace('') : exit;
    }
    return this._buildOpaque(`${stmt.name}(${stmt.args})`, entry);
  }

  /**
   * Emit a single unguarded transition with the given label for statements
   * whose semantics are not modeled.
   *
   * @param {string} label - Label for the transition.
   * @param {string} entry - Entry place id.
   * @returns {string} Exit place id.
   */
  _buildOpaque(label, entry) {
    const next = this._addPlace('');
    const t = this._addTransition(label, null, null, false);
    this._addArc(entry, t);
    this._addArc(t, next);
    return next;
  }

  /**
   * Emit a return statement as a labeled transition terminating in a final place.
   *
   * @param {{expr: string|null}} stmt - Return AST.
   * @param {string} entry - Entry place id.
   * @returns {null} Always null; no fall-through.
   */
  _buildReturn(stmt, entry) {
    const final = this._addPlace('end', 0);
    this._dpn.getPlace(final).finalMarking = 1;
    const t = this._addTransition('return', null, null, false);
    this._addArc(entry, t);
    this._addArc(t, final);
    return null;
  }

  /**
   * Emit a silent edge to the enclosing loop's exit or back place.
   *
   * @param {string} entry - Entry place id.
   * @param {'break'|'continue'} kind - Jump kind.
   * @returns {null} Always null; no fall-through.
   */
  _buildJump(entry, kind) {
    const loop = this._loopStack[this._loopStack.length - 1];
    if (!loop) return entry;
    const target = kind === 'break' ? loop.exit : loop.back;
    const t = this._addTransition(`[${kind}]`, null, null, true);
    this._addArc(entry, t);
    this._addArc(t, target);
    return null;
  }

  /**
   * Split a call's argument string on top-level commas, honoring nested
   * parentheses and brackets.
   *
   * @param {string} args - Raw content between the call's parentheses.
   * @returns {Array<string>} Trimmed argument expressions.
   */
  _splitArgs(args) {
    const out = [];
    let depth = 0;
    let current = '';
    for (const c of args) {
      if (c === '(' || c === '[' || c === '{') depth++;
      else if (c === ')' || c === ']' || c === '}') depth--;
      if (c === ',' && depth === 0) {
        if (current.trim()) out.push(current.trim());
        current = '';
      } else {
        current += c;
      }
    }
    if (current.trim()) out.push(current.trim());
    return out;
  }

  /**
   * Translate a Python expression into the YAPNE restricted infix form.
   *
   * @param {string} expr - Python expression as source text.
   * @returns {string} Translated expression.
   */
  _translateExpr(expr) {
    let e = expr;
    e = e.replace(/\bTrue\b/g, 'true');
    e = e.replace(/\bFalse\b/g, 'false');
    e = e.replace(/\bNone\b/g, 'false');
    e = e.replace(/\/\//g, '/');
    return e;
  }

  /**
   * Test whether a translated expression uses only constructs accepted by
   * the YAPNE guard grammar.
   *
   * @param {string} expr - Translated expression.
   * @returns {boolean} True if all constructs are representable.
   */
  _isSupported(expr) {
    if (!expr) return false;
    if (/\b(in|is)\b/.test(expr)) return false;
    if (/%|\*\*/.test(expr)) return false;
    if (/[\[\]\{\}]/.test(expr)) return false;
    if (/['"]/.test(expr)) return false;
    return true;
  }

  /**
   * Guess the type of a Python right-hand side expression. First-write type
   * wins and is kept for the lifetime of the variable.
   *
   * @param {string} expr - Right-hand side source text.
   * @returns {string} One of 'int', 'float', 'boolean', 'string'.
   */
  _inferType(expr) {
    if (!expr) return 'int';
    const t = expr.trim();
    if (/^(True|False|true|false)$/.test(t)) return 'boolean';
    if (/^['"].*['"]$/.test(t)) return 'string';
    if (/^[+-]?\d+\.\d+/.test(t)) return 'float';
    if (/\b(and|or|not)\b|[<>!]=|==|[<>]/.test(t)) return 'boolean';
    return 'int';
  }

  /**
   * Return the default initial value for a given DataVariable type.
   *
   * @param {string} type - One of 'int', 'float', 'boolean', 'string'.
   * @returns {number|boolean|string} The default initial value.
   */
  _defaultValue(type) {
    switch (type) {
      case 'float':   return 0.0;
      case 'boolean': return false;
      case 'string':  return '';
      default:        return 0;
    }
  }

  /**
   * Register a data variable, keeping the first-seen type.
   *
   * @param {string} name - Variable name.
   * @param {string} type - Inferred variable type.
   * @returns {void}
   */
  _ensureVariable(name, type) {
    if (!this._variables.has(name)) this._variables.set(name, type);
  }

  /**
   * Apply generalization to a precondition. Returns null (no guard) once
   * generalization crosses the precondition-drop threshold.
   *
   * @param {string|null} guard - The raw guard expression or null.
   * @returns {string|null} The kept guard or null.
   */
  _generalizePre(guard) {
    if (!guard) return null;
    return this.generalization >= 0.8 ? null : guard;
  }

  /**
   * Apply generalization to a postcondition. Returns null (no effect) once
   * generalization crosses the postcondition-drop threshold.
   *
   * @param {string|null} post - The raw postcondition expression or null.
   * @returns {string|null} The kept postcondition or null.
   */
  _generalizePost(post) {
    if (!post) return null;
    return this.generalization >= 0.4 ? null : post;
  }

  /**
   * Add a Place to the DPN at an auto-advanced grid position.
   *
   * @param {string} label - Label for the place.
   * @param {number} [tokens=0] - Initial token count.
   * @returns {string} Id of the new place.
   */
  _addPlace(label, tokens = 0) {
    const id = this._uuid();
    this._gridX += 80;
    this._dpn.addPlace(new Place(id, { x: this._gridX, y: this._gridY }, label, tokens));
    return id;
  }

  /**
   * Add a Transition to the DPN. A DataAwareTransition is used when either
   * a precondition or postcondition is provided; otherwise a plain Transition.
   *
   * @param {string} label - Transition label.
   * @param {string|null} pre - Precondition expression or null.
   * @param {string|null} post - Postcondition expression or null.
   * @param {boolean} [silent=false] - Whether the transition is tau.
   * @returns {string} Id of the new transition.
   */
  _addTransition(label, pre, post, silent = false) {
    const id = this._uuid();
    this._gridX += 80;
    const pos = { x: this._gridX, y: this._gridY };
    const t = (pre || post)
      ? new DataAwareTransition(id, pos, label, 1, 0, pre || '', post || '', silent)
      : new Transition(id, pos, label, 1, 0, silent);
    this._dpn.addTransition(t);
    return id;
  }

  /**
   * Add a regular-type Arc with weight 1 between two DPN elements.
   *
   * @param {string} source - Source element id.
   * @param {string} target - Target element id.
   * @returns {string} Id of the new arc.
   */
  _addArc(source, target) {
    const id = this._uuid();
    this._dpn.addArc(new Arc(id, source, target, 1, 'regular'));
    return id;
  }

  /**
   * Generate a UUID v4 string.
   *
   * @returns {string} A freshly generated UUID.
   */
  _uuid() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, c => {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}


export { PythonToDPN };