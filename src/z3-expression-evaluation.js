import { init } from 'z3-solver';
  const { Context } = await init();
  const Z3 = Context('main');


/**
 * Parses and solves a Z3 constraint expression of arbitrary size/operators.
 * Old (un-primed) variables are fixed to the numbers in `oldValues`.
 * Returns, for each primed variable, its computed bounds and a random in-range sample.
 *
 * @param {string} expr Boolean expression like `"x' >= x + 1 && y' <= y * 2"`.
 * @param {{[varName: string]: number}} oldValues Map from old-variable names (no trailing apostrophe) to their numeric values.
 * @param {'int'|'float'} mode `"int"` for integer arithmetic or `"float"` for Real arithmetic.
 * @returns {Promise<{
 *   bounds: {[varName: string]: { lower: number, upper: number }},
 *   newValues: {[varName: string]: number}
 * } | null>} An object with `bounds` and `newValues`, or `null` if unsatisfiable.
 */
export async function solveExpression(expr, oldValues, mode) {


  // 1. Declare Z3 constants for old variables
  const varMap = {};
  for (const name of Object.keys(oldValues)) {
    varMap[name] =
      mode === 'int' ? Z3.Int.const(name) : Z3.Real.const(name);
  }

  // 2. Find primed variable names
  const primedNames = new Set();
  for (const m of expr.matchAll(/([A-Za-z_]\w*)'/g)) {
    primedNames.add(m[1]);
  }

  // 3. Declare Z3 constants for primed variables
  const primedMap = {};
  for (const name of primedNames) {
    const full = `${name}'`;
    primedMap[name] =
      mode === 'int' ? Z3.Int.const(full) : Z3.Real.const(full);
  }

  // 4. Tokenizer
  function tokenize(input) {
    const ops2 = new Set(['>=','<=','==','!=','&&','||']);
    const tokens = [];
    let i = 0;
    while (i < input.length) {
      const ch = input[i];
      if (/\s/.test(ch)) { i++; continue; }
      const two = input.substr(i, 2);
      if (ops2.has(two)) {
        tokens.push({ type: 'operator', value: two });
        i += 2;
        continue;
      }
      if ('+-*/<>!'.includes(ch)) {
        tokens.push({ type: 'operator', value: ch });
        i++;
        continue;
      }
      if (ch === '(' || ch === ')') {
        tokens.push({ type: 'paren', value: ch });
        i++;
        continue;
      }
      if (/[0-9]/.test(ch)) {
        let num = ch; i++;
        while (i < input.length && /[0-9.]/.test(input[i])) {
          num += input[i++];
        }
        tokens.push({ type: 'number', value: num });
        continue;
      }
      if (/[A-Za-z_]/.test(ch)) {
        let id = ch; i++;
        while (i < input.length && /\w/.test(input[i])) {
          id += input[i++];
        }
        if (input[i] === "'") {
          id += "'"; i++;
        }
        tokens.push({ type: 'identifier', value: id });
        continue;
      }
      throw new Error(`Unexpected char '${ch}' at position ${i}`);
    }
    return tokens;
  }

  // 5. Recursive-descent parser
  const tokens = tokenize(expr);
  let pos = 0;

  function peek() {
    return tokens[pos] || null;
  }
  function next() {
    return tokens[pos++];
  }
  function expect(type, val) {
    const tk = peek();
    if (!tk || tk.type !== type || (val && tk.value !== val)) {
      throw new Error(`Expected ${type}${val ? ` '${val}'` : ''} but got ${tk?.type} '${tk?.value}'`);
    }
    return next();
  }

  function parseExpr() { return parseOr(); }
  function parseOr() {
    let left = parseAnd();
    while (peek()?.type === 'operator' && peek().value === '||') {
      next();
      left = Z3.Or(left, parseAnd());
    }
    return left;
  }
  function parseAnd() {
    let left = parseComp();
    while (peek()?.type === 'operator' && peek().value === '&&') {
      next();
      left = Z3.And(left, parseComp());
    }
    return left;
  }
  function parseComp() {
    let left = parseAdd();
    const op = peek();
    if (op?.type === 'operator' && ['>=','<=','>','<','==','!='].includes(op.value)) {
      next();
      const right = parseAdd();
      switch (op.value) {
        case '>=': return left.ge(right);
        case '<=': return left.le(right);
        case '>':  return left.gt(right);
        case '<':  return left.lt(right);
        case '==': return left.eq(right);
        case '!=': return left.neq(right);
      }
    }
    return left;
  }
  function parseAdd() {
    let left = parseMul();
    while (peek()?.type === 'operator' && ['+','-'].includes(peek().value)) {
      const op = next().value;
      const right = parseMul();
      left = op === '+' ? left.add(right) : left.sub(right);
    }
    return left;
  }
  function parseMul() {
    let left = parseUnary();
    while (peek()?.type === 'operator' && ['*','/'].includes(peek().value)) {
      const op = next().value;
      const right = parseUnary();
      left = op === '*' ? left.mul(right) : left.div(right);
    }
    return left;
  }
  function parseUnary() {
    if (peek()?.type === 'operator' && ['+','-'].includes(peek().value)) {
      const op = next().value;
      const sub = parseUnary();
      return op === '-' ? sub.neg() : sub;
    }
    return parsePrimary();
  }
  function parsePrimary() {
    const tk = peek();
    if (!tk) throw new Error('Unexpected end of input');
    if (tk.type === 'number') {
      next();
      return mode === 'int'
        ? Z3.Int.val(parseInt(tk.value, 10))
        : Z3.Real.val(tk.value);
    }
    if (tk.type === 'identifier') {
      next();
      if (tk.value.endsWith("'")) {
        const name = tk.value.slice(0, -1);
        if (!(name in primedMap)) throw new Error(`Unknown primed var '${tk.value}'`);
        return primedMap[name];
      } else {
        if (!(tk.value in varMap)) throw new Error(`Unknown old var '${tk.value}'`);
        return varMap[tk.value];
      }
    }
    if (tk.type === 'paren' && tk.value === '(') {
      next();
      const inside = parseExpr();
      expect('paren', ')');
      return inside;
    }
    throw new Error(`Unexpected token ${tk.type} '${tk.value}'`);
  }

  const constraintAst = parseExpr();
  if (pos < tokens.length) {
    throw new Error(`Trailing tokens: ${tokens.slice(pos).map(t => t.value).join(' ')}`);
  }

  // 6. Fixed-old constraints
  const fixed = [];
  for (const [name, val] of Object.entries(oldValues)) {
    const lit = mode === 'int'
      ? Z3.Int.val(val)
      : Z3.Real.val(val.toString());
    fixed.push(varMap[name].eq(lit));
  }

  // 7. Compute bounds for each primed var
  const bounds = {};
  for (const name of primedNames) {
    const p = primedMap[name];

    const optMin = new Z3.Optimize();
    optMin.add(...fixed, constraintAst);
    optMin.minimize(p);
    if ((await optMin.check()) !== 'sat') return null;
    const lowStr = (await optMin.model().get(p)).toString();
    const lower = mode === 'int' ? parseInt(lowStr, 10) : parseFloat(lowStr);

    const optMax = new Z3.Optimize();
    optMax.add(...fixed, constraintAst);
    optMax.maximize(p);
    await optMax.check();
    const highStr = (await optMax.model().get(p)).toString();
    const upper = mode === 'int' ? parseInt(highStr, 10) : parseFloat(highStr);

    bounds[name] = { lower, upper };

    if (lower === upper) {
      bounds[name].upper = Number.MAX_SAFE_INTEGER;
    }
  }

  // 8. Sample random new values
  const newValues = {};
  for (const name of primedNames) {
    const { lower, upper } = bounds[name];
    newValues[name] =
      mode === 'int'
        ? Math.floor(Math.random() * (upper - lower + 1)) + lower
        : Math.random() * (upper - lower) + lower;
  }

  return { bounds, newValues };
}

window.solveExpression = solveExpression;

// (async () => {
//   const expr = "x' >= x + 100";

//   const result = await solveExpression(expr, { x: 10 }, 'int');

//   if (result) {
//     console.log('Bounds:', result.bounds);    
//     console.log('Sampled x\' Value:', result.newValues)
//   } else {
//     console.log('Constraints unsatisfiable');
//   }
// })();
