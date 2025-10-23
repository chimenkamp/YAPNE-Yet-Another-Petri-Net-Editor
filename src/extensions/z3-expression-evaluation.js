import { parse, evaluate } from 'mathjs';

// Define global exports for z3-solver compatibility
window.global = window;
window.exports = {};
window.module = { exports: {} };

let z3Module = null;
let Context = null;
let Z3 = null;

async function getZ3() {
  if (!z3Module) {
    // Load z3-built.js if not already loaded
    if (!window.initZ3) {
      await new Promise((resolve, reject) => {
        const script = document.createElement('script');
        script.src = '/YAPNE-Yet-Another-Petri-Net-Editor/z3/z3-built.js';
        script.onload = () => window.initZ3 ? resolve() : reject(new Error('initZ3 not found'));
        script.onerror = () => reject(new Error('Failed to load z3-built.js'));
        document.head.appendChild(script);
      });
    }
    
    // Make initZ3 available on global
    if (!window.global) {
      window.global = window;
    }
    window.global.initZ3 = window.initZ3;
    
    // Import and initialize z3-solver
    z3Module = await import('z3-solver');
    const { init } = z3Module;
    
    if (!init || typeof init !== 'function') {
      throw new Error('z3-solver does not export init function');
    }
    
    const result = await init();
    
    if (!result || !result.Context) {
      throw new Error('Z3 initialization failed');
    }
    
    Context = result.Context;
    Z3 = Context('main');
  }
  return { Z3, Context };
}

// Initialize Z3 when the module loads
let z3Ready = null;

async function ensureZ3Ready() {
  if (!z3Ready) {
    z3Ready = getZ3();
  }
  return z3Ready;
}

/**
 * Robust expression solver using Math.js for parsing
 * @param {string} expr Boolean expression like `"x' >= x + 1 && y' <= y * 2"`
 * @param {{[varName: string]: number|boolean}} oldValues Map from variable names to their values
 * @param {'int'|'float'|'bool'|'auto'} mode Type mode for variables
 * @returns {Promise<{bounds: Object, newValues: Object} | null>} Result or null if unsatisfiable
 */
export async function solveExpression(expr, oldValues, mode = 'auto') {
  // Ensure Z3 is ready before proceeding
  const { Z3 } = await ensureZ3Ready();
  
  // Helper function to determine variable type
  function getVarType(value, defaultMode) {
    if (defaultMode === 'auto') {
      if (typeof value === 'boolean') return 'bool';
      if (value === 'true' || value === 'false') return 'bool';
      if (typeof value === 'string' && (value.toLowerCase() === 'true' || value.toLowerCase() === 'false')) return 'bool';
      
      if (typeof value === 'number') {
        if (Number.isInteger(value)) return 'int';
        return 'float';
      }
      
      if (typeof value === 'string') {
        const num = Number(value);
        if (!isNaN(num)) {
          if (Number.isInteger(num)) return 'int';
          return 'float';
        }
      }
      
      return 'bool';
    }
    return defaultMode;
  }

/**
 * Get the string name of a Z3 expression’s sort, regardless of binding version.
 *
 * @param {import('z3-solver').Ast} expr
 * @returns {string} the sort name, e.g. "Int", "Real", "Bool"
 */
function getSortString(expr) {
  // some bindings use a sort() method, others expose a sort property
  const s = typeof expr.sort === 'function'
    ? expr.sort()
    : expr.sort;
  return s.toString();
}

/**
 * Cast two Z3 expressions to a common type so arithmetic/comparison works.
 *
 * @param {import('z3-solver').Ast} left
 * @param {import('z3-solver').Ast} right
 * @returns {[import('z3-solver').Ast, import('z3-solver').Ast]}
 */
function castToCompatibleType(left, right) {
  const ls = getSortString(left);
  const rs = getSortString(right);

  if (ls === rs) {
    return [left, right];
  }
  if (ls.includes('Int') && rs.includes('Real')) {
    return [left.toReal(), right];
  }
  if (ls.includes('Real') && rs.includes('Int')) {
    return [left, right.toReal()];
  }
  return [left, right];
}


  // 1. Declare Z3 constants for old variables
  const varMap = {};
  const varTypes = {};
  for (const [name, value] of Object.entries(oldValues)) {
    const varType = getVarType(value, mode);
    varTypes[name] = varType;
    
    if (varType === 'int') {
      varMap[name] = Z3.Int.const(name);
    } else if (varType === 'float') {
      varMap[name] = Z3.Real.const(name);
    } else if (varType === 'bool') {
      varMap[name] = Z3.Bool.const(name);
    }
  }

  // 2. Find primed variable names using regex
  const primedNames = new Set();
  for (const m of expr.matchAll(/([A-Za-z_]\w*)'/g)) {
    primedNames.add(m[1]);
  }

  // 3. Declare Z3 constants for primed variables
  const primedMap = {};
  const primedTypes = {};
  for (const name of primedNames) {
    const full = `${name}_prime`; // Use _prime instead of ' for Math.js compatibility
    const primedType = varTypes[name] || (mode === 'auto' ? 'int' : mode);
    primedTypes[name] = primedType;
    
    if (primedType === 'int') {
      primedMap[name] = Z3.Int.const(full);
    } else if (primedType === 'float') {
      primedMap[name] = Z3.Real.const(full);
    } else if (primedType === 'bool') {
      primedMap[name] = Z3.Bool.const(full);
    }
  }

  // 4. Preprocess expression to replace ' with _prime for Math.js compatibility
  let processedExpr = expr;
  
  // Replace logical operators for Math.js
  processedExpr = processedExpr.replace(/&&/g, ' and ');
  processedExpr = processedExpr.replace(/\|\|/g, ' or ');
  processedExpr = processedExpr.replace(/==/g, ' == ');
  processedExpr = processedExpr.replace(/!=/g, ' != ');
  
  // Replace primed variables
  for (const name of primedNames) {
    const regex = new RegExp(`\\b${name}'`, 'g');
    processedExpr = processedExpr.replace(regex, `${name}_prime`);
  }
  
  console.log('Original expression:', expr);
  console.log('Processed expression:', processedExpr);

  // 5. Parse the expression using Math.js
  let ast;
  try {
    ast = parse(processedExpr);
    console.log('Parsed AST:', JSON.stringify(ast, null, 2));
  } catch (error) {
    throw new Error(`Failed to parse expression: ${error.message}`);
  }

  // 6. Convert Math.js AST to Z3 expression
  function astToZ3(node) {
    console.log('Converting node:', node.type, node);
    
    switch (node.type) {
      case 'ConstantNode':
        if (typeof node.value === 'boolean') {
          return Z3.Bool.val(node.value);
        } else if (typeof node.value === 'number') {
          if (Number.isInteger(node.value)) {
            return Z3.Int.val(node.value);
          } else {
            return Z3.Real.val(node.value);
          }
        } else if (typeof node.value === 'string') {
          // Handle string boolean literals
          if (node.value === 'true') return Z3.Bool.val(true);
          if (node.value === 'false') return Z3.Bool.val(false);
          throw new Error(`Unsupported string constant: ${node.value}`);
        }
        break;

      case 'SymbolNode':
        const varName = node.name;
        
        // Check if it's a primed variable
        if (varName.endsWith('_prime')) {
          const baseName = varName.slice(0, -6); // Remove '_prime'
          if (primedMap[baseName]) {
            return primedMap[baseName];
          }
        }
        
        // Check if it's a regular variable
        if (varMap[varName]) {
          return varMap[varName];
        }
        
        // Handle boolean literals
        if (varName === 'true') return Z3.Bool.val(true);
        if (varName === 'false') return Z3.Bool.val(false);
        
        throw new Error(`Unknown variable: ${varName}`);

      case 'OperatorNode':
        const args = node.args.map(astToZ3);

        switch (node.fn) {
          case 'add': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.add(r);
          }
          case 'subtract': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.sub(r);
          }
          case 'multiply': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.mul(r);
          }
          case 'divide': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.div(r);
          }
          case 'larger': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.gt(r);
          }
          case 'largerEq': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.ge(r);
          }
          case 'smaller': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.lt(r);
          }
          case 'smallerEq': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.le(r);
          }
          case 'equal': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.eq(r);
          }
          case 'unequal': {
            const [l, r] = castToCompatibleType(args[0], args[1]);
            return l.neq(r);
          }
          case 'and':
            return Z3.And(...args);
          case 'or':
            return Z3.Or(...args);
          case 'not':
            return Z3.Not(args[0]);
          case 'unaryMinus':
            return args[0].neg();
          case 'unaryPlus':
            return args[0];
          default:
            throw new Error(`Unsupported operator: ${node.fn}`);
        }
    

      case 'ParenthesisNode':
        return astToZ3(node.content);

      case 'FunctionNode':
        // Handle function calls if needed
        throw new Error(`Function calls not supported: ${node.fn.name}`);

      default:
        throw new Error(`Unsupported AST node type: ${node.type}`);
    }
  }

  const constraintAst = astToZ3(ast);

  // 7. Create fixed constraints for old variables
  const fixed = [];
  for (const [name, val] of Object.entries(oldValues)) {
    let lit;
    const varType = varTypes[name];
    
    try {
      if (varType === 'int') {
        if (val === 'true' || val === true || val === 'false' || val === false) {
          throw new Error(`Boolean value '${val}' cannot be used as integer. Use mode='auto' or mode='bool' instead.`);
        }
        const intVal = typeof val === 'string' ? parseInt(val, 10) : Math.floor(Number(val));
        if (isNaN(intVal)) {
          throw new Error(`Cannot convert '${val}' to integer`);
        }
        lit = Z3.Int.val(intVal);
      } else if (varType === 'float') {
        if (val === 'true' || val === true || val === 'false' || val === false) {
          throw new Error(`Boolean value '${val}' cannot be used as float. Use mode='auto' or mode='bool' instead.`);
        }
        const floatVal = typeof val === 'string' ? parseFloat(val) : Number(val);
        if (isNaN(floatVal)) {
          throw new Error(`Cannot convert '${val}' to float`);
        }
        lit = Z3.Real.val(floatVal.toString());
      } else if (varType === 'bool') {
        let boolVal;
        if (typeof val === 'boolean') {
          boolVal = val;
        } else if (typeof val === 'string') {
          if (val.toLowerCase() === 'true') {
            boolVal = true;
          } else if (val.toLowerCase() === 'false') {
            boolVal = false;
          } else {
            throw new Error(`Cannot convert string '${val}' to boolean. Expected 'true' or 'false'.`);
          }
        } else {
          boolVal = Boolean(val);
        }
        lit = Z3.Bool.val(boolVal);
      }
      fixed.push(varMap[name].eq(lit));
    } catch (error) {
      throw new Error(`Failed to create Z3 value for variable '${name}' with value '${val}' (type: ${typeof val}) and detected type '${varType}': ${error.message}`);
    }
  }

  // 8. Compute bounds for each primed variable
  const bounds = {};
  for (const name of primedNames) {
    const p = primedMap[name];
    const primedType = primedTypes[name];

    if (primedType === 'bool') {
      const solverTrue = new Z3.Solver();
      solverTrue.add(...fixed, constraintAst, p.eq(Z3.Bool.val(true)));
      const canBeTrue = (await solverTrue.check()) === 'sat';
      
      const solverFalse = new Z3.Solver();
      solverFalse.add(...fixed, constraintAst, p.eq(Z3.Bool.val(false)));
      const canBeFalse = (await solverFalse.check()) === 'sat';
      
      if (!canBeTrue && !canBeFalse) return null;
      
      bounds[name] = { 
        canBeTrue, 
        canBeFalse,
        lower: canBeFalse ? 0 : 1,
        upper: canBeTrue ? 1 : 0
      };
    } else {
      const optMin = new Z3.Optimize();
      optMin.add(...fixed, constraintAst);
      optMin.minimize(p);
      if ((await optMin.check()) !== 'sat') return null;
      const lowStr = (await optMin.model().get(p)).toString();
      const lower = primedType === 'int' ? parseInt(lowStr, 10) : parseFloat(lowStr);

      const optMax = new Z3.Optimize();
      optMax.add(...fixed, constraintAst);
      optMax.maximize(p);
      await optMax.check();
      const highStr = (await optMax.model().get(p)).toString();
      const upper = primedType === 'int' ? parseInt(highStr, 10) : parseFloat(highStr);

      bounds[name] = { lower, upper };

      if (lower === upper) {
        bounds[name].upper = Number.MAX_SAFE_INTEGER;
      }
    }
  }

  // 9. Sample random new values
  const newValues = {};
  for (const name of primedNames) {
    const primedType = primedTypes[name];
    
    if (primedType === 'bool') {
      const { canBeTrue, canBeFalse } = bounds[name];
      if (canBeTrue && canBeFalse) {
        newValues[name] = Math.random() < 0.5;
      } else {
        newValues[name] = canBeTrue;
      }
    } else {
      const { lower, upper } = bounds[name];
      newValues[name] =
        primedType === 'int'
          ? Math.floor(Math.random() * (upper - lower + 1)) + lower
          : Math.random() * (upper - lower) + lower;
    }
  }

  return { bounds, newValues };
}

window.solveExpression = solveExpression;