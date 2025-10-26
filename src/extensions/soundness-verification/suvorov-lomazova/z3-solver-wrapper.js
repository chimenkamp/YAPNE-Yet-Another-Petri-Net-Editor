/**
 * Z3 Solver Wrapper Module
 * Handles Z3 initialization and provides a facade for SMT solving operations
 */

const BASE_PATH = '/YAPNE-Yet-Another-Petri-Net-Editor/';

let _z3 = null;
let _context = null;
let _solver = null;
let _initPromise = null;

/**
 * Initialize Z3 using ES modules and dynamic import
 */
async function initializeZ3() {
  if (_z3) return;
  
  // Prevent multiple simultaneous initializations
  if (_initPromise) {
    return _initPromise;
  } 

  _initPromise = (async () => {
    try {
      // Load z3-built.js to make initZ3 available globally
      if (!window.initZ3) {
        await new Promise((resolve, reject) => {
          const script = document.createElement('script');
          script.src = `${BASE_PATH}z3/z3-built.js`;
          script.onload = () => {
            if (window.initZ3) {
              resolve();
            } else {
              reject(new Error('z3-built.js loaded but initZ3 not found'));
            }
          };
          script.onerror = () => reject(new Error('Failed to load z3-built.js'));
          document.head.appendChild(script);
        });
      }
      
      // Make initZ3 available on global
      if (!window.global) {
        window.global = window;
      }
      window.global.initZ3 = window.initZ3;
      
      // Import z3-solver and call init
      const z3SolverModule = await import('z3-solver');
      const { init } = z3SolverModule;
      
      if (!init || typeof init !== 'function') {
        throw new Error('z3-solver does not export an init function');
      }
      
      // Call init to get the Z3 API
      const api = await init();
      
      // Extract the Z3 low-level API
      if (api.Z3 && typeof api.Z3 === 'object' && api.Z3.mk_config) {
        _z3 = api.Z3;
      } else if (api.mk_config) {
        _z3 = api;
      } else {
        throw new Error('Z3 API not found in init result');
      }
      
      // Create context and solver
      const config = _z3.mk_config();
      _z3.set_param_value(config, "trace", "true");
      _context = _z3.mk_context(config);
      _solver = _z3.mk_solver(_context);
      
      console.log('Z3 initialized successfully for SMT verification');
      
    } catch (error) {
      console.error("Failed to initialize Z3:", error);
      _initPromise = null; // Reset so we can try again
      throw error;
    }
  })();
  
  return _initPromise;
}

/**
 * Z3 Solver facade - provides simplified interface for SMT operations
 */
const Z3Solver = {
  _decls: new Map(),
  _globalDataVariables: new Map(),

  setGlobalDataVariables(dataVariables) {
    this._globalDataVariables = dataVariables || new Map();
    this._decls.clear();
  },

  /**
   * Validate a single SMT-LIB term (very small, conservative checker).
   * Rejects: nullary apps like "(x)", empty "()", wrong arities for common ops,
   * "true"/"false" used as heads with arguments, unknown function applications.
   *
   * @param {string} body
   * @returns {{ ok: boolean, reason?: string }}
   */
  _validateSmtTerm(body) {
    const src = String(body || "").trim();
    if (!src) return { ok: false, reason: "empty formula" };

    // Quick parenthesis balance check.
    let bal = 0;
    for (const ch of src) {
      if (ch === "(") bal++;
      else if (ch === ")") bal--;
      if (bal < 0) return { ok: false, reason: "unbalanced ')'" };
    }
    if (bal !== 0) return { ok: false, reason: "unbalanced parentheses" };

    // S-expression tokenizer and parser to nested arrays.
    const toks = [];
    {
      let i = 0;
      while (i < src.length) {
        const c = src[i];
        if (c === "(" || c === ")") {
          toks.push(c);
          i++;
        } else if (/\s/.test(c)) {
          i++;
        } else {
          let j = i;
          while (j < src.length && !/[\s()]/.test(src[j])) j++;
          toks.push(src.slice(i, j));
          i = j;
        }
      }
    }

    let pos = 0;
    const parse = () => {
      if (pos >= toks.length) return null;
      const t = toks[pos++];
      if (t === "(") {
        const list = [];
        while (pos < toks.length && toks[pos] !== ")") {
          const node = parse();
          if (node === null) return null;
          list.push(node);
        }
        if (pos >= toks.length || toks[pos] !== ")") return null;
        pos++; // consume ')'
        return list;
      }
      if (t === ")") return null;
      return t; // atom
    };

    const ast = parse();
    if (ast === null || pos !== toks.length) {
      return { ok: false, reason: "parse error" };
    }

    // Operator arity table (conservative).
    const MIN_ARITY = {
      not: 1,
      and: 1, // SMT allows 0, we require >=1 to catch "(and)" mistakes
      or: 1,
      "=": 2,
      distinct: 2,
      "<": 2,
      "<=": 2,
      ">": 2,
      ">=": 2,
      "+": 1,
      "-": 1,
      "*": 2,
      "/": 2,
      ite: 3,
      "=>": 2,
    };
    const MAX_ARITY = {
      not: 1,
      ite: 3,
      "=>": 2,
    };

    const isAtom = (x) => typeof x === "string";
    const isNumber = (a) => /^[-+]?\d+(?:\.\d+)?$/.test(a);
    const isIdent = (a) => /^[A-Za-z_][A-Za-z0-9_]*$/.test(a);

    const validateNode = (node) => {
      if (isAtom(node)) return true;

      if (!Array.isArray(node) || node.length === 0) return false;

      // Head must be an atom
      const head = node[0];
      if (!isAtom(head)) return false;

      // (true ...) or (false ...) are illegal (true/false are 0-arity constants)
      if ((head === "true" || head === "false") && node.length > 1)
        return false;

      const args = node.slice(1);

      // Known logical/arithmetic operators
      if (Object.prototype.hasOwnProperty.call(MIN_ARITY, head)) {
        const min = MIN_ARITY[head];
        const max = MAX_ARITY[head] ?? Infinity;
        if (args.length < min || args.length > max) return false;
        return args.every(validateNode);
      }

      // Comparators that might appear normalized from other pipelines
      if (["distinct", "="].includes(head)) {
        if (args.length < 2) return false;
        return args.every(validateNode);
      }

      // Any other head means function application. We do not declare functions in this pipeline,
      // so treat all non-operator applications as invalid (prevents "(x)" and "(f a)").
      if (isIdent(head) || isNumber(head)) {
        // Reject both nullary "(x)" and n-ary "(f a ...)" since we have no such decls.
        return false;
      }

      return false;
    };

    const ok = validateNode(ast);
    return ok
      ? { ok: true }
      : { ok: false, reason: "invalid operator/arity/application" };
  },

  async initialize() {
    if (!_z3) {
      await initializeZ3();
    }
  },

  /**
   * Check satisfiability of a single SMT-LIB term (no full script).
   * Implements:
   * 1) Early short-circuit for "true"/"false".
   * 2) Early *validation* (reject malformed or unknown applications).
   * 3) Parse → solver_assert (no solver_from_string).
   * 4) Correct Z3_lbool mapping: SAT=1, UNSAT=0, UNDEF=-1 (UNDEF → failure).
   *
   * @param {string} formula
   * @returns {Promise<boolean>}
   */
  async isSatisfiable(formula) {
    await this.initialize();

    const body = String(formula || "").trim();
    if (!body || body === "true") return true;
    if (body === "false" || /^\(\s*false\s*\)$/.test(body)) return false;

    // Early structural/arity validation. On failure, treat as UNSAT (fail fast).
    const validation = this._validateSmtTerm(body);
    if (!validation.ok) {
      console.warn(
        "[isSatisfiable] Rejected malformed SMT:",
        validation.reason,
        "— returning UNSAT."
      );
      return false;
    }

    // Collect free symbols and declare them with sensible sorts (reusing your logic)
    const KEYWORDS = new Set([
      "assert",
      "check-sat",
      "set-logic",
      "declare-const",
      "declare-fun",
      "define-fun",
      "and",
      "or",
      "not",
      "xor",
      "=>",
      "ite",
      "let",
      "forall",
      "exists",
      "distinct",
      "true",
      "false",
      "Int",
      "Real",
      "Bool",
      "div",
      "mod",
      "rem",
      "as",
      "select",
      "store",
    ]);

    const getBase = (tok) => tok.replace(/_(?:r|w|prime)$/, "");
    const getSmtSortFromMeta = (meta) => {
      const t = String(meta?.type || "").toLowerCase();
      if (t === "int" || t === "integer") return "Int";
      if (t === "bool" || t === "boolean") return "Bool";
      return "Real";
    };

    const collectBound = (src) => {
      const bound = new Set();
      const qre =
        /\(\s*(?:exists|forall)\s*\(\s*((?:\(\s*[A-Za-z_]\w*\s+[A-Za-z_]\w*\s*\)\s*)+)\)\s*/g;
      let m;
      while ((m = qre.exec(src)) !== null) {
        const blob = m[1];
        for (const mm of blob.matchAll(
          /\(\s*([A-Za-z_]\w*)\s+[A-ZaZ_]\w*\s*\)/g
        )) {
          bound.add(mm[1]);
        }
      }
      return bound;
    };

    const inferBool = (name, src) => {
      const n = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      const ps = [
        new RegExp(`\\(=\\s+${n}\\s+(?:true|false)\\)`),
        new RegExp(`\\(=\\s+(?:true|false)\\s+${n}\\)`),
        new RegExp(`\\(not\\s+${n}\\)`),
        new RegExp(`\\(and\\s+${n}\\b`),
        new RegExp(`\\(or\\s+${n}\\b`),
      ];
      return ps.some((re) => re.test(src));
    };

    const tokens = body.match(/[A-Za-z_][A-Za-z0-9_]*/g) || [];
    const bound = collectBound(body);
    const seen = new Set();
    const declsNeeded = []; // [name, sort] pairs

    for (const tok of tokens) {
      if (KEYWORDS.has(tok)) continue;
      if (bound.has(tok)) continue;
      if (seen.has(tok)) continue;
      seen.add(tok);

      const base = getBase(tok);
      let sort = null;
      const meta = this._globalDataVariables?.get(base);
      if (meta) {
        sort = getSmtSortFromMeta(meta);
      } else if (inferBool(tok, body)) {
        sort = "Bool";
      } else {
        sort = "Real";
      }
      declsNeeded.push([tok, sort]);
    }

    console.log(`[isSatisfiable] Checking "${body.substring(0, 500)}...":`);
    console.log(`  Variables: ${declsNeeded.map(([n, s]) => `${n}:${s}`).join(", ")}`);

    try {
      // Create a fresh solver
      const solver = _z3.mk_solver(_context);
      _z3.solver_inc_ref(_context, solver);
      
      // Build script with declarations and assert wrapper
      const decls = declsNeeded.map(([name, sort]) => `(declare-const ${name} ${sort})`);
      const script = decls.join("\n") + (decls.length ? "\n" : "") + `(assert ${body})`;
      
      console.log(`[isSatisfiable] Full script:\n${script}`);
      
      // Parse the script - parse_smtlib2_string will handle declarations
      const astVec = _z3.parse_smtlib2_string(
        _context, 
        script,
        [],  // sort_names
        [],  // sort_symbols  
        [],  // sorts
        [],  // decl_names
        [],  // decl_symbols
        []   // decls
      );
      const n = _z3.ast_vector_size(_context, astVec);

      if (n <= 0) {
        console.warn("[isSatisfiable] Parser produced 0 assertions — returning UNSAT.");
        _z3.solver_dec_ref(_context, solver);
        return false;
      }

      console.log(`[isSatisfiable] AST vector has ${n} nodes`);
      
      // Assert all nodes (should all be Bool since we're parsing a formula)
      let assertedCount = 0;
      for (let i = 0; i < n; i++) {
        const node = _z3.ast_vector_get(_context, astVec, i);
        const nodeStr = _z3.ast_to_string(_context, node);
        
        const sort = _z3.get_sort(_context, node);
        const sortKind = _z3.get_sort_kind(_context, sort);
        
        console.log(`[isSatisfiable] Node ${i}: sortKind=${sortKind}, ast="${nodeStr.substring(0, 100)}"`);
        
        // Z3_BOOL_SORT = 1
        if (sortKind === 1) {
          _z3.solver_assert(_context, solver, node);
          assertedCount++;
          console.log(`[isSatisfiable]   → Asserted (Bool)`);
        } else {
          console.log(`[isSatisfiable]   → Skipped (not Bool)`);
        }
      }
      
      console.log(`[isSatisfiable] Asserted ${assertedCount} out of ${n} nodes`);

      const res = await _z3.solver_check(_context, solver);
      console.log(`[isSatisfiable] Z3 result for "${body.substring(0, 500)}...": ${res} (1=SAT, 0=UNSAT, -1=UNDEF)`);
      
      // Only get model if SAT
      if (res === 1) {
        const model = _z3.solver_get_model(_context, solver);
        const modelStr = _z3.model_to_string(_context, model);
        console.log(`[isSatisfiable] Model: ${modelStr}`);
      }
      
      // Clean up solver
      _z3.solver_dec_ref(_context, solver);
      
      // Map: SAT=1, UNSAT=0, UNDEF=-1 (treat UNDEF as failure -> UNSAT here).
      if (res === 1) {
        console.log(`[isSatisfiable] Formula is SAT`);
        return true;
      }
      if (res === 0) {
        console.log(`[isSatisfiable] Formula is UNSAT`);
        return false;
      }
      console.warn("[isSatisfiable] Z3 returned UNDEF; treating as UNSAT.");
      return false;
    } catch (e) {
      console.error(
        "[isSatisfiable] Z3 parse/assert failed; returning UNSAT.",
        e
      );
      return false;
    }
  },

  /**
   * SAT check with model, using parse → assert (no solver_from_string).
   * UNDEF is treated as failure. If parsing yields no assertions, returns UNSAT.
   *
   * @param {string} scriptOrFormula  A single term (preferred) or a full script.
   * @returns {Promise<{ isSat: boolean, model: Map<string,string>, rawModel: string, error?: string }>}
   */
  async checkSatWithModel(scriptOrFormula) {
    await this.initialize();

    const s = String(scriptOrFormula || "").trim();
    const looksLikeScript =
      /\(\s*assert\b/.test(s) ||
      /\(\s*check-sat\b/.test(s) ||
      /\(\s*set-logic\b/.test(s) ||
      /\(\s*declare-const\b/.test(s) ||
      /\(\s*declare-fun\b/.test(s);

    // We prefer single-term inputs. If it's a term, validate and wrap with decls.
    if (!looksLikeScript) {
      // Short-circuit true/false
      if (!s || s === "true") {
        return { isSat: true, model: new Map(), rawModel: "" };
      }
      if (s === "false" || /^\(\s*false\s*\)$/.test(s)) {
        return { isSat: false, model: new Map(), rawModel: "" };
      }

      const validation = this._validateSmtTerm(s);
      if (!validation.ok) {
        return {
          isSat: false,
          model: new Map(),
          rawModel: "",
          error: `Rejected malformed SMT: ${validation.reason}`,
        };
      }

      // Reuse the same free-symbol declaration inference as in isSatisfiable
      const KEYWORDS = new Set([
        "assert",
        "check-sat",
        "set-logic",
        "declare-const",
        "declare-fun",
        "define-fun",
        "and",
        "or",
        "not",
        "xor",
        "=>",
        "ite",
        "let",
        "forall",
        "exists",
        "distinct",
        "true",
        "false",
        "Int",
        "Real",
        "Bool",
        "div",
        "mod",
        "rem",
        "as",
        "select",
        "store",
      ]);

      const getBase = (tok) => tok.replace(/_(?:r|w|prime)$/, "");
      const getSmtSortFromMeta = (meta) => {
        const t = String(meta?.type || "").toLowerCase();
        if (t === "int" || t === "integer") return "Int";
        if (t === "bool" || t === "boolean") return "Bool";
        return "Real";
      };
      const collectBound = (src) => {
        const bound = new Set();
        const qre =
          /\(\s*(?:exists|forall)\s*\(\s*((?:\(\s*[A-Za-z_]\w*\s+[A-Za-z_]\w*\s*\)\s*)+)\)\s*/g;
        let m;
        while ((m = qre.exec(src)) !== null) {
          const blob = m[1];
          for (const mm of blob.matchAll(
            /\(\s*([A-Za-z_]\w*)\s+[A-ZaZ_]\w*\s*\)/g
          )) {
            bound.add(mm[1]);
          }
        }
        return bound;
      };

      const inferBool = (name, src) => {
        const n = name.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
        const ps = [
          new RegExp(`\\(=\\s+${n}\\s+(?:true|false)\\)`),
          new RegExp(`\\(=\\s+(?:true|false)\\s+${n}\\)`),
          new RegExp(`\\(not\\s+${n}\\)`),
          new RegExp(`\\(and\\s+${n}\\b`),
          new RegExp(`\\(or\\s+${n}\\b`),
        ];
        return ps.some((re) => re.test(src));
      };

      const tokens = s.match(/[A-Za-z_][A-Za-z0-9_]*/g) || [];
      const bound = collectBound(s);
      const seen = new Set();
      const decls = [];
      for (const tok of tokens) {
        if (KEYWORDS.has(tok)) continue;
        if (bound.has(tok)) continue;
        if (seen.has(tok)) continue;
        seen.add(tok);

        const base = getBase(tok);
        let sort = null;
        const meta = this._globalDataVariables?.get(base);
        if (meta) {
          sort = getSmtSortFromMeta(meta);
        } else if (inferBool(tok, s)) {
          sort = "Bool";
        } else {
          sort = "Real";
        }
        decls.push(`(declare-const ${tok} ${sort})`);
      }

      const script =
        (decls.length ? decls.join("\n") + "\n" : "") +
        `(assert ${s})`;

      try {
        const solver = _z3.mk_solver(_context);
        _z3.solver_inc_ref(_context, solver);
        
        const astVec = _z3.parse_smtlib2_string(
          _context,
          script,
          [],
          [],
          [],
          []
        );
        const n = _z3.ast_vector_size(_context, astVec);
        if (n <= 0) {
          _z3.solver_dec_ref(_context, solver);
          return {
            isSat: false,
            model: new Map(),
            rawModel: "",
            error: "Parser produced 0 assertions",
          };
        }

        // Only assert Bool formulas
        for (let i = 0; i < n; i++) {
          const node = _z3.ast_vector_get(_context, astVec, i);
          const sort = _z3.get_sort(_context, node);
          const sortKind = _z3.get_sort_kind(_context, sort);
          if (sortKind === 1) { // Z3_BOOL_SORT
            _z3.solver_assert(_context, solver, node);
          }
        }

        const res = await _z3.solver_check(_context, solver);
        if (res === 1) {
          const mdl = _z3.solver_get_model(_context, solver);
          const rawModel = _z3.model_to_string(_context, mdl);

          // Parse simple (define-fun x () Sort value) lines into a Map
          const modelMap = new Map();
          for (const line of rawModel.split(/\r?\n/)) {
            const m = line.match(
              /\(define-fun\s+([A-Za-z_][A-Za-z0-9_]*)\s+\(\)\s+[A-Za-z_][A-Za-z0-9_]*\s+(.+)\)/
            );
            if (m) modelMap.set(m[1], m[2].trim());
          }
          
          _z3.solver_dec_ref(_context, solver);
          return { isSat: true, model: modelMap, rawModel };
        }

        if (res === 0) {
          _z3.solver_dec_ref(_context, solver);
          return { isSat: false, model: new Map(), rawModel: "" };
        }

        _z3.solver_dec_ref(_context, solver);
        return {
          isSat: false,
          model: new Map(),
          rawModel: "",
          error: "Z3 returned UNDEF",
        };
      } catch (e) {
        return {
          isSat: false,
          model: new Map(),
          rawModel: "",
          error: String(e?.message || e),
        };
      }
    }

    // If it's a full script: we still avoid solver_from_string.
    try {
      const solver = _z3.mk_solver(_context);
      _z3.solver_inc_ref(_context, solver);
      
      const astVec = _z3.parse_smtlib2_string(_context, s, [], [], [], []);
      const n = _z3.ast_vector_size(_context, astVec);
      if (n <= 0) {
        _z3.solver_dec_ref(_context, solver);
        return {
          isSat: false,
          model: new Map(),
          rawModel: "",
          error: "Script parsed but had 0 assertions",
        };
      }

      // Only assert Bool formulas
      for (let i = 0; i < n; i++) {
        const node = _z3.ast_vector_get(_context, astVec, i);
        const sort = _z3.get_sort(_context, node);
        const sortKind = _z3.get_sort_kind(_context, sort);
        if (sortKind === 1) { // Z3_BOOL_SORT
          _z3.solver_assert(_context, solver, node);
        }
      }

      const res = await _z3.solver_check(_context, solver);
      if (res === 1) {
        const mdl = _z3.solver_get_model(_context, solver);
        const rawModel = _z3.model_to_string(_context, mdl);
        const modelMap = new Map();
        for (const line of rawModel.split(/\r?\n/)) {
          const m = line.match(
            /\(define-fun\s+([A-Za-z_][A-Za-z0-9_]*)\s+\(\)\s+[A-Za-z_][A-ZaZ0-9_]*\s+(.+)\)/
          );
          if (m) modelMap.set(m[1], m[2].trim());
        }
        
        _z3.solver_dec_ref(_context, solver);
        return { isSat: true, model: modelMap, rawModel };
      }

      if (res === 0) {
        _z3.solver_dec_ref(_context, solver);
        return { isSat: false, model: new Map(), rawModel: "" };
      }

      _z3.solver_dec_ref(_context, solver);
      return {
        isSat: false,
        model: new Map(),
        rawModel: "",
        error: "Z3 returned UNDEF",
      };
    } catch (e) {
      return {
        isSat: false,
        model: new Map(),
        rawModel: "",
        error: String(e?.message || e),
      };
    }
  },

  parseModel(modelString) {
    const model = new Map();
    const lines = modelString.split("\n");

    for (const line of lines) {
      const match = line.match(
        /\(define-fun\s+([^\s\)]+)\s+\(\)\s+\w+\s+([^\)]+)\)/
      );
      if (match) {
        const [, varName, value] = match;
        model.set(varName, value.trim());
      }
    }

    return model;
  },
};

export { initializeZ3, Z3Solver };
