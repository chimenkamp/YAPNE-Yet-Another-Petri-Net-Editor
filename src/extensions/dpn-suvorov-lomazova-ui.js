/**
 * Z3 Solver interface - Simple ES module approach
 */
const BASE_PATH = '/YAPNE-Yet-Another-Petri-Net-Editor/';

let _z3 = null;
let _context = null;
let _solver = null;
let _initPromise = null;

// Initialize Z3 using ES modules and dynamic import
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
          script.src = `${BASE_PATH}z3-built.js`;
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
 * Z3 Solver facade adapted from the original working code
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
          /\(\s*([A-Za-z_]\w*)\s+[A-Za-z_]\w*\s*\)/g
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
      } else if (inferBool(tok, body)) {
        sort = "Bool";
      } else {
        sort = "Real";
      }
      decls.push(`(declare-const ${tok} ${sort})`);
    }

    const script =
      `(set-logic ALL)\n` +
      (decls.length ? decls.join("\n") + "\n" : "") +
      `(assert ${body})`;

    try {
      // Parse the script; collect asserted ASTs explicitly.
      const astVec = _z3.parse_smtlib2_string(_context, script, [], [], [], []);
      const n = _z3.ast_vector_size(_context, astVec);

      if (n <= 0) {
        console.warn(
          "[isSatisfiable] Parser produced 0 assertions — returning UNSAT."
        );
        return false;
      }

      // Create a fresh solver, assert ASTs, then check.
      const solver = _z3.mk_solver(_context);
      for (let i = 0; i < n; i++) {
        _z3.solver_assert(
          _context,
          solver,
          _z3.ast_vector_get(_context, astVec, i)
        );
      }

      const res = await _z3.solver_check(_context, solver);
      // Map: SAT=1, UNSAT=0, UNDEF=-1 (treat UNDEF as failure -> UNSAT here).
      if (res === 1) return true;
      if (res === 0) return false;
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
            /\(\s*([A-Za-z_]\w*)\s+[A-Za-z_]\w*\s*\)/g
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
        `(set-logic ALL)\n` +
        (decls.length ? decls.join("\n") + "\n" : "") +
        `(assert ${s})`;

      try {
        const solver = _z3.mk_solver(_context);
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
          return {
            isSat: false,
            model: new Map(),
            rawModel: "",
            error: "Parser produced 0 assertions",
          };
        }

        for (let i = 0; i < n; i++) {
          _z3.solver_assert(
            _context,
            solver,
            _z3.ast_vector_get(_context, astVec, i)
          );
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
          return { isSat: true, model: modelMap, rawModel };
        }

        if (res === 0) {
          return { isSat: false, model: new Map(), rawModel: "" };
        }

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
      const astVec = _z3.parse_smtlib2_string(_context, s, [], [], [], []);
      const n = _z3.ast_vector_size(_context, astVec);
      if (n <= 0) {
        return {
          isSat: false,
          model: new Map(),
          rawModel: "",
          error: "Script parsed but had 0 assertions",
        };
      }

      for (let i = 0; i < n; i++) {
        _z3.solver_assert(
          _context,
          solver,
          _z3.ast_vector_get(_context, astVec, i)
        );
      }

      const res = await _z3.solver_check(_context, solver);
      if (res === 1) {
        const mdl = _z3.solver_get_model(_context, solver);
        const rawModel = _z3.model_to_string(_context, mdl);
        const modelMap = new Map();
        for (const line of rawModel.split(/\r?\n/)) {
          const m = line.match(
            /\(define-fun\s+([A-Za-z_][A-Za-z0-9_]*)\s+\(\)\s+[A-Za-z_][A-Za-z0-9_]*\s+(.+)\)/
          );
          if (m) modelMap.set(m[1], m[2].trim());
        }
        return { isSat: true, model: modelMap, rawModel };
      }

      if (res === 0) {
        return { isSat: false, model: new Map(), rawModel: "" };
      }

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

/**
 * Suvorov–Lomazova Data Petri Net Soundness Verifier
 * Refactored to use SMT-based verification with SmtFromDpnGenerator integration
 */
class SmtFromDpnGenerator {
  /**
   * Generate an SMT-LIB2 encoding aligned with the paper’s step semantics.
   * Key points:
   * - Per-step data variables v_i and markings M_p_i are declared for i=0..K.
   * - For each step i < K and each transition t, a fire flag f_t_i is declared.
   * If τ-transitions are NOT explicitly present in the DPN, we also declare
   * f_tau_t_i and use the paper’s τ-guard:
   * guard(τ(t)) := ¬∃W(t).( pre_t ∧ post_t )
   * Variables in τ do not change when τ fires.
   * - Enabling: token availability on input places; data guard via
   * (pre with reads at i) and (post with writes at i+1). This matches
   * the paper’s “guard(t)” when projecting to step i/i+1.
   * - Frame conditions: for a visible t, variables not written by t remain equal
   * across i→i+1; for τ(t), ALL variables remain equal.
   * - Marking update uses incidence (+outflow - inflow) for both visible and τ.
   * - Firing policy is configurable:
   * - 'atMostOne' (default): at most one of {f_*, f_tau_*[, idle_i]} is true.
   * - 'exactlyOne': exactly one is true per step.
   * - 'free': no mutual-exclusion constraint is imposed.
   * Regardless of policy, if no transition fires at step i, the encoding enforces
   * a full stutter on BOTH data and markings. When idle_i is available,
   * we also enforce (iff idle_i (not anyFire_i)) to forbid the illegal case
   * “no fire ∧ ¬idle”.
   * - Final marking and (optional) coverage are asserted at step K. Coverage
   * excludes τ-transitions by default.
   *
   * @param {object} petriNetObj - Petri net object {places[], transitions[], arcs[], dataVariables[]}.
   * @param {object} [params] - Optional parameters.
   * @param {number} [params.K=6] - The number of steps.
   * @param {string} [params.logic='ALL'] - The SMT logic to use.
   * @param {object} [params.finalMarking] - The final marking.
   * @param {object} [params.initialData] - The initial data values.
   * @param {object} [params.sortsOverride] - Overrides for data variable sorts.
   * @param {boolean} [params.coverage=false] - Whether to check for transition coverage.
   * @param {boolean} [params.coverageIncludesTau=false] - Whether coverage includes tau transitions.
   * @param {('atMostOne'|'exactlyOne'|'free')} [params.firing='atMostOne'] - The firing policy.
   * @returns {string} The generated SMT-LIB2 string.
   */
  generateSMT(petriNetObj, params = {}) {
    const cfg = this._normalizeConfig(petriNetObj, params);
    const {
      logic,
      K,
      placeIds,
      transIds,
      arcsIn,
      arcsOut,
      dataVarsMap,
      dataVarsList,
      initialMarking,
      finalMarking,
      initialData,
      coverage,
    } = cfg;

    const coverageIncludesTau = params.coverageIncludesTau === true;
    const coverageFor = Array.isArray(params.coverageFor)
      ? params.coverageFor.map(String)
      : null;

    // Enforce interleaving semantics: normalize 'free' → 'atMostOne'
    const firingPolicyRaw = params.firing || "atMostOne";
    const firingPolicy =
      firingPolicyRaw === "free" ? "atMostOne" : firingPolicyRaw; // "atMostOne"|"exactlyOne"

    // Detect explicit τ transitions (by id prefix "tau_")
    const isTauId = (id) => String(id).startsWith("tau_");
    const hasExplicitTau = transIds.some(isTauId);

    const lines = [];
    const out = (s) => lines.push(s);

    // --- Header & helpers
    out(`(set-logic ${logic || "ALL"})`);
    out(`(define-fun K () Int ${Number.isInteger(K) ? K : 6})`);
    out(`(define-fun b2i ((b Bool)) Int (ite b 1 0))`);
    out(`(define-fun nonneg ((x Int)) Bool (>= x 0))`);

    // --- Declarations for data variables v_i, markings M_p_i
    for (let i = 0; i <= K; i++) {
      for (const [vName, sort] of dataVarsList) {
        out(`(declare-const ${this._vStep(vName, i)} ${sort})`);
      }
    }
    for (let i = 0; i <= K; i++) {
      for (const p of placeIds) {
        out(`(declare-const ${this._mStep(p, i)} Int)`);
      }
    }

    // --- Firing flags (and optional τ flags if τ not explicit)
    for (let i = 0; i < K; i++) {
      for (const t of transIds) {
        out(`(declare-const ${this._fStep(t, i)} Bool)`);
        if (!hasExplicitTau && !isTauId(t)) {
          out(`(declare-const ${this._ftStep(t, i)} Bool)`);
        }
      }
      if (firingPolicy !== "free") {
        out(`(declare-const idle_${i} Bool)`);
      }
    }

    // --- Initial marking & data
    for (const p of placeIds) {
      out(`(assert (= ${this._mStep(p, 0)} ${initialMarking[p] || 0}))`);
    }
    for (const [vName, sort] of dataVarsList) {
      if (Object.prototype.hasOwnProperty.call(initialData, vName)) {
        out(
          `(assert (= ${this._vStep(vName, 0)} ${this._lit(
            initialData[vName],
            sort
          )}))`
        );
      }
    }

    // --- Marking non-negativity at all steps
    for (let i = 0; i <= K; i++) {
      const conj = placeIds
        .map((p) => `(nonneg ${this._mStep(p, i)})`)
        .join(" ");
      out(`(assert (and ${conj}))`);
    }

    // --- Per-step constraints
    for (let i = 0; i < K; i++) {
      // Each step is either a single firing (visible or τ) or a stutter step.
      // When no firing occurs, data and markings must stutter.

      // 1) Firing policy + "must act or idle" discipline
      const boolFlags = [];
      const intFlags = [];
      for (const t of transIds) {
        const vis = this._fStep(t, i);
        boolFlags.push(vis);
        intFlags.push(`(b2i ${vis})`);
        if (!hasExplicitTau && !isTauId(t)) {
          const tau = this._ftStep(t, i);
          boolFlags.push(tau);
          intFlags.push(`(b2i ${tau})`);
        }
      }
      const anyFire = boolFlags.length
        ? `(or ${boolFlags.join(" ")})`
        : "false";

      if (firingPolicy !== "free") {
        const idle = `idle_${i}`;
        if (firingPolicy === "atMostOne") {
          out(`(assert (<= (+ ${intFlags.join(" ")} (b2i ${idle})) 1))`);
        } else if (firingPolicy === "exactlyOne") {
          out(`(assert (= (+ ${intFlags.join(" ")} (b2i ${idle})) 1))`);
        }
        // Forbid the illegal case: (not anyFire) ∧ (not idle)
        out(`(assert (iff ${idle} (not ${anyFire})))`);
      }

      // 2) Token enabling: ONLY for visible, non-τ transitions
      for (const t of transIds) {
        if (isTauId(t)) continue; // τ never requires tokens
        const firedVis = this._fStep(t, i);
        const inArcs = arcsIn.get(t) || [];
        for (const [p, w] of inArcs) {
          out(`(assert (=> ${firedVis} (>= ${this._mStep(p, i)} ${w})))`);
        }
      }

      // 3) Data guards & frame conditions
      for (const t of transIds) {
        const isTauTransition = isTauId(t);
        const preStr = cfg.transitionPre.get(t) || "";
        const postStr = cfg.transitionPost.get(t) || "";

        const fVis = this._fStep(t, i);
        const fTau =
          !hasExplicitTau && !isTauTransition ? this._ftStep(t, i) : null;

        // Visible guard: pre at step i, post at step i+1
        const preVis = this._rewriteGuard(preStr, i, dataVarsList, false);
        const postVis = this._rewriteGuard(postStr, i, dataVarsList, true);
        if (preVis) out(`(assert (=> ${fVis} ${preVis}))`);
        if (postVis) out(`(assert (=> ${fVis} ${postVis}))`);

        // Frame for variables not written by t under visible firing
        const writes = this._writtenVars(postStr, dataVarsList);
        for (const [vName] of dataVarsList) {
          if (!writes.has(vName)) {
            out(
              `(assert (=> ${fVis} (= ${this._vStep(
                vName,
                i + 1
              )} ${this._vStep(vName, i)})))`
            );
          }
        }

        // τ semantics — implicit τ flags: guard_τ and full stutter on data
        if (fTau) {
          const tauInner = this._tauGuard(preStr, postStr, i, dataVarsList); // ¬∃W.(pre∧post)
          if (tauInner) out(`(assert (=> ${fTau} ${tauInner}))`);
          for (const [vName] of dataVarsList) {
            out(
              `(assert (=> ${fTau} (= ${this._vStep(
                vName,
                i + 1
              )} ${this._vStep(vName, i)})))`
            );
          }
        }

        // Explicit τ transitions: ALWAYS stutter data when they fire
        if (hasExplicitTau && isTauTransition) {
          for (const [vName] of dataVarsList) {
            out(
              `(assert (=> ${fVis} (= ${this._vStep(
                vName,
                i + 1
              )} ${this._vStep(vName, i)})))`
            );
          }
        }
      }

      // 4) Marking update (incidence) — EXCLUDE τ (pure stutter)
      for (const p of placeIds) {
        const inflow = [];
        const outflow = [];
        for (const t of transIds) {
          if (isTauId(t)) continue; // explicit τ never moves tokens
          const vis = this._fStep(t, i);

          for (const [pp, w] of arcsOut.get(t) || []) {
            if (pp === p) {
              inflow.push(`(* ${w} (b2i ${vis}))`);
            }
          }
          for (const [pp, w] of arcsIn.get(t) || []) {
            if (pp === p) {
              outflow.push(`(* ${w} (b2i ${vis}))`);
            }
          }
        }

        const infl = inflow.length ? `(+ ${inflow.join(" ")})` : "0";
        const outf = outflow.length ? `(+ ${outflow.join(" ")})` : "0";
        out(
          `(assert (= ${this._mStep(p, i + 1)} (+ ${this._mStep(
            p,
            i
          )} ${infl} (- ${outf}))))`
        );
      }

      // 5) Stutter frames when no firing (and explicit idle if present)
      const eqMs = placeIds
        .map((p) => `(= ${this._mStep(p, i + 1)} ${this._mStep(p, i)})`)
        .join(" ");
      const eqVs = dataVarsList
        .map(([v]) => `(= ${this._vStep(v, i + 1)} ${this._vStep(v, i)})`)
        .join(" ");

      // Always enforce stutter if no transition fires
      out(`(assert (=> (not ${anyFire}) (and ${eqMs} ${eqVs})))`);

      // Additionally, when idle_i exists, keep idle ⇒ stutter
      if (firingPolicy !== "free") {
        out(`(assert (=> idle_${i} (and ${eqMs} ${eqVs})))`);
      }
    }

    // --- Final marking (if provided) at step K
    if (finalMarking) {
      for (const p of placeIds) {
        out(`(assert (= ${this._mStep(p, K)} ${finalMarking[p] || 0}))`);
      }
    }

    // --- Coverage (default excludes τ); supports coverageFor
    if (
      (coverage || (coverageFor && coverageFor.length > 0)) &&
      transIds.length > 0
    ) {
      const wanted =
        coverageFor && coverageFor.length
          ? transIds.filter((t) => coverageFor.includes(String(t)))
          : transIds;
      for (const t of wanted) {
        if (!coverageIncludesTau && isTauId(t)) continue;
        const ors = Array.from({ length: K }, (_, i) => this._fStep(t, i)).join(
          " "
        );
        if (ors.length) out(`(assert (or ${ors}))`);
      }
    }

    out(`(check-sat)`);

    // Final sanitize: drop any stray apostrophes in identifiers
    const smt = lines.join("\n");
    return this._sanitizePrimes(smt);
  }

  /**
   * Normalize configuration: collect ids, arcs, guards, sorts, initial/final markings and data.
   *
   * @param {object} pn - Petri net object.
   * @param {object} params - Additional parameters.
   * @returns {object} Normalized configuration.
   * @private
   */
  _normalizeConfig(pn, params) {
    const logic = params.logic || "ALL";
    const K = Number.isInteger(params.K) ? params.K : 6;

    const placeIds = (pn.places || []).map((p) => this._sym(p.id));
    const transIds = (pn.transitions || []).map((t) => this._sym(t.id));

    const placeIdSet = new Set(placeIds);
    const transIdSet = new Set(transIds);

    const arcsIn = new Map();
    const arcsOut = new Map();
    for (const t of transIds) {
      arcsIn.set(t, []);
      arcsOut.set(t, []);
    }
    for (const a of pn.arcs || []) {
      const s = this._sym(a.source);
      const tg = this._sym(a.target);
      const w = Number(a.weight) || 1;
      if (placeIdSet.has(s) && transIdSet.has(tg)) arcsIn.get(tg).push([s, w]);
      if (transIdSet.has(s) && placeIdSet.has(tg)) arcsOut.get(s).push([tg, w]);
    }

    const sortsOverride = params.sortsOverride || {};
    const dataVarsMap = new Map();
    for (const dv of pn.dataVariables || []) {
      const v = this._sym(dv.name || dv.id);
      const sort = this._toSort(
        String(dv.type || "real").toLowerCase(),
        sortsOverride
      );
      dataVarsMap.set(v, sort);
    }
    const dataVarsList = Array.from(dataVarsMap.entries()).sort((a, b) =>
      a[0].localeCompare(b[0])
    );

    const transitionPre = new Map();
    const transitionPost = new Map();
    for (const t of pn.transitions || []) {
      transitionPre.set(this._sym(t.id), String(t.precondition || "").trim());
      transitionPost.set(this._sym(t.id), String(t.postcondition || "").trim());
    }

    const initialMarking = {};
    for (const p of pn.places || [])
      initialMarking[this._sym(p.id)] = Number(p.tokens) || 0;

    let finalMarking = params.finalMarking || null;

    const initialData = {};
    for (const dv of pn.dataVariables || []) {
      const v = this._sym(dv.name || dv.id);
      if (typeof dv.currentValue !== "undefined" && dv.currentValue !== null)
        initialData[v] = dv.currentValue;
    }
    Object.assign(initialData, params.initialData || {});

    const coverage = Boolean(params.coverage);

    return {
      logic,
      K,
      placeIds,
      transIds,
      arcsIn,
      arcsOut,
      dataVarsMap,
      dataVarsList,
      transitionPre,
      transitionPost,
      initialMarking,
      finalMarking,
      initialData,
      coverage,
    };
  }

  /**
   * Create the τ-guard for transition t at step i:
   * guard_τ(t,i) := ¬∃W_t . ( pre_i ∧ post_i[W_t] )
   * where:
   * - pre_i is the precondition with reads mapped to step i variables,
   * - post_i[W_t] is the postcondition with each written v' replaced by a fresh bound
   * variable W_v, and all unprimed reads mapped to step i variables,
   * - W_t is the set of variables written by t.
   *
   * This method performs only a *syntactic* construction suitable for embedding in SMT;
   * it does not run QE here (the quantifier remains explicit in the returned string).
   *
   * @param {string} preStr - Raw precondition of t.
   * @param {string} postStr - Raw postcondition of t.
   * @param {number} i - Step index.
   * @param {Array<[string, string]>} dataVarsList - Array<[varName, sort]> of all data variables.
   * @returns {string} SMT-LIB2 string for the τ-guard at step i (never contains apostrophes).
   * @private
   */
  _tauGuard(preStr, postStr, i, dataVarsList) {
    // pre at step i (reads → i)
    const pre =
      this._rewriteGuard(preStr, i, dataVarsList, /*isPost=*/ false) || "true";

    // Identify written variables (v' occurs in post)
    const writes = this._writtenVars(postStr, dataVarsList);

    // Replace each v' in post with its bound write symbol W_v; then map reads to step i
    let postBody = String(postStr || "").trim();
    for (const [vName] of dataVarsList) {
      const rePrime = new RegExp(`\\b${this._escapeReg(vName)}\\s*'`, "g");
      postBody = postBody.replace(rePrime, this._wVar(vName)); // v' → v_w (bound name)
    }
    const post =
      this._rewriteGuard(postBody, i, dataVarsList, /*isPost=*/ false) ||
      "true";

    // Simple simplifications when no writes are present
    if (writes.size === 0) {
      if (pre === "true" && post === "true") return "false"; // ¬(true ∧ true)
      if (post === "true") return `(not ${pre})`; // ¬(pre)
      if (pre === "true") return `(not ${post})`; // ¬(post)
      return `(not (and ${pre} ${post}))`; // ¬(pre ∧ post)
    }

    // Build ∃W_t. (pre ∧ post) where W_t = { v_w | v ∈ writes }
    const boundDecls = [];
    for (const [vName, sort] of dataVarsList) {
      if (writes.has(vName)) boundDecls.push(`(${this._wVar(vName)} ${sort})`);
    }
    const decls = boundDecls.length ? boundDecls.join(" ") : "(dummy_w Int)"; // should not happen because writes.size>0

    // (not (exists (W_t) (and pre post)))
    return `(not (exists (${decls}) (and ${pre} ${post})))`;
  }

  /**
   * Rewrite a guard or postcondition to SMT-LIB2 with per-step variables.
   * Converts primed occurrences x' to step-indexed symbols so no apostrophes remain.
   *
   * @param {string} guardStr - Guard or postcondition string.
   * @param {number} i - Step index.
   * @param {Array<[string, string]>} dataVarsList - List of [varName, sort].
   * @param {boolean} isPost - Whether this is a postcondition (primed writes go to step i+1).
   * @returns {string} SMT-LIB2 expression or empty string.
   * @private
   */
  _rewriteGuard(guardStr, i, dataVarsList, isPost) {
    const s = String(guardStr || "").trim();
    if (!s) return "";
    const withVars = this._applyStepVars(s, i, dataVarsList, isPost);
    if (/^\s*\(/.test(withVars)) return withVars;
    return this._infixToSmt(withVars);
  }

  /**
   * Replace variable names with per-step symbols, handling primed writes (x') robustly.
   * Ensures patterns like "x'","x'=", "x' +", "x' >" are correctly replaced.
   *
   * @param {string} s - Input string.
   * @param {number} i - Step index.
   * @param {Array<[string, string]>} dataVarsList - List of [varName, sort].
   * @param {boolean} isPost - Whether this is a postcondition.
   * @returns {string} String with variables stepped, no apostrophes left for known variables.
   * @private
   */
  _applyStepVars(s, i, dataVarsList, isPost) {
    let r = ` ${s} `;
    r = r.replace(/\btrue\b/gi, "true").replace(/\bfalse\b/gi, "false");

    for (const [vName] of dataVarsList) {
      const primeRe = new RegExp(`\\b${this._escapeReg(vName)}\\s*'`, "g");
      const curRe = new RegExp(`\\b${this._escapeReg(vName)}\\b`, "g");

      r = r.replace(primeRe, this._vStep(vName, i + 1));

      const token = `__TOK_${this._sym(vName)}_${i + 1}__`;
      r = r.replace(new RegExp(this._vStep(vName, i + 1), "g"), token);
      r = r.replace(curRe, this._vStep(vName, i));
      r = r.replace(new RegExp(token, "g"), this._vStep(vName, i + 1));
    }

    return r.trim();
  }

  /**
   * Convert a minimal infix boolean/arithmetic comparison string into SMT-LIB2 prefix form.
   * Supports: and, or, not, parentheses, binary comparators (=,!=,<,<=,>,>=).
   *
   * @param {string} expr - Infix-like expression.
   * @returns {string} SMT-LIB2 s-expression.
   * @private
   */
  _infixToSmt(expr) {
    const e = String(expr || "").trim();
    if (!e) return "";
    const norm = e
      .replace(/\s+/g, " ")
      .replace(/\band\b/gi, "and")
      .replace(/\bor\b/gi, "or")
      .replace(/\bnot\b/gi, "not");

    const isAtom = (s) =>
      /^[A-Za-z_][A-Za-z0-9_]*$/.test(s) ||
      /^[-+]?\d+(?:\.\d+)?$/.test(s) ||
      s === "true" ||
      s === "false";

    const stripOuter = (s) => {
      let t = String(s || "").trim();
      const balanced = (x) => {
        let d = 0;
        for (const ch of x) {
          if (ch === "(") d++;
          else if (ch === ")") d--;
          if (d < 0) return false;
        }
        return d === 0;
      };
      while (t.startsWith("(") && t.endsWith(")") && balanced(t)) {
        const inner = t.slice(1, -1).trim();
        if (!inner.startsWith("(") || !inner.endsWith(")")) {
          // only strip once if inner isn't also wrapped
          t = inner;
          break;
        }
        t = inner;
      }
      return t;
    };

    const splitTop = (s, op) => {
      const parts = [];
      let depth = 0,
        buf = [];
      const tokens = s.split(" ");
      for (let i = 0; i < tokens.length; i++) {
        const tok = tokens[i];
        for (const ch of tok) {
          if (ch === "(") depth++;
          if (ch === ")") depth--;
        }
        if (depth === 0 && tok === op) {
          parts.push(buf.join(" ").trim());
          buf = [];
        } else {
          buf.push(tok);
        }
      }
      const last = buf.join(" ").trim();
      if (last) parts.push(last);
      return parts;
    };

    const rec = (s) => {
      const t = s.trim();
      if (!t) return "true";
      if (t.startsWith("(") && t.endsWith(")")) return rec(t.slice(1, -1));
      const andParts = splitTop(t, "and");
      if (andParts.length > 1) return `(and ${andParts.map(rec).join(" ")})`;
      const orParts = splitTop(t, "or");
      if (orParts.length > 1) return `(or ${orParts.map(rec).join(" ")})`;
      if (t.startsWith("not ")) return `(not ${rec(t.slice(4))})`;
      const cmp = t.match(/^(.+?)\s*(=|!=|<=|>=|<|>)\s*(.+)$/);
      if (cmp) {
        const lhs = rec(cmp[1]);
        const rhs = rec(cmp[3]);
        const op = cmp[2] === "!=" ? "distinct" : cmp[2];
        if (op === "distinct") return `(distinct ${lhs} ${rhs})`;
        if (["=", "<", "<=", ">", ">="].includes(op))
          return `(${op} ${lhs} ${rhs})`;
      }
      return isAtom(t) ? t : t;
    };

    let res = rec(norm).replace(/\s+/g, " ").trim();
    if (isAtom(res)) return res;
    return stripOuter(res.startsWith("(") ? res : `(${res})`);
  }

  /**
   * Compute the set of written variables (those with a primed occurrence) in a postcondition.
   *
   * @param {string} postStr - Postcondition string.
   * @param {Array<[string, string]>} dataVarsList - List of [varName, sort].
   * @returns {Set<string>} Set of variable names.
   * @private
   */
  _writtenVars(postStr, dataVarsList) {
    const set = new Set();
    const s = String(postStr || "");
    for (const [vName] of dataVarsList) {
      if (new RegExp(`\\b${this._escapeReg(vName)}\\s*'`, "g").test(s))
        set.add(vName);
    }
    return set;
  }

  /**
   * Map a domain type string to SMT sort with optional overrides.
   *
   * @param {string} typ - Type string.
   * @param {object} override - Mapping overrides.
   * @returns {string} SMT sort string.
   * @private
   */
  _toSort(typ, override) {
    if (override && override[typ]) return override[typ];
    if (typ === "int" || typ === "integer") return "Int";
    if (typ === "bool" || typ === "boolean") return "Bool";
    return "Real";
  }

  /**
   * Create a per-step data variable symbol.
   *
   * @param {string} name - Base variable name.
   * @param {number} i - Step index.
   * @returns {string} Symbol string.
   * @private
   */
  _vStep(name, i) {
    return `${this._sym(name)}_${i}`;
  }

  /**
   * Create a per-step marking symbol.
   *
   * @param {string} placeId - Place identifier.
   * @param {number} i - Step index.
   * @returns {string} Symbol string.
   * @private
   */
  _mStep(placeId, i) {
    return `M_${this._sym(placeId)}_${i}`;
  }

  /**
   * Create a per-step visible fire flag symbol.
   *
   * @param {string} transId - Transition identifier.
   * @param {number} i - Step index.
   * @returns {string} Symbol string.
   * @private
   */
  _fStep(transId, i) {
    return `f_${this._sym(transId)}_${i}`;
  }

  /**
   * Create a per-step tau fire flag symbol.
   *
   * @param {string} transId - Transition identifier.
   * @param {number} i - Step index.
   * @returns {string} Symbol string.
   * @private
   */
  _ftStep(transId, i) {
    return `f_tau_${this._sym(transId)}_${i}`;
  }

  /**
   * Create a bound variable name for τ existential.
   *
   * @param {string} vName - Variable base name.
   * @returns {string} Bound variable symbol.
   * @private
   */
  _wVar(vName) {
    return `${this._sym(vName)}_w`;
  }

  /**
   * Final safety pass: ensure no apostrophes remain in identifiers (Z3 doesn't allow them).
   * Any residual pattern like name' is rewritten to name_prime.
   *
   * @param {string} smt - SMT-LIB string.
   * @returns {string} Sanitized SMT-LIB string.
   * @private
   */
  _sanitizePrimes(smt) {
    return smt.replace(
      /([A-Za-z_][A-Za-z0-9_]*)\s*'/g,
      (_, id) => `${id}_prime`
    );
  }

  /**
   * Sanitize identifiers to SMT-LIB friendly symbols.
   *
   * @param {string} x - Raw identifier.
   * @returns {string} Sanitized symbol.
   * @private
   */
  _sym(x) {
    return String(x).replace(/[^A-Za-z0-9_]/g, "_");
  }

  /**
   * Escape a string for use in RegExp.
   *
   * @param {string} s - Input string.
   * @returns {string} Escaped string.
   * @private
   */
  _escapeReg(s) {
    return String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }

  /**
   * Render a literal according to sort.
   *
   * @param {*} v - Value.
   * @param {string} sort - SMT sort.
   * @returns {string} SMT-LIB literal.
   * @private
   */
  _lit(v, sort) {
    if (sort === "Bool") return v ? "true" : "false";
    if (typeof v === "number") return Number.isFinite(v) ? `${v}` : "0";
    if (typeof v === "boolean") return v ? "true" : "false";
    return `${v}`;
  }
}

/**
 * Labeled Transition System implementation for DPN analysis
 */
class LabeledTransitionSystem {
  constructor() {
    this.nodes = new Map(); // (markingId, formulaId) -> {marking, formula, id}
    this.edges = new Map(); // edgeId -> {source, target, transition}
    this.nodeCounter = 0;
    this.edgeCounter = 0;
  }

  addNode(marking, formula) {
    const nodeId = `node_${this.nodeCounter++}`;
    const node = {
      id: nodeId,
      marking: marking,
      formula: formula,
      outgoingEdges: [],
      incomingEdges: [],
    };
    this.nodes.set(nodeId, node);
    return nodeId;
  }

  addEdge(sourceId, targetId, transition) {
    const edgeId = `edge_${this.edgeCounter++}`;
    const edge = {
      id: edgeId,
      source: sourceId,
      target: targetId,
      transition: transition,
    };
    this.edges.set(edgeId, edge);

    // Update node references
    if (this.nodes.has(sourceId)) {
      this.nodes.get(sourceId).outgoingEdges.push(edgeId);
    }
    if (this.nodes.has(targetId)) {
      this.nodes.get(targetId).incomingEdges.push(edgeId);
    }

    return edgeId;
  }

  findStronglyConnectedComponents() {
    // Tarjan's algorithm for SCC detection
    const indices = new Map();
    const lowLinks = new Map();
    const onStack = new Set();
    const stack = [];
    let index = 0;
    const sccs = [];

    const strongConnect = (nodeId) => {
      indices.set(nodeId, index);
      lowLinks.set(nodeId, index);
      index++;
      stack.push(nodeId);
      onStack.add(nodeId);

      const node = this.nodes.get(nodeId);
      for (const edgeId of node.outgoingEdges) {
        const edge = this.edges.get(edgeId);
        const targetId = edge.target;

        if (!indices.has(targetId)) {
          strongConnect(targetId);
          lowLinks.set(
            nodeId,
            Math.min(lowLinks.get(nodeId), lowLinks.get(targetId))
          );
        } else if (onStack.has(targetId)) {
          lowLinks.set(
            nodeId,
            Math.min(lowLinks.get(nodeId), indices.get(targetId))
          );
        }
      }

      if (lowLinks.get(nodeId) === indices.get(nodeId)) {
        const scc = [];
        let w;
        do {
          w = stack.pop();
          onStack.delete(w);
          scc.push(w);
        } while (w !== nodeId);
        sccs.push(scc);
      }
    };

    for (const nodeId of this.nodes.keys()) {
      if (!indices.has(nodeId)) {
        strongConnect(nodeId);
      }
    }

    return sccs;
  }

  /**
   * Find a maximal set of node-disjoint elementary cycles (paper-aligned).
   * Strategy:
   * 1) Compute SCCs (only SCCs with ≥2 nodes or a self-loop can contain cycles).
   * 2) For each such SCC, enumerate elementary cycles using Johnson’s algorithm
   * restricted to the SCC’s subgraph (to avoid duplicates and reduce cost).
   * 3) From all discovered cycles, select a maximal disjoint subset by greedy
   * choice (longest-first), as required by the refinement step.
   * 4) For each selected cycle, compute:
   * - transitions: IDs of LTS edges whose source and target are both in the cycle
   * - exitTransitions: IDs of LTS edges that leave the cycle’s node set
   *
   * @returns {Array<{ nodes: string[], transitions: Set<string>, exitTransitions: Set<string> }>}
   */
  findMaximalDisjointCycles() {
    // --- Build adjacency lists once ---
    const adj = new Map(); // nodeId -> nodeId[]
    const selfLoop = new Set(); // nodes with an explicit self-loop edge

    for (const [nid, node] of this.nodes) {
      const outs = [];
      for (const eid of node.outgoingEdges || []) {
        const e = this.edges.get(eid);
        if (!e) continue;
        outs.push(e.target);
        if (e.target === nid) selfLoop.add(nid);
      }
      adj.set(nid, outs);
    }

    // --- Helper: subgraph induced by a set of nodes ---
    const inducedAdj = (nodeSet) => {
      const sub = new Map();
      for (const n of nodeSet) {
        const outs = (adj.get(n) || []).filter((t) => nodeSet.has(t));
        sub.set(n, outs);
      }
      return sub;
    };

    // --- Johnson’s algorithm for elementary cycles on a directed graph (restricted to subgraph) ---
    const elementaryCycles = (subNodesSet) => {
      const nodesArr = Array.from(subNodesSet);
      // Sort for stable iteration order
      nodesArr.sort((a, b) => String(a).localeCompare(String(b)));

      const subAdj0 = inducedAdj(subNodesSet);

      const unblock = (u, blocked, B) => {
        if (!blocked.has(u)) return;
        blocked.delete(u);
        const Bu = B.get(u) || new Set();
        B.set(u, new Set());
        for (const w of Bu) unblock(w, blocked, B);
      };

      const cycles = [];
      const stack = [];

      // We follow the original scheme: for each start index s, work on the
      // subgraph induced by nodes >= s (by position in nodesArr).
      for (let sIdx = 0; sIdx < nodesArr.length; sIdx++) {
        const start = nodesArr[sIdx];
        const allowed = new Set(nodesArr.slice(sIdx));
        const subAdj = inducedAdj(allowed);

        const blocked = new Set();
        const B = new Map();
        for (const v of allowed) B.set(v, new Set());
        stack.length = 0;

        const circuit = (v, startV) => {
          let foundCycle = false;
          stack.push(v);
          blocked.add(v);

          for (const w of subAdj.get(v) || []) {
            if (w === startV) {
              // Found an elementary cycle (copy stack)
              cycles.push([...stack]);
              foundCycle = true;
            } else if (!blocked.has(w)) {
              if (circuit(w, startV)) foundCycle = true;
            }
          }

          if (foundCycle) {
            unblock(v, blocked, B);
          } else {
            for (const w of subAdj.get(v) || []) {
              const Bw = B.get(w);
              if (Bw) Bw.add(v);
            }
          }

          stack.pop();
          return foundCycle;
        };

        circuit(start, start);
      }

      // Deduplicate cycles up to rotation (normalize by lexicographically minimal rotation)
      const normKey = (cyc) => {
        const m = cyc.length;
        let best = null;
        for (let i = 0; i < m; i++) {
          const rot = [...cyc.slice(i), ...cyc.slice(0, i)];
          const key = rot.join("->");
          if (best === null || key < best) best = key;
        }
        return best;
      };
      const seen = new Set();
      const uniq = [];
      for (const c of cycles) {
        if (c.length === 1) {
          // keep single-node cycle only if explicit self-loop exists
          if (!selfLoop.has(c[0])) continue;
        }
        const k = normKey(c);
        if (!seen.has(k)) {
          seen.add(k);
          uniq.push(c);
        }
      }
      return uniq;
    };

    // --- Find SCCs and enumerate cycles per SCC ---
    const sccs = this.findStronglyConnectedComponents();
    const allCycles = [];
    for (const comp of sccs) {
      if (comp.length > 1) {
        for (const cyc of elementaryCycles(new Set(comp))) {
          allCycles.push(cyc);
        }
      } else if (comp.length === 1 && selfLoop.has(comp[0])) {
        // Single-node SCC with a self-loop is a valid cycle
        allCycles.push([comp[0]]);
      }
    }

    if (allCycles.length === 0) return [];

    // --- Select a maximal disjoint subset (greedy, longest-first) ---
    allCycles.sort(
      (a, b) => b.length - a.length || a.join().localeCompare(b.join())
    );
    const used = new Set();
    const selected = [];

    const disjointWithUsed = (cycle) => cycle.every((n) => !used.has(n));

    for (const cyc of allCycles) {
      if (!disjointWithUsed(cyc)) continue;
      selected.push(cyc);
      for (const n of cyc) used.add(n);
    }

    // --- Build cycle descriptors with transitions and exitTransitions ---
    const result = [];
    for (const cyc of selected) {
      const nodeSet = new Set(cyc);
      const transitions = new Set();
      const exitTransitions = new Set();

      // Collect transitions on edges inside the cycle, and exits leaving it
      for (const nid of cyc) {
        const node = this.nodes.get(nid);
        if (!node) continue;
        for (const eid of node.outgoingEdges || []) {
          const e = this.edges.get(eid);
          if (!e) continue;
          if (nodeSet.has(e.target)) {
            transitions.add(String(e.transition));
          } else {
            exitTransitions.add(String(e.transition));
          }
        }
      }

      result.push({
        nodes: [...nodeSet],
        transitions,
        exitTransitions,
      });
    }

    return result;
  }

  /**
   * Performs a forward BFS/DFS to find all nodes reachable from a start node.
   * @param {string} startNodeId The ID of the node to start the search from.
   * @param {Map<string, {prev: string|null, via: string|null}>} [parentMap] Optional map to store parent pointers for trace reconstruction.
   * @returns {string[]} An array of reachable node IDs.
   */
  getReachableNodes(startNodeId, parentMap = null) {
    const visited = new Set();
    const queue = [startNodeId];

    if (!this.nodes.has(startNodeId)) return [];

    visited.add(startNodeId);
    if (parentMap) {
        parentMap.set(startNodeId, { prev: null, via: null });
    }

    let head = 0;
    while (head < queue.length) {
      const nodeId = queue[head++];
      const node = this.nodes.get(nodeId);

      for (const edgeId of node.outgoingEdges) {
        const edge = this.edges.get(edgeId);
        if (edge && !visited.has(edge.target)) {
          visited.add(edge.target);
          if (parentMap) {
              parentMap.set(edge.target, { prev: nodeId, via: edgeId });
          }
          queue.push(edge.target);
        }
      }
    }

    return Array.from(visited);
  }

  /**
   * Performs a backward BFS/DFS to find all nodes that can reach a set of target nodes.
   * @param {string[]} targetNodeIds An array of IDs for the target nodes.
   * @returns {string[]} An array of node IDs that have a path to at least one target node.
   */
  getNodesThatCanReach(targetNodeIds) {
    const canReach = new Set(targetNodeIds);
    const queue = [...targetNodeIds];

    let head = 0;
    while (head < queue.length) {
        const nodeId = queue[head++];
        if (!this.nodes.has(nodeId)) continue;

        const node = this.nodes.get(nodeId);
        for (const edgeId of node.incomingEdges) {
            const edge = this.edges.get(edgeId);
            if (edge && !canReach.has(edge.source)) {
                canReach.add(edge.source);
                queue.push(edge.source);
            }
        }
    }
    return Array.from(canReach);
  }
}

/**
 * DPN Refinement Engine implementing Algorithm 4 from the paper
 */
class DPNRefinementEngine {
  constructor(smtGenerator, z3Solver) {
    this.smtGenerator = smtGenerator;
    this.z3Solver = z3Solver;
  }

  async refineDPN(dpn, maxIterations = 10) {
    let currentDPN = this.cloneDPN(dpn);
    let refined = true;
    let iteration = 0;

    while (refined && iteration < maxIterations) {
      console.log(`Refinement iteration ${iteration + 1}`);

      // Step 1: Construct LTS for current DPN
      const lts = await this.constructLTS(currentDPN);

      // Step 2: Find maximal disjoint cycles
      const cycles = lts.findMaximalDisjointCycles();

      if (cycles.length === 0) {
        console.log("No cycles found, refinement complete");
        break;
      }

      // Step 3: Refine transitions
      const refinedDPN = await this.refineTransitions(currentDPN, cycles, lts);

      // Check if any refinement occurred
      refined = this.hasRefinementOccurred(currentDPN, refinedDPN);
      currentDPN = refinedDPN;
      iteration++;
    }

    console.log(`Refinement completed after ${iteration} iterations`);
    return currentDPN;
  }

  /**
   * Canonicalize/simplify a formula defensively.
   * Repairs malformed snippets and avoids tactics if the term looks risky.
   *
   * @param {string} formula
   * @returns {Promise<string>}
   */
  async canonicalizeFormula(formula) {
    const text = String(formula || "true").trim() || "true";
    if (text === "true" || text === "false") return text;

    const sanitizePrimes = (s) =>
      s.replace(/([A-Za-z_][A-Za-z0-9_]*)'/g, "$1_prime");

    const repairSmt = (s) => {
      let r = String(s || "").trim();
      if (!r) return "true";
      // strip empty apps
      r = r.replace(/\(\s*\)/g, "");
      // collapse "(atom)" → "atom" for non-operators
      const ATOM = "(?:[-+]?\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z0-9_]*)";
      const OPS = new Set([
        "and",
        "or",
        "not",
        "=",
        "distinct",
        "<",
        "<=",
        ">",
        ">=",
        "+",
        "-",
        "*",
        "/",
        "ite",
        "=>",
        "exists",
        "forall",
        "let",
        "assert",
        "true",
        "false",
      ]);
      r = r.replace(new RegExp(`\\(\\s*(${ATOM})\\s*\\)`, "g"), (_, tok) => {
        return OPS.has(tok) ? `(${tok})` : tok;
      });
      r = r.replace(/\(\s*(true|false)\s*\(\s*\)\s*\)/g, "$1");
      // bare pairs → equality
      r = r.replace(
        new RegExp(`\\(\\s*(${ATOM})\\s+(${ATOM})\\s*\\)`, "g"),
        (_, a, b) => (OPS.has(a) ? `(${a} ${b})` : `(= ${a} ${b})`)
      );
      r = r.replace(/\s+/g, " ").trim();
      return r || "true";
    };

    const looksSuspicious = (s) =>
      !s ||
      /\(\s*[A-Za-z_][A-Za-z0-9_]*\s*\)/.test(s) ||
      /\(\s*[-+]?\d+(?:\.\d+)?\s*\)/.test(s) ||
      /\(\s*\)/.test(s) ||
      /\(\s*true\s*\(\s*\)/.test(s);

    const buildScript = (body) => `(set-logic ALL)\n(assert ${body})`;

    let body = repairSmt(sanitizePrimes(text));
    if (looksSuspicious(body)) return body;

    try {
      const astVec = _z3.parse_smtlib2_string(
        _context,
        buildScript(body),
        [],
        [],
        [],
        []
      );
      const vecSize = _z3.ast_vector_size(_context, astVec);
      if (vecSize === 0) return "true";

      const goal = _z3.mk_goal(_context, true, false, false);
      for (let i = 0; i < vecSize; i++) {
        _z3.goal_assert(
          _context,
          goal,
          _z3.ast_vector_get(_context, astVec, i)
        );
      }
      if (_z3.goal_size(_context, goal) === 0) return "true";

      // Only lightweight tactics here
      const tryTactic = async (g, name) => {
        try {
          const t = _z3.mk_tactic(_context, name);
          const r = await _z3.tactic_apply(_context, t, g);
          const n = _z3.apply_result_get_num_subgoals(_context, r);
          return n === 0 ? g : _z3.apply_result_get_subgoal(_context, r, 0);
        } catch (e) {
          console.warn(`[Canon] Tactic '${name}' failed; skipping.`, e);
          return g;
        }
      };

      let g = goal;
      g = await tryTactic(g, "simplify");
      g = await tryTactic(g, "solve-eqs");
      g = await tryTactic(g, "propagate-values");

      // Pretty print back
      const sz = _z3.goal_size(_context, g);
      if (sz === 0) return "true";
      if (sz === 1) {
        return repairSmt(
          _z3.ast_to_string(_context, _z3.goal_formula(_context, g, 0))
        );
      }
      const parts = [];
      for (let i = 0; i < sz; i++) {
        parts.push(
          _z3.ast_to_string(_context, _z3.goal_formula(_context, g, i))
        );
      }
      return repairSmt(`(and ${parts.join(" ")})`);
    } catch (e) {
      console.warn(
        "[Canon] Parse/simplify failed; returning repaired input.",
        e
      );
      return body;
    }
  }

/**
 * Construct LTS (Algorithm 2), merging states up to logical equivalence of constraints.
 * Nodes are ⟨marking, φ⟩ where φ is canonicalized. Edges labeled by transition ids.
 *
 * @param {object} dpn - Normalized DPN.
 * @returns {Promise<LabeledTransitionSystem>} LabeledTransitionSystem instance.
 */
async constructLTS(dpn) {
  const lts = new LabeledTransitionSystem();
  const maxNodes = 5000;

  const initM = this.getInitialMarking(dpn);
  const initF = await this.canonicalizeFormula(this.getInitialFormula(dpn));
  const initId = lts.addNode(initM, initF);

  const queue = [initId];
  const processed = new Set();
  const byMarking = new Map();
  const markingKey = (M) =>
    Object.entries(M)
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([k, v]) => `${k}:${v}`)
      .join(",");

  byMarking.set(markingKey(initM), [initId]);

  while (queue.length && lts.nodes.size < maxNodes) {
    const nid = queue.shift();
    const node = lts.nodes.get(nid);
    const keyHere = this.getStateKey(node);
    if (processed.has(keyHere)) continue;
    processed.add(keyHere);

    for (const t of dpn.transitions || []) {
      const succ = await this.computeSuccessorState(
        node.marking,
        node.formula,
        t,
        dpn
      );
      if (!succ) continue;
      
      const isSat = await Z3Solver.isSatisfiable(succ.formula);
      if (!isSat) {
        console.log(`[LTS] Transition ${t.id} filtered: unsatisfiable constraint. Pre: ${t.precondition}, Post: ${t.postcondition}`);
        continue;
      }

      succ.formula = await this.canonicalizeFormula(succ.formula);

      const mkey = markingKey(succ.marking);
      let targetId = null;
      const candIds = byMarking.get(mkey) || [];
      for (const cid of candIds) {
        const cnode = lts.nodes.get(cid);
        if (await this.equivalentFormulas(cnode.formula, succ.formula)) {
          targetId = cid;
          break;
        }
      }
      if (!targetId) {
        targetId = lts.addNode(succ.marking, succ.formula);
        if (!byMarking.has(mkey)) byMarking.set(mkey, []);
        byMarking.get(mkey).push(targetId);
        queue.push(targetId);
      }
      lts.addEdge(nid, targetId, t.id);
    }
  }

  return lts;
}

  async computeSuccessorState(marking, formula, transition, dpn) {
    // Check if transition is enabled in current marking
    if (!this.isTransitionEnabled(marking, transition, dpn)) {
      return null;
    }

    // Compute new marking
    const newMarking = this.computeNewMarking(marking, transition, dpn);

    // Compute new formula using ⊕ operation (Algorithm 1 from paper)
    const newFormula = await this.computeNewFormula(formula, transition, dpn);

    return {
      marking: newMarking,
      formula: newFormula,
    };
  }

/**
 * Compute successor-state constraint φ ⊕ t (Algorithm 1, paper-aligned).
 * Steps:
 * 1) Partition variables into reads (suffix _r) and writes (suffix _w) for transition t:
 * - In φ (stateFormula) and pre(t): v  → v_r
 * - In post(t): v' → v_w, unprimed v on RHS → v_r
 * 2) Build body := pre_r ∧ post_rw ∧ φ_r
 * 3) Existentially quantify W := { v_w | v is written by t }:
 * ψ := ∃ W . body
 * 4) Quantifier elimination (QE) to stay within the image-closed fragment Φ
 * 5) Project back to base variable names by dropping _r/_w suffixes
 * 6) Canonicalize/simplify the result; if UNSAT at any step, return "false"
 *
 * @param {string} stateFormula - Current node's constraint φ over base variables.
 * @param {object} transition - Transition object { precondition, postcondition, ... }.
 * @param {object} dpn - Normalized DPN with dataVariables [{id,name,type},...].
 * @returns {Promise<string>} SMT-LIB formula string for successor state constraint.
 */
async computeNewFormula(stateFormula, transition, dpn) {
  const dataVars = Array.isArray(dpn.dataVariables) ? dpn.dataVariables : [];
  const varNames = dataVars.map((v) => String(v.name || v.id));
  const nameSet = new Set(varNames);

  const getSortOf = (name) => {
    const dv = dataVars.find((v) => (v.name || v.id) === name);
    const t = (dv && (dv.type || "").toLowerCase()) || "real";
    if (t === "int" || t === "integer") return "Int";
    if (t === "bool" || t === "boolean") return "Bool";
    return "Real";
  };

  const escapeReg = (s) => String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

  const mapVars = (s, mapper) => {
    let r = ` ${String(s || "")} `;
    for (const v of varNames) {
      const tokR = `__TOK_${v}_r__`;
      const tokW = `__TOK_${v}_w__`;
      r = r.replace(new RegExp(`\\b${escapeReg(v)}_r\\b`, "g"), tokR);
      r = r.replace(new RegExp(`\\b${escapeReg(v)}_w\\b`, "g"), tokW);
    }
    for (const v of varNames) {
      r = r.replace(new RegExp(`\\b${escapeReg(v)}\\b`, "g"), mapper(v));
    }
    for (const v of varNames) {
      const tokR = `__TOK_${v}_r__`;
      const tokW = `__TOK_${v}_w__`;
      r = r.replace(new RegExp(tokR, "g"), `${v}_r`);
      r = r.replace(new RegExp(tokW, "g"), `${v}_w`);
    }
    return r.trim();
  };

  const toPrefix = (expr) => {
    const e0 = String(expr || "").trim();
    if (!e0) return "true";
    if (
      /^[A-Za-z_][A-Za-z0-9_]*$/.test(e0) ||
      /^[-+]?\d+(?:\.\d+)?$/.test(e0) ||
      e0 === "true" ||
      e0 === "false"
    ) {
      return e0;
    }
    let e = e0
      .replace(/\bAND\b/gi, "and")
      .replace(/\bOR\b/gi, "or")
      .replace(/\bNOT\b/gi, "not")
      .replace(/\|\|/g, "or")
      .replace(/&&/g, "and");

    const splitTop = (s, op) => {
      const parts = [];
      let depth = 0,
        cur = [];
      const toks = s.split(/\s+/);
      for (const t of toks) {
        for (const ch of t) {
          if (ch === "(") depth++;
          else if (ch === ")") depth--;
        }
        if (depth === 0 && t === op) {
          parts.push(cur.join(" ").trim());
          cur = [];
        } else cur.push(t);
      }
      const last = cur.join(" ").trim();
      if (last) parts.push(last);
      return parts;
    };

    const rec = (s) => {
      const t = s.trim();
      if (!t) return "true";
      if (t.startsWith("(") && t.endsWith(")")) return rec(t.slice(1, -1));
      const a = splitTop(t, "and");
      if (a.length > 1) return `(and ${a.map(rec).join(" ")})`;
      const o = splitTop(t, "or");
      if (o.length > 1) return `(or ${o.map(rec).join(" ")})`;
      if (t.startsWith("not ")) return `(not ${rec(t.slice(4))})`;
      const m = t.match(/^(.+?)\s*(=|!=|<=|>=|<|>)\s*(.+)$/);
      if (m) {
        const op = m[2] === "!=" ? "distinct" : m[2];
        const L = rec(m[1]),
          R = rec(m[3]);
        return op === "distinct"
          ? `(distinct ${L} ${R})`
          : `(${op} ${L} ${R})`;
      }
      const ar = t
        .replace(/([^()\s]+)\s*\+\s*([^()\s]+)/g, "(+ $1 $2)")
        .replace(/([^()\s]+)\s*-\s*([^()\s]+)/g, "(- $1 $2)")
        .replace(/([^()\s]+)\s*\*\s*([^()\s]+)/g, "(* $1 $2)")
        .replace(/([^()\s]+)\s*\/\s*([^()\s]+)/g, "(/ $1 $2)");
      let out = ar.startsWith("(") ? ar : `(${ar})`;
      while (/^\(\s*\((.*)\)\s*\)$/.test(out)) {
        out = out.replace(/^\(\s*\((.*)\)\s*\)$/, "($1)");
      }
      return out;
    };

    let res = rec(e).replace(/\s+/g, " ").trim();
    if (
      /^[A-Za-z_][A-Za-z0-9_]*$/.test(res) ||
      /^[-+]?\d+(?:\.\d+)?$/.test(res) ||
      res === "true" ||
      res === "false"
    ) {
      return res;
    }
    return res.startsWith("(") ? res : `(${res})`;
  };

  const writtenOf = (post) => {
    const set = new Set();
    const s = String(post || "");
    for (const v of varNames) {
      if (
        new RegExp(`\\b${escapeReg(v)}\\s*'\\b`).test(s) ||
        new RegExp(`\\b${escapeReg(v)}_w\\b`).test(s)
      ) {
        set.add(v);
      }
    }
    return set;
  };

  const dropSuffixes = (s) => {
    let r = String(s || "true");
    for (const v of varNames) {
      r = r.replace(new RegExp(`\\b${escapeReg(v)}_(?:r|w)\\b`, "g"), v);
    }
    return r;
  };

  const isFalse = async (f) => !(await Z3Solver.isSatisfiable(f));

  const phi_r = toPrefix(mapVars(stateFormula || "true", (v) => `${v}_r`));

  const pre_r = toPrefix(
    mapVars(transition.precondition || "true", (v) => `${v}_r`)
  );

  let post_rw = String(transition.postcondition || "").trim();
  for (const v of varNames) {
    post_rw = post_rw.replace(
      new RegExp(`\\b${escapeReg(v)}\\s*'\\b`, "g"),
      `${v}_w`
    );
  }
  post_rw = toPrefix(mapVars(post_rw, (v) => `${v}_r`));

  const body_rw = `(and ${pre_r} ${post_rw} ${phi_r})`;

  const W = Array.from(writtenOf(transition.postcondition));
  let psi_rw = body_rw;
  if (W.length > 0) {
    const binders = W.map((v) => `(${v}_w ${getSortOf(v)})`).join(" ");
    psi_rw = `(exists (${binders}) ${body_rw})`;
  }

  let qe;
  try {
    qe = await this.eliminateQuantifiers(psi_rw);
  } catch (_e) {
    if (W.length === 0) {
      qe = body_rw;
    } else {
      qe = `(and ${pre_r} ${phi_r})`;
    }
  }

  let phi_next = dropSuffixes(qe);

  phi_next = await this.canonicalizeFormula(phi_next);

  if (await isFalse(phi_next)) {
    console.log(`[computeNewFormula] Result is UNSAT for transition ${transition.id}: pre=${transition.precondition}, post=${transition.postcondition}`);
    return "false";
  }
  
  try {
    const isSat = await Z3Solver.isSatisfiable(phi_next);
    if (!isSat) {
      console.log(`[computeNewFormula] Z3 confirms UNSAT for transition ${transition.id}`);
      return "false";
    }
  } catch (e) {
    console.warn('[computeNewFormula] Final SAT check failed:', e);
  }
  
  return phi_next;
}

  /**
   * Refine all transitions according to Algorithm 4 (Suvorov–Lomazova).
   * - For each transition t that belongs to at least one maximal disjoint cycle,
   * collect exit transitions of those cycles.
   * - Build a disjoint partition of exit predicates (evaluated AFTER t fires).
   * - For each case, compute a precondition over the current state:
   * ∃W(t).( pre_t(r) ∧ post_t(r,w) ∧ case_after_t(r,w) )
   * using quantifier elimination, then create a refined copy tr with that pre,
   * keeping post_t unchanged.
   * - Duplicate all arcs incident to t to each refined copy, then remove t.
   *
   * @param {Object} dpn
   * @param {Array<{nodes:string[], transitions:Set<string>, exitTransitions:Set<string>}>} cycles
   * @param {LabeledTransitionSystem} lts
   * @returns {Promise<Object>} refined DPN (N_R)
   */
  async refineTransitions(dpn, cycles, lts) {
    const refinedDPN = this.cloneDPN(dpn);
    const transitionsToRefine = new Map();

    // Identify which transitions need refinement
    for (const cycle of cycles) {
      for (const transId of cycle.transitions) {
        if (!transitionsToRefine.has(transId)) {
          transitionsToRefine.set(transId, new Set());
        }
        for (const exit of cycle.exitTransitions) {
          transitionsToRefine.get(transId).add(exit);
        }
      }
    }

    if (transitionsToRefine.size === 0) {
        return refinedDPN;
    }
    
    const originalTransitions = new Map(dpn.transitions.map(t => [t.id, t]));

    // Perform refinement for each identified transition
    for (const [transId, exitTransIds] of transitionsToRefine.entries()) {
      const transition = originalTransitions.get(transId);
      if (!transition) continue;

      const exitTransitions = Array.from(exitTransIds).map(id => originalTransitions.get(id)).filter(Boolean);

      const refinedCopies = await this.refineTransition(transition, exitTransitions, dpn);

      // Replace original transition with refined copies
      const index = refinedDPN.transitions.findIndex((t) => t.id === transId);
      if (index !== -1) {
        refinedDPN.transitions.splice(index, 1, ...refinedCopies);
      }
    }

    return refinedDPN;
  }
  
  /**
   * Refine a single transition t using exit predicates of cycles containing t.
   * Builds a disjoint case partition over the exit predicates evaluated AFTER t.
   * For each case C, computes:
   * pre_ref(C) := QE( ∃W(t). ( pre_t(r) ∧ post_t(r,w) ∧ C(r,w) ) ) projected to base variables,
   * and creates a refined copy with pre_ref(C) and the same post_t.
   *
   * @param {Object} t
   * @param {Array<Object>} exitTransitions
   * @param {Object} dpn
   * @returns {Promise<Array<Object>>}
   */
  async refineTransition(t, exitTransitions, dpn) {
    this.logStep(
      "Refinement",
      `Refining transition ${t.id} with ${exitTransitions.length} exit predicate(s)`
    );

    // Helpers pulled from computeNewFormula
    const getSortOf = (name) => {
      const dv = (dpn.dataVariables || []).find(
        (v) => (v.name || v.id) === name
      );
      const typ = (dv && (dv.type || "").toLowerCase()) || "real";
      if (typ === "int" || typ === "integer") return "Int";
      if (typ === "bool" || typ === "boolean") return "Bool";
      return "Real";
    };

    const toPrefixArithmetic = (s) => {
      let out = String(s || "");
      // boolean chains
      for (let g = 0; g < 8; g++) {
        const before = out;
        out = out
          .replace(/([^()\s][^()]*?)\s*\|\|\s*([^()\s][^()]*)/g, "(or $1 $2)")
          .replace(/([^()\s][^()]*?)\s*&&\s*([^()\s][^()]*)/g, "(and $1 $2)");
        if (out === before) break;
      }
      // unary not
      out = out.replace(
        /\(?\s*not\s+([A-Za-z_][\w]*\s*(?:=|<=|>=|<|>)\s*[^()\s]+)\s*\)?/g,
        "(not $1)"
      );
      // arithmetic ops
      const rules = [
        { re: /([^()\s]+)\s*\+\s*([^()\s]+)/g, tpl: "(+ $1 $2)" },
        { re: /([^()\s]+)\s*-\s*([^()\s]+)/g, tpl: "(- $1 $2)" },
        { re: /([^()\s]+)\s*\*\s*([^()\s]+)/g, tpl: "(* $1 $2)" },
        { re: /([^()\s]+)\s*\/\s*([^()\s]+)/g, tpl: "(/ $1 $2)" },
      ];
      for (let k = 0; k < 8; k++) {
        let changed = false;
        for (const r of rules) {
          const tmp = out.replace(r.re, r.tpl);
          if (tmp !== out) {
            out = tmp;
            changed = true;
          }
        }
        if (!changed) break;
      }
      // comparisons & equality
      out = out
        .replace(
          /([A-Za-z_][\w]*)\s*<=\s*([-+]?\d+(?:\.\d+)?|[A-Za-z_][\w]*)/g,
          "(<= $1 $2)"
        )
        .replace(
          /([A-Za-z_][\w]*)\s*>=\s*([-+]?\d+(?:\.\d+)?|[A-Za-z_][\w]*)/g,
          "(>= $1 $2)"
        )
        .replace(
          /([A-Za-z_][\w]*)\s*<\s*([-+]?\d+(?:\.\d+)?|[A-Za-z_][\w]*)/g,
          "(< $1 $2)"
        )
        .replace(
          /([A-Za-z_][\w]*)\s*>\s*([-+]?\d+(?:\.\d+)?|[A-Za-z_][\w]*)/g,
          "(> $1 $2)"
        )
        .replace(
          /([A-Za-z_][\w]*)\s*=\s*([-+]?\d+(?:\.\d+)?|[A-Za-z_][\w\(\)\/\*\+\-]+)/g,
          "(= $1 $2)"
        );
      return out.trim().startsWith("(") ? out.trim() : `(${out.trim()})`;
    };

    const normalizePre = (expr) => {
      if (!expr) return "true";
      let s = String(expr).trim();
      for (const v of dpn.dataVariables || []) {
        const name = v.name || v.id;
        s = s.replace(new RegExp(`\\b${name}\\b`, "g"), `${name}_r`);
      }
      return toPrefixArithmetic(s);
    };

    const normalizePost = (expr) => {
      if (!expr) return "true";
      let s = String(expr).trim();
      s = s.replace(/([A-Za-z_][\w]*)'/g, "$1_w");
      for (const v of dpn.dataVariables || []) {
        const name = v.name || v.id;
        s = s.replace(new RegExp(`\\b${name}\\b`, "g"), `${name}_r`);
      }
      return toPrefixArithmetic(s);
    };

    const written = new Set(this.getWrittenVariables(t, dpn) || []);

    const normalizeExitAfterT = (exitPre) => {
      if (!exitPre || String(exitPre).trim() === "") return "true";
      let s = String(exitPre).trim();
      // Map base names to _w if written by t, else to _r
      for (const v of dpn.dataVariables || []) {
        const name = v.name || v.id;
        const rep = written.has(name) ? `${name}_w` : `${name}_r`;
        s = s.replace(new RegExp(`\\b${name}\\b`, "g"), rep);
      }
      // Any accidental primes in exit go to _w
      s = s.replace(/([A-Za-z_][\w]*)'/g, "$1_w");
      return toPrefixArithmetic(s);
    };

    // Build a disjoint partition of exit predicates (2^n). Guard against blow-up.
    const MAX_CASES = 64;
    const predicates = exitTransitions.map((et) =>
      normalizeExitAfterT(et.precondition || "true")
    );
    let cases = ["true"];
    for (const p of predicates) {
      const next = [];
      for (const c of cases) {
        next.push(c === "true" ? p : `(and ${c} ${p})`);
        next.push(c === "true" ? `(not ${p})` : `(and ${c} (not ${p}))`);
      }
      cases = next;
      if (cases.length > MAX_CASES) break; // soft cap
    }

    // For each case, compute pre_ref(C) := QE(∃W. pre_r ∧ post_rw ∧ C_rw) → base vars
    const pre_r = normalizePre(t.precondition || "true");
    const post_rw = normalizePost(t.postcondition || "true");

    const quantifiedBinder = () => {
      if (written.size === 0) return "";
      const binds = Array.from(written)
        .map((v) => `(${v}_w ${getSortOf(v)})`)
        .join(" ");
      return `(exists (${binds}) `;
    };

    const projectToBase = (s) => {
      let r = String(s || "true");
      for (const v of dpn.dataVariables || []) {
        const name = v.name || v.id;
        r = r.replace(new RegExp(`\\b${name}_(?:r|w)\\b`, "g"), name);
      }
      return r;
    };

    // Build refined copies and filter UNSAT / redundant (Flatten)
    const candidates = [];

    for (let i = 0; i < cases.length; i++) {
      const c_rw = cases[i];
      const body = `(and ${pre_r} ${post_rw} ${c_rw})`;
      const existsOpen = quantifiedBinder();
      const formulaRW = existsOpen ? `${existsOpen}${body})` : body;

      // QE over writes
      let preBase;
      try {
        const qe = await this.eliminateQuantifiers(formulaRW);
        preBase = projectToBase(qe);
      } catch (_e) {
        // Fallback: keep a conservative precondition
        preBase = projectToBase(`(and ${pre_r} ${c_rw})`);
      }

      // Drop clearly malformed outcomes
      const simplified = preBase.trim() || "true";
      const isSat = await Z3Solver.isSatisfiable(simplified);
      if (!isSat) continue;

      candidates.push({
        idx: i,
        pre: simplified,
      });
    }

    // Flatten: remove redundant cases A implied by some B (if A ⇒ B, drop A)
    const keep = new Array(candidates.length).fill(true);
    for (let i = 0; i < candidates.length; i++) {
      if (!keep[i]) continue;
      for (let j = 0; j < candidates.length; j++) {
        if (i === j || !keep[j]) continue;
        const A = candidates[i].pre;
        const B = candidates[j].pre;
        const implies = !(await Z3Solver.isSatisfiable(
          `(and ${A} (not ${B}))`
        ));
        if (implies) {
          // A is subset of B → prefer the more general one (B); drop A
          keep[i] = false;
          break;
        }
      }
    }

    const refined = [];
    let counter = 0;
    for (let k = 0; k < candidates.length; k++) {
      if (!keep[k]) continue;
      const c = candidates[k];
      const rid = `${t.id}_refined_case_${counter++}`;
      refined.push(this.createRefinedTransition(t, c.pre, rid));
    }

    this.logStep(
      "Refinement",
      `Transition ${t.id}: ${refined.length} refined copy(ies)`
    );
    return refined.length ? refined : [t];
  }

  /**
   * Create a single refined transition with a given precondition.
   * Keeps the original postcondition, label/priority/delay/position are preserved.
   *
   * @param {Object} originalTransition
   * @param {string} refinedPrecondition
   * @param {string} newId
   * @returns {Object}
   */
  createRefinedTransition(originalTransition, refinedPrecondition, newId) {
    const baseLabel = originalTransition.label || originalTransition.id;
    return {
      ...originalTransition,
      id: newId,
      label: `${baseLabel}_ref`,
      precondition: refinedPrecondition || "true",
      postcondition: originalTransition.postcondition || "",
    };
  }

  // Helper methods
  cloneDPN(dpn) {
    return JSON.parse(JSON.stringify(dpn));
  }

  getInitialMarking(dpn) {
    const marking = {};
    for (const place of dpn.places || []) {
      marking[place.id] = place.tokens || 0;
    }
    return marking;
  }

  getInitialFormula(dpn) {
    const conditions = [];
    for (const variable of dpn.dataVariables || []) {
      const varName = variable.name || variable.id;
      const value =
        variable.currentValue !== undefined ? variable.currentValue : 0;
      conditions.push(`(= ${varName} ${value})`);
    }
    return conditions.length > 0 ? `(and ${conditions.join(" ")})` : "true";
  }

  /**
   * Logical equivalence check for formulas over the same variable set.
   *
   * @param {string} f1 - First formula.
   * @param {string} f2 - Second formula.
   * @returns {Promise<boolean>} Whether f1 ⇔ f2.
   */
  async equivalentFormulas(f1, f2) {
    const a = String(f1 || "true").trim() || "true";
    const b = String(f2 || "true").trim() || "true";
    if (a === b) return true;
    const sat1 = await Z3Solver.isSatisfiable(`(and ${a} (not ${b}))`);
    if (sat1) return false;
    const sat2 = await Z3Solver.isSatisfiable(`(and ${b} (not ${a}))`);
    return !sat2;
  }

  /**
   * Stable state key used only after canonicalization.
   *
   * @param {object} node - LTS node {marking, formula}.
   * @returns {string} Key string.
   */
  getStateKey(node) {
    const mk = Object.entries(node.marking)
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([k, v]) => `${k}:${v}`)
      .join(",");
    const ff = String(node.formula || "true")
      .replace(/\s+/g, " ")
      .trim();
    return `${mk}|${ff}`;
  }

  isTransitionEnabled(marking, transition, dpn) {
    // Check if all input places have enough tokens
    for (const arc of dpn.arcs || []) {
      if (
        arc.target === transition.id &&
        marking[arc.source] < (arc.weight || 1)
      ) {
        return false;
      }
    }
    return true;
  }

  computeNewMarking(marking, transition, dpn) {
    const newMarking = { ...marking };

    // Remove tokens from input places
    for (const arc of dpn.arcs || []) {
      if (arc.target === transition.id) {
        newMarking[arc.source] -= arc.weight || 1;
      }
    }

    // Add tokens to output places
    for (const arc of dpn.arcs || []) {
      if (arc.source === transition.id) {
        newMarking[arc.target] += arc.weight || 1;
      }
    }

    return newMarking;
  }

  getWrittenVariables(transition, dpn) {
    const written = [];
    const postcondition = transition.postcondition || "";

    for (const variable of dpn.dataVariables || []) {
      const varName = variable.name || variable.id;
      if (
        postcondition.includes(`${varName}'`) ||
        postcondition.includes(`${varName}_w`)
      ) {
        written.push(varName);
      }
    }

    return written;
  }

  findExistingNode(lts, state) {
    const targetKey = this.getStateKey(state);
    for (const [nodeId, node] of lts.nodes) {
      if (this.getStateKey(node) === targetKey) {
        return nodeId;
      }
    }
    return null;
  }

  hasRefinementOccurred(originalDPN, refinedDPN) {
    return (
      originalDPN.transitions.length !== refinedDPN.transitions.length ||
      !originalDPN.transitions.every((t1) =>
        refinedDPN.transitions.some(
          (t2) => t1.id === t2.id && t1.precondition === t2.precondition
        )
      )
    );
  }

  async isSatisfiable(formula) {
    try {
      return await Z3Solver.isSatisfiable(formula);
    } catch (e) {
      console.warn("Satisfiability check failed:", e);
      return false;
    }
  }

/**
 * Quantifier elimination with strong defensive parsing.
 * - Repairs common malformed SMT patterns (e.g., "(x)" → "x", "(10)" → "10", "(true ())" → "true").
 * - Skips tactics entirely if the input still looks suspicious (prevents WASM thread faults).
 * - Wraps *every* Z3 call in try/catch and short-circuits to a safe fallback.
 *
 * @param {string} formula
 * @returns {Promise<string>} Quantifier-free (best effort) or a sanitized fallback.
 */
async eliminateQuantifiers(formula) {
  const sanitizePrimes = (s) =>
    String(s || "")
      .trim()
      .replace(/([A-Za-z_][A-Za-z0-9_]*)'/g, "$1_prime");

  const stripEmptyConj = (s) =>
    String(s || "")
      .replace(/\(\s*and\s+true\s+([^)]+)\)/g, "$1")
      .replace(/\(\s*and\s+([^)]+)\s+true\s*\)/g, "$1")
      .replace(/\(\s*and\s*\)/g, "true")
      .replace(/\(\s*or\s+false\s+([^)]+)\)/g, "$1")
      .replace(/\(\s*or\s+([^)]+)\s+false\s*\)/g, "$1");
  
  const checkEarlyUnsat = async (f) => {
    try {
      const isSat = await Z3Solver.isSatisfiable(f);
      if (!isSat) {
        console.log('[QE] Early UNSAT detected, returning false');
        return false;
      }
    } catch (e) {
      console.warn('[QE] Early UNSAT check failed:', e);
    }
    return null;
  };

  const repairSmt = (s) => {
    let r = String(s || "").trim();
    if (!r) return "true";
    r = r.replace(/\(\s*\)/g, "");
    const ATOM = "(?:[-+]?\\d+(?:\\.\\d+)?|[A-Za-z_][A-Za-z0-9_]*)";
    const OPS = new Set([
      "and",
      "or",
      "not",
      "=",
      "distinct",
      "<",
      "<=",
      ">",
      ">=",
      "+",
      "-",
      "*",
      "/",
      "ite",
      "=>",
      "exists",
      "forall",
      "let",
      "assert",
      "true",
      "false",
    ]);

    r = r.replace(new RegExp(`\\(\\s*(${ATOM})\\s*\\)`, "g"), (_, tok) => {
      return OPS.has(tok) ? `(${tok})` : tok;
    });
    r = r.replace(/\(\s*(true|false)\s*\(\s*\)\s*\)/g, "$1");
    r = r.replace(
      new RegExp(`\\(\\s*(${ATOM})\\s+(${ATOM})\\s*\\)`, "g"),
      (_, a, b) => {
        if (OPS.has(a)) return `(${a} ${b})`;
        return `(= ${a} ${b})`;
      }
    );
    r = r.replace(/\s+/g, " ").trim();
    return r || "true";
  };

  const looksSuspicious = (s) => {
    if (!s) return true;
    if (/\(\s*[A-Za-z_][A-Za-z0-9_]*\s*\)/.test(s)) return true;
    if (/\(\s*[-+]?\d+(?:\.\d+)?\s*\)/.test(s)) return true;
    if (/\(\s*\)/.test(s)) return true;
    if (/\(\s*true\s*\(\s*\)/.test(s)) return true;
    if (/\(\s*[A-Za-z_][A-Za-z0-9_]*\s+[A-Za-z_0-9.+-]+\s*\)/.test(s))
      return true;
    return false;
  };

  const defQE = (input) => {
    let s = String(input || "").trim();
    const existsTop =
      /^\(\s*exists\s*\(\s*((?:\(\s*[A-Za-z_]\w*\s+[A-Za-z_]\w*\s*\)\s*)+)\)\s*(.+)\)$/s;
    const bindersRe = /\(\s*([A-Za-z_]\w*)\s+[A-Za-z_]\w*\s*\)/g;

    const replaceAll = (str, v, rhs) =>
      str.replace(new RegExp(`\\b${v}\\b`, "g"), rhs);

    const dropTrue = (body) =>
      body
        .replace(/\(\s*and\s+true\s+([^)]+)\)/g, "$1")
        .replace(/\(\s*and\s+([^)]+)\s+true\s*\)/g, "$1")
        .trim() || "true";

    let changed = true;
    while (changed) {
      changed = false;
      const m = s.match(existsTop);
      if (!m) break;

      let bindersBlob = m[1];
      let body = m[2].trim();

      const binders = [];
      let bm;
      while ((bm = bindersRe.exec(bindersBlob)) !== null) binders.push(bm[1]);

      let removedAny = false;
      for (const v of binders) {
        const pat1 = new RegExp(`\\(=\\s+${v}\\s+([^()]+|\\([^)]*\\))\\)`);
        const pat2 = new RegExp(`\\(=\\s+([^()]+|\\([^)]*\\))\\s+${v}\\)`);
        let mm = body.match(pat1);
        let rhs = null;

        if (mm) rhs = mm[1].trim();
        else if ((mm = body.match(pat2))) rhs = mm[1].trim();

        if (rhs && !new RegExp(`\\b${v}\\b`).test(rhs)) {
          const eqRe = mm[0].replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
          body = body.replace(new RegExp(`\\s*${eqRe}\\s*`), " true ");
          body = replaceAll(body, v, rhs);
          removedAny = true;

          bindersBlob = bindersBlob
            .replace(new RegExp(`\\(\\s*${v}\\s+[A-Za-z_]\\w*\\s*\\)`), "")
            .trim();
        }
      }

      if (!removedAny) break;

      body = dropTrue(body);
      if (!bindersBlob.replace(/\s+/g, "")) {
        s = body;
      } else {
        const cleaned = Array.from(
          bindersBlob.matchAll(/\(\s*[A-Za-z_]\w*\s+[A-Za-z_]\w*\s*\)/g)
        )
          .map((x) => x[0])
          .join(" ");
        s = `(exists (${cleaned}) ${body})`;
      }
      changed = true;
    }
    return s;
  };

  const prettyGoal = (g) => {
    try {
      const sz = _z3.goal_size(_context, g);
      if (sz === 0) return "true";
      if (sz === 1) {
        return _z3.ast_to_string(_context, _z3.goal_formula(_context, g, 0));
      }
      const parts = [];
      for (let i = 0; i < sz; i++) {
        parts.push(
          _z3.ast_to_string(_context, _z3.goal_formula(_context, g, i))
        );
      }
      return `(and ${parts.join(" ")})`;
    } catch {
      return "true";
    }
  };

  const original = sanitizePrimes(formula);
  if (!original || original === "true" || original === "false") {
    return original || "true";
  }

  let pre = defQE(original);
  pre = repairSmt(pre);

  if (looksSuspicious(pre)) {
    console.warn("[QE] Suspicious SMT detected — skipping tactics:", pre);
    return pre;
  }
  
  const earlyUnsatResult = await checkEarlyUnsat(pre);
  if (earlyUnsatResult === false) {
    return "false";
  }

  const buildScript = (body) => `(set-logic ALL)\n(assert ${body})`;

  try {
    const astVec = _z3.parse_smtlib2_string(
      _context,
      buildScript(pre),
      [],
      [],
      [],
      []
    );
    const vecSize = _z3.ast_vector_size(_context, astVec);
    if (vecSize === 0) {
      console.warn("[QE] Empty AST after parse; returning repaired input.");
      return pre;
    }

    const goal = _z3.mk_goal(_context, true, false, false);
    for (let i = 0; i < vecSize; i++) {
      _z3.goal_assert(
        _context,
        goal,
        _z3.ast_vector_get(_context, astVec, i)
      );
    }

    if (_z3.goal_size(_context, goal) === 0) {
      return "true";
    }

    const tryTactic = async (g, name) => {
      try {
        const t = _z3.mk_tactic(_context, name);
        const r = await _z3.tactic_apply(_context, t, g);
        const n = _z3.apply_result_get_num_subgoals(_context, r);
        if (n === 0) return g;
        return _z3.apply_result_get_subgoal(_context, r, 0);
      } catch (e) {
        console.warn(
          `[QE] Tactic '${name}' failed; keeping previous goal.`,
          e
        );
        return g;
      }
    };

    let g = goal;
    g = await tryTactic(g, "simplify");
    g = await tryTactic(g, "reduce-quantifiers");
    g = await tryTactic(g, "solve-eqs");
    g = await tryTactic(g, "qe_lite");
    g = await tryTactic(g, "qe");
    g = await tryTactic(g, "qe_rec");

    let out = prettyGoal(g);
    out = repairSmt(out);
    out = stripEmptyConj(out);

    if (looksSuspicious(out)) {
      console.warn(
        "[QE] Result still looks suspicious; returning repaired pre."
      );
      return pre;
    }
    return out || "true";
  } catch (e) {
    console.error(
      "[QE] Z3 parse/apply failed; returning repaired fallback.",
      e
    );
    return pre;
  }
}

  async parseFormulaToAST(formula) {
    try {
      // Clean up the formula for parsing
      const cleanFormula = this.prepareFormulaForParsing(formula);

      const sortNames = [];
      const sorts = [];
      const declNames = [];
      const decls = [];

      // Parse the formula
      const ast = _z3.parse_smtlib2_string(
        _context,
        cleanFormula,
        sortNames,
        sorts,
        declNames,
        decls
      );

      return ast;
    } catch (error) {
      console.warn("Failed to parse formula to AST:", error);
      return null;
    }
  }

  prepareFormulaForParsing(formula) {
    // Prepare the formula for Z3's SMT-LIB parser
    // The parser expects a complete SMT-LIB script, so we need to wrap our formula

    // Extract variable declarations from the existential quantifier
    const existsMatch = formula.match(/\(exists\s+\(([^)]+)\)/);
    let declarations = "";

    if (existsMatch) {
      const varDecls = existsMatch[1];
      // Parse variable declarations like "(x Real) (y Int)"
      const declMatches = varDecls.match(/\([^)]+\)/g);
      if (declMatches) {
        for (const decl of declMatches) {
          const parts = decl.slice(1, -1).split(/\s+/);
          if (parts.length >= 2) {
            const varName = parts[0];
            const sortName = parts[1];
            declarations += `(declare-const ${varName} ${sortName})\n`;
          }
        }
      }
    }

    // Wrap in a complete SMT-LIB script
    const script = `
      (set-logic ALL)
      ${declarations}
      (assert ${formula})
      (check-sat)
    `;
    return script;
  }

  fallbackQuantifierElimination(formula) {
    // Fallback syntactic quantifier elimination for when Z3 API fails
    console.log("Using fallback quantifier elimination");

    // Handle simple existential quantifier patterns
    let result = formula;

    // Pattern: (exists ((x Real) (y Int)) (and (> x 0) (< y x)))
    // Remove the existential wrapper and keep the body
    const existsPattern = /\(exists\s+\([^)]+\)\s*(.+)\)$/;
    const match = result.match(existsPattern);

    if (match) {
      result = match[1];

      // Remove any remaining parentheses that might be unbalanced
      result = this.balanceParentheses(result);
    }

    // Handle universal quantifiers similarly
    const forallPattern = /\(forall\s+\([^)]+\)\s*(.+)\)$/;
    const forallMatch = result.match(forallPattern);

    if (forallMatch) {
      result = forallMatch[1];
      result = this.balanceParentheses(result);
    }

    return result || "true";
  }

  balanceParentheses(formula) {
    // Simple parentheses balancing
    let openCount = 0;
    let result = formula;

    for (let char of result) {
      if (char === "(") openCount++;
      if (char === ")") openCount--;
    }

    // Add missing closing parentheses
    while (openCount > 0) {
      result += ")";
      openCount--;
    }

    // Remove excess closing parentheses
    while (openCount < 0 && result.endsWith(")")) {
      result = result.slice(0, -1);
      openCount++;
    }

    return result;
  }
}


/**
 * Suvorov–Lomazova Data Petri Net Soundness Verifier
 * - Implements Algorithm 5 and 6 from the paper
 * - Uses DPN refinement, LTS construction, and comprehensive soundness analysis
 */
class SuvorovLomazovaVerifier {
  constructor(petriNet, options = {}) {
    this.originalPetriNet = petriNet;
    console.log(
      "Suvorov–Lomazova Verifier initialized with Petri Net:",
      petriNet
    );

    this.options = {
      maxBound: options.maxBound || 10,
      enableTauTransitions: options.enableTauTransitions !== false,
      enableCoverage: options.enableCoverage !== false,
      useImprovedAlgorithm: options.useImprovedAlgorithm !== false,
      ...options,
    };
    this.smtGenerator = new SmtFromDpnGenerator();
    this.refinementEngine = new DPNRefinementEngine(
      this.smtGenerator,
      Z3Solver
    );
    this.verificationSteps = [];
    this.startTime = 0;
    this.counterexampleTraces = [];
    
    const getFinalMarkingsFromPetriNet = (net) => {
      // Extract final markings from the Petri net
      let markings = [];
      let tempMarking = {};
      Array.from(net.places || []).forEach(([id, place]) => {
        tempMarking[id] = place.finalMarking || 0;
      });
      markings.push(tempMarking);

      return markings;
    };

    this.finalMarkings = getFinalMarkingsFromPetriNet(petriNet);

    if (this.finalMarkings.length === 0) {
      throw new Error(
        "No valid final markings specified. Soundness cannot be verified."
      );
    }

    this.logStep(
      "Get Final Markings",
      `Final markings: ${JSON.stringify(this.finalMarkings)}`
    );
  }

/**
 * No dead transitions (P3) aligned with the paper:
 * For each original transition t, at least one refined copy tr ∈ R(t) must fire
 * on some reachable path in the given LTS. τ-transitions do not count toward P3.
 *
 * @param {Object} dpn - The (possibly refined) DPN used to build lts.
 * @param {LabeledTransitionSystem} lts - LTS constructed from dpn (preferably N_R or N_R^τ).
 * @returns {{ satisfied: boolean, details: string, deadTransitions: Array<{ transitionId: string, variants: string[] }>, coveredTransitions: string[] }}
 */
checkDeadTransitions(dpn, lts) {
  this.logStep("DeadTransitions", "Checking P3: no dead transitions");

  const isTau = (id) => String(id).startsWith("tau_");

  const baseOf = (id) => {
    const s = String(id);
    if (isTau(s)) return null;
    const i1 = s.indexOf("_refined_");
    if (i1 >= 0) return s.slice(0, i1);
    const i2 = s.indexOf("_ref_");
    if (i2 >= 0) return s.slice(0, i2);
    return s;
  };

  const variants = new Map();
  const transitionInfo = new Map();
  for (const t of dpn.transitions || []) {
    if (!t || !t.id) continue;
    const bid = baseOf(t.id);
    if (!bid) continue;
    if (!variants.has(bid)) variants.set(bid, new Set());
    variants.get(bid).add(String(t.id));
    
    transitionInfo.set(t.id, {
      precondition: t.precondition || '',
      postcondition: t.postcondition || '',
      label: t.label || t.id
    });
  }

  const originalIds = Array.from(variants.keys());

  if (originalIds.length === 0) {
    this.logStep(
      "DeadTransitions",
      "No (non-τ) transitions present; vacuously satisfied"
    );
    return {
      name: "Dead Transitions (P3)",
      satisfied: true,
      details: "No non-τ transitions to check.",
      deadTransitions: [],
      coveredTransitions: [],
    };
  }

  const covered = new Set();
  const firedVariants = new Map();
  for (const [, e] of lts.edges || []) {
    if (!e || !e.transition) continue;
    const bid = baseOf(e.transition);
    if (bid) {
      covered.add(bid);
      if (!firedVariants.has(bid)) firedVariants.set(bid, new Set());
      firedVariants.get(bid).add(e.transition);
    }
  }

  const deadTransitions = [];
  for (const bid of originalIds) {
    if (!covered.has(bid)) {
      const variantList = Array.from(variants.get(bid) || []);
      const firstVariant = variantList[0];
      const info = transitionInfo.get(firstVariant);
      
      console.log(`[DeadTransitions] Transition ${bid} is DEAD - no variants fired in LTS`);
      console.log(`  Variants: ${variantList.join(', ')}`);
      console.log(`  Precondition: ${info?.precondition || 'none'}`);
      console.log(`  Postcondition: ${info?.postcondition || 'none'}`);
      
      deadTransitions.push({
        transitionId: bid,
        transitionLabel: info?.label || bid,
        variants: variantList,
        precondition: info?.precondition,
        postcondition: info?.postcondition
      });
    }
  }

  const ok = deadTransitions.length === 0;
  this.logStep(
    "DeadTransitions",
    ok
      ? "P3 satisfied: every original transition has a firing refined copy"
      : `${deadTransitions.length} original transition(s) have no firing refined copy (dead due to data constraints)`
  );

  return {
    name: "Dead Transitions (P3)",
    satisfied: ok,
    details: ok
      ? "Each original transition fires via at least one refined copy on some reachable path."
      : `Some original transitions never fire on any reachable path. These transitions are structurally present but their preconditions conflict with data constraints established by earlier transitions.`,
    deadTransitions,
    coveredTransitions: Array.from(covered),
  };
}

  /**
   * Overfinal markings (P2) aligned with the paper:
   * Detects reachable states ⟨M, φ⟩ whose marking M strictly covers a final marking M_F
   * (component-wise ≥ and > in at least one place). Outgoing edges are irrelevant.
   *
   * @param {LabeledTransitionSystem} lts
   * @returns {{satisfied: boolean, overfinalNodes: Array, details: string, trace?: any}}
   */
  checkOverfinalMarkings(lts) {
    this.logStep(
      "OverfinalMarkings",
      "Checking P2: no marking strictly covers M_F"
    );

    const finals = Array.isArray(this.finalMarkings) ? this.finalMarkings : [];
    if (finals.length === 0) {
      this.logStep(
        "OverfinalMarkings",
        "No final marking provided; cannot evaluate P2"
      );
      return {
        name: "Overfinal Marking (P2)",
        satisfied: false,
        overfinalNodes: [],
        details:
          "Final marking (M_F) is not specified; P2 cannot be evaluated.",
      };
    }

    const covers = (ma, mb) => {
      const keys = new Set([
        ...Object.keys(ma || {}),
        ...Object.keys(mb || {}),
      ]);
      for (const p of keys) {
        const a = (ma && Number(ma[p])) || 0;
        const b = (mb && Number(mb[p])) || 0;
        if (a < b) return false;
      }
      return true;
    };

    const strictlyCovers = (ma, mb) => {
      if (!covers(ma, mb)) return false;
      const keys = new Set([
        ...Object.keys(ma || {}),
        ...Object.keys(mb || {}),
      ]);
      for (const p of keys) {
        const a = (ma && Number(ma[p])) || 0;
        const b = (mb && Number(mb[p])) || 0;
        if (a > b) return true;
      }
      return false;
    };

    const overfinalNodes = [];
    for (const [nodeId, node] of lts.nodes || []) {
      for (const mf of finals) {
        if (strictlyCovers(node.marking, mf)) {
          overfinalNodes.push({
            nodeId,
            marking: node.marking,
            formula: node.formula,
            covers: mf,
          });
          break;
        }
      }
    }

    const ok = overfinalNodes.length === 0;
    this.logStep(
      "OverfinalMarkings",
      ok
        ? "No overfinal markings detected"
        : `${overfinalNodes.length} overfinal node(s) detected`
    );

    return {
      name: "Overfinal Marking (P2)",
      satisfied: ok,
      overfinalNodes,
      details: ok
        ? "No marking strictly covers the final marking (M_F)."
        : "There exist reachable states whose marking strictly covers M_F.",
      trace: overfinalNodes[0] || null,
    };
  }

  negatePrecondition(precondition) {
    // Negate the precondition using De Morgan's laws
    if (!precondition || precondition.trim() === "true") {
      return "false"; // Negation of true is false
    }
    if (precondition.trim() === "false") {
      return "true"; // Negation of false is true
    }
    // For more complex preconditions, we can use a simple negation
    return `(not ${precondition})`; // Negate the precondition
  }

  /**
   * Add τ-transitions according to Definition 4.4:
   * For each original transition t, create τ(t) with precondition ¬∃W.(pre(t) ∧ post(t)),
   * where W are the variables written by t. Postcondition of τ(t) is empty (no data change).
   *
   * @param {Object} dpn - Data Petri net in normalized format { places, transitions, arcs, dataVariables }.
   * @returns {Promise<Object>} A new DPN with τ-transitions added.
   */
  async addTauTransitions(dpn) {
    this.logStep("TauTransitions", "Adding τ-transitions (¬∃W.(pre ∧ post))");

    const tauDpn = JSON.parse(JSON.stringify(dpn));
    const originalTransitions = Array.isArray(tauDpn.transitions)
      ? [...tauDpn.transitions]
      : [];
    const makeTauId = (id) => `tau_${String(id)}`; // unique-enough for this scope

    let added = 0;

    // Helper: get SMT sort for a variable name
    const getSort = (name) => {
      const dv = (tauDpn.dataVariables || []).find(
        (v) => String(v.name || v.id) === String(name)
      );
      const typ = (dv && String(dv.type || "").toLowerCase()) || "real";
      if (typ === "int" || typ === "integer") return "Int";
      if (typ === "bool" || typ === "boolean") return "Bool";
      return "Real";
    };

    const esc = (s) => String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");

    for (const t of originalTransitions) {
      if (!t || typeof t.id === "undefined") continue;
      if (String(t.id).startsWith("tau_")) continue; // Skip existing τ transitions

      // Determine written variables W from postcondition (v' or v_w)
      const written = new Set(
        this.refinementEngine.getWrittenVariables(t, tauDpn) || []
      );

      // Build post body where each v' is replaced by a fresh bound symbol v_w
      let postBody = String(t.postcondition || "").trim();
      for (const v of (tauDpn.dataVariables || []).map(
        (dv) => dv.name || dv.id
      )) {
        postBody = postBody.replace(
          new RegExp(`\\b${esc(v)}\\s*'`, "g"),
          `${v}_w`
        );
      }

      // τ-pre := ¬∃W.( pre ∧ post[v'↦v_w] ) ; if W=∅ then τ-pre := ¬(pre ∧ post)
      let tauPre;
      if (written.size === 0) {
        tauPre = `(not (and ${t.precondition || "true"} ${
          postBody || "true"
        }))`;
      } else {
        const binders = Array.from(written)
          .map((v) => `(${v}_w ${getSort(v)})`)
          .join(" ");
        tauPre = `(not (exists (${binders}) (and ${t.precondition || "true"} ${
          postBody || "true"
        })))`;
      }

      const tauTransition = {
        id: makeTauId(t.id),
        label: `τ(${t.label || t.id})`,
        precondition: tauPre,
        postcondition: "", // data stutter
        priority: typeof t.priority === "number" ? t.priority : 1,
        delay: 0,
        position: t.position,
      };

      // Insert τ(t)
      tauDpn.transitions.push(tauTransition);
      added += 1;

      // DO NOT duplicate arcs for τ: τ is a pure stutter step (no token move).
    }

    this.logStep("TauTransitions", "τ-transitions added", {
      originalTransitions: originalTransitions.length,
      tauAdded: added,
      totalTransitions: tauDpn.transitions.length,
    });

    return tauDpn;
  }

  isFinalMarking(marking) {
    // Check if the marking matches any final marking
    return this.finalMarkings.some((finalMarking) => {
      const allPlaces = new Set([...Object.keys(marking), ...Object.keys(finalMarking)]);
      for (const placeId of allPlaces) {
        if ((marking[placeId] || 0) !== (finalMarking[placeId] || 0)) {
          return false;
        }
      }
      return true;
    });
  }
  
  /**
   * Deadlock freedom (P1) aligned with the paper:
   * For every reachable state ⟨M, φ⟩ in 𝓛𝓣𝓢_{N_R^τ}, some final state is reachable.
   * Implementation:
   * 1) Identify the initial node (by initial marking and initial formula).
   * 2) Forward BFS to collect all reachable nodes (FR) and parent pointers for a witness path.
   * 3) Collect the set of final nodes within FR.
   * 4) Backward BFS from all final nodes (over incoming edges) to get nodes that can reach a final (BR).
   * 5) P1 holds iff FR ⊆ BR (i.e., no node in FR fails to reach a final). If violated, return a witness path.
   *
   * @param {LabeledTransitionSystem} lts
   * @param {Object} dpn
   * @returns {Promise<{satisfied: boolean, details: string, violatingNodes?: string[], trace?: Array}>}
   */
  async checkDeadlockFreedom(lts, dpn) {
    this.logStep(
      "DeadlockFreedom",
      "Checking P1: every reachable state can reach a final"
    );

    if (!lts || !lts.nodes || lts.nodes.size === 0) {
      this.logStep("DeadlockFreedom", "Empty LTS; cannot establish P1");
      return {
        name: "Deadlock Freedom (P1)",
        satisfied: false,
        details: "No states in LTS; P1 cannot be established.",
      };
    }

    // --- 1) Identify initial node(s) ---
    const initialIds = [];
    for (const [nid, node] of lts.nodes) {
        if (!node.incomingEdges || node.incomingEdges.length === 0) {
            initialIds.push(nid);
        }
    }
    if (initialIds.length === 0) {
        const firstNode = lts.nodes.keys().next().value;
        if (firstNode) {
            initialIds.push(firstNode);
        } else {
            return {
                name: "Deadlock Freedom (P1)",
                satisfied: false,
                details: "LTS is completely empty; cannot find an initial node.",
            };
        }
    }
    const initialNodeId = initialIds[0];

    // --- 2) Forward Reachability (FR) with parents for witness path ---
    const parent = new Map();
    const reachableNodes = lts.getReachableNodes(initialNodeId, parent);
    const fr = new Set(reachableNodes);

    // --- 3) Final nodes in FR ---
    const finalNodeIds = [];
    for (const nid of fr) {
      const n = lts.nodes.get(nid);
      if (n && this.isFinalMarking(n.marking)) {
        finalNodeIds.push(nid);
      }
    }

    if (finalNodeIds.length === 0) {
      this.logStep(
        "DeadlockFreedom",
        "No final nodes reachable from initial; P1 violated"
      );
      let witnessPath = [];
      for (const nid of fr) {
        const n = lts.nodes.get(nid);
        if (n && (!n.outgoingEdges || n.outgoingEdges.length === 0)) {
          const path = [];
          let current = nid;
          while (current && parent.has(current)) {
              const p = parent.get(current);
              if (!p || p.via === null) break;
              const edge = lts.edges.get(p.via);
              path.push({ transitionId: edge ? edge.transition : "?" });
              current = p.prev;
          }
          witnessPath = path.reverse();
          break;
        }
      }
      return {
        name: "Deadlock Freedom (P1)",
        satisfied: false,
        details: "No final state is reachable from the initial state.",
        trace: witnessPath,
      };
    }

    // --- 4) Backward reachability from finals (BR) ---
    const nodesThatCanReachFinal = lts.getNodesThatCanReach(finalNodeIds);
    const br = new Set(nodesThatCanReachFinal);

    // --- 5) Check FR ⊆ BR ---
    const violatingNodes = [];
    for (const nid of fr) {
      if (!br.has(nid)) {
        violatingNodes.push(nid);
      }
    }

    if (violatingNodes.length === 0) {
      this.logStep(
        "DeadlockFreedom",
        "P1 satisfied: every reachable node can reach a final"
      );
      return {
        name: "Deadlock Freedom (P1)",
        satisfied: true,
        details: "Every reachable state has a path to a final state.",
      };
    }

    // --- Build a witness path to the first violating node ---
    const violatingNodeId = violatingNodes[0];
    const path = [];
    let current = violatingNodeId;
    while (current && parent.has(current)) {
        const p = parent.get(current);
        if (!p || p.via === null) break;
        const edge = lts.edges.get(p.via);
        path.push({ transitionId: edge ? edge.transition : "?" });
        current = p.prev;
    }
    const trace = path.reverse();
    const violatingNode = lts.nodes.get(violatingNodeId);

    this.logStep(
      "DeadlockFreedom",
      `P1 violated: ${violatingNodes.length} reachable nodes cannot reach a final`,
      { sampleViolatingNode: violatingNodeId }
    );

    return {
      name: "Deadlock Freedom (P1)",
      satisfied: false,
      details: "There exists a reachable state from which no final state is reachable.",
      violatingNodes: violatingNodes,
      trace: trace,
      offendingState: violatingNode
        ? { nodeId: violatingNodeId, marking: violatingNode.marking, formula: violatingNode.formula }
        : undefined,
    };
  }

  async verify(progressCallback) {
    this.startTime = Date.now();
    this.verificationSteps = [];
    this.counterexampleTraces = [];

    const dbg = (...args) =>
      console.log(`[verify +${Date.now() - this.startTime}ms]`, ...args);

    try {
      this.logStep(
        "Initialization",
        "Starting comprehensive soundness verification"
      );

      // Initialize Z3 solver
      await Z3Solver.initialize();
      this.logStep("Z3", "Solver initialized");

      // Convert petri net to proper format
      const dpn = this.convertPetriNetFormat(this.originalPetriNet);

      // Set data variables for Z3Solver compatibility
      const dataVariables = new Map();
      if (dpn.dataVariables) {
        for (const dv of dpn.dataVariables) {
          dataVariables.set(dv.name, {
            name: dv.name,
            type: dv.type,
            currentValue: dv.currentValue,
          });
        }
      }
      Z3Solver.setGlobalDataVariables(dataVariables);

      this.logStep(
        "Initialization",
        "DPN converted and final markings identified",
        {
          places: dpn.places?.length || 0,
          transitions: dpn.transitions?.length || 0,
          arcs: dpn.arcs?.length || 0,
          dataVars: dpn.dataVariables?.length || 0,
          finalMarkings: this.finalMarkings.length,
        }
      );

      // Choose algorithm: improved (Algorithm 6) or direct (Algorithm 5)
      if (this.options.useImprovedAlgorithm) {
        return await this.verifyImproved(dpn, progressCallback);
      } else {
        return await this.verifyDirect(dpn, progressCallback);
      }
    } catch (e) {
      console.error(e);
      return this.createResult(false, [
        {
          name: "Internal error",
          satisfied: false,
          details: String(e?.message || e),
        },
      ]);
    }
  }

  /**
   * Implements Algorithm 6 (Improved): boundedness → preliminary checks on LTS_N → refine → add τ → LTS_{N_R^τ} → P1,P2,P3.
   *
   * @param {Object} dpn
   * @param {(msg: string) => void} [progressCallback]
   * @returns {Promise<ReturnType<SuvorovLomazovaVerifier['createResult']>>}
   */
  async verifyImproved(dpn, progressCallback) {
    const say = (m) => {
      if (progressCallback) progressCallback(m);
    };

    // 1) Boundedness (Alg. 3) on N
    say("Checking boundedness (Algorithm 3)...");
    this.logStep("VerifyImproved", "Step 1: Boundedness (Alg. 3)");
    const bnd = await this.checkBoundedness(dpn);
    if (!bnd.bounded) {
      return this.createResult(false, [
        {
          name: "Boundedness (Alg. 3)",
          satisfied: false,
          details: "Net is unbounded (strict cover detected).",
          trace: bnd.trace || [],
        },
      ]);
    }

    // 2) Construct LTS_N and run preliminary checks (P2, P3)
    say("Constructing preliminary LTS for N...");
    this.logStep("VerifyImproved", "Step 2: Preliminary LTS_N construction");
    const ltsN = await this.refinementEngine.constructLTS(dpn);

    say("Running preliminary checks on LTS_N (P2, P3)...");
    const p2_pre = this.checkOverfinalMarkings(ltsN);
    if (!p2_pre.satisfied) {
      return this.createResult(false, [
        { ...p2_pre, name: p2_pre.name + " - Preliminary Check" },
      ]);
    }

    const p3_pre = this.checkDeadTransitions(dpn, ltsN);
    if (!p3_pre.satisfied) {
      return this.createResult(false, [
        { ...p3_pre, name: p3_pre.name + " - Preliminary Check" },
      ]);
    }

    // 3) Refinement → N_R
    say("Refining DPN (Algorithm 4)...");
    this.logStep("VerifyImproved", "Step 3: Refinement → N_R");
    const dpnR = await this.refinementEngine.refineDPN(dpn);

    // 4) Add τ → N_R^τ
    say("Adding τ-transitions (Definition 4.4)...");
    this.logStep("VerifyImproved", "Step 4: Add τ → N_R^τ");
    const dpnRtau = await this.addTauTransitions(dpnR);

    // 5) Build LTS_{N_R^τ} and check P1, P2, P3
    say("Constructing final LTS and analyzing for soundness...");
    this.logStep("VerifyImproved", "Step 5: Final LTS construction and analysis");
    const ltsRtau = await this.refinementEngine.constructLTS(dpnRtau);

    const checks = [];
    const p1 = await this.checkDeadlockFreedom(ltsRtau, dpnRtau);
    const p2 = this.checkOverfinalMarkings(ltsRtau);
    const p3 = this.checkDeadTransitions(dpnR, ltsRtau);
    checks.push(p1, p2, p3);

    const isSound = checks.every((c) => c.satisfied === true);
    this.logStep(
      "VerifyImproved",
      `Done. Soundness = ${isSound ? "YES" : "NO"}`
    );

    return this.createResult(isSound, checks);
  }

  /**
   * Implements Algorithm 5 (Direct): boundedness → refine → add τ → LTS_{N_R^τ} → P1,P2,P3.
   *
   * @param {Object} dpn
   * @param {(msg: string) => void} [progressCallback]
   * @returns {Promise<ReturnType<SuvorovLomazovaVerifier['createResult']>>}
   */
  async verifyDirect(dpn, progressCallback) {
    const say = (m) => {
      if (progressCallback) progressCallback(m);
    };

    // 1) Boundedness (Alg. 3) on N
    say("Checking boundedness (Algorithm 3)...");
    this.logStep("VerifyDirect", "Step 1: Boundedness (Alg. 3)");
    const bnd = await this.checkBoundedness(dpn);
    if (!bnd.bounded) {
      return this.createResult(false, [
        {
          name: "Boundedness (Alg. 3)",
          satisfied: false,
          details: "Net is unbounded (strict cover detected).",
          trace: bnd.trace || [],
        },
      ]);
    }

    // 2) Refinement → N_R
    say("Refining DPN (Algorithm 4)...");
    this.logStep("VerifyDirect", "Step 2: Refinement → N_R");
    const dpnR = await this.refinementEngine.refineDPN(dpn);

    // 3) Add τ → N_R^τ
    say("Adding τ-transitions (Definition 4.4)...");
    this.logStep("VerifyDirect", "Step 3: Add τ → N_R^τ");
    const dpnRtau = await this.addTauTransitions(dpnR);

    // 4) Build LTS_{N_R^τ} and check P1, P2, P3 using GRAPH ANALYSIS
    say("Constructing final LTS and analyzing for soundness...");
    this.logStep("VerifyDirect", "Step 4: Final LTS construction and analysis");
    const ltsRtau = await this.refinementEngine.constructLTS(dpnRtau);

    const checks = [];
    const p1 = await this.checkDeadlockFreedom(ltsRtau, dpnRtau);
    const p2 = this.checkOverfinalMarkings(ltsRtau);
    const p3 = this.checkDeadTransitions(dpnR, ltsRtau);
    checks.push(p1, p2, p3);

    const isSound = checks.every((c) => c.satisfied === true);
    this.logStep("VerifyDirect", `Done. Soundness = ${isSound ? "YES" : "NO"}`);

    return this.createResult(isSound, checks);
  }

  convertPetriNetFormat(petriNet) {
    // Convert from various possible formats to standard format
    const converted = {
      places: [],
      transitions: [],
      arcs: [],
      dataVariables: [],
    };

    // Convert places
    if (petriNet.places) {
      const places = Array.isArray(petriNet.places)
        ? petriNet.places
        : Array.from(petriNet.places.values());
      for (const place of places) {
        converted.places.push({
          id: place.id,
          label: place.label || place.id,
          tokens: place.tokens || 0,
          position: place.position || { x: 0, y: 0 },
        });
      }
    }

    // Convert transitions
    if (petriNet.transitions) {
      const transitions = Array.isArray(petriNet.transitions)
        ? petriNet.transitions
        : Array.from(petriNet.transitions.values());
      for (const transition of transitions) {
        converted.transitions.push({
          id: transition.id,
          label: transition.label || transition.id,
          precondition: transition.precondition || "",
          postcondition: transition.postcondition || "",
          priority: transition.priority || 1,
          delay: transition.delay || 0,
          position: transition.position || { x: 0, y: 0 },
        });
      }
    }

    // Convert arcs
    if (petriNet.arcs) {
      const arcs = Array.isArray(petriNet.arcs)
        ? petriNet.arcs
        : Array.from(petriNet.arcs.values());
      for (const arc of arcs) {
        converted.arcs.push({
          id: arc.id,
          source: arc.source,
          target: arc.target,
          weight: arc.weight || 1,
          type: arc.type || "regular",
        });
      }
    }

    // Convert data variables
    if (petriNet.dataVariables) {
      const dataVars = Array.isArray(petriNet.dataVariables)
        ? petriNet.dataVariables
        : Array.from(petriNet.dataVariables.values());
      for (const variable of dataVars) {
        converted.dataVariables.push({
          id: variable.id,
          name: variable.name,
          type: variable.type || "int",
          currentValue:
            variable.currentValue !== undefined
              ? variable.currentValue
              : variable.value !== undefined
              ? variable.value
              : 0,
          description: variable.description || "",
        });
      }
    }

    return converted;
  }

  /**
   * Boundedness check aligned with Algorithm 3 (coverability over the LTS).
   * Builds a coverability exploration of states ⟨M, φ⟩ using ⊕ (computeNewFormula)
   * and detects unboundedness when a reachable state strictly covers an ancestor
   * along the current path (component-wise ≥ and > in at least one place), with
   * compatible constraints. Uses antichain pruning by coverage to ensure termination.
   *
   * @param {Object} dpn - Normalized DPN.
   * @returns {Promise<{bounded: boolean, trace?: Array}>}
   */
  async checkBoundedness(dpn) {
    this.logStep("Boundedness", "Coverability analysis (Algorithm 3)");

    // Helpers
    const covers = (ma, mb) => {
      // ma ≥ mb component-wise
      for (const p of new Set([...Object.keys(ma), ...Object.keys(mb)])) {
        const a = ma[p] | 0;
        const b = mb[p] | 0;
        if (a < b) return false;
      }
      return true;
    };
    const strictlyCovers = (ma, mb) => {
      if (!covers(ma, mb)) return false;
      for (const p of new Set([...Object.keys(ma), ...Object.keys(mb)])) {
        const a = ma[p] | 0;
        const b = mb[p] | 0;
        if (a > b) return true;
      }
      return false;
    };
    const formulasCompatible = async (f1, f2) => {
      if (!f1 || f1 === "true") return await Z3Solver.isSatisfiable(f2);
      if (!f2 || f2 === "true") return await Z3Solver.isSatisfiable(f1);
      return await Z3Solver.isSatisfiable(`(and ${f1} ${f2})`);
    };
    const stateKey = (marking, formula) => {
      // Canonical key for antichain map (marking only + normalized formula text)
      const mk = Object.entries(marking)
        .sort(([a], [b]) => a.localeCompare(b))
        .map(([k, v]) => `${k}:${v}`)
        .join(",");
      const fk = String(formula || "true")
        .replace(/\s+/g, " ")
        .trim();
      return `${mk}|${fk}`;
    };

    // Initial state
    const initM = this.refinementEngine.getInitialMarking(dpn);
    const initF = this.refinementEngine.getInitialFormula(dpn);
    if (!(await Z3Solver.isSatisfiable(initF))) {
      // If the initial constraint is unsat, the net is trivially bounded (no behavior).
      this.logStep(
        "Boundedness",
        "Initial constraint is UNSAT; treating as bounded."
      );
      return { bounded: true };
    }

    // Frontier stack for DFS; each entry keeps the path for witness extraction
    const stack = [
      {
        marking: initM,
        formula: initF,
        path: [], // sequence of {transitionId, from:{M,F}, to:{M,F}}
      },
    ];

    // Antichain of visited states for pruning:
    // for each key, keep a set of representatives not covered by others.
    const anti = new Map();

    const pushIfNotCovered = async (st) => {
      // If there exists v in anti that covers st (and formulas compatible), prune.
      for (const [_, bucket] of anti) {
        for (const v of bucket) {
          if (
            covers(v.marking, st.marking) &&
            (await formulasCompatible(v.formula, st.formula))
          ) {
            return false; // covered -> prune
          }
        }
      }
      // Otherwise, insert st and remove representatives that st covers.
      const key = stateKey(st.marking, st.formula);
      if (!anti.has(key)) anti.set(key, []);
      const bucket = anti.get(key);
      // Remove dominated reps in this bucket (same key already encodes formula text)
      for (let i = bucket.length - 1; i >= 0; i--) {
        if (covers(st.marking, bucket[i].marking)) {
          bucket.splice(i, 1);
        }
      }
      bucket.push({ marking: st.marking, formula: st.formula });
      return true;
    };

    // Main DFS with coverability checks
    const MAX_EXPLORED = 50000; // safety cap to avoid pathological growth
    let expanded = 0;

    while (stack.length) {
      const cur = stack.pop();
      expanded++;
      if (expanded > MAX_EXPLORED) {
        this.logStep(
          "Boundedness",
          "Exploration cap reached; assuming bounded so far."
        );
        break;
      }

      // Generate successors via ⊕ and marking update
      for (const t of dpn.transitions || []) {
        const succ = await this.refinementEngine.computeSuccessorState(
          cur.marking,
          cur.formula,
          t,
          dpn
        );
        if (!succ) continue;
        if (!(await Z3Solver.isSatisfiable(succ.formula))) continue;

        // Unboundedness witness: if succ strictly covers ANY ancestor marking on this path
        // and the constraints are compatible, we can pump the loop.
        for (let i = 0; i < cur.path.length; i++) {
          const anc = cur.path[i].to; // state after step i
          if (
            strictlyCovers(succ.marking, anc.marking) &&
            (await formulasCompatible(succ.formula, anc.formula))
          ) {
            const witness = [
              ...cur.path.slice(i), // from ancestor forward
              {
                transitionId: t.id,
                from: { marking: cur.marking, formula: cur.formula },
                to: { marking: succ.marking, formula: succ.formula },
              },
            ].map((e) => ({ transitionId: e.transitionId }));
            this.logStep(
              "Boundedness",
              "Unboundedness detected via strict cover on path."
            );
            return { bounded: false, trace: witness };
          }
        }

        // Antichain pruning: skip states covered by visited reps
        const next = {
          marking: succ.marking,
          formula: succ.formula,
          path: [
            ...cur.path,
            {
              transitionId: t.id,
              from: { marking: cur.marking, formula: cur.formula },
              to: { marking: succ.marking, formula: succ.formula },
            },
          ],
        };
        if (await pushIfNotCovered(next)) {
          stack.push(next);
        }
      }
    }

    this.logStep(
      "Boundedness",
      "No strict-cover loop found; net considered bounded."
    );
    return { bounded: true };
  }

  /**
   * Identify final markings M_F strictly from explicit model input.
   * Paper-aligned behavior: do not synthesize finals from topology (e.g., sinks).
   * Accepted sources, in order:
   * 1) dpn.finalMarkings: Array<{ [placeId: string]: number }>
   * 2) dpn.finalMarking:  { [placeId: string]: number }
   * 3) Place-level flags: places with isFinal===true or final===true or type==='final'
   * If none are present, return [] and log that P1/P2 cannot be evaluated.
   *
   * @param {Object} dpn
   * @returns {Array<Object<string, number>>}
   */
  identifyFinalMarkings(dpn) {
    this.logStep("FinalMarkings", "Collecting explicit final marking(s) (M_F)");

    const places = Array.isArray(dpn.places) ? dpn.places : [];
    const placeIds = new Set(places.map((p) => String(p.id)));

    const normalizeMarking = (m) => {
      const out = {};
      for (const p of placeIds) out[p] = 0;
      let anyPositive = false;

      for (const [k, v] of Object.entries(m || {})) {
        const pid = String(k);
        if (!placeIds.has(pid)) {
          this.logStep(
            "FinalMarkings",
            `Ignoring unknown place '${pid}' in provided M_F`
          );
          continue;
        }
        const n = Number(v);
        if (!Number.isInteger(n) || n < 0) {
          this.logStep(
            "FinalMarkings",
            `Invalid token count for place '${pid}': ${v} (must be non-negative integer)`
          );
          return null;
        }
        out[pid] = n;
        if (n > 0) anyPositive = true;
      }

      if (!anyPositive) {
        this.logStep(
          "FinalMarkings",
          "Provided M_F has no tokens in any place; rejecting"
        );
        return null;
      }
      return out;
    };

    // 1) Array of final markings
    if (Array.isArray(dpn.finalMarkings) && dpn.finalMarkings.length > 0) {
      const finals = [];
      for (const m of dpn.finalMarkings) {
        const norm = normalizeMarking(m);
        if (!norm) {
          this.logStep(
            "FinalMarkings",
            "A provided M_F entry is invalid; aborting collection"
          );
          return [];
        }
        finals.push(norm);
      }
      this.logStep(
        "FinalMarkings",
        `Using provided finalMarkings (${finals.length})`
      );
      return finals;
    }

    // 2) Single final marking object
    if (dpn.finalMarking && typeof dpn.finalMarking === "object") {
      const norm = normalizeMarking(dpn.finalMarking);
      if (norm) {
        this.logStep("FinalMarkings", "Using provided finalMarking (single)");
        return [norm];
      }
      this.logStep(
        "FinalMarkings",
        "Provided finalMarking is invalid; ignoring"
      );
    }

    // 3) Place-level flags (explicit metadata only; no sink inference)
    const flagged = places.filter(
      (p) =>
        p &&
        (p.isFinal === true ||
          p.final === true ||
          String(p.type || "").toLowerCase() === "final")
    );
    if (flagged.length > 0) {
      const m = {};
      for (const p of placeIds) m[p] = 0;
      for (const p of flagged) m[String(p.id)] = 1;
      this.logStep(
        "FinalMarkings",
        `Using place-level flags for M_F (${flagged.length} final place(s))`
      );
      return [m];
    }

    // None found: paper requires an explicit M_F
    this.logStep(
      "FinalMarkings",
      "No explicit final marking provided; P1/P2 cannot be evaluated."
    );
    return [];
  }

  getMaxTokensFromModel(model) {
    if (!model) return 0;

    let maxTokens = 0;
    for (const [varName, value] of model.entries()) {
      if (varName.startsWith("M_") && !isNaN(value)) {
        maxTokens = Math.max(maxTokens, parseInt(value));
      }
    }
    return maxTokens;
  }

  extractTraceFromModel(model, k, dpn) {
    if (!model) return [];

    const trace = [];

    for (let i = 0; i < k; i++) {
      for (const trans of dpn.transitions) {
        const transId = this.sanitizeId(trans.id);
        const firedVar = `f_${transId}_${i}`;

        if (model.has(firedVar) && model.get(firedVar) === "true") {
          // Extract variable values at this step
          const vars = {};
          for (const [varName, value] of model.entries()) {
            if (
              varName.endsWith(`_${i}`) &&
              !varName.startsWith("M_") &&
              !varName.startsWith("f_")
            ) {
              const baseName = varName.substring(0, varName.lastIndexOf("_"));
              vars[baseName] = value;
            }
          }

          trace.push({
            transitionId: trans.id,
            transitionLabel: trans.label || trans.id,
            step: i,
            vars: vars,
          });
        }
      }
    }

    return trace;
  }

  sanitizeId(id) {
    return String(id).replace(/[^A-Za-z0-9_]/g, "_");
  }

  logStep(name, details, extra) {
    const step = {
      name,
      details,
      timestamp: Date.now() - this.startTime,
      extra: extra || {},
    };
    this.verificationSteps.push(step);
    console.log(`[${name} +${step.timestamp}ms] ${details}`, extra || "");
  }

  createResult(isSound, checks) {
    return {
      isSound,
      checks,
      counterexamples: this.counterexampleTraces,
      verificationSteps: this.verificationSteps,
      finalMarkings: this.finalMarkings,
      duration: Date.now() - this.startTime,
    };
  }

  // Legacy methods for compatibility (simplified implementations)
  deepCloneDPN(dpn) {
    return JSON.parse(JSON.stringify(dpn));
  }

  buildTrace(path, lts, dpn) {
    return (path || []).map((e) => ({
      transitionId: e.transitionId,
      vars: e.vars || {},
    }));
  }
}


/**
 * Trace Visualization Renderer for Suvorov-Lomazova Verification
 * Single-canvas version: draw overlays AFTER the base renderer, fully sandboxed.
 * - Does NOT wrap the base render in a global save/restore
 * - World-space highlights respect pan/zoom
 * - Screen-space tooltips reset transform to identity
 */
class SuvorovLomazovaTraceVisualizationRenderer {
  constructor(app) {
    this.app = app;
    this.canvas = app.canvas;

    // Visualization state
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.problematicPlaces = new Map();
    this.responsibleVariables = new Map();
    this.violationInfo = null;
    this.isActive = false;

    // HTML overlay management
    this.overlayContainer = null;
    this.htmlOverlays = new Map(); // overlayId -> HTML element
    this.overlayPositions = new Map(); // overlayId -> {worldX, worldY, offsetX, offsetY}

    // Animation
    this.animationTime = 0;
    this.animationFrame = null;
    this.updateInterval = null;

    this.setupHTMLOverlaySystem();
    this.setupEventListeners();
  }

  /**
   * Setup the HTML overlay system
   */
  setupHTMLOverlaySystem() {
    // Create overlay container
    this.overlayContainer = document.createElement('div');
    this.overlayContainer.id = 'sl-overlay-container';
    this.overlayContainer.style.cssText = `
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      pointer-events: none;
      z-index: 100;
      overflow: hidden;
    `;

    // Position container relative to canvas
    const canvasContainer = this.canvas.parentElement;
    if (canvasContainer) {
      canvasContainer.style.position = 'relative';
      canvasContainer.appendChild(this.overlayContainer);
    }

    // Add styles for overlays
    this.injectOverlayStyles();
  }

  /**
   * Setup event listeners for canvas updates
   */
  setupEventListeners() {
    // Listen for canvas events that might change positioning
    this.canvas.addEventListener('wheel', () => this.scheduleUpdate());
    this.canvas.addEventListener('mousedown', () => this.scheduleUpdate());
    this.canvas.addEventListener('mousemove', () => this.scheduleUpdate());
    
    // Listen for window resize
    window.addEventListener('resize', () => this.scheduleUpdate());
    
    // Store references for cleanup
    this.boundEvents = {
      wheel: () => this.scheduleUpdate(),
      mousedown: () => this.scheduleUpdate(),
      mousemove: () => this.scheduleUpdate(),
      resize: () => this.scheduleUpdate()
    };
  }

  /**
   * Schedule an update (debounced)
   */
  scheduleUpdate() {
    if (!this.isActive) return;
    
    // Use requestAnimationFrame for smooth updates
    if (this.updateFrame) {
      cancelAnimationFrame(this.updateFrame);
    }
    
    this.updateFrame = requestAnimationFrame(() => {
      this.updateHTMLOverlays();
    });
  }

  /**
   * Inject CSS styles for HTML overlays
   */
  injectOverlayStyles() {
    if (document.getElementById("sl-overlay-styles")) return;

    const style = document.createElement("style");
    style.id = "sl-overlay-styles";
    style.textContent = `
      .sl-html-overlay {
        position: absolute;
        background: rgba(46, 52, 64, 0.95);
        border: 2px solid;
        border-radius: 8px;
        padding: 12px;
        color: #ECEFF4;
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
        font-size: 13px;
        line-height: 1.4;
        max-width: 250px;
        min-width: 150px;
        box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
        backdrop-filter: blur(10px);
        transform-origin: top left;
        transition: all 0.3s ease;
        pointer-events: auto;
        cursor: move;
        z-index: 101;
      }

      .sl-html-overlay:hover {
        transform: scale(1.05);
        box-shadow: 0 6px 16px rgba(0, 0, 0, 0.4);
      }

      .sl-html-overlay.dragging {
        transition: none;
        transform: scale(1.1);
        z-index: 102;
      }

      .sl-html-overlay.deadTransition {
        border-color: #BF616A;
        background: linear-gradient(135deg, rgba(191, 97, 106, 0.9), rgba(46, 52, 64, 0.95));
        wdith: 10px;
      }

      .sl-html-overlay.overfinal {
        border-color: #D08770;
        background: linear-gradient(135deg, rgba(208, 135, 112, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-html-overlay.traceStep {
        border-color: #88C0D0;
        background: linear-gradient(135deg, rgba(136, 192, 208, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-html-overlay.deadlockMarking {
        border-color: #B48EAD;
        background: linear-gradient(135deg, rgba(180, 142, 173, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-overlay-header {
        font-weight: bold;
        margin-bottom: 8px;
        display: flex;
        align-items: center;
        gap: 6px;
      }

      .sl-overlay-content {
        font-size: 12px;
      }

      .sl-overlay-icon {
        font-size: 16px;
      }

      .sl-overlay-close {
        position: absolute;
        top: 4px;
        right: 4px;
        background: none;
        border: none;
        color: #ECEFF4;
        cursor: pointer;
        font-size: 14px;
        width: 20px;
        height: 20px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        opacity: 0.7;
        transition: all 0.2s ease;
      }

      .sl-overlay-close:hover {
        opacity: 1;
        background: rgba(255, 255, 255, 0.1);
      }

      .sl-data-values {
        margin-top: 8px;
        padding-top: 8px;
        border-top: 1px solid rgba(236, 239, 244, 0.2);
      }

      .sl-data-value {
        display: flex;
        justify-content: space-between;
        margin-bottom: 4px;
        font-family: 'Courier New', monospace;
        font-size: 11px;
      }

      .sl-data-value .variable {
        color: #8FBCBB;
      }

      .sl-data-value .value {
        color: #A3BE8C;
        font-weight: bold;
      }

      /* Highlight styles for elements */
      .sl-element-highlight {
        position: absolute;
        border: 3px solid;
        border-radius: 50%;
        pointer-events: none;
        animation: sl-pulse 2s infinite;
        z-index: 98;
      }

      .sl-element-highlight.transition {
        border-radius: 4px;
      }

      .sl-element-highlight.dead-transition {
        border-color: #BF616A;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(191,97,106,0.12);
      }

      .sl-element-highlight.overfinal {
        border-color: #D08770;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(208,135,112,0.12);
      }

      .sl-element-highlight.trace-step {
        border-color: #88C0D0;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(136,192,208,0.12);
      }

      .sl-element-highlight.deadlock {
        border-color: #B48EAD;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(180,142,173,0.12);
      }

      @keyframes sl-pulse {
        0%, 100% { 
          opacity: 0.5;
          transform: scale(1);
        }
        50% { 
          opacity: 0.8;
          transform: scale(1.1);
        }
      }
    `;
    document.head.appendChild(style);
  }

  /**
   * Update positions and visibility of HTML overlays
   */
  updateHTMLOverlays() {
    if (!this.isActive) return;
    
    this.updateAnimation();
    this.updateOverlayPositions();
    this.updateElementHighlights();
  }

  updateAnimation() {
    this.animationTime += 0.05;
  }

  /**
   * Get the canvas position relative to its container
   */
  getCanvasOffset() {
    const canvasRect = this.canvas.getBoundingClientRect();
    const containerRect = this.canvas.parentElement.getBoundingClientRect();
    
    return {
      x: canvasRect.left - containerRect.left,
      y: canvasRect.top - containerRect.top
    };
  }

  /**
   * Get zoom factor from renderer
   */
  getZoomFactor() {
    return this.app.editor?.renderer?.zoomFactor || 1.0;
  }

  /**
   * Get pan offset from renderer
   */
  getPanOffset() {
    return this.app.editor?.renderer?.panOffset || { x: 0, y: 0 };
  }

  /**
   * Convert world coordinates to screen coordinates
   * This must exactly match the renderer's coordinate transformation
   */
  worldToScreen(worldX, worldY) {
    const zoomFactor = this.getZoomFactor();
    const panOffset = this.getPanOffset();
    
    // Apply the same transformation as the renderer:
    // 1. Scale by zoom factor
    // 2. Translate by pan offset
    const canvasX = worldX * zoomFactor + panOffset.x;
    const canvasY = worldY * zoomFactor + panOffset.y;
    
    // Convert from canvas coordinates to CSS coordinates
    // Account for devicePixelRatio scaling
    const canvasRect = this.canvas.getBoundingClientRect();
    const scaleX = canvasRect.width / this.canvas.width;
    const scaleY = canvasRect.height / this.canvas.height;
    
    // Convert to screen coordinates relative to the canvas
    const screenX = canvasX * scaleX;
    const screenY = canvasY * scaleY;
    
    // Add canvas offset within its container
    const canvasOffset = this.getCanvasOffset();
    
    return {
      x: screenX + canvasOffset.x,
      y: screenY + canvasOffset.y
    };
  }

  /**
   * Update positions of all HTML overlays based on world coordinates
   */
  updateOverlayPositions() {
    for (const [overlayId, overlay] of this.htmlOverlays) {
      const position = this.overlayPositions.get(overlayId);
      if (!position) continue;

      // Convert world coordinates to screen coordinates
      const screenPos = this.worldToScreen(position.worldX, position.worldY);
      
      // Apply user offset (for dragged overlays)
      const finalX = screenPos.x + position.offsetX;
      const finalY = screenPos.y + position.offsetY;

      // Update overlay position
      overlay.style.left = `${finalX}px`;
      overlay.style.top = `${finalY}px`;

      // Hide overlay if it's outside the visible area
      const containerRect = this.overlayContainer.getBoundingClientRect();
      const isVisible = finalX > -overlay.offsetWidth && 
                       finalY > -overlay.offsetHeight &&
                       finalX < containerRect.width + overlay.offsetWidth &&
                       finalY < containerRect.height + overlay.offsetHeight;
      
      overlay.style.display = isVisible ? 'block' : 'none';
    }
  }

  /**
   * Update element highlights (ring around places/transitions)
   */
  updateElementHighlights() {
    // Remove existing highlights
    const existingHighlights = this.overlayContainer.querySelectorAll('.sl-element-highlight');
    existingHighlights.forEach(highlight => highlight.remove());

    // Add new highlights
    for (const elementId of this.highlightedElements) {
      this.createElementHighlight(elementId);
    }
  }

  /**
   * Create a highlight ring around an element
   */
  createElementHighlight(elementId) {
    const element = this.getElementById(elementId);
    if (!element) return;

    const highlight = document.createElement('div');
    highlight.className = 'sl-element-highlight';
    
    // Determine element type and styling
    const isTransition = this.app.api.petriNet.transitions.has(elementId);
    if (isTransition) {
      highlight.classList.add('transition');
    }

    // Add specific styling based on violation type
    if (this.isDeadTransition(elementId)) {
      highlight.classList.add('dead-transition');
    } else if (this.isOverfinalPlace(elementId)) {
      highlight.classList.add('overfinal');
    } else if (this.isTraceElement(elementId)) {
      highlight.classList.add('trace-step');
    } else {
      highlight.classList.add('deadlock');
    }

    const worldPos = { x: element.position.x, y: element.position.y };
    const screenPos = this.worldToScreen(worldPos.x, worldPos.y);
    
    const highlightPadding = 15; // Extra space around element (in world units)
    let worldSize, borderRadius;
    if (isTransition) {
      worldSize = Math.max(element.width, element.height) + highlightPadding;
      borderRadius = '4px';
    } else {
      worldSize = element.radius * 2 + highlightPadding;
      borderRadius = '50%';
    }
    
    // Apply zoom to the size
    const screenSize = worldSize * this.getZoomFactor() * (this.canvas.getBoundingClientRect().width / this.canvas.width);

    highlight.style.cssText += `
      left: ${screenPos.x - (isTransition? screenSize*0.3: screenSize*0.6)}px;
      top: ${screenPos.y - (isTransition? screenSize*0.4: screenSize*0.6)}px;
      width: ${isTransition ? (screenSize / 2) : screenSize}px;
      height: ${screenSize}px;
      border-radius: ${borderRadius};
    `;

    this.overlayContainer.appendChild(highlight);
  }

  /**
   * Create an HTML overlay for a specific data overlay
   */
  createHTMLOverlay(overlayId, overlayData) {
    const element = this.getElementById(overlayData.elementId);
    if (!element) return;

    // Store overlay data
    this.dataOverlays.set(overlayId, overlayData);

    // Create HTML element
    const overlay = document.createElement('div');
    overlay.className = `sl-html-overlay ${overlayData.type}`;
    overlay.id = `overlay-${overlayId}`;

    // Set content
    overlay.innerHTML = this.formatOverlayHTML(overlayData);

    // Position overlay
    const worldPos = { x: element.position.x, y: element.position.y };
    const screenPos = this.worldToScreen(worldPos.x, worldPos.y);
    const defaultOffset = this.calculateDefaultOffset(overlayData.elementType);

    // Store position data
    this.overlayPositions.set(overlayId, {
      worldX: worldPos.x,
      worldY: worldPos.y,
      offsetX: defaultOffset.x,
      offsetY: defaultOffset.y
    });

    // Set initial position
    overlay.style.left = `${screenPos.x + defaultOffset.x}px`;
    overlay.style.top = `${screenPos.y + defaultOffset.y}px`;

    // Add drag functionality
    this.makeDraggable(overlay, overlayId);

    // Add close button functionality
    const closeBtn = overlay.querySelector('.sl-overlay-close');
    if (closeBtn) {
      closeBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        this.removeHTMLOverlay(overlayId);
      });
    }

    // Add to container and map
    this.overlayContainer.appendChild(overlay);
    this.htmlOverlays.set(overlayId, overlay);
  }

  /**
   * Calculate default offset for overlay positioning
   */
  calculateDefaultOffset(elementType) {
    if (elementType === 'transition') {
      return { x: 30, y: -60 };
    } else {
      return { x: 30, y: -30 };
    }
  }

  /**
   * Make an overlay draggable
   */
  makeDraggable(overlay, overlayId) {
    let isDragging = false;
    let startX, startY, startOffsetX, startOffsetY;

    overlay.addEventListener('mousedown', (e) => {
      if (e.target.classList.contains('sl-overlay-close')) return;
      
      isDragging = true;
      startX = e.clientX;
      startY = e.clientY;
      
      const position = this.overlayPositions.get(overlayId);
      startOffsetX = position.offsetX;
      startOffsetY = position.offsetY;
      
      overlay.classList.add('dragging');
      document.addEventListener('mousemove', onMouseMove);
      document.addEventListener('mouseup', onMouseUp);
      e.preventDefault();
    });

    const onMouseMove = (e) => {
      if (!isDragging) return;
      
      const deltaX = e.clientX - startX;
      const deltaY = e.clientY - startY;
      
      const position = this.overlayPositions.get(overlayId);
      position.offsetX = startOffsetX + deltaX;
      position.offsetY = startOffsetY + deltaY;
      
      this.updateOverlayPositions();
    };

    const onMouseUp = () => {
      isDragging = false;
      overlay.classList.remove('dragging');
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    };
  }

  // [Rest of the methods remain the same - visualizeCheck, clearHighlights, etc.]
  
  /**
   * Public: visualize a check result
   */
  visualizeCheck(check) {
    this.clearHighlights(true);
    this.isActive = true;
    this.violationInfo = check;

    if (check.problematicPlaces) {
      for (const place of check.problematicPlaces) {
        this.problematicPlaces.set(place.placeId, place);
      }
    }
    if (check.responsibleVariables) {
      for (const variable of check.responsibleVariables) {
        this.responsibleVariables.set(variable.variable, variable);
      }
    }

    if (!check.satisfied) {
      switch (true) {
        case check.name.includes("Deadlock") || check.name.includes("P1"):
          this.visualizeDeadlockViolation(check);
          break;
        case check.name.includes("Overfinal") || check.name.includes("P2"):
          this.visualizeOverfinalViolation(check);
          break;
        case check.name.includes("Dead") || check.name.includes("P3"):
          this.visualizeDeadTransitionViolation(check);
          break;
        case check.name.includes("Boundedness"):
          this.visualizeBoundednessViolation(check);
          break;
        default:
          this.visualizeGenericViolation(check);
          break;
      }
    }

    this.startAnimation();
  }

  startAnimation() {
    if (this.animationFrame) return;
    
    const animate = () => {
      if (!this.isActive) {
        this.animationFrame = null;
        return;
      }
      this.updateHTMLOverlays();
      this.animationFrame = requestAnimationFrame(animate);
    };
    this.animationFrame = requestAnimationFrame(animate);
  }

  stopAnimation() {
    if (this.animationFrame) {
      cancelAnimationFrame(this.animationFrame);
      this.animationFrame = null;
    }
    if (this.updateFrame) {
      cancelAnimationFrame(this.updateFrame);
      this.updateFrame = null;
    }
  }

  visualizeDeadlockViolation(check) {
    if (check.trace && check.trace.length > 0) {
      this.visualizeTracePath(check.trace, "deadlock");
    }
    if (check.offendingState?.marking) {
      Object.entries(check.offendingState.marking).forEach(([placeId, tokens]) => {
        if (tokens > 0) {
          this.highlightedElements.add(placeId);
          this.createHTMLOverlay(`deadlock_${placeId}`, {
            type: "deadlockMarking",
            elementId: placeId,
            elementType: "place",
            tokens,
            data: check.offendingState,
          });
        }
      });
    }
  }

  visualizeOverfinalViolation(check) {
    if (check.overfinalNodes?.length) {
      check.overfinalNodes.forEach((node, index) => {
        if (!node.marking) return;
        Object.entries(node.marking).forEach(([placeId, tokens]) => {
          if (tokens > 0) {
            this.highlightedElements.add(placeId);
            this.createHTMLOverlay(`overfinal_${placeId}_${index}`, {
              type: "overfinal",
              elementId: placeId,
              elementType: "place",
              tokens,
              nodeData: node,
              formula: node.formula,
            });
          }
        });
      });
    }
    if (check.trace) this.visualizeTracePath(check.trace, "overfinal");
  }

  visualizeDeadTransitionViolation(check) {
    const list = check.deadTransitions || (check.deadTransition ? [check.deadTransition] : []);
    list.forEach((deadTransition) => {
      const id = deadTransition.transitionId;
      if (!id) return;
      this.highlightedElements.add(id);
      this.highlightConnectedElements(id);
      this.createHTMLOverlay(`dead_transition_${id}`, {
        type: "deadTransition",
        elementId: id,
        elementType: "transition",
        data: deadTransition,
        variants: deadTransition.variants || [],
      });
    });
    if (check.trace) this.visualizeTracePath(check.trace, "deadTransition");
  }

  visualizeBoundednessViolation(check) {
    if (check.trace?.length) this.visualizeTracePath(check.trace, "boundedness");
  }

  visualizeGenericViolation(check) {
    if (check.trace) this.visualizeTracePath(check.trace, "generic");
  }

  visualizeTracePath(trace, violationType) {
    if (!trace?.length) return;
    trace.forEach((step, stepIndex) => {
      const transitionId = this.findTransitionId(step.transitionId);
      if (!transitionId) return;
      this.highlightedElements.add(transitionId);
      this.highlightConnectedElements(transitionId);
      this.createHTMLOverlay(`trace_step_${stepIndex}`, {
        type: "traceStep",
        elementId: transitionId,
        elementType: "transition",
        stepIndex,
        violationType,
        data: step,
        vars: step.vars || {},
      });
    });
  }

  /**
   * Remove an HTML overlay
   */
  removeHTMLOverlay(overlayId) {
    const overlay = this.htmlOverlays.get(overlayId);
    if (overlay) {
      overlay.remove();
      this.htmlOverlays.delete(overlayId);
    }
    this.overlayPositions.delete(overlayId);
    this.dataOverlays.delete(overlayId);
  }

  /**
   * Format overlay content as HTML
   */
  formatOverlayHTML(overlayData) {
    const content = this.formatOverlayContent(overlayData);
    const lines = content.split('\n');
    const header = lines[0];
    const body = lines.slice(1).join('\n');

    let html = `
      <button class="sl-overlay-close">×</button>
      <div class="sl-overlay-header">
        <span class="sl-overlay-icon">${this.getOverlayIcon(overlayData.type)}</span>
        <span>${header}</span>
      </div>
    `;

    if (body.trim()) {
      html += `<div class="sl-overlay-content">${this.formatContentAsHTML(body)}</div>`;
    }

    // Add data values if present
    if (overlayData.vars && Object.keys(overlayData.vars).length > 0) {
      html += '<div class="sl-data-values">';
      html += '<strong>Data State:</strong>';
      for (const [variable, value] of Object.entries(overlayData.vars)) {
        html += `
          <div class="sl-data-value">
            <span class="variable">${variable}</span>
            <span class="value">${value}</span>
          </div>
        `;
      }
      html += '</div>';
    }

    return html;
  }

  /**
   * Get icon for overlay type
   */
  getOverlayIcon(type) {
    switch (type) {
      case "deadTransition":
      case "deadlockMarking":
        return "⚠️";
      case "overfinal":
        return "🔥";
      case "traceStep":
        return "🔄";
      default:
        return "❌";
    }
  }

  /**
   * Format content as HTML
   */
  formatContentAsHTML(content) {
    return content
      .split('\n')
      .map(line => line.trim())
      .filter(line => line.length > 0)
      .map(line => `<div>${line}</div>`)
      .join('');
  }

  /**
   * Format overlay content
   */
  formatOverlayContent(overlay) {
    switch (overlay.type) {
      case "deadTransition":
        return `DEAD TRANSITION\n${overlay.data?.transitionLabel || overlay.elementId}\nNever enabled in any reachable state`;
      case "overfinal":
        return `OVERFINAL MARKING\nPlace: ${overlay.elementId}\nTokens: ${overlay.tokens}\nExceeds final marking`;
      case "traceStep": {
        const lines = [`Step ${overlay.stepIndex + 1}: Fire ${overlay.elementId}`];
        return lines.join('\n');
      }
      case "deadlockMarking":
        return `DEADLOCK STATE\nPlace: ${overlay.elementId}\nTokens: ${overlay.tokens}\nCannot reach final marking`;
      default:
        return `Violation detected\n${overlay.elementId}`;
    }
  }

  // Helper methods
  findTransitionId(stepTransitionId) {
    if (!this.app.api?.petriNet) return null;
    if (this.app.api.petriNet.transitions.has(stepTransitionId)) return stepTransitionId;
    for (const [id, transition] of this.app.api.petriNet.transitions) {
      if (
        transition.label === stepTransitionId ||
        id.includes(stepTransitionId) ||
        stepTransitionId?.includes?.(id)
      ) return id;
    }
    return null;
  }

  highlightConnectedElements(transitionId) {
    if (!this.app.api?.petriNet) return;
    for (const arc of this.app.api.petriNet.arcs.values()) {
      if (arc.source === transitionId || arc.target === transitionId) {
        this.highlightedArcs.add(arc.id);
        const connected = arc.source === transitionId ? arc.target : arc.source;
        this.highlightedElements.add(connected);
      }
    }
  }

  getElementById(elementId) {
    if (this.app.api?.petriNet?.places?.has(elementId)) {
      return this.app.api.petriNet.places.get(elementId);
    }
    if (this.app.api?.petriNet?.transitions?.has(elementId)) {
      return this.app.api.petriNet.transitions.get(elementId);
    }
    return null;
  }

  isDeadTransition(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "deadTransition" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  isOverfinalPlace(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "overfinal" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  isTraceElement(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "traceStep" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  /**
   * Clear state and remove all overlays
   */
  clearHighlights(keepInactive = false) {
    this.highlightedElements.clear();
    this.highlightedArcs.clear();
    this.dataOverlays.clear();
    this.problematicPlaces.clear();
    this.responsibleVariables.clear();
    this.violationInfo = null;

    // Clear all HTML overlays
    for (const [overlayId] of this.htmlOverlays) {
      this.removeHTMLOverlay(overlayId);
    }

    if (!keepInactive) this.isActive = false;
    this.stopAnimation();
  }

  /**
   * Cleanup when component is destroyed
   */
  destroy() {
    this.clearHighlights(false);
    
    // Remove event listeners
    if (this.boundEvents) {
      this.canvas.removeEventListener('wheel', this.boundEvents.wheel);
      this.canvas.removeEventListener('mousedown', this.boundEvents.mousedown);
      this.canvas.removeEventListener('mousemove', this.boundEvents.mousemove);
      window.removeEventListener('resize', this.boundEvents.resize);
    }
    
    // Remove overlay container
    if (this.overlayContainer && this.overlayContainer.parentNode) {
      this.overlayContainer.parentNode.removeChild(this.overlayContainer);
    }

    // Remove styles
    const styles = document.getElementById("sl-overlay-styles");
    if (styles && styles.parentNode) {
      styles.parentNode.removeChild(styles);
    }
  }
}
/**
 * Enhanced Verification UI for Suvorov-Lomazova Verification
 * Updated to work with the new HTML overlay system
 */
class SuvorovLomazovaVerificationUI {
  constructor(app) {
    this.app = app;
    this.verifier = null;
    this.traceVisualizer = null;
    this.currentResults = null;
    this.activeCheckIndex = -1;
    this.isVisualizationActive = false;

    this.injectStyles();
    this.createVerificationSection();
    this.createVerificationModal();
    this.initializeTraceVisualizer();
  }

  /**
   * Inject CSS styles for the verification UI
   */
  injectStyles() {
    if (document.getElementById("sl-verification-styles")) return;

    const style = document.createElement("style");
    style.id = "sl-verification-styles";
    style.textContent = `
      .sl-verification-modal {
        position: fixed;
        top: 0;
        left: 0;
        width: 100%;
        height: 100%;
        background-color: rgba(0, 0, 0, 0.8);
        display: none;
        z-index: 1000;
        opacity: 0;
        transition: opacity 0.3s ease;
      }

      .sl-verification-modal.show {
        display: flex;
        align-items: center;
        justify-content: center;
        opacity: 1;
      }

      .sl-modal-content {
        background: linear-gradient(145deg, #3B4252, #434C5E);
        color: #ECEFF4;
        max-width: 1000px;
        max-height: 90vh;
        width: 90%;
        border-radius: 12px;
        box-shadow: 0 20px 40px rgba(0, 0, 0, 0.6);
        overflow: hidden;
        transform: scale(0.9);
        transition: transform 0.3s ease;
      }

      .sl-verification-modal.show .sl-modal-content {
        transform: scale(1);
      }

      .sl-modal-header {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
        padding: 20px 25px;
        display: flex;
        justify-content: space-between;
        align-items: center;
        border-bottom: 1px solid #4C566A;
      }

      .sl-modal-title {
        font-size: 20px;
        font-weight: 600;
        margin: 0;
        display: flex;
        align-items: center;
        gap: 10px;
      }

      .sl-close-btn {
        background: none;
        border: none;
        color: #ECEFF4;
        font-size: 28px;
        cursor: pointer;
        width: 40px;
        height: 40px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        transition: background-color 0.2s ease;
      }

      .sl-close-btn:hover {
        background-color: rgba(255, 255, 255, 0.1);
      }

      .sl-modal-body {
        padding: 25px;
        overflow-y: auto;
        max-height: calc(90vh - 80px);
      }

      .sl-verification-status {
        display: flex;
        align-items: center;
        gap: 15px;
        margin-bottom: 25px;
        padding: 20px;
        border-radius: 8px;
        border-left: 5px solid;
        background: rgba(255, 255, 255, 0.05);
      }

      .sl-verification-status.sound {
        border-left-color: #A3BE8C;
        background: rgba(163, 190, 140, 0.1);
      }

      .sl-verification-status.unsound {
        border-left-color: #BF616A;
        background: rgba(191, 97, 106, 0.1);
      }

      .sl-status-icon {
        font-size: 32px;
        animation: pulse 2s infinite;
      }

      @keyframes pulse {
        0%, 100% { transform: scale(1); }
        50% { transform: scale(1.1); }
      }

      .sl-status-details h3 {
        margin: 0 0 8px 0;
        font-size: 18px;
      }

      .sl-status-details p {
        margin: 0;
        color: #D8DEE9;
        font-size: 14px;
      }

      .sl-properties-grid {
        display: grid;
        grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
        gap: 20px;
        margin-bottom: 25px;
      }

      .sl-property-card {
        background: rgba(67, 76, 94, 0.6);
        border-radius: 8px;
        padding: 20px;
        border: 2px solid transparent;
        transition: all 0.3s ease;
        cursor: pointer;
      }

      .sl-property-card:hover {
        border-color: #88C0D0;
        transform: translateY(-2px);
        box-shadow: 0 8px 16px rgba(0, 0, 0, 0.3);
      }

      .sl-property-card.active {
        border-color: #5E81AC;
        background: rgba(94, 129, 172, 0.2);
      }

      .sl-property-header {
        display: flex;
        justify-content: space-between;
        align-items: flex-start;
        margin-bottom: 12px;
      }

      .sl-property-name {
        font-weight: 600;
        font-size: 16px;
        margin: 0;
        color: #ECEFF4;
      }

      .sl-property-status {
        padding: 4px 12px;
        border-radius: 20px;
        font-size: 12px;
        font-weight: 600;
        text-transform: uppercase;
        letter-spacing: 0.5px;
      }

      .sl-property-status.pass {
        background-color: #A3BE8C;
        color: #2E3440;
      }

      .sl-property-status.fail {
        background-color: #BF616A;
        color: #ECEFF4;
      }

      .sl-property-description {
        color: #D8DEE9;
        font-size: 14px;
        line-height: 1.4;
        margin-bottom: 15px;
      }

      .sl-property-details {
        font-size: 13px;
        color: #81A1C1;
      }

      .sl-counterexample-section {
        background: rgba(76, 86, 106, 0.4);
        border-radius: 6px;
        padding: 15px;
        margin-top: 15px;
        border-left: 3px solid #BF616A;
      }

      .sl-counterexample-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 10px;
      }

      .sl-counterexample-title {
        font-weight: 600;
        color: #ECEFF4;
        margin: 0;
      }

      .sl-visualize-btn {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
        border: none;
        padding: 8px 16px;
        border-radius: 20px;
        cursor: pointer;
        font-size: 12px;
        font-weight: 500;
        transition: all 0.2s ease;
      }

      .sl-visualize-btn:hover {
        transform: translateY(-1px);
        box-shadow: 0 4px 8px rgba(0, 0, 0, 0.3);
      }

      .sl-visualize-btn.active {
        background: linear-gradient(135deg, #A3BE8C, #8FBCBB);
      }

      .sl-trace-info {
        color: #D8DEE9;
        font-size: 13px;
      }

      .sl-control-panel {
        background: rgba(46, 52, 64, 0.8);
        padding: 20px;
        border-top: 1px solid #4C566A;
        display: flex;
        justify-content: space-between;
        align-items: center;
        gap: 15px;
      }

      .sl-control-group {
        display: flex;
        gap: 10px;
        align-items: center;
      }

      .sl-btn {
        padding: 10px 20px;
        border-radius: 6px;
        border: none;
        cursor: pointer;
        font-weight: 500;
        transition: all 0.2s ease;
      }

      .sl-btn-primary {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
      }

      .sl-btn-secondary {
        background: rgba(67, 76, 94, 0.8);
        color: #ECEFF4;
        border: 1px solid #4C566A;
      }

      .sl-btn:hover {
        transform: translateY(-1px);
      }

      .sl-progress {
        text-align: center;
        padding: 60px 20px;
        color: #88C0D0;
      }

      .sl-spinner {
        display: inline-block;
        width: 40px;
        height: 40px;
        border: 4px solid rgba(136, 192, 208, 0.3);
        border-radius: 50%;
        border-top-color: #88C0D0;
        animation: spin 1s linear infinite;
        margin-bottom: 20px;
      }

      @keyframes spin {
        to { transform: rotate(360deg); }
      }

      .sl-timing-info {
        text-align: center;
        color: #81A1C1;
        font-size: 13px;
        margin-top: 20px;
        padding-top: 15px;
        border-top: 1px solid #434C5E;
      }

      .sl-algorithm-info {
        background: rgba(129, 161, 193, 0.1);
        border: 1px solid #81A1C1;
        border-radius: 6px;
        padding: 15px;
        margin-bottom: 20px;
        font-size: 13px;
        color: #D8DEE9;
      }

      .sl-verification-steps {
        max-height: 150px;
        overflow-y: auto;
        background: rgba(46, 52, 64, 0.5);
        border-radius: 4px;
        padding: 10px;
        margin-top: 15px;
      }

      .sl-step {
        font-size: 11px;
        color: #81A1C1;
        margin-bottom: 5px;
        padding: 3px 6px;
        background: rgba(129, 161, 193, 0.1);
        border-radius: 3px;
      }

      /* Enhanced floating control panel for HTML overlay system */
      .sl-floating-controls {
        position: fixed;
        top: 20px;
        right: 20px;
        background: rgba(46, 52, 64, 0.95);
        padding: 15px;
        border-radius: 8px;
        border: 1px solid #4C566A;
        display: none;
        z-index: 999;
        backdrop-filter: blur(10px);
        box-shadow: 0 8px 16px rgba(0, 0, 0, 0.3);
        min-width: 200px;
      }

      .sl-floating-controls.show {
        display: block;
      }

      .sl-floating-controls h4 {
        margin: 0 0 10px 0;
        color: #ECEFF4;
        font-size: 14px;
        display: flex;
        align-items: center;
        gap: 8px;
      }

      .sl-floating-controls .sl-control-group {
        flex-direction: column;
        gap: 8px;
      }

      .sl-floating-controls .sl-btn {
        padding: 8px 16px;
        font-size: 12px;
        width: 100%;
      }

      .sl-overlay-counter {
        font-size: 12px;
        color: #81A1C1;
        margin-bottom: 10px;
        text-align: center;
        padding: 4px 8px;
        background: rgba(129, 161, 193, 0.1);
        border-radius: 4px;
      }

      .sl-overlay-info {
        font-size: 11px;
        color: #8FBCBB;
        margin-top: 8px;
        text-align: center;
        font-style: italic;
      }
    `;
    document.head.appendChild(style);
  }

  /**
   * Create verification section in sidebar
   */
  createVerificationSection() {
    const modelTab = document.querySelector('.sidebar-pane[data-tab="model"]');
    if (!modelTab || document.getElementById("sl-verification-section")) return;

    const section = document.createElement("div");
    section.id = "sl-verification-section";
    section.className = "sidebar-section";
    section.innerHTML = `
      <div class="section-header">
        <div class="section-title">
          <span class="section-icon">🔬</span>
          <h3>Formal Verification</h3>
        </div>
      </div>
      <div class="section-content">
        <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">
          Verify soundness properties using Suvorov & Lomazova algorithms.
        </p>
        <div style="margin-bottom: 10px;">
          <label style="display: block; margin-bottom: 5px; font-size: 13px;">Algorithm:</label>
          <select id="sl-algorithm-select" style="width: 100%; padding: 5px;">
            <option value="improved">Improved (Algorithm 6)</option>
            <option value="direct">Direct (Algorithm 5)</option>
          </select>
        </div>
        <button id="btn-sl-verify" class="button-primary" style="width: 100%; background: linear-gradient(135deg, #5E81AC, #81A1C1); border: none; padding: 12px; border-radius: 6px;">
          🔬 Run Formal Verification
        </button>
      </div>
    `;

    modelTab.appendChild(section);

    // Add event listener
    document.getElementById("btn-sl-verify").addEventListener("click", () => {
      this.startVerification();
    });
  }

  /**
   * Create verification modal dialog
   */
  createVerificationModal() {
    if (document.getElementById("sl-verification-modal")) return;

    const modal = document.createElement("div");
    modal.id = "sl-verification-modal";
    modal.className = "sl-verification-modal";
    modal.innerHTML = `
      <div class="sl-modal-content">
        <div class="sl-modal-header">
          <h2 class="sl-modal-title">
            <span>🔬</span>
            <span>Formal Soundness Verification</span>
          </h2>
          <button class="sl-close-btn" id="sl-close-modal">×</button>
        </div>
        <div class="sl-modal-body" id="sl-modal-body">
          <!-- Content will be dynamically generated -->
        </div>
      </div>
    `;

    document.body.appendChild(modal);

    // Create enhanced floating controls
    const floatingControls = document.createElement("div");
    floatingControls.id = "sl-floating-controls";
    floatingControls.className = "sl-floating-controls";
    floatingControls.innerHTML = `
      <h4>
        <span>🔬</span>
        <span>Verification Overlays</span>
      </h4>
      <div class="sl-overlay-counter" id="sl-overlay-counter">
        0 overlays active
      </div>
      <div class="sl-control-group">
        <button class="sl-btn sl-btn-secondary" id="sl-float-show-results">
          📊 Show Results
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-clear-highlights">
          🧹 Clear Visualization
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-hide-overlays">
          👁️ Hide Overlays
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-show-overlays" style="display: none;">
          👁️ Show Overlays
        </button>
      </div>
      <div class="sl-overlay-info">
        Drag overlays to reposition them
      </div>
    `;
    document.body.appendChild(floatingControls);

    // Event listeners
    document.getElementById("sl-close-modal").addEventListener("click", () => {
      this.closeModal();
    });

    modal.addEventListener("click", (e) => {
      if (e.target === modal) this.closeModal();
    });

    // Enhanced floating controls event listeners
    document.getElementById("sl-float-show-results")?.addEventListener("click", () => {
      this.showModal();
    });

    document.getElementById("sl-float-clear-highlights")?.addEventListener("click", () => {
      this.clearVisualization();
      this.hideFloatingControls();
    });

    document.getElementById("sl-float-hide-overlays")?.addEventListener("click", () => {
      this.hideOverlays();
    });

    document.getElementById("sl-float-show-overlays")?.addEventListener("click", () => {
      this.showOverlays();
    });
  }

  /**
   * Initialize trace visualizer
   */
  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
      this.traceVisualizer = new SuvorovLomazovaTraceVisualizationRenderer(this.app);
    }
  }

  /**
   * Show the verification modal
   */
  showModal() {
    const modal = document.getElementById("sl-verification-modal");
    modal.classList.add("show");
    this.hideFloatingControls();
  }

  /**
   * Close the verification modal (but keep visualization active)
   */
  closeModal() {
    const modal = document.getElementById("sl-verification-modal");
    modal.classList.remove("show");
    
    // Show floating controls if visualization is active
    if (this.isVisualizationActive) {
      this.showFloatingControls();
      this.updateOverlayCounter();
    }
  }

  /**
   * Show floating controls
   */
  showFloatingControls() {
    const controls = document.getElementById("sl-floating-controls");
    if (controls) {
      controls.classList.add("show");
    }
  }

  /**
   * Hide floating controls
   */
  hideFloatingControls() {
    const controls = document.getElementById("sl-floating-controls");
    if (controls) {
      controls.classList.remove("show");
    }
  }

  /**
   * Update overlay counter in floating controls
   */
  updateOverlayCounter() {
    const counter = document.getElementById("sl-overlay-counter");
    if (counter && this.traceVisualizer) {
      const overlayCount = this.traceVisualizer.htmlOverlays.size;
      counter.textContent = `${overlayCount} overlay${overlayCount !== 1 ? 's' : ''} active`;
    }
  }

  /**
   * Hide all overlays temporarily
   */
  hideOverlays() {
    if (this.traceVisualizer && this.traceVisualizer.overlayContainer) {
      this.traceVisualizer.overlayContainer.style.display = 'none';
      
      const hideBtn = document.getElementById("sl-float-hide-overlays");
      const showBtn = document.getElementById("sl-float-show-overlays");
      if (hideBtn) hideBtn.style.display = 'none';
      if (showBtn) showBtn.style.display = 'block';
    }
  }

  /**
   * Show all overlays
   */
  showOverlays() {
    if (this.traceVisualizer && this.traceVisualizer.overlayContainer) {
      this.traceVisualizer.overlayContainer.style.display = 'block';
      
      const hideBtn = document.getElementById("sl-float-hide-overlays");
      const showBtn = document.getElementById("sl-float-show-overlays");
      if (hideBtn) hideBtn.style.display = 'block';
      if (showBtn) showBtn.style.display = 'none';
    }
  }

  /**
   * Start the verification process
   */
  async startVerification() {
    const verifyButton = document.getElementById("btn-sl-verify");
    const algorithmSelect = document.getElementById("sl-algorithm-select");
    const modalBody = document.getElementById("sl-modal-body");

    // Clear any existing visualization
    this.clearVisualization();

    // Disable button and show loading
    verifyButton.disabled = true;
    verifyButton.innerHTML = "⏳ Running Verification...";

    this.showModal();
    modalBody.innerHTML = this.createProgressHTML("Initializing verification...");

    try {
      // Get selected algorithm
      const useImprovedAlgorithm = algorithmSelect.value === "improved";

      // Create verifier with options
      this.verifier = new SuvorovLomazovaVerifier(this.app.api.petriNet, {
        useImprovedAlgorithm: useImprovedAlgorithm,
        maxBound: 10,
        enableTauTransitions: true,
        enableCoverage: true,
      });

      // Run verification with progress updates
      this.currentResults = await this.verifier.verify((progress) => {
        modalBody.innerHTML = this.createProgressHTML(progress);
      });

      console.log("Verification completed:", this.currentResults);

      // Display results
      modalBody.innerHTML = this.createResultsHTML(this.currentResults);
      this.attachEventListeners();
    } catch (error) {
      console.error("Verification error:", error);
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      // Re-enable button
      verifyButton.disabled = false;
      verifyButton.innerHTML = "🔬 Run Formal Verification";
    }
  }

  createProgressHTML(message) {
    return `
      <div class="sl-progress">
        <div class="sl-spinner"></div>
        <h3>${message}</h3>
        <p>This may take a few moments...</p>
      </div>
    `;
  }

  createResultsHTML(results) {
    const algorithmUsed = results.checks?.some((c) =>
      c.name.includes("Algorithm 6")
    )
      ? "Improved (Algorithm 6)"
      : "Direct (Algorithm 5)";

    return `
      ${this.createStatusSection(results)}
      ${this.createAlgorithmInfoSection(algorithmUsed)}
      ${this.createPropertiesSection(results.checks || [])}
      ${this.createControlPanel()}
      ${this.createTimingSection(results)}
    `;
  }

  createStatusSection(results) {
    const statusClass = results.isSound ? "sound" : "unsound";
    const statusIcon = results.isSound ? "✅" : "❌";
    const statusText = results.isSound ? "Formally Sound" : "Formally Unsound";
    const statusDetails = results.isSound
      ? "All soundness properties are satisfied"
      : "One or more soundness properties are violated";

    return `
      <div class="sl-verification-status ${statusClass}">
        <div class="sl-status-icon">${statusIcon}</div>
        <div class="sl-status-details">
          <h3>${statusText}</h3>
          <p>${statusDetails}</p>
        </div>
      </div>
    `;
  }

  createAlgorithmInfoSection(algorithmUsed) {
    return `
      <div class="sl-algorithm-info">
        <strong>Algorithm Used:</strong> ${algorithmUsed}<br>
        <strong>Properties Checked:</strong> P1 (Deadlock Freedom), P2 (No Overfinal Markings), P3 (No Dead Transitions)<br>
        <strong>Visualization:</strong> Interactive HTML overlays show counterexamples directly on the Petri net (drag to reposition)
      </div>
    `;
  }

  createPropertiesSection(checks) {
    if (!checks.length) {
      return "<p>No property checks available.</p>";
    }

    const cardsHTML = checks
      .map((check, index) => this.createPropertyCard(check, index))
      .join("");

    return `
      <div class="sl-properties-grid">
        ${cardsHTML}
      </div>
    `;
  }

  createPropertyCard(check, index) {
    const statusClass = check.satisfied ? "pass" : "fail";
    const statusText = check.satisfied ? "Pass" : "Fail";
    const propertyName = this.getPropertyDisplayName(check.name);

    const hasCounterexample =
      !check.satisfied &&
      (check.trace ||
        check.deadTransitions ||
        check.overfinalNodes ||
        check.violatingNodes);

    const counterexampleSection = hasCounterexample
      ? `
      <div class="sl-counterexample-section">
        <div class="sl-counterexample-header">
          <h4 class="sl-counterexample-title">Counterexample</h4>
          <button class="sl-visualize-btn" data-check-index="${index}">
            Visualize
          </button>
        </div>
        <div class="sl-trace-info">
          ${this.getCounterexampleDescription(check)}
        </div>
      </div>
    `
      : "";

    return `
      <div class="sl-property-card" data-check-index="${index}">
        <div class="sl-property-header">
          <h3 class="sl-property-name">${propertyName}</h3>
          <span class="sl-property-status ${statusClass}">${statusText}</span>
        </div>
        <div class="sl-property-description">
          ${check.details || "No additional details available."}
        </div>
        ${this.getPropertySpecificDetails(check)}
        ${counterexampleSection}
      </div>
    `;
  }

  getPropertyDisplayName(checkName) {
    const nameMap = {
      "Deadlock freedom": "P1: Deadlock Freedom",
      "Deadlock freedom (P1)": "P1: Deadlock Freedom", 
      "Deadlock Freedom (P1)": "P1: Deadlock Freedom",
      DeadlockFreedom: "P1: Deadlock Freedom",
      "Overfinal marking (P2)": "P2: No Overfinal Markings",
      "Overfinal Marking (P2)": "P2: No Overfinal Markings",
      OverfinalMarkings: "P2: No Overfinal Markings",
      "Dead transitions (P3)": "P3: No Dead Transitions",
      "Dead Transitions (P3)": "P3: No Dead Transitions", 
      DeadTransitions: "P3: No Dead Transitions",
      "Boundedness (Alg. 3)": "Boundedness Check",
      Boundedness: "Boundedness Check",
    };
    return nameMap[checkName] || checkName;
  }

  getPropertySpecificDetails(check) {
    let details = "";

    if (check.deadTransitions && check.deadTransitions.length > 0) {
      details += `<div class="sl-property-details">Dead transitions: ${check.deadTransitions.length}</div>`;
    }

    if (check.overfinalNodes && check.overfinalNodes.length > 0) {
      details += `<div class="sl-property-details">Overfinal states: ${check.overfinalNodes.length}</div>`;
    }

    if (check.violatingNodes && check.violatingNodes.length > 0) {
      details += `<div class="sl-property-details">Violating states: ${check.violatingNodes.length}</div>`;
    }

    return details;
  }

  getCounterexampleDescription(check) {
    if (check.trace && check.trace.length > 0) {
      return `Trace with ${check.trace.length} steps showing property violation`;
    }

    if (check.deadTransitions && check.deadTransitions.length > 0) {
      const transitions = check.deadTransitions
        .map((dt) => dt.transitionLabel || dt.transitionId)
        .join(", ");
      return `Dead transitions: ${transitions}`;
    }

    if (check.overfinalNodes && check.overfinalNodes.length > 0) {
      return `${check.overfinalNodes.length} state(s) with overfinal markings`;
    }

    return "Property violation detected";
  }

  createControlPanel() {
    return `
      <div class="sl-control-panel">
        <div class="sl-control-group">
          <button class="sl-btn sl-btn-secondary" id="sl-clear-highlights">
            Clear Highlights
          </button>
          <button class="sl-btn sl-btn-secondary" id="sl-export-results">
            Export Results
          </button>
        </div>
        <div class="sl-control-group">
          <button class="sl-btn sl-btn-primary" id="sl-rerun-verification">
            Run Again
          </button>
          <button class="sl-btn sl-btn-secondary" id="sl-close-to-view">
            Close to View Net
          </button>
        </div>
      </div>
    `;
  }

  createTimingSection(results) {
    const steps = results.verificationSteps || [];
    const stepsHTML = steps
      .slice(-5)
      .map(
        (step) => `
      <div class="sl-step">
        [${step.name}] ${step.details} (+${step.timestamp}ms)
      </div>
    `
      )
      .join("");

    return `
      <div class="sl-timing-info">
        <strong>Verification completed in ${results.duration || 0} ms</strong>
        ${
          steps.length > 0
            ? `
          <div class="sl-verification-steps">
            <strong>Recent Steps:</strong>
            ${stepsHTML}
          </div>
        `
            : ""
        }
      </div>
    `;
  }

  createErrorHTML(error) {
    return `
      <div class="sl-verification-status unsound">
        <div class="sl-status-icon">❌</div>
        <div class="sl-status-details">
          <h3>Verification Error</h3>
          <p>${
            error?.message ||
            error ||
            "An unexpected error occurred during verification."
          }</p>
        </div>
      </div>
      <div class="sl-control-panel">
        <button class="sl-btn sl-btn-primary" id="sl-rerun-verification">
          Try Again
        </button>
      </div>
    `;
  }

  /**
   * Attach event listeners to the results
   */
  attachEventListeners() {
    // Property card clicks and visualize buttons
    document.querySelectorAll(".sl-property-card").forEach((card, index) => {
      card.addEventListener("click", (e) => {
        if (!e.target.classList.contains("sl-visualize-btn")) {
          this.selectPropertyCard(index);
        }
      });
    });

    document.querySelectorAll(".sl-visualize-btn").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const index = parseInt(btn.getAttribute("data-check-index"));
        this.visualizeCheck(index);
      });
    });

    // Control panel buttons
    document.getElementById("sl-clear-highlights")?.addEventListener("click", () => {
      this.clearVisualization();
    });

    document.getElementById("sl-export-results")?.addEventListener("click", () => {
      this.exportResults();
    });

    document.getElementById("sl-rerun-verification")?.addEventListener("click", () => {
      this.closeModal();
      this.startVerification();
    });

    document.getElementById("sl-close-to-view")?.addEventListener("click", () => {
      this.closeModal();
      this.showNotification("HTML overlays show counterexamples directly on the Petri net. Drag them to reposition!");
    });
  }

  /**
   * Select a property card
   */
  selectPropertyCard(index) {
    // Remove active class from all cards
    document.querySelectorAll(".sl-property-card").forEach((card) => {
      card.classList.remove("active");
    });

    // Add active class to selected card
    const selectedCard = document.querySelector(
      `.sl-property-card[data-check-index="${index}"]`
    );
    if (selectedCard) {
      selectedCard.classList.add("active");
      this.activeCheckIndex = index;
    }
  }

  /**
   * Visualize a check result
   */
  visualizeCheck(index) {
    if (
      !this.currentResults ||
      !this.currentResults.checks ||
      index >= this.currentResults.checks.length
    ) {
      return;
    }

    this.selectPropertyCard(index);

    if (this.traceVisualizer) {
      const check = this.currentResults.checks[index];
      this.traceVisualizer.visualizeCheck(check);
      
      // Mark visualization as active
      this.isVisualizationActive = true;

      // Update button state
      const btn = document.querySelector(`[data-check-index="${index}"]`);
      if (btn) {
        btn.classList.add("active");
        btn.textContent = "Visualizing...";
      }

      // Show notification with instructions
      this.showNotification(
        `Visualizing ${this.getPropertyDisplayName(check.name)}. HTML overlays show counterexamples - drag them to reposition!`
      );

      // Update overlay counter
      setTimeout(() => this.updateOverlayCounter(), 100);
    }
  }

  /**
   * Clear visualization
   */
  clearVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
    }

    // Mark visualization as inactive
    this.isVisualizationActive = false;

    // Remove active class from all cards
    document.querySelectorAll(".sl-property-card").forEach((card) => {
      card.classList.remove("active");
    });

    // Reset visualize buttons
    document.querySelectorAll(".sl-visualize-btn").forEach((btn) => {
      btn.classList.remove("active");
      btn.textContent = "Visualize";
    });

    this.activeCheckIndex = -1;
    this.hideFloatingControls();
    this.showNotification("Visualization cleared");
  }

  /**
   * Export verification results
   */
  exportResults() {
    if (!this.currentResults) return;

    const exportData = {
      timestamp: new Date().toISOString(),
      petriNetId: this.app.api.petriNet.id,
      petriNetName: this.app.api.petriNet.name,
      isSound: this.currentResults.isSound,
      duration: this.currentResults.duration,
      checks: this.currentResults.checks,
      verificationSteps: this.currentResults.verificationSteps,
    };

    const blob = new Blob([JSON.stringify(exportData, null, 2)], {
      type: "application/json",
    });

    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `verification-results-${new Date().getTime()}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);

    this.showNotification("Results exported successfully");
  }

  /**
   * Show a brief notification
   */
  showNotification(message) {
    // Create and show a temporary notification
    const notification = document.createElement("div");
    notification.style.cssText = `
      position: fixed;
      top: 20px;
      right: 20px;
      background: linear-gradient(135deg, #5E81AC, #81A1C1);
      color: #ECEFF4;
      padding: 12px 20px;
      border-radius: 6px;
      z-index: 10000;
      font-size: 14px;
      font-weight: 500;
      box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
      transform: translateX(100%);
      transition: transform 0.3s ease;
      max-width: 300px;
    `;
    notification.textContent = message;

    document.body.appendChild(notification);

    // Animate in
    setTimeout(() => {
      notification.style.transform = "translateX(0)";
    }, 10);

    // Remove after delay
    setTimeout(() => {
      notification.style.transform = "translateX(100%)";
      setTimeout(() => {
        if (notification.parentNode) {
          document.body.removeChild(notification);
        }
      }, 300);
    }, 4000);
  }

  /**
   * Cleanup when component is destroyed
   */
  destroy() {
    this.clearVisualization();
    
    if (this.traceVisualizer) {
      this.traceVisualizer.destroy();
    }

    // Remove modal if it exists
    const modal = document.getElementById("sl-verification-modal");
    if (modal && modal.parentNode) {
      modal.parentNode.removeChild(modal);
    }

    // Remove floating controls
    const controls = document.getElementById("sl-floating-controls");
    if (controls && controls.parentNode) {
      controls.parentNode.removeChild(controls);
    }

    // Remove styles
    const styles = document.getElementById("sl-verification-styles");
    if (styles && styles.parentNode) {
      styles.parentNode.removeChild(styles);
    }
  }
}

// Export classes for use in the main application
window.SuvorovLomazovaTraceVisualizationRenderer = SuvorovLomazovaTraceVisualizationRenderer;
window.SuvorovLomazovaVerificationUI = SuvorovLomazovaVerificationUI;

export { SuvorovLomazovaTraceVisualizationRenderer, SuvorovLomazovaVerificationUI };

// Enhanced initialization script for HTML overlay system
document.addEventListener('DOMContentLoaded', () => {
  // Wait for the main app to be ready
  const initTimer = setInterval(() => {
    if (window.petriApp && window.petriApp.editor && window.petriApp.editor.renderer) {
      // Initialize the verification UI with HTML overlay system
      if (!window.suvorovLomazovaUI) {
        console.log("Initializing Suvorov-Lomazova Verification UI with HTML Overlay System");
        window.suvorovLomazovaUI = new SuvorovLomazovaVerificationUI(window.petriApp);
        
      }
      clearInterval(initTimer);
    }
  }, 100);

  // Enhanced canvas resize handling for overlay system
  let resizeTimeout;
  function handleCanvasResize() {
    clearTimeout(resizeTimeout);
    resizeTimeout = setTimeout(() => {
      if (window.suvorovLomazovaUI && 
          window.suvorovLomazovaUI.traceVisualizer && 
          window.suvorovLomazovaUI.isVisualizationActive) {
        // Update overlay positions after canvas resize
        window.suvorovLomazovaUI.traceVisualizer.updateHTMLOverlays();
      }
    }, 100);
  }

  // Listen for window resize events that might affect canvas
  window.addEventListener('resize', handleCanvasResize);
  
  // Listen for fullscreen toggle events
  document.addEventListener('keydown', (e) => {
    if ((e.key === 'F' && (e.ctrlKey || e.metaKey)) || e.key === 'F11') {
      setTimeout(handleCanvasResize, 300); // Delay to allow fullscreen transition
    }
  });
});

export default { SuvorovLomazovaTraceVisualizationRenderer, SuvorovLomazovaVerificationUI };