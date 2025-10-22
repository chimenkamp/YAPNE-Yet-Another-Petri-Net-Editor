class SmtFromDpnGenerator {
  /**
   * Generate an SMT-LIB2 string for a Data Petri Net with bounded unrolling, τ-transitions,
   * per-step data variables/markings, enabling, frame conditions, τ-guards (as ¬∃W.(pre ∧ post)),
   * incidence-based marking updates, optional final marking and coverage, and a concluding (check-sat).
   *
   * This version ensures postconditions with primed variables (e.g., x' > 0, y' = x + 15) are
   * rewritten to valid SMT symbols (step-indexed variables), so no apostrophes remain in the output.
   *
   * :param petriNetObj: Object matching the provided interfaces (places[], transitions[], arcs[], dataVariables[]).
   * :param params: Optional settings:
   *   {
   *     K?: number,
   *     logic?: string,
   *     coverage?: boolean,
   *     finalMarking?: { [placeId]: number },
   *     initialData?: { [varName]: number|boolean },
   *     sortsOverride?: { [key: string]: "Int"|"Real"|"Bool" }
   *   }
   * :return : of objects.
   * :return: SMT-LIB2 string.
   */
  generateSMT(petriNetObj, params = {}) {
    const cfg = this._normalizeConfig(petriNetObj, params);
    const {
      logic, K, placeIds, transIds, arcsIn, arcsOut, dataVarsMap, dataVarsList,
      initialMarking, finalMarking, initialData, coverage
    } = cfg;

    const lines = [];
    const out = (s) => lines.push(s);

    out(`(set-logic ${logic})`);
    out(`(define-fun K () Int ${K})`);

    for (let i = 0; i <= K; i++) {
      for (const [vName, sort] of dataVarsList) out(`(declare-const ${this._vStep(vName, i)} ${sort})`);
    }

    for (let i = 0; i <= K; i++) {
      for (const p of placeIds) out(`(declare-const ${this._mStep(p, i)} Int)`);
    }

    for (let i = 0; i < K; i++) {
      for (const t of transIds) {
        out(`(declare-const ${this._fStep(t, i)} Bool)`);
        out(`(declare-const ${this._ftStep(t, i)} Bool)`);
      }
    }

    out(`(define-fun b2i ((b Bool)) Int (ite b 1 0))`);
    out(`(define-fun nonneg ((x Int)) Bool (>= x 0))`);

    for (const p of placeIds) out(`(assert (= ${this._mStep(p, 0)} ${initialMarking[p] || 0}))`);

    for (const [vName, sort] of dataVarsList) {
      const val = (vName in initialData) ? initialData[vName] : undefined;
      if (typeof val !== "undefined") out(`(assert (= ${this._vStep(vName, 0)} ${this._lit(val, sort)}))`);
    }

    for (let i = 0; i <= K; i++) {
      const c = placeIds.map((p) => `(nonneg ${this._mStep(p, i)})`).join(" ");
      out(`(assert (and ${c}))`);
    }

    for (let i = 0; i < K; i++) {
      const sumFlags = transIds.map((t) => `(+ (b2i ${this._fStep(t, i)}) (b2i ${this._ftStep(t, i)}))`).join(" ");
      out(`(assert (= (+ ${sumFlags}) 1))`);

      for (const t of transIds) {
        const firedOrTau = `(or ${this._fStep(t, i)} ${this._ftStep(t, i)})`;
        const inArcs = arcsIn.get(t) || [];
        for (const [p, w] of inArcs) out(`(assert (=> ${firedOrTau} (>= ${this._mStep(p, i)} ${w})))`);
      }

      for (const t of transIds) {
        const preStr = cfg.transitionPre.get(t) || "";
        const postStr = cfg.transitionPost.get(t) || "";

        const preVis = this._rewriteGuard(preStr, i, dataVarsList, false);
        const postVis = this._rewriteGuard(postStr, i, dataVarsList, true);

        if (preVis) out(`(assert (=> ${this._fStep(t, i)} ${preVis}))`);
        if (postVis) out(`(assert (=> ${this._fStep(t, i)} ${postVis}))`);

        const writes = this._writtenVars(postStr, dataVarsList);
        for (const [vName] of dataVarsList) {
          if (!writes.has(vName)) out(`(assert (=> ${this._fStep(t, i)} (= ${this._vStep(vName, i + 1)} ${this._vStep(vName, i)})))`);
        }

        const tauInner = this._tauGuard(preStr, postStr, i, dataVarsList);
        if (tauInner) out(`(assert (=> ${this._ftStep(t, i)} ${tauInner}))`);
        for (const [vName] of dataVarsList) out(`(assert (=> ${this._ftStep(t, i)} (= ${this._vStep(vName, i + 1)} ${this._vStep(vName, i)})))`);
      }

      for (const p of placeIds) {
        const inflow = [];
        const outflow = [];
        for (const t of transIds) {
          for (const [pp, w] of (arcsOut.get(t) || [])) if (pp === p) {
            inflow.push(`(* ${w} (b2i ${this._fStep(t, i)}))`);
            inflow.push(`(* ${w} (b2i ${this._ftStep(t, i)}))`);
          }
          for (const [pp, w] of (arcsIn.get(t) || [])) if (pp === p) {
            outflow.push(`(* ${w} (b2i ${this._fStep(t, i)}))`);
            outflow.push(`(* ${w} (b2i ${this._ftStep(t, i)}))`);
          }
        }
        const infl = inflow.length ? `(+ ${inflow.join(" ")})` : "0";
        const outf = outflow.length ? `(+ ${outflow.join(" ")})` : "0";
        out(`(assert (= ${this._mStep(p, i + 1)} (+ ${this._mStep(p, i)} ${infl} (- ${outf}))))`);
      }
    }

    if (finalMarking) {
      for (const p of placeIds) out(`(assert (= ${this._mStep(p, K)} ${finalMarking[p] || 0}))`);
    }

    if (coverage && transIds.length > 0) {
      for (const t of transIds) {
        const ors = Array.from({ length: K }, (_, i) => this._fStep(t, i)).join(" ");
        out(`(assert (or ${ors}))`);
      }
    }

    out(`(check-sat)`);

    const smt = lines.join("\n");
    return this._sanitizePrimes(smt);
  }

  /**
   * Normalize configuration: collect ids, arcs, guards, sorts, initial/final markings and data.
   *
   * :param pn: Petri net object.
   * :param params: Additional parameters.
   * :return : of objects.
   * :return: Normalized configuration.
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
    for (const t of transIds) { arcsIn.set(t, []); arcsOut.set(t, []); }
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
      const sort = this._toSort(String(dv.type || "real").toLowerCase(), sortsOverride);
      dataVarsMap.set(v, sort);
    }
    const dataVarsList = Array.from(dataVarsMap.entries()).sort((a, b) => a[0].localeCompare(b[0]));

    const transitionPre = new Map();
    const transitionPost = new Map();
    for (const t of pn.transitions || []) {
      transitionPre.set(this._sym(t.id), String(t.precondition || "").trim());
      transitionPost.set(this._sym(t.id), String(t.postcondition || "").trim());
    }

    const initialMarking = {};
    for (const p of pn.places || []) initialMarking[this._sym(p.id)] = Number(p.tokens) || 0;

    let finalMarking = params.finalMarking || null;

    const initialData = {};
    for (const dv of pn.dataVariables || []) {
      const v = this._sym(dv.name || dv.id);
      if (typeof dv.currentValue !== "undefined" && dv.currentValue !== null) initialData[v] = dv.currentValue;
    }
    Object.assign(initialData, params.initialData || {});

    const coverage = Boolean(params.coverage);

    return {
      logic, K, placeIds, transIds, arcsIn, arcsOut,
      dataVarsMap, dataVarsList, transitionPre, transitionPost,
      initialMarking, finalMarking, initialData, coverage
    };
  }

  /**
   * Create τ-guard = ¬∃W.(pre_i ∧ post_i(with W)), ensuring all primes are replaced.
   *
   * :param preStr: Precondition string.
   * :param postStr: Postcondition string.
   * :param i: Step index.
   * :param dataVarsList: List of [varName, sort].
   * :return : of objects.
   * :return: SMT-LIB2 string for τ-guard or empty string.
   */
  _tauGuard(preStr, postStr, i, dataVarsList) {
    const pre = this._rewriteGuard(preStr, i, dataVarsList, false) || "true";
    const writes = this._writtenVars(postStr, dataVarsList);

    const boundDecls = [];
    for (const [vName, sort] of dataVarsList) if (writes.has(vName)) boundDecls.push(`(${this._wVar(vName)} ${sort})`);

    let postBody = String(postStr || "").trim();
    for (const [vName] of dataVarsList) {
      const rePrime = new RegExp(`\\b${this._escapeReg(vName)}\\s*'`, "g");
      postBody = postBody.replace(rePrime, this._wVar(vName));
    }

    const post = this._rewriteGuard(postBody, i, dataVarsList, false) || "true";
    const decls = boundDecls.length ? boundDecls.join(" ") : `(dummy_w Int)`;
    const postAdj = boundDecls.length ? post : "true";
    return `(not (exists (${decls}) (and ${pre} ${postAdj})))`;
  }

  /**
   * Rewrite a guard or postcondition to SMT-LIB2 with per-step variables.
   * Converts primed occurrences x' to step-indexed symbols so no apostrophes remain.
   *
   * :param guardStr: Guard or postcondition string.
   * :param i: Step index.
   * :param dataVarsList: List of [varName, sort].
   * :param isPost: Whether this is a postcondition (primed writes go to step i+1).
   * :return : of objects.
   * :return: SMT-LIB2 expression or empty string.
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
   * :param s: Input string.
   * :param i: Step index.
   * :param dataVarsList: List of [varName, sort].
   * :param isPost: Whether this is a postcondition.
   * :return : of objects.
   * :return: String with variables stepped, no apostrophes left for known variables.
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
   * :param expr: Infix-like expression.
   * :return : of objects.
   * :return: SMT-LIB2 s-expression.
   */
  _infixToSmt(expr) {
    const e = expr.trim();
    if (!e) return "";
    const norm = e.replace(/\s+/g, " ")
      .replace(/\band\b/gi, "and")
      .replace(/\bor\b/gi, "or")
      .replace(/\bnot\b/gi, "not");

    const splitTop = (s, op) => {
      const parts = [];
      let depth = 0, buf = [];
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
      if (t.startsWith("(") && t.endsWith(")")) return `(${rec(t.slice(1, -1))})`;
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
        if (["=", "<", "<=", ">", ">="].includes(op)) return `(${op} ${lhs} ${rhs})`;
      }
      return t;
    };

    const res = rec(norm);
    return res.startsWith("(") ? res : `(${res})`;
  }

  /**
   * Compute the set of written variables (those with a primed occurrence) in a postcondition.
   *
   * :param postStr: Postcondition string.
   * :param dataVarsList: List of [varName, sort].
   * :return : of objects.
   * :return: Set of variable names.
   */
  _writtenVars(postStr, dataVarsList) {
    const set = new Set();
    const s = String(postStr || "");
    for (const [vName] of dataVarsList) {
      if (new RegExp(`\\b${this._escapeReg(vName)}\\s*'`, "g").test(s)) set.add(vName);
    }
    return set;
  }

  /**
   * Map a domain type string to SMT sort with optional overrides.
   *
   * :param typ: Type string.
   * :param override: Mapping overrides.
   * :return : of objects.
   * :return: SMT sort string.
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
   * :param name: Base variable name.
   * :param i: Step index.
   * :return : of objects.
   * :return: Symbol string.
   */
  _vStep(name, i) {
    return `${this._sym(name)}_${i}`;
  }

  /**
   * Create a per-step marking symbol.
   *
   * :param placeId: Place identifier.
   * :param i: Step index.
   * :return : of objects.
   * :return: Symbol string.
   */
  _mStep(placeId, i) {
    return `M_${this._sym(placeId)}_${i}`;
  }

  /**
   * Create a per-step visible fire flag symbol.
   *
   * :param transId: Transition identifier.
   * :param i: Step index.
   * :return : of objects.
   * :return: Symbol string.
   */
  _fStep(transId, i) {
    return `f_${this._sym(transId)}_${i}`;
  }

  /**
   * Create a per-step tau fire flag symbol.
   *
   * :param transId: Transition identifier.
   * :param i: Step index.
   * :return : of objects.
   * :return: Symbol string.
   */
  _ftStep(transId, i) {
    return `f_tau_${this._sym(transId)}_${i}`;
  }

  /**
   * Create a bound variable name for τ existential.
   *
   * :param vName: Variable base name.
   * :return : of objects.
   * :return: Bound variable symbol.
   */
  _wVar(vName) {
    return `${this._sym(vName)}_w`;
  }

  /**
   * Final safety pass: ensure no apostrophes remain in identifiers (Z3 doesn't allow them).
   * Any residual pattern like name' is rewritten to name_prime.
   *
   * :param smt: SMT-LIB string.
   * :return : of objects.
   * :return: Sanitized SMT-LIB string.
   */
  _sanitizePrimes(smt) {
    return smt.replace(/([A-Za-z_][A-Za-z0-9_]*)\s*'/g, (_, id) => `${id}_prime`);
  }

  /**
   * Sanitize identifiers to SMT-LIB friendly symbols.
   *
   * :param x: Raw identifier.
   * :return : of objects.
   * :return: Sanitized symbol.
   */
  _sym(x) {
    return String(x).replace(/[^A-Za-z0-9_]/g, "_");
  }

  /**
   * Escape a string for use in RegExp.
   *
   * :param s: Input string.
   * :return : of objects.
   * :return: Escaped string.
   */
  _escapeReg(s) {
    return String(s).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  }

  /**
   * Render a literal according to sort.
   *
   * :param v: Value.
   * :param sort: SMT sort.
   * :return : of objects.
   * :return: SMT-LIB literal.
   */
  _lit(v, sort) {
    if (sort === "Bool") return v ? "true" : "false";
    if (typeof v === "number") return Number.isFinite(v) ? `${v}` : "0";
    if (typeof v === "boolean") return v ? "true" : "false";
    return `${v}`;
  }
}
export { SmtFromDpnGenerator };


// const dpnStringSat = "{\"id\":\"net1\",\"name\":\"Digital whiteboard: transfer\",\"description\":\"\",\"places\":[{\"id\":\"start\",\"position\":{\"x\":-600,\"y\":-350},\"label\":\"start\",\"tokens\":1,\"capacity\":null,\"radius\":20},{\"id\":\"p1\",\"position\":{\"x\":-400,\"y\":-150},\"label\":\"p1\",\"tokens\":0,\"capacity\":null,\"radius\":20},{\"id\":\"p2\",\"position\":{\"x\":-200,\"y\":-150},\"label\":\"p2\",\"tokens\":0,\"capacity\":null,\"radius\":20},{\"id\":\"p3\",\"position\":{\"x\":0,\"y\":-150},\"label\":\"p3\",\"tokens\":0,\"capacity\":null,\"radius\":20},{\"id\":\"p4\",\"position\":{\"x\":200,\"y\":-150},\"label\":\"p4\",\"tokens\":0,\"capacity\":null,\"radius\":20},{\"id\":\"p5\",\"position\":{\"x\":400,\"y\":-150},\"label\":\"p5\",\"tokens\":0,\"capacity\":null,\"radius\":20},{\"id\":\"end\",\"position\":{\"x\":600,\"y\":-150},\"label\":\"end\",\"tokens\":0,\"capacity\":null,\"radius\":20}],\"transitions\":[{\"id\":\"bed1\",\"position\":{\"x\":-500,\"y\":-350},\"label\":\"bed status\",\"width\":20,\"height\":50,\"isEnabled\":true,\"priority\":1,\"delay\":0,\"precondition\":\"\",\"postcondition\":\"org1' > 0\"},{\"id\":\"bed2\",\"position\":{\"x\":-300,\"y\":-350},\"label\":\"bed status\",\"width\":20,\"height\":50,\"isEnabled\":false,\"priority\":1,\"delay\":0,\"precondition\":\"\",\"postcondition\":\"org2' > 0\"},{\"id\":\"eom1\",\"position\":{\"x\":-100,\"y\":-350},\"label\":\"Eom\",\"width\":20,\"height\":50,\"isEnabled\":false,\"priority\":1,\"delay\":0,\"precondition\":\"\",\"postcondition\":\"roomTransfer' = true\"},{\"id\":\"eom2\",\"position\":{\"x\":100,\"y\":-350},\"label\":\"Eom\",\"width\":20,\"height\":50,\"isEnabled\":false,\"priority\":1,\"delay\":0,\"precondition\":\"\",\"postcondition\":\"roomTransfer' = true\"},{\"id\":\"tra1\",\"position\":{\"x\":300,\"y\":-350},\"label\":\"Transfer\",\"width\":20,\"height\":50,\"isEnabled\":false,\"priority\":1,\"delay\":0,\"precondition\":\"org1 != 207\",\"postcondition\":\"\"},{\"id\":\"tra2\",\"position\":{\"x\":500,\"y\":-350},\"label\":\"Transfer\",\"width\":20,\"height\":50,\"isEnabled\":false,\"priority\":1,\"delay\":0,\"precondition\":\"org1 != 207\",\"postcondition\":\"\"}],\"arcs\":[{\"id\":\"252bb7b2-6fce-42a3-bd35-359f046403c7\",\"source\":\"start\",\"target\":\"bed1\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"facafde5-87a1-492b-b6e7-21ecf3c859f0\",\"source\":\"bed1\",\"target\":\"p1\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"2df0fbbb-0499-47aa-8792-b81a38675f37\",\"source\":\"p1\",\"target\":\"bed2\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"f33c1710-04f7-4bdf-b0a2-cd5bace9ac0f\",\"source\":\"bed2\",\"target\":\"p2\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"2f799c40-357b-4cc5-bbb6-4819c1fe0f92\",\"source\":\"p2\",\"target\":\"eom1\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"a13af8a1-817d-4e9e-bcaf-b1e6f09bdf5c\",\"source\":\"eom1\",\"target\":\"p3\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"0a544666-1a54-4fde-afdd-1499fbd04ec6\",\"source\":\"p3\",\"target\":\"eom2\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"698214a5-bc8f-478a-9ac7-61d210f36a40\",\"source\":\"eom2\",\"target\":\"p4\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"093a9fef-61aa-44f8-ae27-14689b246c16\",\"source\":\"p4\",\"target\":\"tra1\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"162d2464-c1a5-4ef2-80e1-a69ce26e9257\",\"source\":\"tra1\",\"target\":\"p5\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"5e8e1eee-2abd-43d9-b843-3f72dc65f058\",\"source\":\"p5\",\"target\":\"tra2\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"},{\"id\":\"bcb75f6d-81b9-44e8-b54d-e0a65ded2872\",\"source\":\"tra2\",\"target\":\"end\",\"weight\":1,\"type\":\"regular\",\"points\":[],\"label\":\"1\"}],\"dataVariables\":[{\"id\":\"da368d15-8108-4867-9e5f-5be16716ceb2\",\"name\":\"org1\",\"type\":\"int\",\"currentValue\":1,\"description\":\"\"},{\"id\":\"e161c7b3-e5d8-4a44-aec6-981c51e8f7d6\",\"name\":\"org2\",\"type\":\"int\",\"currentValue\":1,\"description\":\"\"},{\"id\":\"16b8727b-5877-4b4d-9605-4f110cfa28a9\",\"name\":\"roomTransfer\",\"type\":\"boolean\",\"currentValue\":true,\"description\":\"\"}]}"

// fetch("http://localhost:5173/src/test.json")
//   .then(response => response.text())
//   .then(data => {
//     const dpn = JSON.parse(data);

//     const generator = new SmtFromDpnGenerator();
//     const smtString = generator.generateSMT(dpn);

//     console.log("Generated SMT-LIB2 string:\n", smtString);
//   })
//   .catch(error => console.error("Error fetching or parsing DPN:", error));


