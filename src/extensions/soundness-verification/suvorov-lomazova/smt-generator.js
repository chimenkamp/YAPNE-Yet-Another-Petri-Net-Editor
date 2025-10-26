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
    // Don't strip outer parens - they're part of the SMT-LIB2 syntax
    return res.startsWith("(") ? res : `(${res})`;
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

export { SmtFromDpnGenerator };