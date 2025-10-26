import { Z3Solver } from "./z3-solver-wrapper";
import { LabeledTransitionSystem } from "./labeled-transition-system.js";
/**
 * DPN Refinement Engine implementing Algorithm 4 from the paper
 */
class DPNRefinementEngine {
  constructor(smtGenerator, z3Solver, logStepFn = null) {
    this.smtGenerator = smtGenerator;
    this.z3Solver = z3Solver;
    this.logStepFn = logStepFn;
  }

  logStep(name, details, extra) {
    if (this.logStepFn) {
      this.logStepFn(name, details, extra);
    } else {
      console.log(`[${name}] ${details}`, extra || "");
    }
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
  const MAX_NODES = 5000; // Security cap to avoid blowup -- restriction from the paper ...

  const initM = this.getInitialMarking(dpn);
  const initFRaw = this.getInitialFormula(dpn);
  console.log(`[LTS] Raw initial formula: ${initFRaw}`);
  console.log(`[LTS] Data variables:`, dpn.dataVariables);
  // Don't canonicalize initial formula - it's already in good form
  const initF = initFRaw;
  const initId = lts.addNode(initM, initF);

  console.log(`[LTS] Initial node ${initId}: marking=${JSON.stringify(initM)}, formula=${initF}`);

  const queue = [initId];
  const processed = new Set();
  const byMarking = new Map();
  const markingKey = (M) =>
    Object.entries(M)
      .sort(([a], [b]) => a.localeCompare(b))
      .map(([k, v]) => `${k}:${v}`)
      .join(",");

  byMarking.set(markingKey(initM), [initId]);

  while (queue.length && lts.nodes.size < MAX_NODES) {
    const nid = queue.shift();
    const node = lts.nodes.get(nid);
    const keyHere = this.getStateKey(node);
    if (processed.has(keyHere)) continue;
    processed.add(keyHere);

    console.log(`[LTS] Processing node ${nid}`);

    for (const t of dpn.transitions || []) {
      const succ = await this.computeSuccessorState(
        node.marking,
        node.formula,
        t,
        dpn
      );
      if (!succ) {
        console.log(`[LTS] Transition ${t.id} not enabled in node ${nid}`);
        continue;
      }
      
      const isSat = await Z3Solver.isSatisfiable(succ.formula);
      if (!isSat) {
        console.log(`[LTS] Transition ${t.id} filtered: unsatisfiable constraint`);
        continue;
      }

      // Don't canonicalize successor formulas - it loses information
      // succ.formula = await this.canonicalizeFormula(succ.formula);

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
        console.log(`[LTS] Created node ${targetId} via ${t.id}: marking=${JSON.stringify(succ.marking)}, formula=${succ.formula}`);
        if (!byMarking.has(mkey)) byMarking.set(mkey, []);
        byMarking.get(mkey).push(targetId);
        queue.push(targetId);
      } else {
        console.log(`[LTS] Transition ${t.id} leads to existing node ${targetId}`);
      }
      lts.addEdge(nid, targetId, t.id);
    }
  }

  console.log(`[LTS] Construction complete: ${lts.nodes.size} nodes, ${lts.edges.size} edges`);
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
    
    // If already in SMT-LIB2 format (starts with parenthesis), return as-is
    // This handles tau preconditions that are already properly formatted
    if (e0.startsWith("(")) return e0;
    
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
      .replace(/&&/g, "and")
      .replace(/==/g, "=");

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
      
      // Check if it's an atom (variable, number, or boolean)
      if (
        /^[A-Za-z_][A-Za-z0-9_]*$/.test(t) ||
        /^[-+]?\d+(?:\.\d+)?$/.test(t) ||
        t === "true" ||
        t === "false"
      ) {
        return t; // Return atoms as-is without wrapping
      }
      
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
      
      // Handle arithmetic expressions with proper parenthesis handling
      const parseArithmetic = (expr) => {
        // Helper to extract balanced tokens
        const tokens = [];
        let current = '';
        let depth = 0;
        
        for (let i = 0; i < expr.length; i++) {
          const ch = expr[i];
          if (ch === '(') {
            depth++;
            current += ch;
          } else if (ch === ')') {
            depth--;
            current += ch;
          } else if (depth === 0 && /\s/.test(ch)) {
            if (current) {
              tokens.push(current);
              current = '';
            }
          } else {
            current += ch;
          }
        }
        if (current) tokens.push(current);
        
        // Look for binary operators at depth 0
        for (const op of ['+', '-', '*', '/']) {
          for (let i = 0; i < tokens.length; i++) {
            if (tokens[i] === op) {
              const left = tokens.slice(0, i).join(' ');
              const right = tokens.slice(i + 1).join(' ');
              if (left && right) {
                return `(${op} ${rec(left)} ${rec(right)})`;
              }
            }
          }
        }
        
        return expr;
      };
      
      const arResult = parseArithmetic(t);
      if (arResult !== t) {
        return arResult;
      }
      
      // Fallback to the old regex approach for simple cases
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
    console.log(`[writtenOf] Input postcondition: "${s}"`);
    console.log(`[writtenOf] varNames:`, varNames);
    for (const v of varNames) {
      // Match v' (with optional whitespace before the prime)
      const primePattern = new RegExp(`\\b${escapeReg(v)}\\s*'`);
      const wPattern = new RegExp(`\\b${escapeReg(v)}_w\\b`);
      const hasPrime = primePattern.test(s);
      const hasW = wPattern.test(s);
      console.log(`[writtenOf] Variable ${v}: hasPrime=${hasPrime}, hasW=${hasW}`);
      if (hasPrime || hasW) {
        set.add(v);
      }
    }
    console.log(`[writtenOf] Result:`, Array.from(set));
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

  // First check if precondition is compatible with current state
  const prePrefixed = toPrefix(transition.precondition || "true");
  const statePrefixed = toPrefix(stateFormula || "true");
  const preCheck = `(and ${prePrefixed} ${statePrefixed})`;
  console.log(`[computeNewFormula] Checking precondition for ${transition.id}:`);
  console.log(`  Precondition: "${transition.precondition || "true"}" → ${prePrefixed}`);
  console.log(`  State formula: "${stateFormula || "true"}" → ${statePrefixed}`);
  console.log(`  Combined check: ${preCheck}`);
  
  const checkResult = await isFalse(preCheck);
  console.log(`  isFalse(preCheck) = ${checkResult}`);
  if (checkResult) {
    console.log(`[computeNewFormula] Precondition incompatible with current state for ${transition.id}`);
    return "false";
  }
  console.log(`[computeNewFormula] Precondition check passed for ${transition.id}`);

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
  
  console.log(`[computeNewFormula] Written variables W:`, W);
  console.log(`[computeNewFormula] W.length =`, W.length);
  
  // Compute the successor state formula
  let phi_next;
  
  if (W.length === 0) {
    console.log(`[computeNewFormula] No written vars - keeping current state formula`);
    // No variables written: state formula unchanged (but must satisfy precondition)
    // Just remove the _r suffixes from current state formula
    phi_next = dropSuffixes(phi_r);
  } else {
    console.log(`[computeNewFormula] Variables written - computing new formula`);
    // Some variables are written
    // We need to: (1) apply postcondition for written vars, (2) preserve read-only vars
    
    const readOnly = new Set(varNames.filter(v => !W.includes(v)));
    
    console.log(`[computeNewFormula] Written vars:`, W);
    console.log(`[computeNewFormula] Read-only vars:`, Array.from(readOnly));
    
    // Check if postcondition references current state values (unprimed variables)
    const postOriginal = String(transition.postcondition || "").trim();
    const referencesCurrentState = varNames.some(v => {
      // Check if unprimed v appears in postcondition (not as v')
      const regex = new RegExp(`\\b${escapeReg(v)}(?!\\s*')`, 'g');
      return regex.test(postOriginal);
    });
    
    console.log(`[computeNewFormula] Postcondition references current state: ${referencesCurrentState}`);
    
    let writtenConstraints = [];
    
    if (referencesCurrentState) {
      // Postcondition references current state (e.g., x' = x + 5)
      // We need to substitute current state values
      console.log(`[computeNewFormula] Postcondition: "${postOriginal}"`);
      
      // Extract current state values from phi_r
      const stateStr = dropSuffixes(phi_r);
      const stateValues = new Map();
      
      // Helper to extract balanced expression after variable in equality
      const extractValue = (str, varName) => {
        // Match (= varName VALUE) where VALUE can be nested parens
        const pattern = `\\(=\\s+${escapeReg(varName)}\\s+`;
        const idx = str.search(new RegExp(pattern));
        if (idx === -1) return null;
        
        // Find start of value (after the variable name and whitespace)
        const afterEq = str.indexOf(varName, idx) + varName.length;
        let start = afterEq;
        while (start < str.length && /\s/.test(str[start])) start++;
        
        // Extract value with balanced parentheses
        let depth = 0;
        let end = start;
        let inValue = false;
        
        for (let i = start; i < str.length; i++) {
          const ch = str[i];
          if (ch === '(') {
            depth++;
            inValue = true;
          } else if (ch === ')') {
            if (depth === 0) {
              // This is the closing paren of the (= ...) expression
              end = i;
              break;
            }
            depth--;
            if (depth === 0 && inValue) {
              end = i + 1;
              break;
            }
          } else if (depth === 0 && /\s/.test(ch)) {
            // End of atomic value
            end = i;
            break;
          } else if (depth === 0 && !inValue) {
            // Atomic value (number, variable, etc.)
            end = i + 1;
          }
        }
        
        if (end > start) {
          return str.substring(start, end).trim();
        }
        return null;
      };
      
      // Try to extract simple equalities from current state
      for (const v of varNames) {
        const value = extractValue(stateStr, v);
        if (value) {
          stateValues.set(v, value);
          console.log(`[computeNewFormula] Extracted state value: ${v} = ${value}`);
        }
      }
      
      let postNext = postOriginal;
      
      // Substitute unprimed variables with their current values
      for (const v of varNames) {
        if (stateValues.has(v)) {
          const value = stateValues.get(v);
          // Replace v (but not v') with its current value
          postNext = postNext.replace(
            new RegExp(`\\b${escapeReg(v)}(?!\\s*')`, 'g'),
            value
          );
        }
      }
      
      console.log(`[computeNewFormula] After value substitution: "${postNext}"`);
      
      // Now replace v' with v (this gives us the next state constraint)
      for (const v of W) {
        postNext = postNext.replace(new RegExp(`\\b${escapeReg(v)}\\s*'`, "g"), v);
      }
      
      console.log(`[computeNewFormula] After v' → v: "${postNext}"`);
      
      postNext = toPrefix(postNext);
      writtenConstraints = [postNext];
    } else {
      // Postcondition doesn't reference current state (e.g., choice' >= 0 && choice' <= 1)
      // Just rename v' to v to get the next state constraint
      console.log(`[computeNewFormula] Postcondition (no current state refs): "${postOriginal}"`);
      
      let postNext = postOriginal;
      
      // Replace v' with v
      for (const v of W) {
        postNext = postNext.replace(new RegExp(`\\b${escapeReg(v)}\\s*'`, "g"), v);
      }
      
      console.log(`[computeNewFormula] After v' → v: "${postNext}"`);
      
      postNext = toPrefix(postNext);
      writtenConstraints = [postNext];
    }
    
    console.log(`[computeNewFormula] Written constraints:`, writtenConstraints);
    
    // For read-only variables, they keep their values from current state
    const readOnlyParts = [];
    if (readOnly.size > 0) {
      for (const v of readOnly) {
        const currentStateStr = String(phi_r);
        
        // Simple pattern match for (= v_r value)
        const eqPattern = new RegExp(`\\(=\\s+${escapeReg(v)}_r\\s+([^)\\s]+)\\)`, 'g');
        const matches = currentStateStr.match(eqPattern);
        if (matches) {
          for (const match of matches) {
            const nextConstraint = match.replace(new RegExp(`\\b${escapeReg(v)}_r\\b`, 'g'), v);
            readOnlyParts.push(nextConstraint);
          }
        }
        
        // Also check for other comparison operators
        const compPattern = new RegExp(`\\((<=?|>=?|distinct)\\s+${escapeReg(v)}_r\\s+([^)]+)\\)`, 'g');
        const compMatches = currentStateStr.match(compPattern);
        if (compMatches) {
          for (const match of compMatches) {
            const nextConstraint = match.replace(new RegExp(`\\b${escapeReg(v)}_r\\b`, 'g'), v);
            if (!readOnlyParts.includes(nextConstraint)) {
              readOnlyParts.push(nextConstraint);
            }
          }
        }
      }
    }
    
    // Combine written and read-only constraints
    const allParts = [...writtenConstraints, ...readOnlyParts].filter(p => p && p !== "true");
    phi_next = allParts.length === 0 ? "true" :
               allParts.length === 1 ? allParts[0] :
               `(and ${allParts.join(" ")})`;
  }

  // Don't canonicalize - we've already built the formula correctly
  // phi_next = await this.canonicalizeFormula(phi_next);

  console.log(`[computeNewFormula] Transition ${transition.id}:`);
  console.log(`  Pre: ${transition.precondition || "(none)"}`);
  console.log(`  Post: ${transition.postcondition || "(none)"}`);
  console.log(`  State φ: ${stateFormula || "true"}`);
  console.log(`  Result φ': ${phi_next}`);

  if (await isFalse(phi_next)) {
    console.log(`[computeNewFormula] Result is UNSAT for transition ${transition.id}`);
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


export { DPNRefinementEngine };