import { SmtFromDpnGenerator } from './smt-generator.js';
import { DPNRefinementEngine } from './DPN-refinement-engine.js';
import { Z3Solver } from './z3-solver-wrapper.js';


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
      Z3Solver,
      (name, details, extra) => this.logStep(name, details, extra)
    );
    this.verificationSteps = [];
    this.startTime = 0;
    this.counterexampleTraces = [];
    
    const getFinalMarkingsFromPetriNet = (net) => {
      // Extract final markings from the Petri net
      let markings = [];
      let tempMarking = {};
      
      // Handle both Map and Array formats
      const places = net.places instanceof Map 
        ? Array.from(net.places.values())
        : Array.isArray(net.places) 
        ? net.places
        : [];
      
      for (const place of places) {
        if (place && place.id) {
          tempMarking[place.id] = place.finalMarking || 0;
        }
      }
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
    
    // Helper: convert infix expression to SMT-LIB2 format
    const toSmtLib = (expr) => {
      if (!expr || expr === "true" || expr === "false") return expr || "true";
      // If already in SMT-LIB2 format (starts with '('), return as-is
      if (expr.trim().startsWith("(")) return expr;
      // Otherwise, use the SmtFromDpnGenerator's conversion
      const gen = new SmtFromDpnGenerator();
      return gen._infixToSmt(expr);
    };

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

      // Convert pre and post to SMT-LIB2 format
      const preSmt = toSmtLib(t.precondition || "true");
      const postSmt = toSmtLib(postBody || "true");

      // τ-pre := ¬∃W.( pre ∧ post[v'↦v_w] ) ; if W=∅ then τ-pre := ¬(pre ∧ post)
      let tauPre;
      if (written.size === 0) {
        tauPre = `(not (and ${preSmt} ${postSmt}))`;
      } else {
        const binders = Array.from(written)
          .map((v) => `(${v}_w ${getSort(v)})`)
          .join(" ");
        tauPre = `(not (exists (${binders}) (and ${preSmt} ${postSmt})))`;
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

      // For tau transitions, copy arcs to create self-loops (marking stutter)
      // τ transitions should have the same enabling conditions as the original transition
      // but don't change the marking (input places = output places)
      for (const arc of (tauDpn.arcs || [])) {
        if (arc.target === t.id || arc.source === t.id) {
          const tauArc = {
            ...arc,
            id: `${arc.id}_tau_${t.id}`,
            source: arc.source === t.id ? makeTauId(t.id) : arc.source,
            target: arc.target === t.id ? makeTauId(t.id) : arc.target,
          };
          tauDpn.arcs.push(tauArc);
        }
      }
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

    console.log(`[P1 Check] LTS has ${lts.nodes.size} nodes, ${lts.edges.size} edges`);

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
    console.log(`[P1 Check] Initial node: ${initialNodeId}`);

    // --- 2) Forward Reachability (FR) with parents for witness path ---
    const parent = new Map();
    const reachableNodes = lts.getReachableNodes(initialNodeId, parent);
    const fr = new Set(reachableNodes);
    console.log(`[P1 Check] Forward reachable nodes: ${fr.size}`);

    // --- 3) Final nodes in FR ---
    const finalNodeIds = [];
    for (const nid of fr) {
      const n = lts.nodes.get(nid);
      if (n && this.isFinalMarking(n.marking)) {
        finalNodeIds.push(nid);
        console.log(`[P1 Check] Found final node: ${nid} with marking ${JSON.stringify(n.marking)}`);
      }
    }

    if (finalNodeIds.length === 0) {
      console.log(`[P1 Check] NO final nodes reachable! Expected final markings:`, this.finalMarkings);
      // Check all reachable node markings for debugging
      for (const nid of fr) {
        const n = lts.nodes.get(nid);
        console.log(`[P1 Check]   Node ${nid}: marking = ${JSON.stringify(n.marking)}, formula = ${n.formula}`);
      }
      
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

    console.log(`[P1 Check] Found ${finalNodeIds.length} final nodes in FR`);

    // --- 4) Backward reachability from finals (BR) ---
    const nodesThatCanReachFinal = lts.getNodesThatCanReach(finalNodeIds);
    const br = new Set(nodesThatCanReachFinal);
    console.log(`[P1 Check] Backward reachable nodes: ${br.size}`);

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
    this.debugLogs = []; // Initialize debug logs array
    this.counterexampleTraces = [];
    
    // Intercept console.log to capture all debug output
    const originalConsoleLog = console.log;
    const self = this;
    console.log = function(...args) {
      // Call original console.log
      originalConsoleLog.apply(console, args);
      
      // Extract category and message from log format like "[Category] message"
      const firstArg = String(args[0] || '');
      const categoryMatch = firstArg.match(/^\[([^\]]+)\]/);
      
      if (categoryMatch) {
        const category = categoryMatch[1];
        const message = firstArg.substring(categoryMatch[0].length).trim();
        const data = args.length > 1 ? args.slice(1) : null;
        
        self.debugLogs.push({
          category,
          level: 'debug',
          message,
          data,
          timestamp: Date.now() - self.startTime,
        });
      }
    };
    
    try {
      // Verification logic continues...
      const result = await this._performVerification(progressCallback);
      return result;
    } finally {
      // Restore original console.log
      console.log = originalConsoleLog;
    }
  }
  
  async _performVerification(progressCallback) {

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

    say("Running preliminary checks on LTS_N (P2 only - P3 requires refinement)...");
    const p2_pre = this.checkOverfinalMarkings(ltsN);
    if (!p2_pre.satisfied) {
      return this.createResult(false, [
        { ...p2_pre, name: p2_pre.name + " - Preliminary Check" },
      ]);
    }

    // NOTE: P3 (dead transitions) is NOT checked here because it requires refinement.
    // The original transitions might not fire in LTS_N due to unrefined guards.
    // P3 will be checked after refinement on the final LTS_{N_R^τ}.

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
    
    // Store the LTS for display in UI
    this.lts = ltsRtau;

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

    // Set data variables on Z3Solver so it knows the types
    if (dpn.dataVariables) {
      const varMap = new Map();
      for (const v of dpn.dataVariables) {
        varMap.set(v.name || v.id, v);
      }
      Z3Solver._globalDataVariables = varMap;
    }

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
    
    // Store the LTS for display in UI
    this.lts = ltsRtau;

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

  /**
   * Format log data for display in debug logs
   */
  _formatLogData(data) {
    if (typeof data === 'string') return data;
    if (typeof data === 'object') {
      try {
        return JSON.stringify(data, null, 2);
      } catch (e) {
        return String(data);
      }
    }
    return String(data);
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

  /**
   * Add a debug log entry (visible in the UI)
   * @param {string} category - Category of the log (e.g., 'Z3', 'LTS', 'Refinement')
   * @param {string} level - Log level ('info', 'debug', 'warn', 'error')
   * @param {string} message - Log message
   * @param {*} data - Additional data to log
   */
  debugLog(category, level, message, data) {
    if (!this.debugLogs) {
      this.debugLogs = [];
    }
    
    const logEntry = {
      category,
      level,
      message,
      data: data !== undefined ? data : null,
      timestamp: Date.now() - this.startTime,
    };
    
    this.debugLogs.push(logEntry);
    
    // Also keep console.log for developer console
    const prefix = `[${category}]`;
    if (data !== undefined && data !== null && data !== "") {
      console.log(prefix, message, data);
    } else {
      console.log(prefix, message);
    }
  }

  createResult(isSound, checks) {
    return {
      isSound,
      checks,
      counterexamples: this.counterexampleTraces,
      verificationSteps: this.verificationSteps,
      debugLogs: this.debugLogs || [],
      finalMarkings: this.finalMarkings,
      duration: Date.now() - this.startTime,
      lts: this.lts || null, // Include the LTS for display in UI
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

export { SuvorovLomazovaVerifier };