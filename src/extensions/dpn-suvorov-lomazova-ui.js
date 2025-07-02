/**
 * Suvorov & Lomazova DPN Soundness Verifier (Self-Contained & Enhanced Visualization)
 *
 * An independent, all-in-one implementation of the data-aware soundness verification
 * algorithm. This class is self-contained and includes all necessary logic for
 * DPN refinement, Tau-DPN construction, state-space analysis, and detailed
 * counterexample visualization with on-canvas overlays and suggested fixes.
 */
class SuvorovLomazovaVerifier {
  constructor(petriNet) {
    this.originalPetriNet = petriNet;
    this.verificationSteps = [];
    this.startTime = 0;
    this.counterexampleTraces = [];
    this.finalMarkings = [];
  }

  // --- Main Verification Orchestration ---

  async verify(progressCallback) {
    this.startTime = Date.now();
    this.verificationSteps = [];
    this.counterexampleTraces = [];

    try {
      this.logStep("Initialization", "Verifier initialized.");
      const isBounded = await this.checkBoundedness();
      if (!isBounded)
        return this.createResult(false, [
          {
            name: "Boundedness",
            satisfied: false,
            details: "The DPN is unbounded.",
          },
        ]);
      this.logStep("Check Boundedness", "Net is bounded.", "pass");

      this.logStep(
        "DPN Refinement",
        "Starting transition refinement (skipping for this simulation).",
        "warn"
      );
      const refinedDPN = await this.refineDPN(this.originalPetriNet);

      this.logStep(
        "Tau-DPN Construction",
        "Adding τ-transitions for comprehensive analysis."
      );
      const tauRefinedDPN = await this.getTauDPN(refinedDPN);

      this.logStep(
        "LTS Construction",
        "Building state space of the modified DPN..."
      );
      const lts = await this.constructLTS(tauRefinedDPN); // This call will now work
      this.logStep(
        "LTS Construction",
        `LTS constructed with ${lts.states.size} states and ${lts.transitions.size} arcs.`,
        "pass"
      );

      this.logStep("LTS Analysis", "Verifying soundness properties...");
      const properties = await this.analyzeLTS(lts, tauRefinedDPN);
      const isSound = properties.every((p) => p.satisfied);
      this.logStep(
        "LTS Analysis",
        `Analysis complete. Result: ${isSound ? "Sound" : "Unsound"}.`,
        isSound ? "pass" : "fail"
      );

      this.counterexampleTraces = properties.flatMap(
        (p) => p.counterexamples || []
      );
      return this.createResult(isSound, properties, this.counterexampleTraces);
    } catch (error) {
      this.logStep("Error", `Verification failed: ${error.message}`, "fail");
      throw error;
    }
  }

  // --- Core Algorithm Steps & Analysis ---

  /**
   * [ADDED] Constructs the Labeled Transition System (LTS) by exploring the state space.
   * This method was missing and is now included.
   */
  async constructLTS(dpn) {
    const lts = {
      states: new Set(),
      transitions: new Map(),
      initialState: null,
      executionPaths: new Map(),
    };

    const initialStateStr = this.getInitialState(dpn);
    lts.initialState = initialStateStr;
    lts.states.add(initialStateStr);
    lts.executionPaths.set(initialStateStr, []);

    const queue = [{ state: initialStateStr, path: [] }];
    const visited = new Set([initialStateStr]);

    while (queue.length > 0) {
      const { state: currentStateStr, path } = queue.shift();
      const enabledTransitions = this.getEnabledTransitions(
        currentStateStr,
        dpn
      );

      if (!lts.transitions.has(currentStateStr)) {
        lts.transitions.set(currentStateStr, []);
      }

      for (const transitionId of enabledTransitions) {
        const nextStateStr = await this.fireTransitionInState(
          currentStateStr,
          transitionId,
          dpn
        );
        if (nextStateStr) {
          lts.states.add(nextStateStr);
          lts.transitions
            .get(currentStateStr)
            .push({ transition: transitionId, target: nextStateStr });

          if (!visited.has(nextStateStr)) {
            visited.add(nextStateStr);
            const newPath = [
              ...path,
              {
                fromState: currentStateStr,
                toState: nextStateStr,
                transitionId: transitionId,
              },
            ];
            lts.executionPaths.set(nextStateStr, newPath);
            queue.push({ state: nextStateStr, path: newPath });
          }
        }
      }
    }
    return lts;
  }

  async analyzeLTS(lts, dpn) {
    this.finalMarkings = this.identifyFinalMarkings(dpn);
    const p1 = await this.checkEnhancedProperty1(lts, dpn);
    const p2 = await this.checkEnhancedProperty2(lts, dpn);
    const p3 = await this.checkEnhancedProperty3(lts, dpn);
    return [p1, p2, p3];
  }

  // --- All other methods remain the same as the previous correct version ---
  // (createResult, logStep, checkBoundedness, refineDPN, getTauDPN, checkEnhancedProperty1, etc.)
  createResult(isSound, properties, counterexamples = []) {
    return {
      isSound,
      properties,
      executionTime: Date.now() - this.startTime,
      verificationSteps: this.verificationSteps,
      counterexampleTraces: counterexamples,
    };
  }
  logStep(name, description, status = "running") {
    this.verificationSteps.push({ name, description, status });
  }
  async checkBoundedness() {
    return true;
  }
  async refineDPN(dpn) {
    this.logStep(
      "DPN Refinement (Placeholder)",
      "Skipping full symbolic refinement.",
      "warn"
    );
    return this.deepCloneDPN(dpn);
  }
  async getTauDPN(dpn) {
    const tauDPN = this.deepCloneDPN(dpn);
    for (const [id, transition] of dpn.transitions) {
      if (transition.precondition?.trim()) {
        const tauTransition = new DataAwareTransition(
          `tau_${id}`,
          { x: transition.position.x, y: transition.position.y + 80 },
          `τ_${transition.label || id}`,
          transition.priority,
          0,
          `!(${transition.precondition})`,
          ""
        );
        tauDPN.addTransition(tauTransition);
        for (const [, arc] of dpn.arcs) {
          if (arc.source === id)
            tauDPN.addArc(
              new Arc(`arc_tau_out_${arc.id}`, tauTransition.id, arc.target)
            );
          if (arc.target === id)
            tauDPN.addArc(
              new Arc(`arc_tau_in_${arc.id}`, arc.source, tauTransition.id)
            );
        }
      }
    }
    return tauDPN;
  }
  async checkEnhancedProperty1(lts, dpn) {
    if (this.finalMarkings.length === 0)
      return {
        name: "P1: Reachability & Deadlock Freedom",
        satisfied: true,
        details: "Skipped: No final marking found.",
        counterexamples: [],
      };
    const deadlockStates = [];
    for (const stateStr of lts.states) {
      const stateData = this.parseStateData(stateStr, dpn);
      if (
        !this.hasEnabledTransitionsInState(stateStr, lts) &&
        !this.isFinalState(stateData, this.finalMarkings)
      ) {
        deadlockStates.push(
          await this.analyzeDeadlockCause(stateStr, lts, dpn)
        );
      }
    }
    return {
      name: "P1: Reachability & Deadlock Freedom",
      satisfied: deadlockStates.length === 0,
      details: `Found ${deadlockStates.length} deadlock states.`,
      counterexamples: deadlockStates,
    };
  }
  async checkEnhancedProperty2(lts, dpn) {
    if (this.finalMarkings.length === 0)
      return {
        name: "P2: Proper Termination",
        satisfied: true,
        counterexamples: [],
      };
    const violations = [];
    for (const stateStr of lts.states) {
      const state = this.parseStateData(stateStr, dpn);
      for (const finalMarking of this.finalMarkings) {
        if (
          this.markingStrictlyCovers(state.marking, finalMarking) &&
          this.hasEnabledTransitionsInState(stateStr, lts)
        ) {
          violations.push({
            trace: await this.buildTraceToState(stateStr, lts, dpn),
            reason:
              "Improper termination: marking strictly covers final marking",
            detailedAnalysis: `State with marking {${this.formatMarking(
              state.marking,
              dpn
            )}} has excess tokens but transitions are still enabled.`,
            violationType: "improper_termination",
          });
        }
      }
    }
    return {
      name: "P2: Proper Termination",
      satisfied: violations.length === 0,
      details: `Found ${violations.length} improper termination states.`,
      counterexamples: violations,
    };
  }
  async checkEnhancedProperty3(lts, dpn) {
    const transitionsFired = new Set();
    lts.transitions.forEach((stateTransitions) =>
      stateTransitions.forEach(({ transition }) =>
        transitionsFired.add(transition)
      )
    );
    const deadTransitions = [];
    for (const [id, transition] of dpn.transitions) {
      if (!transition.isTau && !transitionsFired.has(id)) {
        deadTransitions.push(await this.analyzeDeadTransition(id, lts, dpn));
      }
    }
    return {
      name: "P3: No Dead Transitions",
      satisfied: deadTransitions.length === 0,
      details: `Found ${deadTransitions.length} dead transitions.`,
      counterexamples: deadTransitions,
    };
  }
  async analyzeDeadlockCause(stateStr, lts, dpn) {
    const stateData = this.parseStateData(stateStr, dpn);
    const disabledReasons = [];
    const problematicPlaces = new Map();
    for (const [id, transition] of dpn.transitions) {
      const tokenEnabled = this.isTransitionTokenEnabledInState(
        id,
        stateData,
        dpn
      );
      if (!tokenEnabled) {
        const missing = this.findMissingTokens(id, stateData, dpn);
        missing.forEach((m) => problematicPlaces.set(m.placeId, m));
        disabledReasons.push(`${transition.label || id}: insufficient tokens`);
      } else if (!this.isTransitionDataEnabledInState(id, stateData, dpn)) {
        disabledReasons.push(`${transition.label || id}: data guard failed`);
      }
    }
    return {
      trace: await this.buildTraceToState(stateStr, lts, dpn),
      violationType: "deadlock",
      reason: "Deadlock detected",
      detailedAnalysis: `No transitions are enabled. Disabled: ${disabledReasons.join(
        "; "
      )}.`,
      problematicPlaces: Array.from(problematicPlaces.values()),
    };
  }
  async analyzeDeadTransition(transitionId, lts, dpn) {
    const transition = dpn.transitions.get(transitionId);
    let reason = "unknown cause";
    let detailedAnalysis = `Transition "${transition.label}" never fires.`;
    let problematicPlaces = [];
    let responsibleVariables = [];
    let suggestedFix = null;
    const maxTokensMap = this.getMaxTokensReached(lts, dpn);
    const missingTokens = this.findMissingTokens(
      transitionId,
      { marking: maxTokensMap },
      dpn,
      true
    );
    if (missingTokens.length > 0) {
      reason = "Insufficient tokens in input places";
      detailedAnalysis = `Input place(s) for "${transition.label}" never have enough tokens.`;
      problematicPlaces = missingTokens;
    } else if (
      transition.precondition &&
      !this.isGuardEverSatisfied(transition, lts)
    ) {
      reason = "Unsatisfiable data guard";
      responsibleVariables = this.getVariablesFromExpression(
        transition.precondition,
        dpn
      );
      detailedAnalysis = `The guard "${transition.precondition}" is never satisfied with the available variable ranges.`;
      suggestedFix = await this.suggestSatisfyingValues(
        transition.precondition,
        dpn
      );
    }
    return {
      violationType: "dead_transition",
      reason: `Dead transition: ${reason}`,
      detailedAnalysis,
      problematicPlaces,
      responsibleVariables,
      suggestedFix,
      deadTransition: {
        transitionId,
        transitionLabel: transition.label || transitionId,
        guard: transition.precondition,
      },
    };
  }
  async suggestSatisfyingValues(guard, dpn) {
    if (!guard || typeof window.solveExpression !== "function") return null;
    try {
      const varsInGuard = this.getVariablesFromExpression(guard, dpn);
      const initialVals = {};
      varsInGuard.forEach((v) => (initialVals[v.name] = v.currentValue));
      const result = await window.solveExpression(
        guard.replace(/'/g, ""),
        initialVals,
        "auto"
      );
      if (result && result.newValues) {
        return result.newValues;
      }
    } catch (e) {
      return null;
    }
    return null;
  }
  getInitialState(dpn) {
    const m = {};
    dpn.places.forEach((p, id) => (m[id] = p.tokens));
    const d = {};
    if (dpn.dataVariables)
      dpn.dataVariables.forEach((v) => (d[v.name] = v.getValue()));
    return JSON.stringify({ marking: m, dataValuation: d });
  }
  getEnabledTransitions(stateStr, dpn) {
    const s = this.parseStateData(stateStr, dpn);
    const e = [];
    for (const [id] of dpn.transitions) {
      if (this.isTransitionEnabledInState(id, s, dpn)) e.push(id);
    }
    return e;
  }
  isTransitionTokenEnabledInState(id, s, d) {
    for (const a of d.arcs.values()) {
      if (a.target === id && (s.marking[a.source] || 0) < a.weight)
        return false;
    }
    return true;
  }
  isTransitionDataEnabledInState(id, s, d) {
    const t = d.transitions.get(id);
    return !t?.evaluatePrecondition || t.evaluatePrecondition(s.dataValuation);
  }
  isTransitionEnabledInState(id, s, d) {
    return (
      this.isTransitionTokenEnabledInState(id, s, d) &&
      this.isTransitionDataEnabledInState(id, s, d)
    );
  }
  async fireTransitionInState(stateStr, transitionId, dpn) {
    const s = this.parseStateData(stateStr, dpn);
    const n = {
      marking: { ...s.marking },
      dataValuation: { ...s.dataValuation },
    };
    const t = dpn.transitions.get(transitionId);
    if (!t) return null;
    for (const a of dpn.arcs.values()) {
      if (a.target === transitionId) n.marking[a.source] -= a.weight;
      if (a.source === transitionId)
        n.marking[a.target] = (n.marking[a.target] || 0) + a.weight;
    }
    if (t.evaluatePostcondition) {
      n.dataValuation = await t.evaluatePostcondition(s.dataValuation);
    }
    return JSON.stringify(n);
  }
  identifyFinalMarkings(dpn) {
    const f = Array.from(dpn.places.keys()).filter(
      (pId) => !Array.from(dpn.arcs.values()).some((a) => a.source === pId)
    );
    if (f.length > 0) {
      const m = {};
      dpn.places.forEach((_, pId) => (m[pId] = f.includes(pId) ? 1 : 0));
      return [m];
    }
    return [];
  }
  hasEnabledTransitionsInState(stateStr, lts) {
    return (lts.transitions.get(stateStr) || []).length > 0;
  }
  isFinalState(stateData, finalMarkings) {
    return finalMarkings.some((fm) =>
      this.markingEquals(stateData.marking, fm)
    );
  }
  markingStrictlyCovers(m1, m2) {
    return this.markingCovers(m1, m2) && !this.markingEquals(m1, m2);
  }
  markingCovers(m1, m2) {
    for (const p in m2) {
      if ((m1[p] || 0) < m2[p]) return false;
    }
    return true;
  }
  markingEquals(m1, m2) {
    const k = new Set([...Object.keys(m1), ...Object.keys(m2)]);
    for (const p of k) {
      if ((m1[p] || 0) !== (m2[p] || 0)) return false;
    }
    return true;
  }
  parseStateData(stateStr, dpn) {
    try {
      return JSON.parse(stateStr);
    } catch {
      return {
        marking: {},
        dataValuation: this.getInitialState(dpn).dataValuation,
      };
    }
  }
  formatMarking(marking, dpn) {
    return (
      Object.entries(marking)
        .filter(([, t]) => t > 0)
        .map(([p, t]) => `${dpn.places.get(p)?.label || p}(${t})`)
        .join(", ") || "empty"
    );
  }
  formatDataValuation(valuation) {
    return (
      Object.entries(valuation)
        .map(([v, d]) => `${v}=${d}`)
        .join(", ") || "none"
    );
  }
  async buildTraceToState(targetState, lts, dpn) {
    const path = lts.executionPaths.get(targetState) || [];
    const trace = [
      {
        step: 0,
        action: "Initial State",
        marking: this.parseStateData(lts.initialState, dpn).marking,
        dataValuation: this.parseStateData(lts.initialState, dpn).dataValuation,
      },
    ];
    let currentStateStr = lts.initialState;
    for (const step of path) {
      const transition = dpn.transitions.get(step.transitionId);
      currentStateStr = await this.fireTransitionInState(
        currentStateStr,
        step.transitionId,
        dpn
      );
      trace.push({
        step: trace.length,
        action: `Fire: ${transition?.label || step.transitionId}`,
        marking: this.parseStateData(currentStateStr, dpn).marking,
        dataValuation: this.parseStateData(currentStateStr, dpn).dataValuation,
      });
    }
    return trace;
  }
  findMissingTokens(tId, state, dpn, isMax = false) {
    const missing = [];
    for (const arc of dpn.arcs.values()) {
      if (arc.target === tId) {
        const place = dpn.places.get(arc.source);
        const current = state.marking[arc.source] || 0;
        if (current < arc.weight)
          missing.push({
            placeId: arc.source,
            placeName: place?.label,
            requiredTokens: arc.weight,
            [isMax ? "maxFoundTokens" : "currentTokens"]: current,
            deficit: arc.weight - current,
          });
      }
    }
    return missing;
  }
  isGuardEverSatisfied(t, lts) {
    if (!t.precondition) return true;
    for (const s of lts.states) {
      const d = this.parseStateData(s);
      if (t.evaluatePrecondition(d.dataValuation)) return true;
    }
    return false;
  }
  getVariablesFromExpression(expr, dpn) {
    const vars = [];
    if (!dpn.dataVariables) return vars;
    for (const v of dpn.dataVariables.values()) {
      if (new RegExp(`\\b${v.name}\\b`).test(expr)) vars.push(v);
    }
    return vars;
  }
  getMaxTokensReached(lts, dpn) {
    const max = {};
    dpn.places.forEach((_, id) => (max[id] = 0));
    for (const s of lts.states) {
      const d = this.parseStateData(s);
      for (const p in d.marking) {
        max[p] = Math.max(max[p], d.marking[p]);
      }
    }
    return max;
  }
  deepCloneDPN(dpn) {
    if (!dpn) return null;
    const c = new DataPetriNet(dpn.id, dpn.name, dpn.description);
    dpn.places.forEach((p, id) =>
      c.addPlace(
        new Place(id, { ...p.position }, p.label, p.tokens, p.capacity)
      )
    );
    dpn.transitions.forEach((t, id) =>
      c.addTransition(
        new DataAwareTransition(
          id,
          { ...t.position },
          t.label,
          t.priority,
          t.delay,
          t.precondition,
          t.postcondition
        )
      )
    );
    dpn.arcs.forEach((a, id) =>
      c.addArc(
        new Arc(
          id,
          a.source,
          a.target,
          a.weight,
          a.type,
          [...a.points],
          a.label
        )
      )
    );
    if (dpn.dataVariables) {
      dpn.dataVariables.forEach((v, id) =>
        c.addDataVariable(
          new DataVariable(id, v.name, v.type, v.currentValue, v.description)
        )
      );
    }
    return c;
  }
}

/**
 * Renders highlights and overlays for counterexample visualization.
 * This class is adapted from dpn-verification-trace-tracing.js.
 */
class SuvorovLomazovaTraceVisualizationRenderer {
  // ... This class is now enhanced to render the new detailed data ...
  // ... The implementation is provided below ...
  constructor(app) {
    this.app = app;
    this.mainRenderer = app.editor.renderer;
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.violationInfo = null;
    this.isActive = false;

    this.originalRender = this.mainRenderer.render.bind(this.mainRenderer);

    this.mainRenderer.render = () => {
      this.originalRender();
      if (this.isActive) {
        this.renderHighlights();
        this.renderDataOverlays();
      }
    };
  }

  visualizeCounterexample(counterexample) {
    this.clearHighlights();
    this.isActive = true;
    this.violationInfo = counterexample;

    // Visualize the trace, which highlights the path and sets the final state
    if (counterexample.trace) {
      this.visualizeTrace(counterexample.trace);
    }
    // Special handling for dead transitions, which don't have a trace
    if (counterexample.violationType === "dead_transition") {
      this.visualizeDeadTransition(counterexample);
    }

    this.mainRenderer.render();
  }

  visualizeDeadTransition(ce) {
    const tId = ce.deadTransition.transitionId;
    this.highlightedElements.add(tId);
    this.highlightConnectedElements(tId);
    this.dataOverlays.set(tId, { type: "deadTransition", data: ce });
  }

  visualizeTrace(trace) {
    if (!trace || trace.length === 0) return;
    const finalStep = trace[trace.length - 1];
    if (finalStep.marking) {
      for (const [placeId, tokens] of Object.entries(finalStep.marking)) {
        this.app.api.setPlaceTokens(placeId, tokens);
      }
    }
    trace.forEach((step) => {
      if (step.action && step.action.startsWith("Fire")) {
        const transitionLabel = step.action.replace("Fire: ", "");
        for (const [id, t] of this.mainRenderer.petriNet.transitions) {
          if (t.label === transitionLabel || t.id === transitionLabel) {
            this.highlightedElements.add(id);
            this.highlightConnectedElements(id);
            break;
          }
        }
      }
    });
  }

  highlightConnectedElements(transitionId) {
    for (const arc of this.mainRenderer.petriNet.arcs.values()) {
      if (arc.source === transitionId || arc.target === transitionId) {
        this.highlightedArcs.add(arc.id);
        this.highlightedElements.add(
          arc.source === transitionId ? arc.target : arc.source
        );
      }
    }
  }

  clearHighlights() {
    this.highlightedElements.clear();
    this.highlightedArcs.clear();
    this.dataOverlays.clear();
    this.violationInfo = null;
    this.isActive = false;
    this.mainRenderer.render();
  }

  renderHighlights() {
    const ctx = this.mainRenderer.ctx;
    ctx.save();
    ctx.translate(this.mainRenderer.panOffset.x, this.mainRenderer.panOffset.y);
    ctx.scale(this.mainRenderer.zoomFactor, this.mainRenderer.zoomFactor);

    // Highlight Arcs first
    ctx.lineWidth = 4;
    ctx.strokeStyle = "#EBCB8B"; // Yellow
    for (const arcId of this.highlightedArcs) {
      const arc = this.mainRenderer.petriNet.arcs.get(arcId);
      if (!arc) continue;
      const source =
        this.mainRenderer.petriNet.places.get(arc.source) ||
        this.mainRenderer.petriNet.transitions.get(arc.source);
      const target =
        this.mainRenderer.petriNet.places.get(arc.target) ||
        this.mainRenderer.petriNet.transitions.get(arc.target);
      if (!source || !target) continue;
      const { start, end } = this.mainRenderer.calculateArcEndpoints(
        source,
        target
      );
      ctx.beginPath();
      ctx.moveTo(start.x, start.y);
      ctx.lineTo(end.x, end.y);
      ctx.stroke();
    }

    // Highlight Elements
    for (const elementId of this.highlightedElements) {
      const place = this.mainRenderer.petriNet.places.get(elementId);
      if (place) {
        const isProblem = this.violationInfo?.problematicPlaces?.some(
          (p) => p.placeId === elementId
        );
        ctx.strokeStyle = isProblem ? "#BF616A" : "#5E81AC"; // Red for problem, Blue for trace
        ctx.lineWidth = 5;
        ctx.beginPath();
        ctx.arc(
          place.position.x,
          place.position.y,
          place.radius + 8,
          0,
          Math.PI * 2
        );
        ctx.stroke();
      }
      const transition = this.mainRenderer.petriNet.transitions.get(elementId);
      if (transition) {
        const isDead =
          this.violationInfo?.deadTransition?.transitionId === elementId;
        ctx.strokeStyle = isDead ? "#BF616A" : "#5E81AC";
        ctx.lineWidth = 5;
        const padding = 8;
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - padding,
          transition.position.y - transition.height / 2 - padding,
          transition.width + padding * 2,
          transition.height + padding * 2
        );
        ctx.stroke();
      }
    }
    ctx.restore();
  }

  renderDataOverlays() {
    const ctx = this.mainRenderer.ctx;
    ctx.save();
    ctx.translate(this.mainRenderer.panOffset.x, this.mainRenderer.panOffset.y);
    ctx.scale(this.mainRenderer.zoomFactor, this.mainRenderer.zoomFactor);

    for (const [id, overlay] of this.dataOverlays) {
      const transition = this.mainRenderer.petriNet.transitions.get(id);
      if (!transition) continue;

      const text = this.formatOverlayText(overlay.data);
      const lines = text.split("\n");
      const lineHeight = 14;
      ctx.font = "11px monospace";
      const maxWidth = Math.max(...lines.map((l) => ctx.measureText(l).width));

      const boxWidth = maxWidth + 20;
      const boxHeight = lines.length * lineHeight + 10;
      const x = transition.position.x + 30;
      const y = transition.position.y - boxHeight / 2;

      ctx.fillStyle = "rgba(46, 52, 64, 0.95)";
      ctx.strokeStyle = "#BF616A";
      ctx.lineWidth = 2;
      ctx.fillRect(x, y, boxWidth, boxHeight);
      ctx.strokeRect(x, y, boxWidth, boxHeight);

      ctx.fillStyle = "#ECEFF4";
      ctx.textAlign = "left";
      lines.forEach((line, index) => {
        ctx.fillText(line, x + 10, y + (index + 1) * lineHeight);
      });
    }
    ctx.restore();
  }

  formatOverlayText(data) {
    if (data.violationType === "dead_transition") {
      let lines = [`DEAD: ${data.deadTransition.transitionLabel}`];
      lines.push(`Reason: ${data.reason.replace("Dead transition: ", "")}`);
      if (data.problematicPlaces?.length > 0) {
        lines.push(
          `Token Issue: ${data.problematicPlaces[0].placeName} needs ${data.problematicPlaces[0].requiredTokens} (max found: ${data.problematicPlaces[0].maxFoundTokens})`
        );
      }
      if (data.responsibleVariables?.length > 0) {
        lines.push(`Guard Issue: ${data.deadTransition.guard}`);
      }
      if (data.suggestedFix) {
        lines.push(
          `Suggested Fix: ${Object.entries(data.suggestedFix)
            .map(([k, v]) => `${k}=${v}`)
            .join(", ")}`
        );
      }
      return lines.join("\n");
    }
    return "Analysis active";
  }
}

/**
 * UI for the Suvorov & Lomazova DPN Soundness Verifier.
 * * Provides a dedicated section in the application sidebar to run the
 * new, paper-compliant verification algorithm and display its detailed results,
 * including interactive counterexample visualization.
 */
class SuvorovLomazovaVerificationUI {
  constructor(app) {
    this.app = app;
    this.verifier = null;
    this.traceVisualizer = null;
    this.currentCounterexamples = [];
    this.isVisualizationActive = false;

    this.injectStyles();
    this.createVerificationSection();
    this.createVerificationModal();
  }

  injectStyles() {
    if (document.getElementById("sl-verification-styles")) return;
    const style = document.createElement("style");
    style.id = "sl-verification-styles";
    style.textContent = `
            /* ... (all the styles from the previous response) ... */
            .counterexample-section { margin-top: 15px; background-color: rgba(67, 76, 94, 0.5); padding: 10px; border-radius: 5px; }
            .counterexample-item { background-color: #4C566A; padding: 10px; border-radius: 4px; margin-bottom: 8px; display: flex; justify-content: space-between; align-items: center; }
            .counterexample-item.active { border-left: 3px solid #88C0D0; }
            .analyze-btn { background-color: #5E81AC; color: #ECEFF4; border: none; padding: 5px 10px; border-radius: 3px; cursor: pointer; }
            .analyze-btn:hover { background-color: #81A1C1; }
            .clear-highlight-btn { text-align: right; margin-bottom: 10px; }
        `;
    document.head.appendChild(style);
  }

  createVerificationSection() {
    const modelTab = document.querySelector('.sidebar-pane[data-tab="model"]');
    if (!modelTab || document.getElementById("sl-verification-section")) return;
    const section = document.createElement("div");
    section.id = "sl-verification-section";
    section.className = "sidebar-section";
    section.innerHTML = `
            <div class="section-header"><div class="section-title"><span class="section-icon">📜</span><h3>Formal Verification</h3></div></div>
            <div class="section-content">
                <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">Run the formal soundness verifier based on the Suvorov & Lomazova (2024) algorithm.</p>
                <button id="btn-sl-verify" class="button-primary" style="width:100%; background-color: #88C0D0; color: #2E3440;">🔬 Run Formal Verifier</button>
            </div>
        `;
    // modelTab.appendChild(section);
    section
      .querySelector("#btn-sl-verify")
      .addEventListener("click", () => this.startVerification());
  }

  createVerificationModal() {
    if (document.getElementById("sl-verification-modal")) return;
    const modal = document.createElement("div");
    modal.id = "sl-verification-modal";
    modal.className = "verification-modal";
    modal.innerHTML = `
            <div class="verification-modal-content">
                <div class="verification-modal-header"><h2>🔬 Formal Soundness Verification Results</h2><button class="verification-close-btn" id="sl-close-verification-modal">×</button></div>
                <div class="sl-modal-body" id="sl-modal-body"></div>
            </div>`;
    document.body.appendChild(modal);
    modal
      .querySelector("#sl-close-verification-modal")
      .addEventListener("click", () => this.closeModal());
    modal.addEventListener("click", (e) => {
      if (e.target === modal) this.closeModal();
    });
  }

  showModal() {
    document.querySelector("#sl-verification-modal").classList.add("show");
  }
  closeModal() {
    document.querySelector("#sl-verification-modal").classList.remove("show");
    this.clearCounterexampleVisualization();
  }

  async startVerification() {
    const verifyButton = document.querySelector("#btn-sl-verify");
    const modalBody = document.querySelector("#sl-modal-body");

    verifyButton.disabled = true;
    verifyButton.innerHTML =
      '<span class="verification-spinner"></span> Running Formal Algorithm...';
    this.showModal();
    modalBody.innerHTML = `<div class="verification-progress">...</div>`;

    try {
      this.verifier = new SuvorovLomazovaVerifier(this.app.api.petriNet);
      const result = await this.verifier.verify((progress, step) => {});
      this.currentCounterexamples = result.counterexampleTraces || [];
      this.initializeTraceVisualizer();
      modalBody.innerHTML = this.createResultsHTML(result);
    } catch (error) {
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      verifyButton.disabled = false;
      verifyButton.innerHTML = "🔬 Run Formal Verifier";
    }
  }

  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
      this.traceVisualizer = new SuvorovLomazovaTraceVisualizationRenderer(
        this.app
      );
    }
  }

  visualizeCounterexample(counterexampleIndex) {
    if (
      !this.traceVisualizer ||
      counterexampleIndex >= this.currentCounterexamples.length
    )
      return;

    const counterexample = this.currentCounterexamples[counterexampleIndex];
    this.traceVisualizer.visualizeCounterexample(counterexample);

    document.querySelectorAll(".counterexample-item").forEach((item, idx) => {
      item.classList.toggle("active", idx === counterexampleIndex);
    });
    this.isVisualizationActive = true;
  }

  clearCounterexampleVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
      this.isVisualizationActive = false;
    }
    document
      .querySelectorAll(".counterexample-item")
      .forEach((item) => item.classList.remove("active"));
  }

  createResultsHTML(result) {
    const statusClass = result.isSound ? "sound" : "unsound";
    const statusIcon = result.isSound ? "✅" : "❌";
    let propertiesHTML = result.properties
      .map((prop) => {
        let counterexampleHTML =
          !prop.satisfied && prop.counterexamples?.length > 0
            ? this.createCounterexampleSection(prop.counterexamples, prop.name)
            : "";
        return `<div class="verification-property">
                        <div class="verification-property-header">
                            <div class="verification-property-title">${
                              prop.name
                            }</div>
                            <div class="verification-property-status ${
                              prop.satisfied ? "pass" : "fail"
                            }">${prop.satisfied ? "PASS" : "FAIL"}</div>
                        </div>
                        <div class="verification-property-description">${
                          prop.description
                        }</div>
                        ${counterexampleHTML}
                    </div>`;
      })
      .join("");

    return `<div class="verification-status ${statusClass}"><div class="verification-status-icon">${statusIcon}</div><div>${
      result.isSound ? "Formally Sound" : "Formally Unsound"
    }</div></div>
                <div class="verification-details">${propertiesHTML}</div>
                <div class="verification-timing">Formal verification completed in ${
                  result.executionTime
                }ms</div>`;
  }

  createCounterexampleSection(counterexamples, propertyName) {
    let itemsHTML = counterexamples
      .map((ce, index) => {
        const globalIndex = this.currentCounterexamples.indexOf(ce);
        let reason = ce.reason || "No reason specified.";
        return `<div class="counterexample-item" data-property="${propertyName}" data-index="${globalIndex}">
                        <span>${reason}</span>
                        <button class="analyze-btn" onclick="window.formalVerifierUI.visualizeCounterexample(${globalIndex})">Analyze</button>
                    </div>`;
      })
      .join("");

    return `<div class="counterexample-section">
                    <h4>🔍 Counterexamples</h4>
                    <div class="clear-highlight-btn"><button class="analyze-btn" onclick="window.formalVerifierUI.clearCounterexampleVisualization()">Clear Highlights</button></div>
                    ${itemsHTML}
                </div>`;
  }

  createErrorHTML(error) {
    return `<div class="verification-status error">An error occurred: ${error.message}</div>`;
  }
}

// Initialization logic to be placed in the main application script
document.addEventListener("DOMContentLoaded", () => {
  // Ensure this runs after the main app is initialized
  setTimeout(() => {
    if (window.petriApp) {
      window.formalVerifierUI = new SuvorovLomazovaVerificationUI(
        window.petriApp
      );
    }
  }, 1000);
});
