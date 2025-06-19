/**
 * Enhanced Data Petri Net Verification Extension with Trace Visualization
 * 
 * Implements data-aware soundness verification with counterexample trace visualization
 * and enhanced debugging capabilities for Data Petri nets.
 */

class EnhancedDataAwareVerifier extends DataAwareVerifier {
  constructor(petriNet) {
    super(petriNet);
    this.traceCapture = true;
    this.counterexampleTraces = [];
  }

  /**
   * Enhanced verification method with trace capture
   */
  async verify(progressCallback) {
    this.startTime = Date.now();
    this.counterexampleTraces = [];
    
    try {
      progressCallback(10, "Checking basic structure...");
      await this.delay(100);

      if (!this.hasProperStructure()) {
        throw new Error("Net must have at least one place and one transition");
      }

      progressCallback(25, "Checking boundedness...");
      await this.delay(200);

      const isBounded = this.checkBoundedness();
      if (!isBounded) {
        return this.createResult(false, [
          { name: "P0: Boundedness", satisfied: false, description: "The net must be bounded for verification", details: "The net has unbounded places" }
        ]);
      }

      progressCallback(50, "Constructing labeled transition system with trace capture...");
      await this.delay(300);

      const lts = this.constructEnhancedLTS();
      
      progressCallback(75, "Checking soundness properties with counterexample detection...");
      await this.delay(200);

      const p1 = this.checkProperty1(lts);
      const p2 = this.checkProperty2(lts);
      const p3 = this.checkProperty3(lts);

      progressCallback(100, "Verification complete!");
      await this.delay(100);

      const properties = [
        {
          name: "P1: Reachability",
          satisfied: p1.satisfied,
          description: "All reachable states can reach a final state",
          details: p1.details,
          counterexamples: p1.counterexamples || []
        },
        {
          name: "P2: Proper Termination", 
          satisfied: p2.satisfied,
          description: "No markings strictly cover the final marking",
          details: p2.details,
          counterexamples: p2.counterexamples || []
        },
        {
          name: "P3: No Dead Transitions",
          satisfied: p3.satisfied, 
          description: "All transitions can be executed in some reachable state",
          details: p3.details,
          counterexamples: p3.counterexamples || []
        }
      ];

      const isSound = p1.satisfied && p2.satisfied && p3.satisfied;
      const executionTime = Date.now() - this.startTime;
      
      return {
        isSound,
        properties,
        executionTime,
        hasCounterexamples: this.counterexampleTraces.length > 0,
        counterexampleTraces: this.counterexampleTraces
      };

    } catch (error) {
      throw error;
    }
  }

  /**
   * Enhanced LTS construction with execution path tracking
   */
  constructEnhancedLTS() {
    const lts = super.constructLTS();
    
    lts.executionPaths = new Map();
    lts.stateMetadata = new Map();
    
    const visited = new Set();
    const queue = [{ state: lts.initialState, path: [] }];
    
    while (queue.length > 0) {
      const { state, path } = queue.shift();
      
      if (visited.has(state)) continue;
      visited.add(state);
      
      lts.executionPaths.set(state, [...path]);
      
      const stateTransitions = lts.transitions.get(state) || [];
      
      for (const transition of stateTransitions) {
        if (!visited.has(transition.target)) {
          const newPath = [...path, {
            fromState: state,
            toState: transition.target,
            transitionId: transition.transition,
            transitionLabel: this.getTransitionLabel(transition.transition)
          }];
          
          queue.push({ state: transition.target, path: newPath });
        }
      }
    }
    
    return lts;
  }

  /**
   * Enhanced Property 1 checking with conservative deadlock detection
   */
  checkProperty1(lts) {
    const finalMarkings = this.identifyFinalMarkings();
    if (finalMarkings.length === 0) {
      return { 
        satisfied: true,
        details: "No explicit final marking found - assuming sound",
        counterexamples: []
      };
    }

    const deadlockStates = [];
    
    for (const state of lts.states) {
      const stateData = this.parseStateData(state);
      const hasEnabledTransitions = this.hasEnabledTransitionsInState(state, lts);
      
      if (!hasEnabledTransitions && !this.isFinalState(stateData, finalMarkings)) {
        const trace = this.buildTraceToState(state, lts);
        deadlockStates.push({
          state: state,
          trace: trace,
          reason: "True deadlock - no enabled transitions and not final",
          stateData: stateData
        });
      }
    }

    if (deadlockStates.length > 0) {
      this.counterexampleTraces.push(...deadlockStates);
      return { 
        satisfied: false, 
        details: `Found ${deadlockStates.length} true deadlock states`,
        counterexamples: deadlockStates
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced Property 2 checking with strict coverage analysis
   */
  checkProperty2(lts) {
    const finalMarkings = this.identifyFinalMarkings();
    if (finalMarkings.length === 0) {
      return { satisfied: true, counterexamples: [] };
    }
    
    const violations = [];
    
    for (const stateStr of lts.states) {
      const state = JSON.parse(stateStr);
      
      for (const finalMarking of finalMarkings) {
        if (this.markingStrictlyCovers(state.marking, finalMarking)) {
          const hasEnabledTransitions = this.hasEnabledTransitionsInState(stateStr, lts);
          
          if (hasEnabledTransitions) {
            const trace = this.buildTraceToState(stateStr, lts);
            violations.push({
              state: stateStr,
              trace: trace,
              reason: "Marking strictly covers final marking with enabled transitions",
              stateData: this.parseStateData(stateStr),
              coveringMarking: state.marking,
              finalMarking: finalMarking
            });
          }
        }
      }
    }

    if (violations.length > 0) {
      this.counterexampleTraces.push(...violations);
      return { 
        satisfied: false, 
        details: `Found ${violations.length} markings that strictly cover final marking with enabled transitions`,
        counterexamples: violations
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced Property 3 checking with precise dead transition detection
   */
  checkProperty3(lts) {
    const transitionsFired = new Set();
    const transitionsEnabledButNotFired = new Set();
    
    for (const [state, stateTransitions] of lts.transitions) {
      for (const { transition } of stateTransitions) {
        transitionsFired.add(transition);
      }
    }
    
    for (const [state] of lts.transitions) {
      const enabledInState = this.getEnabledTransitionsInState(state);
      for (const transitionId of enabledInState) {
        if (!transitionsFired.has(transitionId)) {
          transitionsEnabledButNotFired.add(transitionId);
        }
      }
    }
    
    const trulyDeadTransitions = [];
    for (const [id, transition] of this.petriNet.transitions) {
      if (!transitionsFired.has(id) && !transitionsEnabledButNotFired.has(id)) {
        trulyDeadTransitions.push({
          transitionId: id,
          transitionLabel: transition.label || id,
          reason: "Transition never enabled in any reachable state"
        });
      }
    }
    
    if (trulyDeadTransitions.length > 0) {
      this.counterexampleTraces.push(...trulyDeadTransitions.map(dt => ({
        state: "global",
        trace: [],
        reason: dt.reason,
        deadTransition: dt
      })));
      
      return { 
        satisfied: false, 
        details: `Truly dead transitions found: ${trulyDeadTransitions.map(dt => dt.transitionLabel).join(', ')}`,
        counterexamples: trulyDeadTransitions
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Check if marking strictly covers another marking
   */
  markingStrictlyCovers(marking1, marking2) {
    let hasMore = false;
    
    for (const placeId in marking2) {
      const tokens1 = marking1[placeId] || 0;
      const tokens2 = marking2[placeId] || 0;
      
      if (tokens1 < tokens2) {
        return false;
      }
      if (tokens1 > tokens2) {
        hasMore = true;
      }
    }
    
    return hasMore;
  }

  /**
   * Check if a state has enabled transitions
   */
  hasEnabledTransitionsInState(stateStr, lts) {
    const stateTransitions = lts.transitions.get(stateStr) || [];
    return stateTransitions.length > 0;
  }

  /**
   * Check if a state is a final state
   */
  isFinalState(stateData, finalMarkings) {
    for (const finalMarking of finalMarkings) {
      if (this.markingEquals(stateData.marking, finalMarking)) {
        return true;
      }
    }
    return false;
  }

  /**
   * Get enabled transitions in a specific state
   */
  getEnabledTransitionsInState(stateStr) {
    const state = JSON.parse(stateStr);
    const enabled = [];
    
    for (const [id, transition] of this.petriNet.transitions) {
      if (this.isTransitionEnabledInState(id, state)) {
        enabled.push(id);
      }
    }
    
    return enabled;
  }

  /**
   * Build execution trace to reach a specific state
   */
  buildTraceToState(targetState, lts) {
    const trace = [];
    const path = lts.executionPaths.get(targetState) || [];
    
    let currentMarking = this.getInitialMarking();
    let currentValuation = this.getInitialValuation();
    
    trace.push({
      step: 0,
      action: "Initial State",
      transitionId: null,
      transitionLabel: "Initial",
      marking: { ...currentMarking },
      dataValuation: { ...currentValuation },
      timestamp: new Date().toISOString()
    });

    for (let i = 0; i < path.length; i++) {
      const step = path[i];
      const transition = this.petriNet.transitions.get(step.transitionId);
      
      if (transition) {
        const newState = this.simulateTransitionFiring(currentMarking, currentValuation, step.transitionId);
        currentMarking = newState.marking;
        currentValuation = newState.dataValuation;
        
        trace.push({
          step: i + 1,
          action: `Fire Transition`,
          transitionId: step.transitionId,
          transitionLabel: step.transitionLabel,
          marking: { ...currentMarking },
          dataValuation: { ...currentValuation },
          timestamp: new Date().toISOString(),
          dataChanges: this.detectDataChanges(trace[i].dataValuation, currentValuation)
        });
      }
    }
    
    return trace;
  }

  /**
   * Get initial marking
   */
  getInitialMarking() {
    const marking = {};
    for (const [id, place] of this.petriNet.places) {
      marking[place.label] = place.tokens || 0;
    }
    return marking;
  }

  /**
   * Get initial data valuation
   */
  getInitialValuation() {
    const valuation = {};
    if (this.petriNet.dataVariables) {
      for (const [id, variable] of this.petriNet.dataVariables) {
        valuation[variable.name] = variable.getValue ? variable.getValue() : (variable.currentValue || 0);
      }
    }
    return valuation;
  }

  /**
   * Simulate transition firing for trace building
   */
  simulateTransitionFiring(marking, valuation, transitionId) {
    const newMarking = { ...marking };
    let newValuation = { ...valuation };
    
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.source === transitionId);
    
    for (const arc of inputArcs) {
      const place = this.petriNet.places.get(arc.source);
      if (place && arc.type === "regular") {
        newMarking[place.label] = (newMarking[place.label] || 0) - (arc.weight || 1);
      }
    }
    
    for (const arc of outputArcs) {
      const place = this.petriNet.places.get(arc.target);
      if (place) {
        newMarking[place.label] = (newMarking[place.label] || 0) + (arc.weight || 1);
      }
    }
    
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePostcondition === 'function') {
      try {
        newValuation = transition.evaluatePostcondition(valuation);
      } catch (error) {
        // Continue with original valuation if postcondition fails
      }
    }
    
    return { marking: newMarking, dataValuation: newValuation };
  }

  /**
   * Detect changes in data valuation between two states
   */
  detectDataChanges(oldValuation, newValuation) {
    const changes = [];
    
    for (const [variable, newValue] of Object.entries(newValuation)) {
      const oldValue = oldValuation[variable];
      if (oldValue !== newValue) {
        changes.push({
          variable: variable,
          oldValue: oldValue,
          newValue: newValue,
          changeType: oldValue === undefined ? 'created' : 'modified'
        });
      }
    }
    
    return changes;
  }

  /**
   * Parse state data from state string
   */
  parseStateData(stateStr) {
    try {
      return JSON.parse(stateStr);
    } catch (error) {
      return { marking: {}, dataValuation: {} };
    }
  }

  /**
   * Get transition label for display
   */
  getTransitionLabel(transitionId) {
    const transition = this.petriNet.transitions.get(transitionId);
    return transition ? (transition.label || transitionId) : transitionId;
  }
}

/**
 * Trace Visualization Renderer for counterexample display
 */
class TraceVisualizationRenderer {
  constructor(mainRenderer) {
    this.mainRenderer = mainRenderer;
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.isActive = false;
    
    this.originalRender = mainRenderer.render.bind(mainRenderer);
    
    mainRenderer.render = () => {
      this.originalRender();
      if (this.isActive) {
        this.renderHighlights();
        this.renderDataOverlays();
      }
    };
  }

  /**
   * Highlight elements involved in a trace
   */
  visualizeTrace(trace, currentStep = -1) {
    this.clearHighlights();
    this.isActive = true;
    
    if (!trace || trace.length === 0) {
      this.mainRenderer.render();
      return;
    }
    
    const stepsToShow = currentStep >= 0 ? currentStep + 1 : trace.length;
    
    for (let i = 0; i < Math.min(stepsToShow, trace.length); i++) {
      const step = trace[i];
      
      if (step.transitionId) {
        this.highlightedElements.add(step.transitionId);
        this.highlightConnectedElements(step.transitionId);
        
        if (step.dataChanges && step.dataChanges.length > 0) {
          this.addDataOverlay(step.transitionId, step.dataChanges, step.dataValuation);
        }
      }
    }
    
    this.mainRenderer.render();
  }

  /**
   * Highlight elements connected to a transition
   */
  highlightConnectedElements(transitionId) {
    const petriNet = this.mainRenderer.petriNet;
    const arcs = Array.from(petriNet.arcs.values());
    
    for (const arc of arcs) {
      if (arc.source === transitionId || arc.target === transitionId) {
        this.highlightedArcs.add(arc.id);
        
        if (arc.source !== transitionId) {
          this.highlightedElements.add(arc.source);
        }
        if (arc.target !== transitionId) {
          this.highlightedElements.add(arc.target);
        }
      }
    }
  }

  /**
   * Add data overlay to a transition
   */
  addDataOverlay(transitionId, dataChanges, currentValuation) {
    const petriNet = this.mainRenderer.petriNet;
    const transition = petriNet.transitions.get(transitionId);
    if (!transition) return;
    
    this.dataOverlays.set(transitionId, {
      changes: dataChanges,
      valuation: currentValuation,
      position: { ...transition.position }
    });
  }

  /**
   * Clear all highlights and overlays
   */
  clearHighlights() {
    this.highlightedElements.clear();
    this.highlightedArcs.clear();
    this.dataOverlays.clear();
    this.isActive = false;
    this.mainRenderer.render();
  }

  /**
   * Animate through trace steps
   */
  async animateTrace(trace) {
    for (let i = 0; i < trace.length; i++) {
      this.visualizeTrace(trace, i);
      await this.delay(1000);
    }
  }

  /**
   * Render element highlights
   */
  renderHighlights() {
    const ctx = this.mainRenderer.ctx;
    const renderer = this.mainRenderer;
    
    ctx.save();
    ctx.translate(renderer.panOffset.x, renderer.panOffset.y);
    ctx.scale(renderer.zoomFactor, renderer.zoomFactor);
    
    for (const elementId of this.highlightedElements) {
      const place = renderer.petriNet.places.get(elementId);
      if (place) {
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 8, 0, Math.PI * 2);
        ctx.strokeStyle = 'rgba(255, 107, 107, 0.3)';
        ctx.lineWidth = 6;
        ctx.stroke();
        
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 4, 0, Math.PI * 2);
        ctx.strokeStyle = '#FF6B6B';
        ctx.lineWidth = 3;
        ctx.stroke();
      }
      
      const transition = renderer.petriNet.transitions.get(elementId);
      if (transition) {
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 8,
          transition.position.y - transition.height / 2 - 8,
          transition.width + 16,
          transition.height + 16
        );
        ctx.strokeStyle = 'rgba(78, 205, 196, 0.3)';
        ctx.lineWidth = 6;
        ctx.stroke();
        
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 4,
          transition.position.y - transition.height / 2 - 4,
          transition.width + 8,
          transition.height + 8
        );
        ctx.strokeStyle = '#4ECDC4';
        ctx.lineWidth = 3;
        ctx.stroke();
      }
    }
    
    for (const arcId of this.highlightedArcs) {
      const arc = renderer.petriNet.arcs.get(arcId);
      if (arc) {
        const sourceElement = renderer.petriNet.places.get(arc.source) || 
                            renderer.petriNet.transitions.get(arc.source);
        const targetElement = renderer.petriNet.places.get(arc.target) || 
                            renderer.petriNet.transitions.get(arc.target);
        
        if (sourceElement && targetElement) {
          const { start, end } = renderer.calculateArcEndpoints(sourceElement, targetElement);
          
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = 'rgba(255, 230, 109, 0.3)';
          ctx.lineWidth = 8;
          ctx.stroke();
          
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = '#FFE66D';
          ctx.lineWidth = 4;
          ctx.stroke();
        }
      }
    }
    
    ctx.restore();
  }

  /**
   * Render data overlays
   */
  renderDataOverlays() {
    const ctx = this.mainRenderer.ctx;
    const renderer = this.mainRenderer;
    
    ctx.save();
    ctx.translate(renderer.panOffset.x, renderer.panOffset.y);
    ctx.scale(renderer.zoomFactor, renderer.zoomFactor);
    
    for (const [transitionId, overlay] of this.dataOverlays) {
      const transition = renderer.petriNet.transitions.get(transitionId);
      if (!transition) continue;
      
      const x = transition.position.x + 40;
      const y = transition.position.y - 30;
      
      const text = this.formatDataOverlay(overlay);
      const lines = text.split('\n');
      const lineHeight = 16;
      const padding = 10;
      
      ctx.font = '12px monospace';
      const maxWidth = Math.max(...lines.map(line => ctx.measureText(line).width));
      const boxWidth = maxWidth + padding * 2;
      const boxHeight = lines.length * lineHeight + padding * 2;
      
      ctx.fillStyle = 'rgba(46, 52, 64, 0.95)';
      ctx.fillRect(x, y - boxHeight, boxWidth, boxHeight);
      
      ctx.strokeStyle = '#88C0D0';
      ctx.lineWidth = 2;
      ctx.strokeRect(x, y - boxHeight, boxWidth, boxHeight);
      
      ctx.fillStyle = '#ECEFF4';
      ctx.textAlign = 'left';
      
      lines.forEach((line, index) => {
        ctx.fillText(line, x + padding, y - boxHeight + padding + (index + 1) * lineHeight);
      });
    }
    
    ctx.restore();
  }

  /**
   * Format data overlay text
   */
  formatDataOverlay(overlay) {
    const lines = ['Data Changes:'];
    
    for (const change of overlay.changes) {
      const symbol = change.changeType === 'created' ? '+' : '~';
      lines.push(`${symbol} ${change.variable}: ${change.oldValue} → ${change.newValue}`);
    }
    
    return lines.join('\n');
  }

  delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

/**
 * Enhanced Data Petri Net Verification with Trace Visualization
 */
class EnhancedDataPetriNetVerification extends DataPetriNetVerification {
  constructor(app) {
    super(app);
    this.traceVisualizer = null;
    this.currentCounterexamples = [];
    this.isVisualizationActive = false;
  }

  /**
   * Start verification with enhanced verifier
   */
  async startVerification() {
    const verifyButton = document.querySelector('#btn-verify-soundness');
    const modal = document.querySelector('#verification-modal');
    const modalBody = document.querySelector('#verification-modal-body');

    verifyButton.disabled = true;
    verifyButton.innerHTML = '<span class="verification-spinner"></span> Verifying...';

    this.showModal();
    modalBody.innerHTML = this.createProgressHTML();

    try {
      const dpn = this.app.api.petriNet;
      
      const verifier = new EnhancedDataAwareVerifier(dpn);
      const result = await verifier.verify((progress, step) => {
        this.updateProgress(progress, step);
      });

      this.currentCounterexamples = result.counterexampleTraces || [];
      this.initializeTraceVisualizer();
      modalBody.innerHTML = this.createEnhancedResultsHTML(result);

    } catch (error) {
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      verifyButton.disabled = false;
      verifyButton.innerHTML = '<span class="verify-btn-icon">🔍</span> Verify Soundness';
    }
  }

  /**
   * Initialize trace visualizer
   */
  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
      this.traceVisualizer = new TraceVisualizationRenderer(this.app.editor.renderer);
    }
  }

  /**
   * Visualize a specific trace on the editor
   */
  visualizeTrace(traceIndex, propertyName) {
    if (!this.traceVisualizer) {
      this.initializeTraceVisualizer();
    }

    if (!this.traceVisualizer) {
      return;
    }

    const counterexample = this.findCounterexample(traceIndex, propertyName);
    if (!counterexample) {
      return;
    }

    let trace = counterexample.trace;
    if (!trace || trace.length === 0) {
      if (counterexample.deadTransition) {
        trace = [{
          step: 0,
          action: "Initial State",
          transitionId: null,
          transitionLabel: "Initial"
        }];
      }
    }

    if (trace && trace.length > 0) {
      this.traceVisualizer.visualizeTrace(trace);
      this.updateTraceVisualizationUI(traceIndex, propertyName);
      this.isVisualizationActive = true;
    }
  }

  /**
   * Animate a specific trace on the editor
   */
  async animateTrace(traceIndex, propertyName) {
    if (!this.traceVisualizer) {
      this.initializeTraceVisualizer();
    }

    if (!this.traceVisualizer) {
      return;
    }

    const counterexample = this.findCounterexample(traceIndex, propertyName);
    if (!counterexample || !counterexample.trace) {
      return;
    }

    this.updateTraceVisualizationUI(traceIndex, propertyName);
    await this.traceVisualizer.animateTrace(counterexample.trace);
    this.isVisualizationActive = true;
  }

  /**
   * Clear trace visualization
   */
  clearTraceVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
      this.isVisualizationActive = false;
    }
    
    document.querySelectorAll('.counterexample-item').forEach(item => {
      item.classList.remove('active-trace');
    });
  }

  /**
   * Find counterexample by index and property name
   */
  findCounterexample(traceIndex, propertyName) {
    let relevantCounterexamples = this.currentCounterexamples;
    
    if (propertyName.includes('P1')) {
      relevantCounterexamples = this.currentCounterexamples.filter(ce => 
        ce.reason && ce.reason.includes('deadlock'));
    } else if (propertyName.includes('P2')) {
      relevantCounterexamples = this.currentCounterexamples.filter(ce => 
        ce.reason && ce.reason.includes('covers'));
    } else if (propertyName.includes('P3')) {
      relevantCounterexamples = this.currentCounterexamples.filter(ce => 
        ce.deadTransition || (ce.reason && ce.reason.includes('dead')));
    }
    
    if (traceIndex < relevantCounterexamples.length) {
      return relevantCounterexamples[traceIndex];
    }
    
    if (traceIndex < this.currentCounterexamples.length) {
      return this.currentCounterexamples[traceIndex];
    }
    
    return null;
  }

  /**
   * Update UI to show active trace
   */
  updateTraceVisualizationUI(traceIndex, propertyName) {
    document.querySelectorAll('.counterexample-item').forEach(item => {
      item.classList.remove('active-trace');
    });
    
    const traceElements = document.querySelectorAll('.counterexample-item');
    if (traceIndex < traceElements.length) {
      traceElements[traceIndex].classList.add('active-trace');
    }
  }

  /**
   * Create enhanced results HTML with counterexample sections
   */
  createEnhancedResultsHTML(result) {
    const isSound = result.isSound;
    const statusClass = isSound ? 'sound' : 'unsound';
    const statusIcon = isSound ? '✅' : '❌';
    const statusText = isSound ? 'Sound' : 'Unsound';

    let html = `
      <div class="verification-algorithm-info">
        <h4>🔬 Algorithm: Enhanced Data-Aware Soundness Verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Advanced verification with counterexample detection and interactive visualization.
        </p>
      </div>

      <div class="verification-status ${statusClass}">
        <div class="verification-status-icon">${statusIcon}</div>
        <div>
          <div style="font-size: 18px;">${statusText}</div>
          <div style="font-size: 14px; opacity: 0.8;">
            ${isSound ? 
              'The Data Petri Net satisfies all data-aware soundness properties.' : 
              'The Data Petri Net violates one or more soundness properties.'}
          </div>
        </div>
      </div>

      <div class="verification-details">
    `;

    result.properties.forEach((prop, propIndex) => {
      const propStatus = prop.satisfied ? 'pass' : 'fail';
      const propIcon = prop.satisfied ? '✅' : '❌';
      
      html += `
        <div class="verification-property">
          <div class="verification-property-header">
            <div class="verification-property-title">${prop.name}</div>
            <div class="verification-property-status ${propStatus}">${propIcon} ${prop.satisfied ? 'PASS' : 'FAIL'}</div>
          </div>
          <div class="verification-property-description">
            ${prop.description}
            ${!prop.satisfied && prop.details ? `<br><strong>Issue:</strong> ${prop.details}` : ''}
          </div>
          ${!prop.satisfied && prop.counterexamples && prop.counterexamples.length > 0 ? 
            this.createCounterexampleSection(prop.counterexamples, prop.name, propIndex) : ''}
        </div>
      `;
    });

    html += `
      </div>
      <div class="verification-timing">
        Verification completed in ${result.executionTime}ms
      </div>
    `;

    return html;
  }

  /**
   * Create counterexample section with visualization controls
   */
  createCounterexampleSection(counterexamples, propertyName, propertyIndex) {
    if (!counterexamples || counterexamples.length === 0) return '';

    let html = `
      <div class="counterexample-section">
        <h4>🔍 Counterexamples (${counterexamples.length})</h4>
        <div class="counterexample-controls">
          <button class="trace-control-btn" onclick="window.dpnVerification.clearTraceVisualization()">
            Clear Highlights
          </button>
        </div>
        <div class="counterexample-list">
    `;

    counterexamples.forEach((ce, index) => {
      const globalIndex = this.currentCounterexamples.indexOf(ce);
      const displayIndex = globalIndex >= 0 ? globalIndex : index;
      
      html += `
        <div class="counterexample-item" data-property="${propertyName}" data-index="${displayIndex}">
          <div class="counterexample-header">
            <span class="counterexample-title">Counterexample ${index + 1}</span>
            <div class="counterexample-actions">
              <button class="trace-btn" onclick="window.dpnVerification.visualizeTrace(${displayIndex}, '${propertyName}')">
                👁️ Visualize
              </button>
              ${ce.trace && ce.trace.length > 0 ? 
                `<button class="trace-btn" onclick="window.dpnVerification.animateTrace(${displayIndex}, '${propertyName}')">
                  ▶️ Animate
                </button>` : ''}
            </div>
          </div>
          <div class="counterexample-details">
            <strong>Reason:</strong> ${ce.reason}
            ${ce.trace && ce.trace.length > 0 ? 
              `<br><strong>Execution steps:</strong> ${ce.trace.length}` : ''}
            ${ce.deadTransition ? 
              `<br><strong>Dead transition:</strong> ${ce.deadTransition.transitionLabel}` : ''}
          </div>
        </div>
      `;
    });

    html += `
        </div>
      </div>
    `;

    return html;
  }
}

// Enhanced verification styles
const enhancedVerificationStyles = `
  .counterexample-section {
    background-color: #2E3440;
    border-radius: 6px;
    padding: 15px;
    margin-top: 15px;
    border-left: 4px solid #BF616A;
  }

  .counterexample-item.active-trace {
    border-color: #88C0D0 !important;
    background-color: rgba(136, 192, 208, 0.2) !important;
    box-shadow: 0 0 10px rgba(136, 192, 208, 0.3);
  }

  .trace-btn {
    background-color: #5E81AC;
    color: #ECEFF4;
    border: none;
    padding: 4px 8px;
    border-radius: 3px;
    cursor: pointer;
    font-size: 11px;
    transition: all 0.2s;
  }

  .trace-btn:hover {
    background-color: #81A1C1;
    transform: translateY(-1px);
  }

  .trace-control-btn {
    background-color: #4C566A;
    color: #ECEFF4;
    border: none;
    padding: 6px 12px;
    border-radius: 4px;
    cursor: pointer;
    font-size: 12px;
    transition: all 0.2s;
  }

  .trace-control-btn:hover {
    background-color: #5E81AC;
  }

  .counterexample-controls {
    margin-bottom: 15px;
    text-align: right;
  }

  .counterexample-list {
    display: flex;
    flex-direction: column;
    gap: 10px;
  }

  .counterexample-item {
    background-color: #434C5E;
    border-radius: 4px;
    padding: 12px;
    border: 1px solid transparent;
    transition: all 0.2s;
  }

  .counterexample-item:hover {
    border-color: #5E81AC;
  }

  .counterexample-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 8px;
  }

  .counterexample-title {
    font-weight: 600;
    color: #E5E9F0;
    font-size: 14px;
  }

  .counterexample-actions {
    display: flex;
    gap: 6px;
  }

  .counterexample-details {
    font-size: 12px;
    color: #D8DEE9;
    line-height: 1.4;
  }
`;

// Inject styles
function injectEnhancedVerificationStyles() {
  const existingStyles = document.getElementById('verification-styles');
  if (existingStyles) {
    existingStyles.textContent += '\n' + enhancedVerificationStyles;
  } else {
    const style = document.createElement('style');
    style.id = 'enhanced-verification-styles';
    style.textContent = enhancedVerificationStyles;
    document.head.appendChild(style);
  }
}

// Initialize enhanced verification system
document.addEventListener('DOMContentLoaded', () => {
  const initEnhancedVerification = () => {
    if (window.petriApp && window.dataPetriNetIntegration) {
      if (!window.enhancedDpnVerification) {
        injectEnhancedVerificationStyles();
        window.enhancedDpnVerification = new EnhancedDataPetriNetVerification(window.petriApp);
        window.dpnVerification = window.enhancedDpnVerification;
      }
    } else {
      setTimeout(initEnhancedVerification, 500);
    }
  };
  
  setTimeout(initEnhancedVerification, 2000);
});