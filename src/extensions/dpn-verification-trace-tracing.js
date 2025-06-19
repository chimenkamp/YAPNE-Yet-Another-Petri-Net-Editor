/**
 * Enhanced Data Petri Net Verification Extension with Trace Visualization
 * 
 * This enhancement adds counterexample trace visualization and data-aware debugging
 * capabilities to the existing soundness verification system.
 */

// Enhance the DataAwareVerifier class to capture detailed traces
class EnhancedDataAwareVerifier extends DataAwareVerifier {
  constructor(petriNet) {
    super(petriNet);
    this.traceCapture = true;
    this.counterexampleTraces = [];
  }

  /**
   * Enhanced verification method that captures detailed counterexample traces
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

      const p1 = this.checkProperty1WithTraces(lts);
      const p2 = this.checkProperty2WithTraces(lts);
      const p3 = this.checkProperty3WithTraces(lts);

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
   * Enhanced LTS construction that tracks execution paths
   */
  constructEnhancedLTS() {
    const lts = this.constructLTS(); // Use the existing method
    
    // Enhance with trace information
    lts.executionPaths = new Map();
    lts.stateMetadata = new Map();
    
    // Track how we reached each state
    for (const [state, transitions] of lts.transitions) {
      for (const transition of transitions) {
        const path = lts.executionPaths.get(transition.target) || [];
        const newPath = [...path, {
          fromState: state,
          toState: transition.target,
          transitionId: transition.transitionId,
          transitionLabel: this.getTransitionLabel(transition.transitionId),
          firedAt: Date.now()
        }];
        lts.executionPaths.set(transition.target, newPath);
      }
    }
    
    return lts;
  }

  /**
   * Enhanced property checking with counterexample trace capture
   */
  checkProperty1WithTraces(lts) {
    const finalMarkings = this.identifyFinalMarkings();
    if (finalMarkings.length === 0) {
      return { 
        satisfied: false, 
        details: "No clear final marking identified. Consider adding an explicit end place.",
        counterexamples: []
      };
    }

    const deadlockStates = [];
    
    // Check if all states can reach a final state
    for (const state of lts.states) {
      if (!this.canReachFinalState(state, lts, finalMarkings)) {
        // Capture the execution path that led to this deadlock
        const trace = this.buildTraceToState(state, lts);
        deadlockStates.push({
          state: state,
          trace: trace,
          reason: "Cannot reach final marking",
          stateData: this.parseStateData(state)
        });
      }
    }

    if (deadlockStates.length > 0) {
      this.counterexampleTraces.push(...deadlockStates);
      return { 
        satisfied: false, 
        details: `Found ${deadlockStates.length} states that cannot reach any final state (potential deadlock)`,
        counterexamples: deadlockStates
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced property 2 checking with trace capture
   */
  checkProperty2WithTraces(lts) {
    const finalMarkings = this.identifyFinalMarkings();
    const violations = [];
    
    for (const stateStr of lts.states) {
      const state = JSON.parse(stateStr);
      
      for (const finalMarking of finalMarkings) {
        if (this.markingCovers(state.marking, finalMarking) && 
            !this.markingEquals(state.marking, finalMarking)) {
          
          const trace = this.buildTraceToState(stateStr, lts);
          violations.push({
            state: stateStr,
            trace: trace,
            reason: "Marking strictly covers final marking",
            stateData: this.parseStateData(stateStr),
            coveringMarking: state.marking,
            finalMarking: finalMarking
          });
        }
      }
    }

    if (violations.length > 0) {
      this.counterexampleTraces.push(...violations);
      return { 
        satisfied: false, 
        details: `Found ${violations.length} markings that strictly cover a final marking`,
        counterexamples: violations
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced property 3 checking with trace capture
   */
  checkProperty3WithTraces(lts) {
    const transitionsFired = new Set();
    
    for (const [state, stateTransitions] of lts.transitions) {
      for (const { transitionId } of stateTransitions) {
        transitionsFired.add(transitionId);
      }
    }
    
    const deadTransitions = [];
    for (const [id, transition] of this.petriNet.transitions) {
      if (!transitionsFired.has(id)) {
        deadTransitions.push({
          transitionId: id,
          transitionLabel: transition.label || id,
          reason: "Transition never fired in any reachable state"
        });
      }
    }
    
    if (deadTransitions.length > 0) {
      this.counterexampleTraces.push(...deadTransitions.map(dt => ({
        state: "global",
        trace: [],
        reason: dt.reason,
        deadTransition: dt
      })));
      
      return { 
        satisfied: false, 
        details: `Dead transitions found: ${deadTransitions.map(dt => dt.transitionLabel).join(', ')}`,
        counterexamples: deadTransitions
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Build execution trace to reach a specific state
   */
  buildTraceToState(targetState, lts) {
    const trace = [];
    const path = lts.executionPaths.get(targetState) || [];
    
    // Convert execution path to detailed trace
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
        // Simulate firing this transition
        const newMarking = this.simulateTransitionFiring(currentMarking, currentValuation, step.transitionId);
        currentMarking = newMarking.marking;
        currentValuation = newMarking.dataValuation;
        
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
   * Simulate transition firing for trace building
   */
  simulateTransitionFiring(marking, valuation, transitionId) {
    const newMarking = { ...marking };
    let newValuation = { ...valuation };
    
    // Update marking
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
    
    // Update data valuation
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePostcondition === 'function') {
      newValuation = transition.evaluatePostcondition(valuation);
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

// Add trace visualization capabilities to the renderer
class TraceVisualizationRenderer {
  constructor(renderer) {
    this.renderer = renderer;
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.traceStep = 0;
    this.animationSpeed = 1000; // ms per step
  }

  /**
   * Highlight elements involved in a trace
   */
  visualizeTrace(trace, currentStep = -1) {
    this.clearHighlights();
    
    if (!trace || trace.length === 0) return;
    
    // Highlight path up to current step
    const stepsToShow = currentStep >= 0 ? currentStep + 1 : trace.length;
    
    for (let i = 0; i < Math.min(stepsToShow, trace.length); i++) {
      const step = trace[i];
      
      if (step.transitionId) {
        // Highlight transition
        this.highlightedElements.add(step.transitionId);
        
        // Highlight connected places
        this.highlightConnectedPlaces(step.transitionId);
        
        // Add data overlay if there are data changes
        if (step.dataChanges && step.dataChanges.length > 0) {
          this.addDataOverlay(step.transitionId, step.dataChanges, step.dataValuation);
        }
      }
    }
    
    this.render();
  }

  /**
   * Highlight places connected to a transition
   */
  highlightConnectedPlaces(transitionId) {
    const arcs = Array.from(this.renderer.petriNet.arcs.values());
    
    for (const arc of arcs) {
      if (arc.source === transitionId || arc.target === transitionId) {
        this.highlightedArcs.add(arc.id);
        
        // Highlight connected places
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
    const transition = this.renderer.petriNet.transitions.get(transitionId);
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
  }

  /**
   * Animate through trace steps
   */
  async animateTrace(trace) {
    for (let i = 0; i < trace.length; i++) {
      this.visualizeTrace(trace, i);
      await this.delay(this.animationSpeed);
    }
  }

  /**
   * Render with highlights and overlays
   */
  render() {
    // Call original render
    this.renderer.render();
    
    // Add highlights
    this.renderHighlights();
    
    // Add data overlays
    this.renderDataOverlays();
  }

  /**
   * Render element highlights
   */
  renderHighlights() {
    const ctx = this.renderer.ctx;
    
    ctx.save();
    ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);
    
    // Highlight places
    for (const elementId of this.highlightedElements) {
      const place = this.renderer.petriNet.places.get(elementId);
      if (place) {
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 6, 0, Math.PI * 2);
        ctx.strokeStyle = '#FF6B6B'; // Red highlight
        ctx.lineWidth = 4;
        ctx.stroke();
        
        // Add pulsing effect
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 8, 0, Math.PI * 2);
        ctx.strokeStyle = 'rgba(255, 107, 107, 0.5)';
        ctx.lineWidth = 2;
        ctx.stroke();
      }
      
      // Highlight transitions
      const transition = this.renderer.petriNet.transitions.get(elementId);
      if (transition) {
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 6,
          transition.position.y - transition.height / 2 - 6,
          transition.width + 12,
          transition.height + 12
        );
        ctx.strokeStyle = '#4ECDC4'; // Teal highlight
        ctx.lineWidth = 4;
        ctx.stroke();
        
        // Add pulsing effect
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 8,
          transition.position.y - transition.height / 2 - 8,
          transition.width + 16,
          transition.height + 16
        );
        ctx.strokeStyle = 'rgba(78, 205, 196, 0.5)';
        ctx.lineWidth = 2;
        ctx.stroke();
      }
    }
    
    // Highlight arcs
    for (const arcId of this.highlightedArcs) {
      const arc = this.renderer.petriNet.arcs.get(arcId);
      if (arc) {
        const sourceElement = this.renderer.petriNet.places.get(arc.source) || 
                            this.renderer.petriNet.transitions.get(arc.source);
        const targetElement = this.renderer.petriNet.places.get(arc.target) || 
                            this.renderer.petriNet.transitions.get(arc.target);
        
        if (sourceElement && targetElement) {
          const { start, end } = this.renderer.calculateArcEndpoints(sourceElement, targetElement);
          
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = '#FFE66D'; // Yellow highlight
          ctx.lineWidth = 5;
          ctx.stroke();
          
          // Add glow effect
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = 'rgba(255, 230, 109, 0.5)';
          ctx.lineWidth = 8;
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
    const ctx = this.renderer.ctx;
    
    ctx.save();
    ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);
    
    for (const [transitionId, overlay] of this.dataOverlays) {
      const transition = this.renderer.petriNet.transitions.get(transitionId);
      if (!transition) continue;
      
      const x = transition.position.x + 30; // Offset to the right
      const y = transition.position.y - 20; // Offset above
      
      // Background box
      const text = this.formatDataOverlay(overlay);
      const lines = text.split('\n');
      const lineHeight = 14;
      const padding = 8;
      const boxWidth = Math.max(...lines.map(line => ctx.measureText(line).width)) + padding * 2;
      const boxHeight = lines.length * lineHeight + padding * 2;
      
      // Draw background
      ctx.fillStyle = 'rgba(46, 52, 64, 0.9)';
      ctx.fillRect(x, y - boxHeight, boxWidth, boxHeight);
      
      // Draw border
      ctx.strokeStyle = '#88C0D0';
      ctx.lineWidth = 1;
      ctx.strokeRect(x, y - boxHeight, boxWidth, boxHeight);
      
      // Draw text
      ctx.fillStyle = '#ECEFF4';
      ctx.font = '12px monospace';
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
      const changeSymbol = change.changeType === 'created' ? '+' : '~';
      lines.push(`${changeSymbol} ${change.variable}: ${change.oldValue} → ${change.newValue}`);
    }
    
    return lines.join('\n');
  }

  delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

// Enhance the DataPetriNetVerification class to include trace visualization
class EnhancedDataPetriNetVerification extends DataPetriNetVerification {
  constructor(app) {
    super(app);
    this.traceVisualizer = null;
    this.currentCounterexamples = [];
  }

  /**
   * Override startVerification to use enhanced verifier
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
      
      // Use the enhanced verifier
      const verifier = new EnhancedDataAwareVerifier(dpn);
      const result = await verifier.verify((progress, step) => {
        this.updateProgress(progress, step);
      });

      // Store counterexamples for trace visualization
      this.currentCounterexamples = result.counterexampleTraces || [];

      // Initialize trace visualizer
      if (!this.traceVisualizer && this.app.editor.renderer) {
        this.traceVisualizer = new TraceVisualizationRenderer(this.app.editor.renderer);
      }

      modalBody.innerHTML = this.createEnhancedResultsHTML(result);

    } catch (error) {
      console.error('Verification error:', error);
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      verifyButton.disabled = false;
      verifyButton.innerHTML = '<span class="verify-btn-icon">🔍</span> Verify Soundness';
    }
  }

  /**
   * Create enhanced results HTML with counterexample traces
   */
  createEnhancedResultsHTML(result) {
    const isSound = result.isSound;
    const statusClass = isSound ? 'sound' : 'unsound';
    const statusIcon = isSound ? '✅' : '❌';
    const statusText = isSound ? 'Sound' : 'Unsound';

    let html = `
      <div class="verification-algorithm-info">
        <h4>Algorithm: Data-Aware Soundness Verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Based on the approach by Suvorov & Lomazova (2024) for checking soundness of Data Petri nets.
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

    // Add property details
    result.properties.forEach(prop => {
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
            this.createCounterexampleSection(prop.counterexamples, prop.name) : ''}
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
   * Create counterexample section with trace visualization buttons
   */
  createCounterexampleSection(counterexamples, propertyName) {
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
      const traceId = `trace-${propertyName.replace(/\W/g, '')}-${index}`;
      
      html += `
        <div class="counterexample-item" data-trace-id="${traceId}">
          <div class="counterexample-header">
            <span class="counterexample-title">Trace ${index + 1}</span>
            <div class="counterexample-actions">
              <button class="trace-btn" onclick="window.dpnVerification.visualizeTrace(${index}, '${propertyName}')">
                👁️ Visualize
              </button>
              <button class="trace-btn" onclick="window.dpnVerification.animateTrace(${index}, '${propertyName}')">
                ▶️ Animate
              </button>
            </div>
          </div>
          <div class="counterexample-details">
            <strong>Reason:</strong> ${ce.reason}
            ${ce.trace && ce.trace.length > 0 ? 
              `<br><strong>Steps:</strong> ${ce.trace.length}` : ''}
            ${ce.stateData && ce.stateData.dataValuation ? 
              `<br><strong>Data Issues:</strong> ${Object.keys(ce.stateData.dataValuation).length} variables involved` : ''}
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

  /**
   * Visualize a specific trace on the editor
   */
  visualizeTrace(traceIndex, propertyName) {
    if (!this.traceVisualizer) {
      this.initializeTraceVisualizer();
    }

    const counterexample = this.findCounterexample(traceIndex, propertyName);
    if (!counterexample || !counterexample.trace) {
      console.warn('Trace not found');
      return;
    }

    this.traceVisualizer.visualizeTrace(counterexample.trace);
    
    // Update UI to show which trace is being visualized
    this.updateTraceVisualizationUI(traceIndex, propertyName);
  }

  /**
   * Animate a specific trace on the editor
   */
  async animateTrace(traceIndex, propertyName) {
    if (!this.traceVisualizer) {
      this.initializeTraceVisualizer();
    }

    const counterexample = this.findCounterexample(traceIndex, propertyName);
    if (!counterexample || !counterexample.trace) {
      console.warn('Trace not found');
      return;
    }

    await this.traceVisualizer.animateTrace(counterexample.trace);
  }

  /**
   * Clear trace visualization
   */
  clearTraceVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
      this.traceVisualizer.render();
    }
    
    // Clear UI highlights
    document.querySelectorAll('.counterexample-item').forEach(item => {
      item.classList.remove('active-trace');
    });
  }

  /**
   * Initialize trace visualizer
   */
  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer) {
      this.traceVisualizer = new TraceVisualizationRenderer(this.app.editor.renderer);
      
      // Override the renderer's render method to include trace visualization
      const originalRender = this.app.editor.renderer.render.bind(this.app.editor.renderer);
      this.app.editor.renderer.render = () => {
        originalRender();
        if (this.traceVisualizer) {
          this.traceVisualizer.renderHighlights();
          this.traceVisualizer.renderDataOverlays();
        }
      };
    }
  }

  /**
   * Find counterexample by index and property name
   */
  findCounterexample(traceIndex, propertyName) {
    for (const ce of this.currentCounterexamples) {
      // Match by property and index (simplified matching)
      if (this.currentCounterexamples.indexOf(ce) === traceIndex) {
        return ce;
      }
    }
    return null;
  }

  /**
   * Update UI to show active trace
   */
  updateTraceVisualizationUI(traceIndex, propertyName) {
    // Clear previous highlights
    document.querySelectorAll('.counterexample-item').forEach(item => {
      item.classList.remove('active-trace');
    });
    
    // Highlight current trace
    const traceElement = document.querySelector(`[data-trace-id="trace-${propertyName.replace(/\W/g, '')}-${traceIndex}"]`);
    if (traceElement) {
      traceElement.classList.add('active-trace');
    }
  }
}

// Enhanced CSS styles for trace visualization
const enhancedVerificationStyles = `
  /* Counterexample section styles */
  .counterexample-section {
    background-color: #2E3440;
    border-radius: 6px;
    padding: 15px;
    margin-top: 15px;
    border-left: 4px solid #BF616A;
  }

  .counterexample-section h4 {
    margin: 0 0 15px 0;
    color: #BF616A;
    font-weight: 600;
  }

  .counterexample-controls {
    margin-bottom: 15px;
    text-align: right;
  }

  .trace-control-btn {
    background-color: #4C566A;
    color: #ECEFF4;
    border: none;
    padding: 6px 12px;
    border-radius: 4px;
    cursor: pointer;
    font-size: 12px;
    transition: background-color 0.2s;
  }

  .trace-control-btn:hover {
    background-color: #5E81AC;
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

  .counterexample-item.active-trace {
    border-color: #88C0D0;
    background-color: rgba(136, 192, 208, 0.1);
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

  .counterexample-details {
    font-size: 12px;
    color: #D8DEE9;
    line-height: 1.4;
  }
`;

// Inject enhanced styles
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

// Replace the original DataPetriNetVerification with the enhanced version
document.addEventListener('DOMContentLoaded', () => {
  const initEnhancedVerification = () => {
    if (window.petriApp && window.dataPetriNetIntegration) {
      if (!window.enhancedDpnVerification) {
        console.log("Initializing Enhanced Data Petri Net Verification with trace visualization");
        
        // Inject enhanced styles
        injectEnhancedVerificationStyles();
        
        // Create enhanced verification instance
        window.enhancedDpnVerification = new EnhancedDataPetriNetVerification(window.petriApp);
        
        // Replace the original verification instance
        if (window.dpnVerification) {
          window.dpnVerification = window.enhancedDpnVerification;
        }
        
        console.log("Enhanced verification with trace visualization ready");
      }
    } else {
      setTimeout(initEnhancedVerification, 500);
    }
  };
  
  setTimeout(initEnhancedVerification, 1500);
});
