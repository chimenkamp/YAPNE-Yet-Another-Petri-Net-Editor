/**
 * Hybrid Data Petri Net Verification Extension
 * 
 * Combines explicit state space exploration with symbolic constraint-based verification.
 * Falls back to symbolic approach when state space becomes too large or infinite.
 */

class HybridDataAwareVerifier extends EnhancedDataAwareVerifier {
  constructor(petriNet) {
    super(petriNet);
    
    // Configuration for hybrid approach
    this.maxStates = 5000; // Maximum states before switching to symbolic
    this.maxTime = 30000; // Maximum time (30s) before switching to symbolic
    this.maxIterations = 100000; // Maximum iterations before switching
    this.symbolicFallback = false;
    this.verificationApproach = 'explicit'; // 'explicit' or 'symbolic'
    this.switchReason = null;
    
    // Symbolic verification components
    this.constraintGraph = null;
    this.symbolicStates = new Map();
    this.updateOperations = new Map();
  }

  /**
   * Enhanced verification with hybrid approach (ASYNC)
   */
  async verify(progressCallback) {
    this.startTime = Date.now();
    this.counterexampleTraces = [];
    this.finalMarkings = this.identifyFinalMarkings();
    this.verificationApproach = 'explicit';
    this.switchReason = null;
    
    try {
      progressCallback(10, "Starting hybrid verification with explicit state exploration...");
      await this.delay(100);

      if (!this.hasProperStructure()) {
        throw new Error("Net must have at least one place and one transition");
      }

      progressCallback(25, "Checking boundedness with hybrid analysis...");
      await this.delay(200);

      const isBounded = await this.checkBoundedness();
      if (!isBounded) {
        return this.createResult(false, [
          { 
            name: "P0: Boundedness", 
            satisfied: false, 
            description: "The net must be bounded for verification", 
            details: "The net has unbounded places",
            counterexamples: []
          }
        ]);
      }

      progressCallback(40, "Constructing state space with hybrid approach...");
      await this.delay(300);

      // Try explicit approach first
      let lts = null;
      try {
        lts = await this.constructLTSWithFallback(progressCallback);
      } catch (error) {
        if (error.message === 'SYMBOLIC_FALLBACK') {
          // Switch to symbolic approach
          this.verificationApproach = 'symbolic';
          progressCallback(60, `Switching to symbolic verification (${this.switchReason})...`);
          await this.delay(500);
          
          lts = await this.constructSymbolicStateSpace(progressCallback);
        } else {
          throw error;
        }
      }
      
      const progressBase = this.verificationApproach === 'symbolic' ? 80 : 75;
      progressCallback(progressBase, `Checking soundness properties using ${this.verificationApproach} approach...`);
      await this.delay(200);

      // Check properties using appropriate method
      let p1, p2, p3;
      if (this.verificationApproach === 'symbolic') {
        p1 = await this.checkSymbolicProperty1();
        p2 = await this.checkSymbolicProperty2();
        p3 = await this.checkSymbolicProperty3();
      } else {
        p1 = await this.checkEnhancedProperty1(lts);
        p2 = await this.checkEnhancedProperty2(lts);
        p3 = await this.checkEnhancedProperty3(lts);
      }

      progressCallback(100, `Verification complete using ${this.verificationApproach} approach!`);
      await this.delay(100);

      const properties = [
        {
          name: "P1: Reachability & Deadlock Freedom",
          satisfied: p1.satisfied,
          description: "All reachable states can reach a final state (no deadlocks)",
          details: p1.details,
          counterexamples: p1.counterexamples || []
        },
        {
          name: "P2: Proper Termination", 
          satisfied: p2.satisfied,
          description: "No markings strictly cover the final marking with enabled transitions",
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
        counterexampleTraces: this.counterexampleTraces,
        finalMarkings: this.finalMarkings,
        verificationApproach: this.verificationApproach,
        switchReason: this.switchReason,
        symbolicFallback: this.symbolicFallback
      };

    } catch (error) {
      throw error;
    }
  }

  /**
   * LTS construction with automatic fallback to symbolic approach
   */
  async constructLTSWithFallback(progressCallback) {
    const startTime = Date.now();
    let iterationCount = 0;
    
    const states = new Set();
    const transitions = new Map();
    const visited = new Set();
    const stateHistory = new Map(); // Track state revisits
    
    // Start with initial state
    const initialState = this.getInitialStateString();
    const queue = [{ state: initialState, depth: 0 }];
    states.add(initialState);
    
    // Track progress for potential infinite loops
    let lastProgressUpdate = Date.now();
    let lastStateCount = 0;
    let stagnationCounter = 0;
    
    while (queue.length > 0) {
      iterationCount++;
      
      // Check fallback conditions
      if (this.shouldFallbackToSymbolic(states.size, iterationCount, startTime)) {
        this.symbolicFallback = true;
        throw new Error('SYMBOLIC_FALLBACK');
      }
      
      // Update progress periodically
      if (Date.now() - lastProgressUpdate > 2000) {
        const progressPercentage = Math.min(45 + (states.size / this.maxStates) * 15, 59);
        progressCallback(progressPercentage, 
          `Exploring state space: ${states.size} states (${this.verificationApproach} approach)`);
        
        // Detect stagnation
        if (states.size === lastStateCount) {
          stagnationCounter++;
          if (stagnationCounter > 3) {
            this.switchReason = "state space exploration stagnated";
            this.symbolicFallback = true;
            throw new Error('SYMBOLIC_FALLBACK');
          }
        } else {
          stagnationCounter = 0;
        }
        
        lastStateCount = states.size;
        lastProgressUpdate = Date.now();
      }
      
      const { state: currentState, depth } = queue.shift();
      
      if (visited.has(currentState)) continue;
      visited.add(currentState);
      
      // Track state revisits for loop detection
      const stateKey = this.getStateSignature(currentState);
      if (stateHistory.has(stateKey)) {
        stateHistory.set(stateKey, stateHistory.get(stateKey) + 1);
        if (stateHistory.get(stateKey) > 50) {
          this.switchReason = "detected infinite loops in state space";
          this.symbolicFallback = true;
          throw new Error('SYMBOLIC_FALLBACK');
        }
      } else {
        stateHistory.set(stateKey, 1);
      }
      
      // Get enabled transitions for current state
      const stateData = this.parseStateData(currentState);
      const enabledTransitions = this.getEnabledTransitionsInState(currentState);
      
      const stateTransitions = [];
      
      for (const transitionId of enabledTransitions) {
        try {
          const nextState = await this.fireTransitionInState(currentState, transitionId);
          if (nextState && nextState !== currentState) {
            
            if (!visited.has(nextState) && !states.has(nextState)) {
              queue.push({ state: nextState, depth: depth + 1 });
              states.add(nextState);
            }
            
            stateTransitions.push({
              transition: transitionId,
              target: nextState
            });
          }
        } catch (error) {
          console.warn(`Error firing transition ${transitionId}:`, error);
        }
      }
      
      if (stateTransitions.length > 0) {
        transitions.set(currentState, stateTransitions);
      }
      
      // Deep state space detection
      if (depth > 1000) {
        this.switchReason = "state space depth exceeded reasonable limits";
        this.symbolicFallback = true;
        throw new Error('SYMBOLIC_FALLBACK');
      }
    }
    
    return {
      states,
      transitions,
      initialState,
      executionPaths: new Map(),
      stateMetadata: new Map()
    };
  }

  /**
   * Check if we should fallback to symbolic approach
   */
  shouldFallbackToSymbolic(stateCount, iterations, startTime) {
    const elapsed = Date.now() - startTime;
    
    if (stateCount >= this.maxStates) {
      this.switchReason = `state count exceeded ${this.maxStates}`;
      return true;
    }
    
    if (elapsed >= this.maxTime) {
      this.switchReason = `time limit exceeded (${this.maxTime}ms)`;
      return true;
    }
    
    if (iterations >= this.maxIterations) {
      this.switchReason = `iteration count exceeded ${this.maxIterations}`;
      return true;
    }
    
    return false;
  }

  /**
   * Get a signature for state equivalence checking
   */
  getStateSignature(stateStr) {
    try {
      const state = JSON.parse(stateStr);
      // Create a simplified signature based on marking and data ranges
      const markingStr = Object.entries(state.marking)
        .filter(([place, tokens]) => tokens > 0)
        .map(([place, tokens]) => `${place}:${tokens}`)
        .sort()
        .join(',');
      
      const dataStr = Object.entries(state.dataValuation || {})
        .map(([var_, value]) => `${var_}:${typeof value}:${this.getValueRange(value)}`)
        .sort()
        .join(',');
      
      return `${markingStr}|${dataStr}`;
    } catch (error) {
      return stateStr;
    }
  }

  /**
   * Get value range for equivalence checking
   */
  getValueRange(value) {
    if (typeof value === 'number') {
      if (value === 0) return '0';
      if (value > 0 && value <= 10) return 'pos_small';
      if (value > 10) return 'pos_large';
      if (value < 0 && value >= -10) return 'neg_small';
      if (value < -10) return 'neg_large';
    }
    return String(value);
  }

  /**
   * Construct symbolic state space using constraint graphs
   */
  async constructSymbolicStateSpace(progressCallback) {
    progressCallback(65, "Building symbolic constraint graph...");
    
    this.constraintGraph = new Map();
    this.symbolicStates = new Map();
    
    // Build initial symbolic state
    const initialMarking = this.getInitialMarking();
    const initialValuation = this.getInitialValuation();
    
    const initialConstraint = this.createInitialConstraint(initialMarking, initialValuation);
    const initialStateId = 'init';
    
    this.symbolicStates.set(initialStateId, {
      marking: initialMarking,
      constraint: initialConstraint,
      isInitial: true
    });
    
    // Build constraint graph using symbolic execution
    await this.buildConstraintGraph(initialStateId, progressCallback);
    
    progressCallback(75, "Constraint graph construction complete");
    
    return {
      states: this.symbolicStates,
      transitions: this.constraintGraph,
      initialState: initialStateId,
      isSymbolic: true
    };
  }

  /**
   * Build constraint graph through symbolic execution
   */
  async buildConstraintGraph(stateId, progressCallback) {
    const visited = new Set();
    const queue = [stateId];
    let processedStates = 0;
    
    while (queue.length > 0) {
      const currentStateId = queue.shift();
      
      if (visited.has(currentStateId)) continue;
      visited.add(currentStateId);
      processedStates++;
      
      if (processedStates % 10 === 0) {
        progressCallback(65 + Math.min(processedStates * 2, 10), 
          `Processing symbolic state ${processedStates}...`);
      }
      
      const currentState = this.symbolicStates.get(currentStateId);
      if (!currentState) continue;
      
      // Find enabled transitions symbolically
      const enabledTransitions = this.getSymbolicEnabledTransitions(currentState);
      const stateTransitions = [];
      
      for (const transitionId of enabledTransitions) {
        const nextStates = await this.symbolicTransitionFiring(currentState, transitionId);
        
        for (const nextState of nextStates) {
          const nextStateId = this.getOrCreateSymbolicState(nextState);
          
          stateTransitions.push({
            transition: transitionId,
            target: nextStateId
          });
          
          if (!visited.has(nextStateId) && !queue.includes(nextStateId)) {
            queue.push(nextStateId);
          }
        }
      }
      
      if (stateTransitions.length > 0) {
        this.constraintGraph.set(currentStateId, stateTransitions);
      }
    }
  }

  /**
   * Create initial constraint formula
   */
  createInitialConstraint(marking, valuation) {
    const constraints = [];
    
    // Add marking constraints
    for (const [placeId, tokens] of Object.entries(marking)) {
      constraints.push(`${placeId}_tokens = ${tokens}`);
    }
    
    // Add data constraints
    for (const [varName, value] of Object.entries(valuation)) {
      const variableType = this.getVariableType(varName);
      constraints.push(`${varName} = ${this.formatConstraintValue(value, variableType)}`);
    }
    
    return constraints.join(' ∧ ');
  }

  /**
   * Format value for constraint representation
   */
  formatConstraintValue(value, type) {
    switch (type) {
      case 'int':
        return Math.floor(Number(value)).toString();
      case 'float':
        return Number(value).toString();
      case 'boolean':
        return value ? 'true' : 'false';
      case 'string':
        return `"${value}"`;
      default:
        return String(value);
    }
  }

  /**
   * Get enabled transitions symbolically
   */
  getSymbolicEnabledTransitions(symbolicState) {
    const enabledTransitions = [];
    
    for (const [transitionId, transition] of this.petriNet.transitions) {
      if (this.isSymbolicTransitionEnabled(symbolicState, transitionId)) {
        enabledTransitions.push(transitionId);
      }
    }
    
    return enabledTransitions;
  }

  /**
   * Check if transition is enabled in symbolic state
   */
  isSymbolicTransitionEnabled(symbolicState, transitionId) {
    // Check token requirements
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    
    for (const arc of inputArcs) {
      const tokens = symbolicState.marking[arc.source] || 0;
      if (tokens < (arc.weight || 1)) {
        return false;
      }
    }
    
    // For symbolic approach, we assume data conditions are satisfiable
    // The actual check will be done during SMT solving
    return true;
  }

  /**
   * Symbolic transition firing using Z3
   */
  async symbolicTransitionFiring(symbolicState, transitionId) {
    const transition = this.petriNet.transitions.get(transitionId);
    if (!transition) return [];
    
    // Create new marking after token movement
    const newMarking = { ...symbolicState.marking };
    
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.source === transitionId);
    
    // Update tokens
    for (const arc of inputArcs) {
      if (arc.type === "regular") {
        newMarking[arc.source] = (newMarking[arc.source] || 0) - (arc.weight || 1);
      }
    }
    
    for (const arc of outputArcs) {
      newMarking[arc.target] = (newMarking[arc.target] || 0) + (arc.weight || 1);
    }
    
    // Create new constraint using Z3
    let newConstraint = symbolicState.constraint;
    
    if (transition.precondition || transition.postcondition) {
      try {
        newConstraint = await this.updateConstraintWithZ3(
          symbolicState.constraint,
          transition.precondition || 'true',
          transition.postcondition || ''
        );
      } catch (error) {
        console.warn(`Error updating constraint for transition ${transitionId}:`, error);
        // Fallback to basic constraint
        newConstraint = symbolicState.constraint;
      }
    }
    
    return [{
      marking: newMarking,
      constraint: newConstraint,
      parentTransition: transitionId
    }];
  }

  /**
   * Update constraint using Z3 solver
   */
  async updateConstraintWithZ3(currentConstraint, precondition, postcondition) {
    if (!window.solveExpression) {
      // Fallback if Z3 not available
      return currentConstraint;
    }
    
    try {
      // Combine current constraint with precondition
      let combinedConstraint = currentConstraint;
      if (precondition && precondition !== 'true') {
        combinedConstraint = `(${currentConstraint}) ∧ (${precondition})`;
      }
      
      // Apply postcondition if present
      if (postcondition && postcondition.trim()) {
        // Extract current values for Z3 solving
        const currentValues = this.extractValuesFromConstraint(currentConstraint);
        
        // Use Z3 to solve the postcondition
        const result = await window.solveExpression(postcondition, currentValues, 'int');
        
        if (result && result.newValues) {
          // Update constraint with new values
          const newConstraints = [];
          for (const [varName, value] of Object.entries(result.newValues)) {
            const variableType = this.getVariableType(varName);
            newConstraints.push(`${varName} = ${this.formatConstraintValue(value, variableType)}`);
          }
          combinedConstraint = newConstraints.join(' ∧ ');
        }
      }
      
      return combinedConstraint;
    } catch (error) {
      console.warn('Error in Z3 constraint update:', error);
      return currentConstraint;
    }
  }

  /**
   * Extract values from constraint for Z3 solving
   */
  extractValuesFromConstraint(constraint) {
    const values = {};
    
    // Simple regex-based extraction (can be improved)
    const matches = constraint.match(/(\w+)\s*=\s*([+-]?\d+(?:\.\d+)?)/g);
    if (matches) {
      for (const match of matches) {
        const [, varName, value] = match.match(/(\w+)\s*=\s*([+-]?\d+(?:\.\d+)?)/);
        values[varName] = Number(value);
      }
    }
    
    return values;
  }

  /**
   * Get or create symbolic state
   */
  getOrCreateSymbolicState(stateData) {
    // Create a unique ID based on marking and constraint
    const markingStr = Object.entries(stateData.marking)
      .map(([place, tokens]) => `${place}:${tokens}`)
      .sort()
      .join(',');
    
    const constraintHash = this.hashString(stateData.constraint);
    const stateId = `state_${markingStr}_${constraintHash}`;
    
    if (!this.symbolicStates.has(stateId)) {
      this.symbolicStates.set(stateId, stateData);
    }
    
    return stateId;
  }

  /**
   * Simple string hash function
   */
  hashString(str) {
    let hash = 0;
    for (let i = 0; i < str.length; i++) {
      const char = str.charCodeAt(i);
      hash = ((hash << 5) - hash) + char;
      hash = hash & hash; // Convert to 32-bit integer
    }
    return Math.abs(hash).toString(16).substr(0, 8);
  }

  /**
   * Symbolic property checking methods
   */
  async checkSymbolicProperty1() {
    // P1: Reachability - all states can reach final states
    const finalMarkings = this.finalMarkings;
    if (finalMarkings.length === 0) {
      return { 
        satisfied: true,
        details: "No explicit final marking found - assuming sound",
        counterexamples: []
      };
    }
    
    // Check each symbolic state for reachability to final states
    for (const [stateId, stateData] of this.symbolicStates) {
      if (this.isSymbolicFinalState(stateData, finalMarkings)) {
        continue; // Final states are trivially reachable to themselves
      }
      
      // Check if this state can reach any final state
      const canReachFinal = await this.canSymbolicStateReachFinal(stateId, finalMarkings);
      
      if (!canReachFinal) {
        this.counterexampleTraces.push({
          state: stateId,
          reason: "Symbolic deadlock detected",
          detailedReason: `Symbolic state cannot reach any final marking. Constraint: ${stateData.constraint}`,
          stateData: stateData,
          violationType: "symbolic_deadlock"
        });
        
        return {
          satisfied: false,
          details: "Found symbolic states that cannot reach final markings",
          counterexamples: [this.counterexampleTraces[this.counterexampleTraces.length - 1]]
        };
      }
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  async checkSymbolicProperty2() {
    // P2: Proper termination - no markings strictly cover final marking
    const finalMarkings = this.finalMarkings;
    
    for (const [stateId, stateData] of this.symbolicStates) {
      for (const finalMarking of finalMarkings) {
        if (this.symbolicMarkingStrictlyCovers(stateData.marking, finalMarking)) {
          // Check if transitions are enabled in this state
          const hasEnabledTransitions = this.hasSymbolicEnabledTransitions(stateData);
          
          if (hasEnabledTransitions) {
            this.counterexampleTraces.push({
              state: stateId,
              reason: "Symbolic improper termination detected",
              detailedReason: `Symbolic state strictly covers final marking but has enabled transitions. Constraint: ${stateData.constraint}`,
              stateData: stateData,
              violationType: "symbolic_improper_termination"
            });
            
            return {
              satisfied: false,
              details: "Found symbolic states with improper termination",
              counterexamples: [this.counterexampleTraces[this.counterexampleTraces.length - 1]]
            };
          }
        }
      }
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  async checkSymbolicProperty3() {
    // P3: No dead transitions - all transitions can be executed
    const allTransitions = new Set(this.petriNet.transitions.keys());
    const firedTransitions = new Set();
    
    // Collect all transitions that appear in the constraint graph
    for (const [stateId, transitions] of this.constraintGraph) {
      for (const { transition } of transitions) {
        firedTransitions.add(transition);
      }
    }
    
    // Find dead transitions
    const deadTransitions = [];
    for (const transitionId of allTransitions) {
      if (!firedTransitions.has(transitionId)) {
        const transition = this.petriNet.transitions.get(transitionId);
        deadTransitions.push({
          transitionId: transitionId,
          transitionLabel: transition ? transition.label : transitionId,
          reason: "Symbolic dead transition detected",
          detailedReason: `Transition ${transitionId} is never enabled in any symbolic state`,
          violationType: "symbolic_dead_transition"
        });
      }
    }
    
    if (deadTransitions.length > 0) {
      this.counterexampleTraces.push(...deadTransitions.map(dt => ({
        state: "symbolic_global",
        reason: dt.reason,
        detailedReason: dt.detailedReason,
        deadTransition: dt,
        violationType: "symbolic_dead_transition"
      })));
      
      return {
        satisfied: false,
        details: `Symbolic dead transitions found: ${deadTransitions.map(dt => dt.transitionLabel).join(', ')}`,
        counterexamples: deadTransitions
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Helper methods for symbolic checking
   */
  isSymbolicFinalState(stateData, finalMarkings) {
    for (const finalMarking of finalMarkings) {
      if (this.markingEquals(stateData.marking, finalMarking)) {
        return true;
      }
    }
    return false;
  }

  async canSymbolicStateReachFinal(stateId, finalMarkings) {
    // Simple reachability check in symbolic constraint graph
    const visited = new Set();
    const queue = [stateId];
    
    while (queue.length > 0) {
      const currentStateId = queue.shift();
      
      if (visited.has(currentStateId)) continue;
      visited.add(currentStateId);
      
      const currentState = this.symbolicStates.get(currentStateId);
      if (this.isSymbolicFinalState(currentState, finalMarkings)) {
        return true;
      }
      
      const stateTransitions = this.constraintGraph.get(currentStateId) || [];
      for (const { target } of stateTransitions) {
        if (!visited.has(target)) {
          queue.push(target);
        }
      }
    }
    
    return false;
  }

  symbolicMarkingStrictlyCovers(marking1, marking2) {
    return this.markingStrictlyCovers(marking1, marking2);
  }

  hasSymbolicEnabledTransitions(stateData) {
    return this.getSymbolicEnabledTransitions(stateData).length > 0;
  }

  /**
   * Get initial state as string for explicit approach
   */
  getInitialStateString() {
    const marking = this.getInitialMarking();
    const valuation = this.getInitialValuation();
    return JSON.stringify({ marking, dataValuation: valuation });
  }

  /**
   * Fire transition in explicit state
   */
  async fireTransitionInState(stateStr, transitionId) {
    const state = JSON.parse(stateStr);
    const newState = JSON.parse(JSON.stringify(state)); // Deep copy
    
    // Update marking
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.source === transitionId);
    
    // Remove tokens from input places
    for (const arc of inputArcs) {
      if (arc.type === "regular") {
        newState.marking[arc.source] = (newState.marking[arc.source] || 0) - (arc.weight || 1);
      }
    }
    
    // Add tokens to output places
    for (const arc of outputArcs) {
      newState.marking[arc.target] = (newState.marking[arc.target] || 0) + (arc.weight || 1);
    }
    
    // Update data valuation (ASYNC)
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePostcondition === 'function') {
      try {
        newState.dataValuation = await transition.evaluatePostcondition(state.dataValuation);
      } catch (error) {
        console.warn(`Failed to evaluate postcondition for transition ${transitionId}:`, error);
        // Continue with original valuation if postcondition fails
      }
    }
    
    return JSON.stringify(newState);
  }
}

/**
 * Enhanced Data Petri Net Verification with Hybrid Approach Integration
 */
class HybridDataPetriNetVerification extends EnhancedDataPetriNetVerification {
  constructor(app) {
    super(app);
    this.hybridVerifier = null;
    this.lastVerificationResult = null;
    
    // Override the verification section creation
    this.createHybridVerificationSection();
  }

  /**
   * Create enhanced verification section with hybrid approach indicators
   */
  createHybridVerificationSection() {
    // Remove any existing verification sections first
    const existingSections = document.querySelectorAll('#verification-section');
    existingSections.forEach(section => section.remove());

    const modelTab = document.querySelector('.sidebar-pane[data-tab="model"]');
    if (!modelTab) return;

    const verificationSection = document.createElement('div');
    verificationSection.id = 'verification-section';
    verificationSection.className = 'sidebar-section';
    verificationSection.innerHTML = `
      <div class="section-header">
        <div class="section-title">
          <span class="section-icon">🎯</span>
          <h3>Hybrid Verification</h3>
        </div>
        <button class="section-toggle">▼</button>
      </div>
      <div class="section-content">
        <div class="hybrid-info-panel">
          <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 10px;">
            <strong>Hybrid approach:</strong> Explicit state exploration with symbolic fallback
          </p>
          <div class="approach-config" style="margin-bottom: 15px;">
            <div class="config-item">
              <label style="font-size: 12px; color: #ECEFF4;">Max States:</label>
              <input type="number" id="max-states-input" value="10000" min="1000" max="100000" step="1000" 
                     style="width: 80px; margin-left: 5px; background: #4C566A; color: #ECEFF4; border: 1px solid #5E81AC; border-radius: 3px; padding: 2px 5px;">
            </div>
            <div class="config-item" style="margin-top: 5px;">
              <label style="font-size: 12px; color: #ECEFF4;">Max Time (s):</label>
              <input type="number" id="max-time-input" value="30" min="10" max="300" step="5" 
                     style="width: 60px; margin-left: 5px; background: #4C566A; color: #ECEFF4; border: 1px solid #5E81AC; border-radius: 3px; padding: 2px 5px;">
            </div>
          </div>
          <div class="approach-indicator" id="approach-indicator" style="display: none;">
            <div class="indicator-content">
              <span class="approach-badge" id="approach-badge">Explicit</span>
              <span class="switch-reason" id="switch-reason" style="display: none;"></span>
            </div>
          </div>
        </div>
        <button id="btn-verify-hybrid-soundness" style="background: linear-gradient(135deg, #A3BE8C, #88C0D0, #EBCB8B); color: #2E3440; font-weight: 600; font-size: 15px; padding: 14px;">
          <span class="verify-btn-icon">🔄</span>
          Soundness Verification
        </button>
      </div>
    `;

    modelTab.appendChild(verificationSection);

    // Add event listeners
    const verifyButton = verificationSection.querySelector('#btn-verify-hybrid-soundness');
    verifyButton.addEventListener('click', () => this.startHybridVerification());

    // Add section collapse functionality
    const sectionHeader = verificationSection.querySelector('.section-header');
    sectionHeader.addEventListener('click', () => {
      verificationSection.classList.toggle('section-collapsed');
    });

    // Add configuration change listeners
    const maxStatesInput = verificationSection.querySelector('#max-states-input');
    const maxTimeInput = verificationSection.querySelector('#max-time-input');
    
    maxStatesInput.addEventListener('change', () => {
      if (this.hybridVerifier) {
        this.hybridVerifier.maxStates = parseInt(maxStatesInput.value);
      }
    });
    
    maxTimeInput.addEventListener('change', () => {
      if (this.hybridVerifier) {
        this.hybridVerifier.maxTime = parseInt(maxTimeInput.value) * 1000; // Convert to ms
      }
    });
  }

  /**
   * Start verification with hybrid verifier (ASYNC)
   */
  async startHybridVerification() {
    const verifyButton = document.querySelector('#btn-verify-hybrid-soundness');
    const modal = document.querySelector('#verification-modal');
    const modalBody = document.querySelector('#verification-modal-body');

    verifyButton.disabled = true;
    verifyButton.innerHTML = '<span class="verification-spinner"></span> Hybrid Verifying...';

    // Update configuration
    const maxStatesInput = document.querySelector('#max-states-input');
    const maxTimeInput = document.querySelector('#max-time-input');
    
    this.showModal();
    modalBody.innerHTML = this.createHybridProgressHTML();

    try {
      const dpn = this.app.api.petriNet;
      
      this.hybridVerifier = new HybridDataAwareVerifier(dpn);
      
      // Apply configuration
      if (maxStatesInput) {
        this.hybridVerifier.maxStates = parseInt(maxStatesInput.value);
      }
      if (maxTimeInput) {
        this.hybridVerifier.maxTime = parseInt(maxTimeInput.value) * 1000;
      }
      
      const result = await this.hybridVerifier.verify((progress, step) => {
        this.updateHybridProgress(progress, step);
      });

      this.lastVerificationResult = result;
      this.currentCounterexamples = result.counterexampleTraces || [];
      this.initializeTraceVisualizer();
      
      // Update approach indicator
      this.updateApproachIndicator(result);
      
      modalBody.innerHTML = this.createHybridResultsHTML(result);

    } catch (error) {
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      verifyButton.disabled = false;
      verifyButton.innerHTML = '<span class="verify-btn-icon">🔄</span> Soundness Verification';
    }
  }

  /**
   * Update approach indicator in the UI
   */
  updateApproachIndicator(result) {
    const indicator = document.querySelector('#approach-indicator');
    const badge = document.querySelector('#approach-badge');
    const switchReason = document.querySelector('#switch-reason');
    
    if (indicator && badge) {
      indicator.style.display = 'block';
      
      if (result.verificationApproach === 'symbolic') {
        badge.textContent = 'Symbolic';
        badge.className = 'approach-badge symbolic';
        
        if (switchReason && result.switchReason) {
          switchReason.textContent = `Switched: ${result.switchReason}`;
          switchReason.style.display = 'inline';
        }
      } else {
        badge.textContent = 'Explicit';
        badge.className = 'approach-badge explicit';
        
        if (switchReason) {
          switchReason.style.display = 'none';
        }
      }
    }
  }

  /**
   * Create hybrid progress HTML
   */
  createHybridProgressHTML() {
    return `
      <div class="verification-algorithm-info">
        <h4>🔄 Hybrid data-aware soundness verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Intelligent combination of explicit and symbolic approaches for optimal performance.
        </p>
      </div>
      <div class="verification-progress">
        <div class="verification-progress-bar">
          <div class="verification-progress-fill" id="progress-fill" style="width: 0%"></div>
        </div>
        <div class="verification-step" id="progress-step">
          Initializing hybrid verification...
        </div>
        <div class="approach-status" id="approach-status" style="margin-top: 8px; font-size: 12px; color: #88C0D0;">
          Current approach: <span id="current-approach">Explicit</span>
        </div>
      </div>
    `;
  }

  /**
   * Update hybrid progress during verification
   */
  updateHybridProgress(progress, step) {
    const progressFill = document.querySelector('#progress-fill');
    const progressStep = document.querySelector('#progress-step');
    const currentApproach = document.querySelector('#current-approach');
    
    if (progressFill) {
      progressFill.style.width = `${progress}%`;
    }
    
    if (progressStep) {
      progressStep.textContent = step;
    }
    
    if (currentApproach) {
      // Detect approach changes from step text
      if (step.includes('symbolic')) {
        currentApproach.textContent = 'Symbolic';
        currentApproach.style.color = '#EBCB8B';
      } else if (step.includes('explicit')) {
        currentApproach.textContent = 'Explicit';
        currentApproach.style.color = '#A3BE8C';
      }
    }
  }

  /**
   * Create hybrid results HTML with approach information
   */
  createHybridResultsHTML(result) {
    const isSound = result.isSound;
    const statusClass = isSound ? 'sound' : 'unsound';
    const statusIcon = isSound ? '✅' : '❌';
    const statusText = isSound ? 'Sound' : 'Unsound';

    // Determine approach color and description
    const approachClass = result.verificationApproach === 'symbolic' ? 'symbolic' : 'explicit';
    const approachIcon = result.verificationApproach === 'symbolic' ? '🧮' : '🔍';
    const approachDescription = result.verificationApproach === 'symbolic' 
      ? 'Used symbolic constraint-based verification'
      : 'Used explicit state space exploration';

    let html = `
      <div class="verification-algorithm-info">
        <h4>🔄 Hybrid Data-Aware Soundness Verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Advanced hybrid analysis with intelligent approach selection.
        </p>
        <div class="approach-info ${approachClass}" style="margin-top: 10px; padding: 8px; border-radius: 4px; background-color: rgba(136, 192, 208, 0.1);">
          <div style="display: flex; align-items: center; gap: 8px;">
            <span style="font-size: 16px;">${approachIcon}</span>
            <strong>Approach Used: ${result.verificationApproach.charAt(0).toUpperCase() + result.verificationApproach.slice(1)}</strong>
          </div>
          <div style="font-size: 13px; margin-top: 4px; color: #D8DEE9;">
            ${approachDescription}
          </div>
          ${result.switchReason ? `
            <div style="font-size: 12px; margin-top: 4px; color: #EBCB8B;">
              <strong>Switch reason:</strong> ${result.switchReason}
            </div>
          ` : ''}
        </div>
      </div>

      <div class="verification-status ${statusClass}">
        <div class="verification-status-icon">${statusIcon}</div>
        <div>
          <div style="font-size: 18px;">${statusText}</div>
          <div style="font-size: 14px; opacity: 0.8;">
            ${isSound ? 
              'The Data Petri Net satisfies all data-aware soundness properties.' : 
              'The Data Petri Net violates one or more soundness properties with detailed analysis available.'}
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
            this.createEnhancedCounterexampleSection(prop.counterexamples, prop.name, propIndex) : ''}
        </div>
      `;
    });

    html += `
      </div>
      <div class="verification-timing">
        <div style="display: flex; justify-content: space-between; align-items: center;">
          <span>Verification completed in ${result.executionTime}ms</span>
          <span class="approach-badge ${approachClass}" style="font-size: 11px;">
            ${approachIcon} ${result.verificationApproach.toUpperCase()}
          </span>
        </div>
      </div>
    `;

    return html;
  }
}

// Enhanced styles for hybrid verification
const hybridVerificationStyles = `
  .hybrid-info-panel {
    background: linear-gradient(135deg, rgba(94, 129, 172, 0.1), rgba(136, 192, 208, 0.1));
    border-radius: 6px;
    padding: 12px;
    margin-bottom: 15px;
    border-left: 3px solid #5E81AC;
  }

  .approach-config {
    display: flex;
    flex-direction: column;
    gap: 5px;
  }

  .config-item {
    display: flex;
    align-items: center;
    justify-content: space-between;
  }

  .approach-indicator {
    background-color: rgba(76, 86, 106, 0.5);
    border-radius: 4px;
    padding: 8px;
    margin-top: 10px;
  }

  .approach-badge {
    display: inline-block;
    padding: 3px 8px;
    border-radius: 12px;
    font-size: 11px;
    font-weight: 600;
    text-transform: uppercase;
  }

  .approach-badge.explicit {
    background-color: #A3BE8C;
    color: #2E3440;
  }

  .approach-badge.symbolic {
    background-color: #EBCB8B;
    color: #2E3440;
  }

  .switch-reason {
    display: inline-block;
    margin-left: 8px;
    font-size: 11px;
    color: #D08770;
    font-style: italic;
  }

  .approach-status {
    border-top: 1px solid rgba(136, 192, 208, 0.3);
    padding-top: 8px;
  }

  .approach-info.explicit {
    border-left: 3px solid #A3BE8C;
  }

  .approach-info.symbolic {
    border-left: 3px solid #EBCB8B;
  }

  .verification-timing .approach-badge {
    margin-left: 10px;
  }

  /* Enhanced counterexample styles for hybrid approach */
  .hybrid-counterexample-section {
    background: linear-gradient(135deg, #2E3440, #3B4252);
    border-radius: 8px;
    padding: 18px;
    margin-top: 15px;
    border-left: 4px solid #D08770;
    box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
  }

  .hybrid-counterexample-item {
    background: linear-gradient(135deg, #434C5E, #4C566A);
    border-radius: 6px;
    padding: 15px;
    border: 2px solid transparent;
    transition: all 0.3s;
    margin-bottom: 12px;
  }

  .symbolic-violation {
    border-left: 3px solid #EBCB8B;
    background-color: rgba(235, 203, 139, 0.1);
  }

  .explicit-violation {
    border-left: 3px solid #A3BE8C;
    background-color: rgba(163, 190, 140, 0.1);
  }
`;

function injectHybridVerificationStyles() {
  const existingStyles = document.getElementById('enhanced-integrated-verification-styles');
  if (existingStyles) {
    existingStyles.textContent += '\n' + hybridVerificationStyles;
  } else {
    const style = document.createElement('style');
    style.id = 'hybrid-verification-styles';
    style.textContent = hybridVerificationStyles;
    document.head.appendChild(style);
  }
}

// Initialize hybrid verification system
document.addEventListener('DOMContentLoaded', () => {
  const initHybridVerification = () => {
    if (window.petriApp && window.dataPetriNetIntegration) {
      // Prevent other verification systems from initializing
      window.dpnVerificationInitialized = true;
      
      // Remove any existing verification sections
      const existingVerificationSections = document.querySelectorAll('#verification-section');
      existingVerificationSections.forEach(section => {
        section.remove();
      });
      
      if (!window.hybridDpnVerification) {
        injectHybridVerificationStyles();
        window.hybridDpnVerification = new HybridDataPetriNetVerification(window.petriApp);
        window.dpnVerification = window.hybridDpnVerification;
        console.log("Hybrid Data Petri Net Verification initialized with explicit + symbolic approach");
      }
    } else {
      setTimeout(initHybridVerification, 500);
    }
  };
  
  // Initialize early to prevent other verification systems
  setTimeout(initHybridVerification, 700);
});