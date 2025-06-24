/**
 * Enhanced Data Petri Net Verification Extension with Integrated Detailed Analysis
 * 
 * Integrates comprehensive counterexample analysis with detailed reasons,
 * problematic marking visualization, and responsible variable highlighting
 * into the existing class structure. Updated to support int/float types.
 */

class EnhancedDataAwareVerifier extends DataAwareVerifier {
  constructor(petriNet) {
    super(petriNet);
    this.traceCapture = true;
    this.counterexampleTraces = [];
    this.finalMarkings = [];
  }

  /**
   * Enhanced verification method with detailed counterexample capture (ASYNC)
   */
  async verify(progressCallback) {
    this.startTime = Date.now();
    this.counterexampleTraces = [];
    this.finalMarkings = this.identifyFinalMarkings();
    
    try {
      progressCallback(10, "Analyzing net structure and identifying final markings...");
      await this.delay(100);

      if (!this.hasProperStructure()) {
        throw new Error("Net must have at least one place and one transition");
      }

      progressCallback(25, "Checking boundedness with detailed analysis...");
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

      progressCallback(50, "Constructing state space with detailed trace capture...");
      await this.delay(300);

      const lts = await this.constructLTS();
      
      progressCallback(75, "Checking soundness properties with comprehensive counterexample analysis...");
      await this.delay(200);

      const p1 = await this.checkEnhancedProperty1(lts);
      const p2 = await this.checkEnhancedProperty2(lts);
      const p3 = await this.checkEnhancedProperty3(lts);

      progressCallback(100, "Verification complete with detailed analysis!");
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
        finalMarkings: this.finalMarkings
      };

    } catch (error) {
      throw error;
    }
  }

  /**
   * Enhanced Property 1 checking with detailed deadlock analysis (ASYNC)
   */
  async checkEnhancedProperty1(lts) {
    if (this.finalMarkings.length === 0) {
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
      
      if (!hasEnabledTransitions && !this.isFinalState(stateData, this.finalMarkings)) {
        const trace = await this.buildTraceToState(state, lts);
        const analysis = this.analyzeDeadlockCause(stateData, state, lts);
        
        deadlockStates.push({
          state: state,
          trace: trace,
          reason: analysis.reason,
          detailedReason: analysis.detailedReason,
          stateData: stateData,
          problematicPlaces: analysis.problematicPlaces,
          responsibleVariables: analysis.responsibleVariables,
          expectedFinalMarking: this.finalMarkings[0], // Use first final marking
          actualMarking: stateData.marking,
          violationType: "deadlock"
        });
      }
    }

    if (deadlockStates.length > 0) {
      this.counterexampleTraces.push(...deadlockStates);
      return { 
        satisfied: false, 
        details: `Found ${deadlockStates.length} deadlock states`,
        counterexamples: deadlockStates
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced Property 2 checking with detailed coverage analysis (ASYNC)
   */
  async checkEnhancedProperty2(lts) {
    if (this.finalMarkings.length === 0) {
      return { satisfied: true, counterexamples: [] };
    }
    
    const violations = [];
    
    for (const stateStr of lts.states) {
      const state = JSON.parse(stateStr);
      
      for (const finalMarking of this.finalMarkings) {
        if (this.markingStrictlyCovers(state.marking, finalMarking)) {
          const hasEnabledTransitions = this.hasEnabledTransitionsInState(stateStr, lts);
          
          if (hasEnabledTransitions) {
            const trace = await this.buildTraceToState(stateStr, lts);
            const analysis = this.analyzeProperTerminationViolation(state, finalMarking, stateStr, lts);
            
            violations.push({
              state: stateStr,
              trace: trace,
              reason: analysis.reason,
              detailedReason: analysis.detailedReason,
              stateData: this.parseStateData(stateStr),
              problematicPlaces: analysis.problematicPlaces,
              responsibleVariables: analysis.responsibleVariables,
              coveringMarking: state.marking,
              finalMarking: finalMarking,
              enabledTransitions: analysis.enabledTransitions,
              violationType: "improper_termination"
            });
          }
        }
      }
    }

    if (violations.length > 0) {
      this.counterexampleTraces.push(...violations);
      return { 
        satisfied: false, 
        details: `Found ${violations.length} improper termination violations`,
        counterexamples: violations
      };
    }
    
    return { satisfied: true, counterexamples: [] };
  }

  /**
   * Enhanced Property 3 checking with detailed dead transition analysis (ASYNC)
   */
  async checkEnhancedProperty3(lts) {
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
    
    const deadTransitions = [];
    for (const [id, transition] of this.petriNet.transitions) {
      if (!transitionsFired.has(id) && !transitionsEnabledButNotFired.has(id)) {
        const analysis = await this.analyzeDeadTransition(id, transition, lts); // Make this async
        
        deadTransitions.push({
          transitionId: id,
          transitionLabel: transition.label || id,
          reason: analysis.reason,
          detailedReason: analysis.detailedReason,
          preventingConditions: analysis.preventingConditions,
          problematicPlaces: analysis.problematicPlaces,
          responsibleVariables: analysis.responsibleVariables,
          violationType: "dead_transition"
        });
      }
    }
    
    if (deadTransitions.length > 0) {
      this.counterexampleTraces.push(...deadTransitions.map(dt => ({
        state: "global",
        trace: [],
        reason: dt.reason,
        detailedReason: dt.detailedReason,
        deadTransition: dt,
        violationType: "dead_transition",
        problematicPlaces: dt.problematicPlaces,
        responsibleVariables: dt.responsibleVariables
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
   * Analyze the cause of a deadlock
   */
  analyzeDeadlockCause(stateData, stateStr, lts) {
    const problematicPlaces = [];
    const responsibleVariables = [];
    let reason = "Deadlock detected";
    let detailedReason = "";

    // Check which transitions are disabled and why
    const disabledReasons = [];
    
    for (const [id, transition] of this.petriNet.transitions) {
      const tokenEnabled = this.isTransitionTokenEnabledInState(id, stateData);
      const dataEnabled = this.isTransitionDataEnabledInState(id, stateData);
      
      if (!tokenEnabled) {
        const missingTokens = this.findMissingTokens(id, stateData);
        if (missingTokens.length > 0) {
          problematicPlaces.push(...missingTokens);
          disabledReasons.push(`${transition.label || id}: insufficient tokens in ${missingTokens.map(p => p.placeName).join(', ')}`);
        }
      } else if (!dataEnabled) {
        const failedGuards = this.findFailedDataGuards(id, stateData);
        if (failedGuards.length > 0) {
          responsibleVariables.push(...failedGuards);
          disabledReasons.push(`${transition.label || id}: data guard failed (${failedGuards.map(v => `${v.variable}=${this.formatVariableValue(v.value, v.type)}`).join(', ')})`);
        }
      }
    }

    detailedReason = `No transitions are enabled in this state. ` +
      `Current marking: ${this.formatMarking(stateData.marking)}. ` +
      `Data values: ${this.formatDataValuation(stateData.dataValuation)}. ` +
      `Disabled transitions: ${disabledReasons.join('; ')}.`;

    return {
      reason,
      detailedReason,
      problematicPlaces,
      responsibleVariables
    };
  }

  /**
   * Analyze proper termination violation
   */
  analyzeProperTerminationViolation(state, finalMarking, stateStr, lts) {
    const problematicPlaces = [];
    const responsibleVariables = [];
    const enabledTransitions = [];

    // Find places with excess tokens
    for (const [placeId, tokens] of Object.entries(state.marking)) {
      const finalTokens = finalMarking[placeId] || 0;
      if (tokens > finalTokens) {
        const place = this.findPlaceById(placeId);
        problematicPlaces.push({
          placeId: placeId,
          placeName: place ? place.label : placeId,
          actualTokens: tokens,
          expectedTokens: finalTokens,
          excessTokens: tokens - finalTokens
        });
      }
    }

    // Find enabled transitions
    const stateTransitions = this.getEnabledTransitionsInState(stateStr);
    for (const transitionId of stateTransitions) {
      const transition = this.petriNet.transitions.get(transitionId);
      enabledTransitions.push({
        transitionId,
        transitionLabel: transition ? transition.label : transitionId
      });
    }

    // Check if data conditions contribute to the problem
    for (const [varName, value] of Object.entries(state.dataValuation)) {
      if (this.isVariableContributingToTerminationProblem(varName, value, state)) {
        const variableType = this.getVariableType(varName);
        responsibleVariables.push({
          variable: varName,
          value: value,
          type: variableType,
          problem: "contributes to improper termination"
        });
      }
    }

    const reason = "Improper termination: marking strictly covers final marking with enabled transitions";
    const detailedReason = `The current marking has excess tokens compared to the final marking, ` +
      `but transitions are still enabled. ` +
      `Excess tokens in: ${problematicPlaces.map(p => `${p.placeName}(+${p.excessTokens})`).join(', ')}. ` +
      `Enabled transitions: ${enabledTransitions.map(t => t.transitionLabel).join(', ')}. ` +
      `This violates proper termination as the net should stop at the final marking.`;

    return {
      reason,
      detailedReason,
      problematicPlaces,
      responsibleVariables,
      enabledTransitions
    };
  }

  /**
   * Analyze dead transition (ASYNC - Fixed to handle async data updates)
   */
  async analyzeDeadTransition(transitionId, transition, lts) {
    const problematicPlaces = [];
    const responsibleVariables = [];
    const preventingConditions = [];

    // Check input places
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    
    let hasInsufficientTokenIssue = false;
    let hasDataGuardIssue = false;

    for (const arc of inputArcs) {
      const place = this.petriNet.places.get(arc.source);
      if (place) {
        // Check if this place ever has enough tokens across all states
        let maxTokensFound = 0;
        for (const state of lts.states) {
          const stateData = JSON.parse(state);
          const tokens = stateData.marking[arc.source] || 0;
          maxTokensFound = Math.max(maxTokensFound, tokens);
        }
        
        if (maxTokensFound < arc.weight) {
          problematicPlaces.push({
            placeId: arc.source,
            placeName: place.label,
            requiredTokens: arc.weight,
            maxFoundTokens: maxTokensFound,
            deficit: arc.weight - maxTokensFound
          });
          hasInsufficientTokenIssue = true;
        }
      }
    }

    // Check data guards (ASYNC)
    if (typeof transition.evaluatePrecondition === 'function' && transition.precondition) {
      const guardAnalysis = await this.analyzeDataGuardSatisfiability(transition, lts);
      if (!guardAnalysis.canBeSatisfied) {
        hasDataGuardIssue = true;
        responsibleVariables.push(...guardAnalysis.problematicVariables);
        preventingConditions.push(guardAnalysis.reason);
      }
    }

    let reason, detailedReason;
    
    if (hasInsufficientTokenIssue && hasDataGuardIssue) {
      reason = "Dead transition: insufficient tokens AND unsatisfiable data guard";
      detailedReason = `Transition "${transition.label || transitionId}" is dead due to multiple issues: ` +
        `insufficient tokens (${problematicPlaces.map(p => `${p.placeName} needs ${p.requiredTokens}, max found ${p.maxFoundTokens}`).join(', ')}) ` +
        `and unsatisfiable data guard (${preventingConditions.join(', ')}).`;
    } else if (hasInsufficientTokenIssue) {
      reason = "Dead transition: insufficient tokens in input places";
      detailedReason = `Transition "${transition.label || transitionId}" is dead because input places never have enough tokens: ` +
        `${problematicPlaces.map(p => `${p.placeName} needs ${p.requiredTokens} but maximum found is ${p.maxFoundTokens}`).join(', ')}.`;
    } else if (hasDataGuardIssue) {
      reason = "Dead transition: unsatisfiable data guard";
      detailedReason = `Transition "${transition.label || transitionId}" is dead because its data guard can never be satisfied: ` +
        `${preventingConditions.join(', ')}.`;
    } else {
      reason = "Dead transition: unknown cause";
      detailedReason = `Transition "${transition.label || transitionId}" is never fired, but the exact cause could not be determined.`;
    }

    return {
      reason,
      detailedReason,
      preventingConditions,
      problematicPlaces,
      responsibleVariables
    };
  }

  // Helper methods for detailed analysis
  findMissingTokens(transitionId, stateData) {
    const missingTokens = [];
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    
    for (const arc of inputArcs) {
      const place = this.petriNet.places.get(arc.source);
      if (place) {
        const currentTokens = stateData.marking[arc.source] || 0;
        if (currentTokens < arc.weight) {
          missingTokens.push({
            placeId: arc.source,
            placeName: place.label,
            currentTokens,
            requiredTokens: arc.weight,
            missingTokens: arc.weight - currentTokens
          });
        }
      }
    }
    
    return missingTokens;
  }

  findFailedDataGuards(transitionId, stateData) {
    const failedGuards = [];
    const transition = this.petriNet.transitions.get(transitionId);
    
    if (transition && typeof transition.evaluatePrecondition === 'function') {
      try {
        const isEnabled = transition.evaluatePrecondition(stateData.dataValuation);
        if (!isEnabled) {
          for (const [varName, value] of Object.entries(stateData.dataValuation)) {
            const variableType = this.getVariableType(varName);
            failedGuards.push({
              variable: varName,
              value: value,
              type: variableType,
              guard: transition.precondition || "unknown guard"
            });
          }
        }
      } catch (error) {
        failedGuards.push({
          variable: "evaluation_error",
          value: error.message,
          type: "error",
          guard: transition.precondition || "unknown guard"
        });
      }
    }
    
    return failedGuards;
  }

  /**
   * Get the type of a variable by name
   * @param {string} varName - Variable name
   * @returns {string} Variable type
   */
  getVariableType(varName) {
    if (this.petriNet.dataVariables) {
      for (const [id, variable] of this.petriNet.dataVariables) {
        if (variable.name === varName) {
          return variable.type;
        }
      }
    }
    return 'unknown';
  }

  /**
   * Format variable value based on its type
   * @param {*} value - The value to format
   * @param {string} type - The type of the variable
   * @returns {string} Formatted value
   */
  formatVariableValue(value, type) {
    if (value === undefined || value === null) return 'null';
    
    switch (type) {
      case 'int':
        return Math.floor(Number(value)).toString();
      case 'float':
        const floatValue = Number(value);
        return floatValue % 1 === 0 ? floatValue.toString() : floatValue.toFixed(3).replace(/\.?0+$/, '');
      case 'boolean':
        return value ? 'true' : 'false';
      case 'string':
        return `"${value}"`;
      default:
        return value.toString();
    }
  }

  isTransitionTokenEnabledInState(transitionId, stateData) {
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    
    for (const arc of inputArcs) {
      const tokens = stateData.marking[arc.source] || 0;
      if (tokens < arc.weight) {
        return false;
      }
    }
    
    return true;
  }

  /**
   * Enhanced LTS construction with execution path tracking (ASYNC)
   */
  async constructLTS() {
    const lts = await super.constructLTS();
    
    // Add execution path tracking
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
   * Get transition label for display
   */
  getTransitionLabel(transitionId) {
    const transition = this.petriNet.transitions.get(transitionId);
    return transition ? (transition.label || transitionId) : transitionId;
  }

  isTransitionDataEnabledInState(transitionId, stateData) {
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePrecondition === 'function') {
      try {
        return transition.evaluatePrecondition(stateData.dataValuation);
      } catch (error) {
        return false;
      }
    }
    return true;
  }

  /**
   * Enhanced data guard satisfiability analysis (ASYNC)
   */
  async analyzeDataGuardSatisfiability(transition, lts) {
    const problematicVariables = [];
    let canBeSatisfied = false;
    let reason = "Data guard is never satisfied";

    if (!transition.precondition) {
      return { canBeSatisfied: true, problematicVariables: [], reason: "No guard" };
    }

    // Check across all states if the guard is ever satisfied
    for (const state of lts.states) {
      const stateData = JSON.parse(state);
      try {
        if (transition.evaluatePrecondition(stateData.dataValuation)) {
          canBeSatisfied = true;
          break;
        }
      } catch (error) {
        // Continue checking other states
      }
    }

    if (!canBeSatisfied) {
      const variableRanges = this.analyzeVariableRanges(lts);
      
      // Get all available variables from the petri net definition if ranges are incomplete
      const allVariables = new Set();
      if (this.petriNet.dataVariables) {
        for (const [id, variable] of this.petriNet.dataVariables) {
          allVariables.add(variable.name);
        }
      }
      
      // Add variables from ranges analysis
      for (const varName of Object.keys(variableRanges)) {
        allVariables.add(varName);
      }
      
      // Create problematic variables list
      for (const varName of allVariables) {
        const range = variableRanges[varName];
        const variableType = this.getVariableType(varName);
        
        // Get current value from petri net definition if range analysis failed
        let currentValue = null;
        if (this.petriNet.dataVariables) {
          for (const [id, variable] of this.petriNet.dataVariables) {
            if (variable.name === varName) {
              currentValue = variable.getValue ? variable.getValue() : variable.currentValue;
              break;
            }
          }
        }
        
        problematicVariables.push({
          variable: varName,
          type: variableType,
          minValue: range ? range.min : currentValue,
          maxValue: range ? range.max : currentValue,
          currentValue: currentValue,
          guard: transition.precondition
        });
      }
      
      reason = `Guard "${transition.precondition}" is never satisfied with available variable ranges`;
    }

    return { canBeSatisfied, problematicVariables, reason };
  }

  /**
   * Enhanced variable range analysis with proper undefined handling
   */
  analyzeVariableRanges(lts) {
    const ranges = {};
    
    for (const state of lts.states) {
      const stateData = JSON.parse(state);
      
      // Ensure dataValuation exists
      if (!stateData.dataValuation) {
        continue;
      }
      
      for (const [varName, value] of Object.entries(stateData.dataValuation)) {
        // Get variable type
        const variableType = this.getVariableType(varName);
        
        // Skip undefined, null, or non-numeric values for range analysis (except for known numeric types)
        if (value === undefined || value === null) {
          continue;
        }
        
        // Handle different types appropriately
        if (variableType === 'int' || variableType === 'float') {
          const numericValue = Number(value);
          if (isNaN(numericValue)) continue;
          
          if (!ranges[varName]) {
            ranges[varName] = { min: numericValue, max: numericValue };
          } else {
            ranges[varName].min = Math.min(ranges[varName].min, numericValue);
            ranges[varName].max = Math.max(ranges[varName].max, numericValue);
          }
        } else if (variableType === 'boolean') {
          // For boolean, track the possible values
          if (!ranges[varName]) {
            ranges[varName] = { values: new Set([value]) };
          } else {
            if (!ranges[varName].values) ranges[varName].values = new Set();
            ranges[varName].values.add(value);
          }
        } else if (variableType === 'string') {
          // For string, track the possible values
          if (!ranges[varName]) {
            ranges[varName] = { values: new Set([value]) };
          } else {
            if (!ranges[varName].values) ranges[varName].values = new Set();
            ranges[varName].values.add(value);
          }
        }
      }
    }
    
    return ranges;
  }

  isVariableContributingToTerminationProblem(varName, value, state) {
    for (const [id, transition] of this.petriNet.transitions) {
      if (typeof transition.evaluatePrecondition === 'function' && 
          transition.precondition && 
          transition.precondition.includes(varName)) {
        return true;
      }
    }
    return false;
  }

  findPlaceById(placeId) {
    return this.petriNet.places.get(placeId);
  }

  formatMarking(marking) {
    return Object.entries(marking)
      .filter(([place, tokens]) => tokens > 0)
      .map(([place, tokens]) => {
        const placeObj = this.findPlaceById(place);
        const placeName = placeObj ? placeObj.label : place;
        return `${placeName}(${tokens})`;
      })
      .join(', ') || 'empty';
  }

  formatDataValuation(valuation) {
    if (!valuation) return 'no data';
    
    return Object.entries(valuation)
      .map(([variable, value]) => {
        const variableType = this.getVariableType(variable);
        return `${variable}=${this.formatVariableValue(value, variableType)}`;
      })
      .join(', ') || 'no data';
  }

  // Additional helper methods that were missing
  parseStateData(stateStr) {
    try {
      const parsed = JSON.parse(stateStr);
      
      // Ensure dataValuation exists and is properly initialized
      if (!parsed.dataValuation) {
        parsed.dataValuation = this.getInitialValuation();
      }
      
      return parsed;
    } catch (error) {
      return { 
        marking: {}, 
        dataValuation: this.getInitialValuation() 
      };
    }
  }

  hasEnabledTransitionsInState(stateStr, lts) {
    const stateTransitions = lts.transitions.get(stateStr) || [];
    return stateTransitions.length > 0;
  }

  isFinalState(stateData, finalMarkings) {
    for (const finalMarking of finalMarkings) {
      if (this.markingEquals(stateData.marking, finalMarking)) {
        return true;
      }
    }
    return false;
  }

  async buildTraceToState(targetState, lts) {
    const trace = [];
    const path = lts.executionPaths ? lts.executionPaths.get(targetState) : [];
    
    if (!path) {
      // If no execution path is available, create a simple trace
      trace.push({
        step: 0,
        action: "State reached",
        transitionId: null,
        transitionLabel: "Unknown path",
        marking: this.parseStateData(targetState).marking,
        dataValuation: this.parseStateData(targetState).dataValuation,
        timestamp: new Date().toISOString()
      });
      return trace;
    }
    
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
        const newState = await this.simulateTransitionFiring(currentMarking, currentValuation, step.transitionId);
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

  getInitialMarking() {
    const marking = {};
    for (const [id, place] of this.petriNet.places) {
      marking[id] = place.tokens || 0;
    }
    return marking;
  }

  getInitialValuation() {
    const valuation = {};
    if (this.petriNet.dataVariables) {
      for (const [id, variable] of this.petriNet.dataVariables) {
        const value = variable.getValue ? variable.getValue() : variable.currentValue;
        // Ensure we have a valid value, use appropriate defaults based on type
        if (value === undefined || value === null) {
          switch (variable.type) {
            case 'int':
            case 'float':
              valuation[variable.name] = 0;
              break;
            case 'boolean':
              valuation[variable.name] = false;
              break;
            case 'string':
              valuation[variable.name] = '';
              break;
            default:
              valuation[variable.name] = 0;
          }
        } else {
          valuation[variable.name] = value;
        }
      }
    }
    return valuation;
  }

  async simulateTransitionFiring(marking, valuation, transitionId) {
    const newMarking = { ...marking };
    let newValuation = { ...valuation };
    
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.source === transitionId);
    
    for (const arc of inputArcs) {
      if (arc.type === "regular") {
        newMarking[arc.source] = (newMarking[arc.source] || 0) - (arc.weight || 1);
      }
    }
    
    for (const arc of outputArcs) {
      newMarking[arc.target] = (newMarking[arc.target] || 0) + (arc.weight || 1);
    }
    
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePostcondition === 'function') {
      try {
        newValuation = await transition.evaluatePostcondition(valuation);
      } catch (error) {
        console.warn(`Failed to evaluate postcondition for transition ${transitionId}:`, error);
        // Keep the original valuation if postcondition fails
      }
    }
    
    return { marking: newMarking, dataValuation: newValuation };
  }

  detectDataChanges(oldValuation, newValuation) {
    const changes = [];
    
    if (!oldValuation || !newValuation) return changes;
    
    for (const [variable, newValue] of Object.entries(newValuation)) {
      const oldValue = oldValuation[variable];
      if (oldValue !== newValue) {
        const variableType = this.getVariableType(variable);
        changes.push({
          variable: variable,
          type: variableType,
          oldValue: oldValue !== undefined ? this.formatVariableValue(oldValue, variableType) : 'undefined',
          newValue: newValue !== undefined ? this.formatVariableValue(newValue, variableType) : 'undefined',
          changeType: oldValue === undefined ? 'created' : 'modified'
        });
      }
    }
    
    return changes;
  }

  getEnabledTransitionsInState(stateStr) {
    const state = this.parseStateData(stateStr);
    const enabled = [];
    
    for (const [id, transition] of this.petriNet.transitions) {
      if (this.isTransitionEnabledInState(id, state)) {
        enabled.push(id);
      }
    }
    
    return enabled;
  }

  isTransitionEnabledInState(transitionId, state) {
    // Check token prerequisites
    const inputArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);
    
    for (const arc of inputArcs) {
      const tokens = state.marking[arc.source] || 0;
      if (tokens < (arc.weight || 1)) {
        return false;
      }
    }
    
    // Check data precondition
    const transition = this.petriNet.transitions.get(transitionId);
    if (transition && typeof transition.evaluatePrecondition === 'function') {
      try {
        return transition.evaluatePrecondition(state.dataValuation);
      } catch (error) {
        return false;
      }
    }
    
    return true;
  }
}

/**
 * Enhanced Trace Visualization Renderer with detailed highlighting and type-aware display
 */
class TraceVisualizationRenderer {
  constructor(app) {
    this.app = app;
    this.mainRenderer = app.editor.renderer;
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.problematicPlaces = new Map();
    this.responsibleVariables = new Map();
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

  /**
   * Enhanced trace visualization with problem highlighting
   */
  visualizeCounterexample(counterexample, currentStep = -1) {
    this.clearHighlights();
    this.isActive = true;
    this.violationInfo = counterexample;

    // Store problematic elements for special highlighting
    if (counterexample.problematicPlaces) {
      for (const place of counterexample.problematicPlaces) {
        this.problematicPlaces.set(place.placeId, place);
 
      }
    }

    if (counterexample.responsibleVariables) {
      for (const variable of counterexample.responsibleVariables) {
        this.responsibleVariables.set(variable.variable, variable);
      }
    }

    // Handle different types of counterexamples
    if (counterexample.violationType === "dead_transition") {
      this.visualizeDeadTransition(counterexample);
    } else if (counterexample.trace) {
      // Visualize the trace if available (for P1, P2)
      this.visualizeTrace(counterexample.trace, currentStep);
    }

    // Add special highlighting for problematic elements
    this.addProblemHighlighting();
    
    this.mainRenderer.render();
  }

  /**
   * Visualize dead transition counterexample (P3)
   */
  visualizeDeadTransition(counterexample) {
    if (!counterexample.deadTransition) return;

    const transitionId = counterexample.deadTransition.transitionId;
    
    // Highlight the dead transition
    this.highlightedElements.add(transitionId);
    
    // Highlight all connected elements (places and arcs)
    this.highlightConnectedElements(transitionId);
    
    // Add data overlay showing why the transition is dead
    this.addDeadTransitionDataOverlay(transitionId, counterexample.deadTransition);
    
    // Highlight problematic input places
    if (counterexample.problematicPlaces) {
      for (const place of counterexample.problematicPlaces) {
        this.highlightedElements.add(place.placeId);
      }
    }
  }

  /**
   * Add data overlay explaining why a transition is dead
   */
  addDeadTransitionDataOverlay(transitionId, deadTransition) {
    const petriNet = this.mainRenderer.petriNet;
    const transition = petriNet.transitions.get(transitionId);
    if (!transition) return;
    
    // Create overlay data explaining the problem
    const overlayData = {
      transitionLabel: deadTransition.transitionLabel,
      reason: deadTransition.reason,
      detailedReason: deadTransition.detailedReason,
      problematicPlaces: deadTransition.problematicPlaces || [],
      responsibleVariables: deadTransition.responsibleVariables || [],
      preventingConditions: deadTransition.preventingConditions || []
    };
    
    this.dataOverlays.set(transitionId, {
      type: 'deadTransition',
      data: overlayData,
      position: { ...transition.position }
    });
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

    // Add final trace Token marking
    const finalMarking = trace[trace.length - 1].marking || {};
    
    for (const [placeId, tokens] of Object.entries(finalMarking)) {
       this.app.api.setPlaceTokens(placeId, tokens);
       this.app.updateTokensDisplay();
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
   * Add special highlighting for problematic places and responsible variables
   */
  addProblemHighlighting() {
    // Highlight problematic places
    for (const [placeId, placeInfo] of this.problematicPlaces) {
      this.highlightedElements.add(placeId);
    }

    // For dead transitions, highlight the transition itself
    if (this.violationInfo && this.violationInfo.deadTransition) {
      this.highlightedElements.add(this.violationInfo.deadTransition.transitionId);
    }
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
    this.problematicPlaces.clear();
    this.responsibleVariables.clear();
    this.violationInfo = null;
    this.isActive = false;
    this.mainRenderer.render();
  }

  /**
   * Animate through trace steps (ASYNC)
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
        // Check if this is a problematic place for special highlighting
        const placeInfo = this.problematicPlaces.get(elementId);
        if (placeInfo) {
          // Different colors based on problem type
          let highlightColor = '#FF0000'; // Default red
          let strokeColor = 'rgba(255, 0, 0, 0.4)';
          
          if (placeInfo.deficit !== undefined) {
            // Orange for token deficit (dead transition case)
            highlightColor = '#FF8C00';
            strokeColor = 'rgba(255, 140, 0, 0.4)';
          } else if (placeInfo.missingTokens !== undefined) {
            // Red for missing tokens (deadlock case)
            highlightColor = '#FF0000';
            strokeColor = 'rgba(255, 0, 0, 0.4)';
          } else if (placeInfo.excessTokens !== undefined) {
            // Purple for excess tokens (improper termination case)
            highlightColor = '#8B008B';
            strokeColor = 'rgba(139, 0, 139, 0.4)';
          }
          
          ctx.beginPath();
          ctx.arc(place.position.x, place.position.y, place.radius + 12, 0, Math.PI * 2);
          ctx.strokeStyle = strokeColor;
          ctx.lineWidth = 8;
          ctx.stroke();
          
          ctx.beginPath();
          ctx.arc(place.position.x, place.position.y, place.radius + 8, 0, Math.PI * 2);
          ctx.strokeStyle = highlightColor;
          ctx.lineWidth = 4;
          ctx.stroke();

          // Add problem indicator text
          this.renderPlaceProblemInfo(place, placeInfo);
        } else {
          // Regular highlighting for trace elements
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
      }
      
      const transition = renderer.petriNet.transitions.get(elementId);
      if (transition) {
        // Check if this is a dead transition
        const isDead = this.violationInfo && 
                      this.violationInfo.deadTransition && 
                      this.violationInfo.deadTransition.transitionId === elementId;
        
        if (isDead) {
          // Dark red highlight for dead transitions with pulsing effect
          ctx.beginPath();
          ctx.rect(
            transition.position.x - transition.width / 2 - 12,
            transition.position.y - transition.height / 2 - 12,
            transition.width + 24,
            transition.height + 24
          );
          ctx.strokeStyle = 'rgba(139, 0, 0, 0.5)';
          ctx.lineWidth = 8;
          ctx.stroke();
          
          ctx.beginPath();
          ctx.rect(
            transition.position.x - transition.width / 2 - 8,
            transition.position.y - transition.height / 2 - 8,
            transition.width + 16,
            transition.height + 16
          );
          ctx.strokeStyle = '#8B0000';
          ctx.lineWidth = 4;
          ctx.stroke();

          // Add "DEAD" indicator with background
          ctx.font = 'bold 12px Arial';
          ctx.textAlign = 'center';
          const text = 'DEAD';
          const textWidth = ctx.measureText(text).width;
          const textX = transition.position.x;
          const textY = transition.position.y - transition.height / 2 - 20;
          
          // Background for text
          ctx.fillStyle = 'rgba(139, 0, 0, 0.9)';
          ctx.fillRect(textX - textWidth/2 - 4, textY - 10, textWidth + 8, 14);
          
          // Text
          ctx.fillStyle = '#FFFFFF';
          ctx.fillText(text, textX, textY);
        } else {
          // Regular highlighting for trace transitions
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
    }
    
    // Highlight arcs with different colors based on context
    for (const arcId of this.highlightedArcs) {
      const arc = renderer.petriNet.arcs.get(arcId);
      if (arc) {
        const sourceElement = renderer.petriNet.places.get(arc.source) || 
                            renderer.petriNet.transitions.get(arc.source);
        const targetElement = renderer.petriNet.places.get(arc.target) || 
                            renderer.petriNet.transitions.get(arc.target);
        
        if (sourceElement && targetElement) {
          const { start, end } = renderer.calculateArcEndpoints(sourceElement, targetElement);
          
          // Different arc colors for dead transitions vs traces
          let arcColor = '#FFE66D'; // Default yellow
          let arcColorFaded = 'rgba(255, 230, 109, 0.3)';
          
          if (this.violationInfo && this.violationInfo.violationType === "dead_transition") {
            arcColor = '#FF8C00'; // Orange for dead transition arcs
            arcColorFaded = 'rgba(255, 140, 0, 0.3)';
          }
          
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = arcColorFaded;
          ctx.lineWidth = 8;
          ctx.stroke();
          
          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = arcColor;
          ctx.lineWidth = 4;
          ctx.stroke();
        }
      }
    }
    
    ctx.restore();
  }

  /**
   * Render problem information for a place
   */
  renderPlaceProblemInfo(place, placeInfo) {
    const ctx = this.mainRenderer.ctx;
    const x = place.position.x + 30;
    const y = place.position.y - 30;
    
    let text = '';
    let bgColor = 'rgba(255, 0, 0, 0.9)'; // Default red
    
    if (placeInfo.missingTokens !== undefined) {
      text = `Missing: ${placeInfo.missingTokens}`;
      bgColor = 'rgba(255, 0, 0, 0.9)'; // Red for missing tokens
    } else if (placeInfo.excessTokens !== undefined) {
      text = `Excess: +${placeInfo.excessTokens}`;
      bgColor = 'rgba(139, 0, 139, 0.9)'; // Purple for excess tokens
    } else if (placeInfo.deficit !== undefined) {
      text = `Need: ${placeInfo.requiredTokens}`;
      bgColor = 'rgba(255, 140, 0, 0.9)'; // Orange for token deficit (dead transitions)
    } else if (placeInfo.maxFoundTokens !== undefined) {
      text = `Max: ${placeInfo.maxFoundTokens}/${placeInfo.requiredTokens}`;
      bgColor = 'rgba(255, 140, 0, 0.9)'; // Orange for insufficient capacity
    }

    if (text) {
      ctx.font = 'bold 10px Arial';
      const textWidth = ctx.measureText(text).width;
      const padding = 6;
      
      // Background
      ctx.fillStyle = bgColor;
      ctx.fillRect(x - padding, y - 15, textWidth + padding * 2, 16);
      
      // Border
      ctx.strokeStyle = 'rgba(255, 255, 255, 0.8)';
      ctx.lineWidth = 1;
      ctx.strokeRect(x - padding, y - 15, textWidth + padding * 2, 16);
      
      // Text
      ctx.fillStyle = '#FFFFFF';
      ctx.textAlign = 'left';
      ctx.fillText(text, x, y);
    }
  }

  /**
   * Render data overlays with type-aware formatting
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
      
      let text;
      if (overlay.type === 'deadTransition') {
        text = this.formatDeadTransitionOverlay(overlay.data);
      } else {
        text = this.formatDataOverlay(overlay);
      }
      
      const lines = text.split('\n');
      const lineHeight = 16;
      const padding = 10;
      
      ctx.font = '12px monospace';
      const maxWidth = Math.max(...lines.map(line => ctx.measureText(line).width));
      const boxWidth = maxWidth + padding * 2;
      const boxHeight = lines.length * lineHeight + padding * 2;
      
      // Different background color for dead transitions
      if (overlay.type === 'deadTransition') {
        ctx.fillStyle = 'rgba(139, 0, 0, 0.95)'; // Dark red for dead transitions
        ctx.strokeStyle = '#8B0000';
      } else {
        ctx.fillStyle = 'rgba(46, 52, 64, 0.95)';
        ctx.strokeStyle = '#88C0D0';
      }
      
      ctx.fillRect(x, y - boxHeight, boxWidth, boxHeight);
      ctx.lineWidth = 2;
      ctx.strokeRect(x, y - boxHeight, boxWidth, boxHeight);
      
      ctx.fillStyle = '#ECEFF4';
      ctx.textAlign = 'left';
      
      lines.forEach((line, index) => {
        ctx.fillText(line, x + padding, y - boxHeight + padding + (index + 1) * lineHeight);
      });
    }

    // Render responsible variables with type information
    this.renderResponsibleVariables();
    
    ctx.restore();
  }

  /**
   * Format dead transition overlay text with type information
   */
  formatDeadTransitionOverlay(data) {
    const lines = [`DEAD: ${data.transitionLabel}`];
    
    // Add the main reason
    lines.push(`Reason: ${data.reason.replace('Dead transition: ', '')}`);
    
    // Add problematic places if any
    if (data.problematicPlaces && data.problematicPlaces.length > 0) {
      lines.push('');
      lines.push('Token Issues:');
      for (const place of data.problematicPlaces) {
        lines.push(`• ${place.placeName}: needs ${place.requiredTokens}, max ${place.maxFoundTokens}`);
      }
    }
    
    // Add responsible variables if any with type-aware formatting
    if (data.responsibleVariables && data.responsibleVariables.length > 0) {
      lines.push('');
      lines.push('Data Guard Issues:');
      for (const variable of data.responsibleVariables) {
        const value = this.formatVariableForDisplay(variable);
        lines.push(`• ${variable.variable} = ${value}`);
      }
    }
    
    // Add preventing conditions if any
    if (data.preventingConditions && data.preventingConditions.length > 0) {
      lines.push('');
      lines.push('Preventing Conditions:');
      data.preventingConditions.forEach(condition => {
        lines.push(`• ${condition}`);
      });
    }
    
    return lines.join('\n');
  }

  /**
   * Format variable for display based on type
   */
  formatVariableForDisplay(variable) {
    const value = variable.value !== undefined ? variable.value : 
                 (variable.currentValue !== undefined ? variable.currentValue : 'undefined');
    const type = variable.type || 'unknown';
    
    switch (type) {
      case 'int':
        return `${Math.floor(Number(value))} (int)`;
      case 'float':
        const floatValue = Number(value);
        const formattedFloat = floatValue % 1 === 0 ? floatValue.toString() : floatValue.toFixed(3).replace(/\.?0+$/, '');
        return `${formattedFloat} (float)`;
      case 'boolean':
        return `${value ? 'true' : 'false'} (bool)`;
      case 'string':
        return `"${value}" (str)`;
      default:
        return `${value} (${type})`;
    }
  }

  /**
   * Render responsible variable information with type awareness
   */
  renderResponsibleVariables() {
    const ctx = this.mainRenderer.ctx;
    const renderer = this.mainRenderer;

    if (this.responsibleVariables.size > 0) {
      // Find a good position to display variable info
      const canvasRect = renderer.canvas.getBoundingClientRect();
      const worldPos = renderer.screenToWorld(canvasRect.width - 20, 100);
      
      const x = worldPos.x - 250; // Wider for type information
      const y = worldPos.y + 50;
      
      const lines = ['Responsible Variables:'];
      for (const [varName, varInfo] of this.responsibleVariables) {
        const displayValue = this.formatVariableForDisplay(varInfo);
        lines.push(`${varName}: ${displayValue}`);
        if (varInfo.problem) {
          lines.push(`  → ${varInfo.problem}`);
        }
      }
      
      const lineHeight = 16;
      const padding = 10;
      
      ctx.font = '12px monospace';
      const maxWidth = Math.max(...lines.map(line => ctx.measureText(line).width));
      const boxWidth = maxWidth + padding * 2;
      const boxHeight = lines.length * lineHeight + padding * 2;
      
      // Background
      ctx.fillStyle = 'rgba(255, 140, 0, 0.95)';
      ctx.fillRect(x, y, boxWidth, boxHeight);
      
      // Border
      ctx.strokeStyle = '#FF8C00';
      ctx.lineWidth = 2;
      ctx.strokeRect(x, y, boxWidth, boxHeight);
      
      // Text
      ctx.fillStyle = '#FFFFFF';
      ctx.textAlign = 'left';
      
      lines.forEach((line, index) => {
        ctx.fillText(line, x + padding, y + padding + (index + 1) * lineHeight);
      });
    }
  }

  /**
   * Format data overlay text with type information
   */
  formatDataOverlay(overlay) {
    const lines = ['Data Changes:'];
    
    for (const change of overlay.changes) {
      const symbol = change.changeType === 'created' ? '+' : '~';
      const typeInfo = change.type ? ` (${change.type})` : '';
      lines.push(`${symbol} ${change.variable}${typeInfo}: ${change.oldValue} → ${change.newValue}`);
    }
    
    return lines.join('\n');
  }

  delay(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
  }
}

/**
 * Enhanced Data Petri Net Verification with Integrated Detailed Analysis and Type Support
 */
class EnhancedDataPetriNetVerification extends DataPetriNetVerification {
  constructor(app) {
    super(app);
    this.traceVisualizer = null;
    this.currentCounterexamples = [];
    this.isVisualizationActive = false;
    
    // Override and enhance the verification section
    this.createEnhancedVerificationSection();
  }

  /**
   * Create enhanced verification section with detailed analysis features
   */
  createEnhancedVerificationSection() {
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
          <h3>Verification</h3>
        </div>
        <button class="section-toggle">▼</button>
      </div>
      <div class="section-content">
        <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">
          <strong>Data-aware soundness verification</strong> with support for int/float types
        </p>
        <button id="btn-verify-soundness" style="background: linear-gradient(135deg, #A3BE8C, #88C0D0, #EBCB8B); color: #2E3440; font-weight: 600; font-size: 15px; padding: 14px;">
          <span class="verify-btn-icon">🎯</span>
          Soundness Verification
        </button>
      </div>
    `;

    modelTab.appendChild(verificationSection);

    // Add event listeners
    const verifyButton = verificationSection.querySelector('#btn-verify-soundness');
    verifyButton.addEventListener('click', () => this.startVerification());

    // Add section collapse functionality
    const sectionHeader = verificationSection.querySelector('.section-header');
    sectionHeader.addEventListener('click', () => {
      verificationSection.classList.toggle('section-collapsed');
    });
  }

  /**
   * Start verification with enhanced verifier (ASYNC)
   */
  async startVerification() {
    const verifyButton = document.querySelector('#btn-verify-soundness');
    const modal = document.querySelector('#verification-modal');
    const modalBody = document.querySelector('#verification-modal-body');

    verifyButton.disabled = true;
    verifyButton.innerHTML = '<span class="verification-spinner"></span> Enhanced Verifying...';

    this.showModal();
    modalBody.innerHTML = this.createEnhancedProgressHTML();

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
      verifyButton.innerHTML = '<span class="verify-btn-icon">🎯</span> Enhanced Verification';
    }
  }

  /**
   * Initialize trace visualizer
   */
  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
      this.traceVisualizer = new TraceVisualizationRenderer(this.app);
    }
  }

  /**
   * Visualize counterexample with enhanced details
   */
  visualizeCounterexample(counterexampleIndex, propertyName) {
    if (!this.traceVisualizer) {
      this.initializeTraceVisualizer();
    }

    if (!this.traceVisualizer) {
      return;
    }

    const counterexample = this.findCounterexample(counterexampleIndex, propertyName);
    if (!counterexample) {
      return;
    }

    this.traceVisualizer.visualizeCounterexample(counterexample);
    this.updateCounterexampleVisualizationUI(counterexampleIndex, propertyName);
    this.isVisualizationActive = true;
  }

  /**
   * Clear counterexample visualization
   */
  clearCounterexampleVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
      this.isVisualizationActive = false;
    }
    
    document.querySelectorAll('.enhanced-counterexample-item').forEach(item => {
      item.classList.remove('active-counterexample');
    });
  }

  /**
   * Update UI to show active counterexample
   */
  updateCounterexampleVisualizationUI(counterexampleIndex, propertyName) {
    document.querySelectorAll('.enhanced-counterexample-item').forEach(item => {
      item.classList.remove('active-counterexample');
    });
    
    const counterexampleElements = document.querySelectorAll('.enhanced-counterexample-item');
    if (counterexampleIndex < counterexampleElements.length) {
      counterexampleElements[counterexampleIndex].classList.add('active-counterexample');
    }
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
   * Create enhanced progress HTML
   */
  createEnhancedProgressHTML() {
    return `
      <div class="verification-algorithm-info">
        <h4>🎯 Algorithm: Enhanced Data-Aware Soundness Verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Advanced verification with comprehensive counterexample analysis, detailed problem visualization, and full support for int/float types.
        </p>
      </div>
      <div class="verification-progress">
        <div class="verification-progress-bar">
          <div class="verification-progress-fill" id="progress-fill" style="width: 0%"></div>
        </div>
        <div class="verification-step" id="progress-step">
          Initializing enhanced verification...
        </div>
      </div>
    `;
  }

  /**
   * Create enhanced results HTML with counterexample sections and type support
   */
  createEnhancedResultsHTML(result) {
    const isSound = result.isSound;
    const statusClass = isSound ? 'sound' : 'unsound';
    const statusIcon = isSound ? '✅' : '❌';
    const statusText = isSound ? 'Sound' : 'Unsound';

    let html = `
      <div class="verification-algorithm-info">
        <h4>🎯 Enhanced Data-Aware Soundness Verification</h4>
        <p style="color: #D8DEE9; margin: 0;">
          Advanced analysis with detailed counterexample reasons, responsible variable tracking, and full int/float type support.
        </p>
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
        Enhanced verification completed in ${result.executionTime}ms
      </div>
    `;

    return html;
  }

  /**
   * Create enhanced counterexample section with visualization controls and type information
   */
  createEnhancedCounterexampleSection(counterexamples, propertyName, propertyIndex) {
    if (!counterexamples || counterexamples.length === 0) return '';

    let html = `
      <div class="enhanced-counterexample-section">
        <h4>🔍 Detailed Counterexample Analysis (${counterexamples.length}) - Int/Float Aware</h4>
        <div class="counterexample-controls">
          <button class="trace-control-btn" onclick="window.enhancedDpnVerification.clearCounterexampleVisualization()">
            Clear All Highlights
          </button>
        </div>
        <div class="enhanced-counterexample-list">
    `;

    counterexamples.forEach((ce, index) => {
      const globalIndex = this.currentCounterexamples.indexOf(ce);
      const displayIndex = globalIndex >= 0 ? globalIndex : index;
      
      html += `
        <div class="enhanced-counterexample-item" data-property="${propertyName}" data-index="${displayIndex}">
          <div class="counterexample-header">
            <span class="counterexample-title">Counterexample ${index + 1}</span>
            <div class="counterexample-actions">
              <button class="trace-btn enhanced-btn" onclick="window.enhancedDpnVerification.visualizeCounterexample(${displayIndex}, '${propertyName}')">
                🎯 Analyze & Highlight
              </button>
            </div>
          </div>
          <div class="enhanced-counterexample-details">
            <div class="violation-summary">
              <strong>Violation:</strong> ${ce.reason}
            </div>
            ${ce.detailedReason ? `
              <div class="detailed-reason">
                <strong>Detailed Analysis:</strong><br>
                ${ce.detailedReason}
              </div>
            ` : ''}
            ${ce.problematicPlaces && ce.problematicPlaces.length > 0 ? `
              <div class="problematic-places">
                <strong>Problematic Places:</strong><br>
                ${ce.problematicPlaces.map(p => 
                  `• ${p.placeName}: ${this.formatPlaceProblem(p)}`
                ).join('<br>')}
              </div>
            ` : ''}
            ${ce.responsibleVariables && ce.responsibleVariables.length > 0 ? `
              <div class="responsible-variables">
                <strong>Responsible Variables:</strong><br>
                ${ce.responsibleVariables.map(v => 
                  `• ${v.variable} = ${this.formatVariableForCounterexample(v)} (${v.type || 'unknown'} type)${v.problem ? ` - ${v.problem}` : ''}`
                ).join('<br>')}
              </div>
            ` : ''}
            ${ce.trace && ce.trace.length > 0 ? 
              `<div class="execution-info"><strong>Execution steps:</strong> ${ce.trace.length}</div>` : ''}
            ${ce.deadTransition ? 
              `<div class="dead-transition-info"><strong>Dead transition:</strong> ${ce.deadTransition.transitionLabel}</div>` : ''}
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
   * Format variable for counterexample display with type information
   */
  formatVariableForCounterexample(variable) {
    const value = variable.value !== undefined ? variable.value : 
                 (variable.currentValue !== undefined ? variable.currentValue : 'undefined');
    const type = variable.type || 'unknown';
    
    switch (type) {
      case 'int':
        return Math.floor(Number(value)).toString();
      case 'float':
        const floatValue = Number(value);
        return floatValue % 1 === 0 ? floatValue.toString() : floatValue.toFixed(3).replace(/\.?0+$/, '');
      case 'boolean':
        return value ? 'true' : 'false';
      case 'string':
        return `"${value}"`;
      default:
        return value.toString();
    }
  }

  /**
   * Format place problem description
   */
  formatPlaceProblem(placeInfo) {
    if (placeInfo.missingTokens !== undefined) {
      return `needs ${placeInfo.requiredTokens}, has ${placeInfo.currentTokens} (missing ${placeInfo.missingTokens})`;
    } else if (placeInfo.excessTokens !== undefined) {
      return `has ${placeInfo.actualTokens}, expected ${placeInfo.expectedTokens} (excess ${placeInfo.excessTokens})`;
    } else if (placeInfo.deficit !== undefined) {
      return `max found ${placeInfo.maxFoundTokens}, needs ${placeInfo.requiredTokens} (deficit ${placeInfo.deficit})`;
    }
    return 'problem detected';
  }
}

// Enhanced verification styles
const enhancedIntegratedVerificationStyles = `
  .enhanced-counterexample-section {
    background: linear-gradient(135deg, #2E3440, #3B4252);
    border-radius: 8px;
    padding: 18px;
    margin-top: 15px;
    border-left: 4px solid #BF616A;
    box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
  }

  .enhanced-counterexample-item {
    background: linear-gradient(135deg, #434C5E, #4C566A);
    border-radius: 6px;
    padding: 15px;
    border: 2px solid transparent;
    transition: all 0.3s;
    margin-bottom: 12px;
  }

  .enhanced-counterexample-item:hover {
    border-color: #5E81AC;
    transform: translateY(-2px);
    box-shadow: 0 6px 20px rgba(0, 0, 0, 0.2);
  }

  .enhanced-counterexample-item.active-counterexample {
    border-color: #88C0D0 !important;
    background: linear-gradient(135deg, rgba(136, 192, 208, 0.2), rgba(94, 129, 172, 0.1)) !important;
    box-shadow: 0 0 15px rgba(136, 192, 208, 0.4);
  }

  .enhanced-btn {
    background: linear-gradient(135deg, #A3BE8C, #88C0D0) !important;
    color: #2E3440 !important;
    font-weight: 600 !important;
    padding: 6px 12px !important;
    border-radius: 5px !important;
  }

  .enhanced-btn:hover {
    background: linear-gradient(135deg, #B4CFB0, #A3D0E4) !important;
    transform: translateY(-2px) !important;
    box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3) !important;
  }

  .enhanced-counterexample-details {
    font-size: 13px;
    line-height: 1.5;
  }

  .violation-summary {
    background-color: rgba(191, 97, 106, 0.2);
    padding: 10px;
    border-radius: 4px;
    margin-bottom: 10px;
    border-left: 3px solid #BF616A;
  }

  .detailed-reason {
    background-color: rgba(94, 129, 172, 0.2);
    padding: 10px;
    border-radius: 4px;
    margin-bottom: 10px;
    border-left: 3px solid #5E81AC;
  }

  .problematic-places {
    background-color: rgba(208, 135, 112, 0.2);
    padding: 10px;
    border-radius: 4px;
    margin-bottom: 10px;
    border-left: 3px solid #D08770;
  }

  .responsible-variables {
    background-color: rgba(235, 203, 139, 0.2);
    padding: 10px;
    border-radius: 4px;
    margin-bottom: 10px;
    border-left: 3px solid #EBCB8B;
  }

  .execution-info, .dead-transition-info {
    background-color: rgba(76, 86, 106, 0.3);
    padding: 8px;
    border-radius: 4px;
    margin-top: 8px;
    font-size: 12px;
  }

  .enhanced-counterexample-list {
    display: flex;
    flex-direction: column;
    gap: 12px;
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
    transition: all 0.2s;
  }

  .trace-control-btn:hover {
    background-color: #5E81AC;
  }
  
  .counterexample-header {
    display: flex;
    justify-content: space-between;
    align-items: center;
    margin-bottom: 8px;
  }
`;

// Inject enhanced styles
function injectEnhancedIntegratedVerificationStyles() {
  const existingStyles = document.getElementById('enhanced-verification-styles');
  if (existingStyles) {
    existingStyles.textContent += '\n' + enhancedIntegratedVerificationStyles;
  } else {
    const style = document.createElement('style');
    style.id = 'enhanced-integrated-verification-styles';
    style.textContent = enhancedIntegratedVerificationStyles;
    document.head.appendChild(style);
  }
}

// Initialize enhanced verification system (replaces existing initialization)
document.addEventListener('DOMContentLoaded', () => {
  const initEnhancedVerification = () => {
    if (window.petriApp && window.dataPetriNetIntegration) {
      // Prevent other verification systems from initializing
      window.dpnVerificationInitialized = true;
      
      // Remove any existing verification sections
      const existingVerificationSections = document.querySelectorAll('#verification-section');
      existingVerificationSections.forEach(section => {
        section.remove();
      });
      
      if (!window.enhancedDpnVerification) {
        injectEnhancedIntegratedVerificationStyles();
        window.enhancedDpnVerification = new EnhancedDataPetriNetVerification(window.petriApp);
        window.dpnVerification = window.enhancedDpnVerification;
        console.log("Enhanced Data Petri Net Verification initialized with integrated detailed analysis and int/float support");
      }
    } else {
      setTimeout(initEnhancedVerification, 500);
    }
  };
  
  // Initialize early to prevent other verification systems
  setTimeout(initEnhancedVerification, 600);
});