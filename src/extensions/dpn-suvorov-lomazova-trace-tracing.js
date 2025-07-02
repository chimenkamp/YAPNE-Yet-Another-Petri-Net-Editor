/**
 * Enhanced Suvorov & Lomazova DPN Soundness Verifier with Advanced Visualization
 * 
 * This enhanced version keeps the formal Suvorov-Lomazova verification algorithm unchanged
 * while adding the rich visualization and counterexample analysis from the previous system.
 */

/**
 * Enhanced Suvorov & Lomazova Verifier with detailed analysis
 * The core verification algorithm remains unchanged, but with enhanced counterexample analysis
 */
class EnhancedSuvorovLomazovaVerifier extends SuvorovLomazovaVerifier {
    constructor(petriNet) {
        super(petriNet);
        this.detailedCounterexamples = [];
    }

    /**
     * Enhanced deadlock analysis with detailed reasoning
     */
    async analyzeDeadlockCause(stateStr, lts, dpn) {
        const stateData = this.parseStateData(stateStr, dpn);
        const problematicPlaces = [];
        const responsibleVariables = [];
        const disabledReasons = [];
        
        // Analyze each transition to understand why it's disabled
        for (const [id, transition] of dpn.transitions) {
            const tokenEnabled = this.isTransitionTokenEnabledInState(id, stateData, dpn);
            const dataEnabled = this.isTransitionDataEnabledInState(id, stateData, dpn);
            
            if (!tokenEnabled) {
                const missingTokens = this.findMissingTokensDetailed(id, stateData, dpn);
                problematicPlaces.push(...missingTokens);
                disabledReasons.push(`${transition.label || id}: insufficient tokens in ${missingTokens.map(p => p.placeName).join(', ')}`);
            } else if (!dataEnabled) {
                const failedGuards = this.findFailedDataGuardsDetailed(id, stateData, dpn);
                responsibleVariables.push(...failedGuards);
                disabledReasons.push(`${transition.label || id}: data guard failed (${failedGuards.map(v => `${v.variable}=${this.formatVariableValue(v.value, v.type)}`).join(', ')})`);
            }
        }

        const reason = "Deadlock detected";
        const detailedReason = `No transitions are enabled in this state. ` +
            `Current marking: ${this.formatMarkingDetailed(stateData.marking, dpn)}. ` +
            `Data values: ${this.formatDataValuationDetailed(stateData.dataValuation, dpn)}. ` +
            `Disabled transitions: ${disabledReasons.join('; ')}.`;

        // Enhanced trace construction with proper data change tracking
        const enhancedTrace = await this.buildEnhancedTraceToState(stateStr, lts, dpn);

        return {
            trace: enhancedTrace,
            violationType: "deadlock",
            reason,
            detailedReason,
            problematicPlaces,
            responsibleVariables,
            stateData: stateData,
            detailedAnalysis: {
                disabledReasons,
                tokenIssues: problematicPlaces.length > 0,
                dataIssues: responsibleVariables.length > 0
            }
        };
    }

    /**
     * Enhanced transition analysis with suggested fixes
     */
    async analyzeDeadTransition(transitionId, lts, dpn) {
        const transition = dpn.transitions.get(transitionId);
        let reason = "unknown cause";
        let detailedReason = `Transition "${transition.label}" never fires.`;
        let problematicPlaces = [];
        let responsibleVariables = [];
        let suggestedFix = null;
        let preventingConditions = [];

        // Analyze token requirements
        const maxTokensMap = this.getMaxTokensReached(lts, dpn);
        const missingTokens = this.findMissingTokensDetailed(transitionId, { marking: maxTokensMap }, dpn, true);
        
        if (missingTokens.length > 0) {
            reason = "Insufficient tokens in input places";
            detailedReason = `Input place(s) for "${transition.label}" never have enough tokens. ` +
                `Maximum tokens found: ${missingTokens.map(p => `${p.placeName}(${p.maxFoundTokens}/${p.requiredTokens})`).join(', ')}.`;
            problematicPlaces = missingTokens;
            preventingConditions.push(`Token deficit in places: ${missingTokens.map(p => p.placeName).join(', ')}`);
            
            // Suggest adding tokens
            suggestedFix = {
                type: "add_tokens",
                description: "Add tokens to input places",
                actions: missingTokens.map(p => ({
                    placeId: p.placeId,
                    placeName: p.placeName,
                    addTokens: p.requiredTokens - p.maxFoundTokens
                }))
            };
        } 
        // Analyze data guard
        else if (transition.precondition && !this.isGuardEverSatisfied(transition, lts)) {
            reason = "Unsatisfiable data guard";
            responsibleVariables = this.getVariablesFromExpressionDetailed(transition.precondition, dpn);
            detailedReason = `The guard "${transition.precondition}" is never satisfied with the available variable ranges. ` +
                `Variables involved: ${responsibleVariables.map(v => `${v.variable}=${this.formatVariableValue(v.currentValue, v.type)}`).join(', ')}.`;
            preventingConditions.push(`Unsatisfiable guard: ${transition.precondition}`);
            
            // Try to suggest satisfying values
            suggestedFix = await this.suggestSatisfyingValuesDetailed(transition.precondition, dpn);
        }

        return {
            violationType: "dead_transition",
            reason: `Dead transition: ${reason}`,
            detailedReason,
            problematicPlaces,
            responsibleVariables,
            suggestedFix,
            preventingConditions,
            deadTransition: {
                transitionId,
                transitionLabel: transition.label || transitionId,
                guard: transition.precondition
            },
            detailedAnalysis: {
                hasTokenIssues: problematicPlaces.length > 0,
                hasDataIssues: responsibleVariables.length > 0,
                canBeSolved: suggestedFix !== null
            }
        };
    }

    /**
     * Enhanced improper termination analysis
     */
    async analyzeImproperTermination(state, finalMarking, stateStr, lts, dpn) {
        const problematicPlaces = [];
        const responsibleVariables = [];
        const enabledTransitions = [];

        // Find places with excess tokens
        for (const [placeId, tokens] of Object.entries(state.marking)) {
            const finalTokens = finalMarking[placeId] || 0;
            if (tokens > finalTokens) {
                const place = dpn.places.get(placeId);
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
        const stateTransitions = this.getEnabledTransitionsInState(stateStr, lts);
        for (const transitionId of stateTransitions) {
            const transition = dpn.transitions.get(transitionId);
            enabledTransitions.push({
                transitionId,
                transitionLabel: transition ? transition.label : transitionId
            });
        }

        // Check if data conditions contribute to the problem
        for (const [varName, value] of Object.entries(state.dataValuation)) {
            if (this.isVariableContributingToTerminationProblem(varName, value, state, dpn)) {
                const variableType = this.getVariableType(varName, dpn);
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

        // Enhanced trace construction with proper data change tracking
        const enhancedTrace = await this.buildEnhancedTraceToState(stateStr, lts, dpn);

        return {
            trace: enhancedTrace,
            violationType: "improper_termination",
            reason,
            detailedReason,
            problematicPlaces,
            responsibleVariables,
            enabledTransitions,
            stateData: state,
            detailedAnalysis: {
                excessTokenCount: problematicPlaces.reduce((sum, p) => sum + p.excessTokens, 0),
                enabledTransitionCount: enabledTransitions.length,
                canReachFinalState: problematicPlaces.length === 0
            }
        };
    }

    /**
     * Enhanced trace construction that properly tracks data changes
     */
    async buildEnhancedTraceToState(targetState, lts, dpn) {
        const path = lts.executionPaths.get(targetState) || [];
        const trace = [];
        
        // Initial state
        const initialStateData = this.parseStateData(lts.initialState, dpn);
        trace.push({
            step: 0,
            action: "Initial State",
            marking: initialStateData.marking,
            dataValuation: initialStateData.dataValuation,
            dataChanges: [] // No changes in initial state
        });

        let currentStateStr = lts.initialState;
        let previousDataValuation = { ...initialStateData.dataValuation };
        
        for (let i = 0; i < path.length; i++) {
            const step = path[i];
            const transition = dpn.transitions.get(step.transitionId);
            
            // Fire the transition to get the new state
            currentStateStr = await this.fireTransitionInState(
                currentStateStr,
                step.transitionId,
                dpn
            );
            
            const newStateData = this.parseStateData(currentStateStr, dpn);
            
            // Calculate data changes
            const dataChanges = this.calculateDataChanges(
                previousDataValuation, 
                newStateData.dataValuation
            );
            
            trace.push({
                step: i + 1,
                action: `Fire: ${transition?.label || step.transitionId}`,
                transitionId: step.transitionId,
                marking: newStateData.marking,
                dataValuation: newStateData.dataValuation,
                dataChanges: dataChanges
            });
            
            previousDataValuation = { ...newStateData.dataValuation };
        }
        
        return trace;
    }

    /**
     * Calculate the changes between two data valuations
     */
    calculateDataChanges(oldValuation, newValuation) {
        const changes = [];
        
        // Find all variables that changed
        const allVars = new Set([...Object.keys(oldValuation), ...Object.keys(newValuation)]);
        
        for (const varName of allVars) {
            const oldValue = oldValuation[varName];
            const newValue = newValuation[varName];
            
            if (oldValue !== newValue) {
                changes.push({
                    variable: varName,
                    oldValue: oldValue,
                    newValue: newValue,
                    changeType: oldValue === undefined ? 'created' : (newValue === undefined ? 'deleted' : 'modified')
                });
            }
        }
        
        return changes;
    }

    // --- Enhanced Helper Methods ---

    findMissingTokensDetailed(transitionId, stateData, dpn, isMaxAnalysis = false) {
        const missingTokens = [];
        const inputArcs = Array.from(dpn.arcs.values()).filter(arc => arc.target === transitionId);
        
        for (const arc of inputArcs) {
            const place = dpn.places.get(arc.source);
            if (place) {
                const currentTokens = stateData.marking[arc.source] || 0;
                if (currentTokens < arc.weight) {
                    missingTokens.push({
                        placeId: arc.source,
                        placeName: place.label,
                        currentTokens: isMaxAnalysis ? currentTokens : currentTokens,
                        requiredTokens: arc.weight,
                        missingTokens: arc.weight - currentTokens,
                        [isMaxAnalysis ? 'maxFoundTokens' : 'currentTokens']: currentTokens,
                        deficit: arc.weight - currentTokens
                    });
                }
            }
        }
        return missingTokens;
    }

    findFailedDataGuardsDetailed(transitionId, stateData, dpn) {
        const failedGuards = [];
        const transition = dpn.transitions.get(transitionId);
        
        if (transition && typeof transition.evaluatePrecondition === 'function') {
            try {
                const isEnabled = transition.evaluatePrecondition(stateData.dataValuation);
                if (!isEnabled) {
                    for (const [varName, value] of Object.entries(stateData.dataValuation)) {
                        const variableType = this.getVariableType(varName, dpn);
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

    getVariablesFromExpressionDetailed(expression, dpn) {
        const variables = [];
        if (!dpn.dataVariables) return variables;
        
        for (const [id, variable] of dpn.dataVariables) {
            if (new RegExp(`\\b${variable.name}\\b`).test(expression)) {
                variables.push({
                    variable: variable.name,
                    type: variable.type,
                    currentValue: variable.getValue ? variable.getValue() : variable.currentValue,
                    id: id
                });
            }
        }
        return variables;
    }

    async suggestSatisfyingValuesDetailed(guard, dpn) {
        if (!guard || typeof window.solveExpression !== 'function') return null;
        
        try {
            const varsInGuard = this.getVariablesFromExpressionDetailed(guard, dpn);
            const initialVals = {};
            varsInGuard.forEach(v => initialVals[v.variable] = v.currentValue);
            
            const result = await window.solveExpression(guard.replace(/'/g, ""), initialVals, 'auto');
            if (result && result.newValues) {
                return {
                    type: "satisfying_values",
                    description: "Suggested variable values that would satisfy the guard",
                    values: Object.entries(result.newValues).map(([varName, value]) => {
                        const variable = varsInGuard.find(v => v.variable === varName);
                        return {
                            variable: varName,
                            currentValue: variable ? variable.currentValue : 'unknown',
                            suggestedValue: value,
                            type: variable ? variable.type : 'unknown'
                        };
                    })
                };
            }
        } catch (error) {
            return {
                type: "error",
                description: "Could not generate satisfying values",
                error: error.message
            };
        }
        return null;
    }

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

    formatMarkingDetailed(marking, dpn) {
        return Object.entries(marking)
            .filter(([place, tokens]) => tokens > 0)
            .map(([place, tokens]) => {
                const placeObj = dpn.places.get(place);
                const placeName = placeObj ? placeObj.label : place;
                return `${placeName}(${tokens})`;
            })
            .join(', ') || 'empty';
    }

    formatDataValuationDetailed(valuation, dpn) {
        if (!valuation) return 'no data';
        
        return Object.entries(valuation)
            .map(([variable, value]) => {
                const variableType = this.getVariableType(variable, dpn);
                return `${variable}=${this.formatVariableValue(value, variableType)}`;
            })
            .join(', ') || 'no data';
    }

    getVariableType(varName, dpn) {
        if (dpn.dataVariables) {
            for (const [id, variable] of dpn.dataVariables) {
                if (variable.name === varName) {
                    return variable.type;
                }
            }
        }
        return 'unknown';
    }

    isVariableContributingToTerminationProblem(varName, value, state, dpn) {
        for (const [id, transition] of dpn.transitions) {
            if (typeof transition.evaluatePrecondition === 'function' && 
                transition.precondition && 
                transition.precondition.includes(varName)) {
                return true;
            }
        }
        return false;
    }

    getEnabledTransitionsInState(stateStr, lts) {
        return (lts.transitions.get(stateStr) || []).map(t => t.transition);
    }

    // Override the parent methods to use enhanced analysis
    async checkEnhancedProperty1(lts, dpn) {
        if (this.finalMarkings.length === 0) {
            return { 
                name: "P1: Reachability & Deadlock Freedom", 
                satisfied: true, 
                details: "Skipped: No final marking found.", 
                counterexamples: [] 
            };
        }

        const deadlockStates = [];
        for (const stateStr of lts.states) {
            const stateData = this.parseStateData(stateStr, dpn);
            if (!this.hasEnabledTransitionsInState(stateStr, lts) && 
                !this.isFinalState(stateData, this.finalMarkings)) {
                const enhancedAnalysis = await this.analyzeDeadlockCause(stateStr, lts, dpn);
                deadlockStates.push(enhancedAnalysis);
            }
        }

        return {
            name: "P1: Reachability & Deadlock Freedom",
            satisfied: deadlockStates.length === 0,
            details: `Found ${deadlockStates.length} deadlock states.`,
            counterexamples: deadlockStates
        };
    }

    async checkEnhancedProperty2(lts, dpn) {
        if (this.finalMarkings.length === 0) {
            return { 
                name: "P2: Proper Termination", 
                satisfied: true, 
                counterexamples: [] 
            };
        }

        const violations = [];
        for (const stateStr of lts.states) {
            const state = this.parseStateData(stateStr, dpn);
            for (const finalMarking of this.finalMarkings) {
                if (this.markingStrictlyCovers(state.marking, finalMarking) && 
                    this.hasEnabledTransitionsInState(stateStr, lts)) {
                    const enhancedAnalysis = await this.analyzeImproperTermination(state, finalMarking, stateStr, lts, dpn);
                    violations.push(enhancedAnalysis);
                }
            }
        }

        return {
            name: "P2: Proper Termination",
            satisfied: violations.length === 0,
            details: `Found ${violations.length} improper termination states.`,
            counterexamples: violations
        };
    }

    async checkEnhancedProperty3(lts, dpn) {
        const transitionsFired = new Set();
        lts.transitions.forEach(stateTransitions => 
            stateTransitions.forEach(({ transition }) => transitionsFired.add(transition))
        );

        const deadTransitions = [];
        for (const [id, transition] of dpn.transitions) {
            if (!transition.isTau && !transitionsFired.has(id)) {
                const enhancedAnalysis = await this.analyzeDeadTransition(id, lts, dpn);
                deadTransitions.push(enhancedAnalysis);
            }
        }

        return {
            name: "P3: No Dead Transitions",
            satisfied: deadTransitions.length === 0,
            details: `Found ${deadTransitions.length} dead transitions.`,
            counterexamples: deadTransitions
        };
    }
}

/**
 * Enhanced Trace Visualization Renderer with rich problem highlighting
 */
class EnhancedSuvorovLomazovaTraceVisualizationRenderer {
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
        this.persistentHighlights = false; // Flag to control clearing behavior
        
        // Store original render method
        this.originalRender = this.mainRenderer.render.bind(this.mainRenderer);
        
        // Override render method with enhanced version
        this.mainRenderer.render = () => {
            // Call original render first
            this.originalRender();
            
            // Then add our enhancements if active
            if (this.isActive) {
                try {
                    this.renderHighlights();
                    this.renderDataOverlays();
                } catch (error) {
                    console.error("Error in enhanced rendering:", error);
                }
            }
        };
        
        console.log("Enhanced trace visualizer initialized");
    }

    /**
     * Helper method to map tau_ prefixed IDs back to original transition IDs
     * @param {string} transitionId - The transition ID (possibly with tau_ prefix)
     * @returns {string} - The original transition ID without tau_ prefix
     */
    mapTauTransitionId(transitionId) {
        if (transitionId && transitionId.startsWith('tau_')) {
            return transitionId.substring(4); // Remove 'tau_' prefix
        }
        return transitionId;
    }

    visualizeCounterexample(counterexample, currentStep = -1) {
        console.log("Visualizing counterexample:", counterexample);
        
        // Don't clear if we want persistent highlights
        if (!this.persistentHighlights) {
            this.clearHighlights();
        }
        
        this.isActive = true;
        this.violationInfo = counterexample;

        // Store problematic elements for special highlighting
        if (counterexample.problematicPlaces) {
            console.log("Adding problematic places:", counterexample.problematicPlaces);
            for (const place of counterexample.problematicPlaces) {
                this.problematicPlaces.set(place.placeId, place);
            }
        }

        if (counterexample.responsibleVariables) {
            console.log("Adding responsible variables:", counterexample.responsibleVariables);
            for (const variable of counterexample.responsibleVariables) {
                this.responsibleVariables.set(variable.variable, variable);
            }
        }

        // Handle different types of counterexamples
        if (counterexample.violationType === "dead_transition") {
            console.log("Visualizing dead transition");
            this.visualizeDeadTransition(counterexample);
        } else if (counterexample.trace) {
            console.log("Visualizing trace with", counterexample.trace.length, "steps");
            this.visualizeTrace(counterexample.trace, currentStep);
        }

        // Add special highlighting for problematic elements AFTER trace visualization
        this.addProblemHighlighting();
        
        // Force immediate render
        console.log("Forcing render with", this.highlightedElements.size, "highlighted elements");
        this.mainRenderer.render();
        
        // Also trigger a manual render to ensure visibility
        setTimeout(() => {
            if (this.isActive) {
                this.mainRenderer.render();
            }
        }, 100);
    }

    visualizeDeadTransition(counterexample) {
        if (!counterexample.deadTransition) return;

        const originalTransitionId = this.mapTauTransitionId(counterexample.deadTransition.transitionId);
        
        console.log("Visualizing dead transition:", counterexample.deadTransition.transitionId, "->", originalTransitionId);
        
        // Highlight the dead transition
        this.highlightedElements.add(originalTransitionId);
        
        // Highlight all connected elements (places and arcs)
        this.highlightConnectedElements(originalTransitionId);
        
        // Add data overlay showing why the transition is dead
        this.addDeadTransitionDataOverlay(originalTransitionId, counterexample);
        
        // Highlight problematic input places
        if (counterexample.problematicPlaces) {
            for (const place of counterexample.problematicPlaces) {
                this.highlightedElements.add(place.placeId);
            }
        }
    }

    addDeadTransitionDataOverlay(transitionId, counterexample) {
        const petriNet = this.mainRenderer.petriNet;
        const transition = petriNet.transitions.get(transitionId);
        if (!transition) return;
        
        this.dataOverlays.set(transitionId, {
            type: 'deadTransition',
            data: counterexample,
            position: { ...transition.position }
        });
    }

    visualizeTrace(trace, currentStep = -1) {
        // DO NOT clear highlights here - preserve problematic places highlighting
        this.isActive = true;
        
        if (!trace || trace.length === 0) {
            this.mainRenderer.render();
            return;
        }

        console.log("Visualizing trace with", trace.length, "steps");
        
        // Add final trace token marking
        const finalStep = trace[trace.length - 1];
        if (finalStep.marking) {
            for (const [placeId, tokens] of Object.entries(finalStep.marking)) {
                this.app.api.setPlaceTokens(placeId, tokens);
            }
            this.app.updateTokensDisplay();
        }

        const stepsToShow = currentStep >= 0 ? currentStep + 1 : trace.length;
        
        for (let i = 0; i < Math.min(stepsToShow, trace.length); i++) {
            const step = trace[i];
            console.log(`Processing trace step ${i}:`, step);
            
            if (step.transitionId) {
                // Map tau_ prefixed transition IDs back to original IDs
                const originalTransitionId = this.mapTauTransitionId(step.transitionId);
                console.log("Trace step transition:", step.transitionId, "->", originalTransitionId);
                
                this.highlightedElements.add(originalTransitionId);
                this.highlightConnectedElements(originalTransitionId);
                
                // Add data overlay for this step
                if (step.dataChanges && step.dataChanges.length > 0) {
                    console.log("Adding data overlay for transition", originalTransitionId, "with changes:", step.dataChanges);
                    this.addDataOverlay(originalTransitionId, step.dataChanges, step.dataValuation);
                } else if (step.dataValuation) {
                    // Even if no explicit data changes, show current valuation
                    console.log("Adding data valuation overlay for transition", originalTransitionId);
                    this.addDataValuationOverlay(originalTransitionId, step.dataValuation);
                }
            }
        }
        
        console.log("Trace visualization complete. Highlighted elements:", this.highlightedElements.size);
        this.mainRenderer.render();
    }

    addProblemHighlighting() {
        console.log("Adding problem highlighting");
        
        // Highlight problematic places
        for (const [placeId, placeInfo] of this.problematicPlaces) {
            console.log("Highlighting problematic place:", placeId, placeInfo);
            this.highlightedElements.add(placeId);
            
            // Add special overlay for problematic places
            this.addProblematicPlaceOverlay(placeId, placeInfo);
        }

        // For dead transitions, highlight the transition itself
        if (this.violationInfo && this.violationInfo.deadTransition) {
            const originalTransitionId = this.mapTauTransitionId(this.violationInfo.deadTransition.transitionId);
            
            console.log("Mapped tau transition ID for highlighting:", this.violationInfo.deadTransition.transitionId, "->", originalTransitionId);
            console.log("Highlighting dead transition:", originalTransitionId);
            this.highlightedElements.add(originalTransitionId);
        }
        
        console.log("Total highlighted elements:", this.highlightedElements.size);
        console.log("Highlighted element IDs:", Array.from(this.highlightedElements));
    }

    addProblematicPlaceOverlay(placeId, placeInfo) {
        const petriNet = this.mainRenderer.petriNet;
        const place = petriNet.places.get(placeId);
        if (!place) return;
        
        let overlayId = `place_problem_${placeId}`;
        this.dataOverlays.set(overlayId, {
            type: 'problematicPlace',
            placeInfo: placeInfo,
            position: { ...place.position },
            isPlace: true
        });
    }

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

    addDataOverlay(transitionId, dataChanges, currentValuation) {
        const petriNet = this.mainRenderer.petriNet;
        const transition = petriNet.transitions.get(transitionId);
        if (!transition) return;
        
        this.dataOverlays.set(transitionId, {
            type: 'dataChanges',
            changes: dataChanges,
            valuation: currentValuation,
            position: { ...transition.position }
        });
    }

    addDataValuationOverlay(transitionId, currentValuation) {
        const petriNet = this.mainRenderer.petriNet;
        const transition = petriNet.transitions.get(transitionId);
        if (!transition) return;
        
        this.dataOverlays.set(transitionId, {
            type: 'dataValuation',
            valuation: currentValuation,
            position: { ...transition.position }
        });
    }

    clearHighlights() {
        console.log("Clearing highlights");
        this.highlightedElements.clear();
        this.highlightedArcs.clear();
        this.dataOverlays.clear();
        this.problematicPlaces.clear();
        this.responsibleVariables.clear();
        this.violationInfo = null;
        this.isActive = false;
        this.persistentHighlights = false;
        
        // Force a render to clear the highlights
        this.mainRenderer.render();
        console.log("Highlights cleared and render forced");
    }

    setPersistentHighlights(persistent) {
        this.persistentHighlights = persistent;
    }

    // Method to manually trigger highlighting for debugging
    debugHighlight(elementIds = []) {
        console.log("Debug highlighting elements:", elementIds);
        this.isActive = true;
        
        for (const elementId of elementIds) {
            this.highlightedElements.add(elementId);
        }
        
        this.mainRenderer.render();
    }

    async animateTrace(trace) {
        for (let i = 0; i < trace.length; i++) {
            this.visualizeTrace(trace, i);
            await this.delay(1000);
        }
    }

    renderHighlights() {
        const ctx = this.mainRenderer.ctx;
        const renderer = this.mainRenderer;
        
        console.log("Rendering highlights, elements:", this.highlightedElements.size, "arcs:", this.highlightedArcs.size);
        
        // Ensure we have a valid context
        if (!ctx || !renderer) {
            console.error("No valid context or renderer");
            return;
        }
        
        ctx.save();
        ctx.translate(renderer.panOffset.x, renderer.panOffset.y);
        ctx.scale(renderer.zoomFactor, renderer.zoomFactor);
        
        // First render arc highlights (behind elements)
        for (const arcId of this.highlightedArcs) {
            this.renderArcHighlight(ctx, renderer, arcId);
        }
        
        // Then render element highlights
        for (const elementId of this.highlightedElements) {
            console.log("Rendering highlight for element:", elementId);
            
            const place = renderer.petriNet.places.get(elementId);
            if (place) {
                console.log("Rendering place highlight:", elementId, place.label);
                this.renderPlaceHighlight(ctx, place, elementId);
            }
            
            const transition = renderer.petriNet.transitions.get(elementId);
            if (transition) {
                console.log("Rendering transition highlight:", elementId, transition.label);
                this.renderTransitionHighlight(ctx, transition, elementId);
            }
            
            if (!place && !transition) {
                console.warn("Element not found for highlighting:", elementId);
            }
        }
        
        ctx.restore();
        console.log("Highlights rendering complete");
    }

    renderPlaceHighlight(ctx, place, elementId) {
        const placeInfo = this.problematicPlaces.get(elementId);
        
        if (placeInfo) {
            // Different colors based on problem type
            let highlightColor = '#FF0000'; // Default red
            let strokeColor = 'rgba(255, 0, 0, 0.6)';
            let glowColor = 'rgba(255, 0, 0, 0.3)';
            
            if (placeInfo.deficit !== undefined || placeInfo.maxFoundTokens !== undefined) {
                // Orange for token deficit (dead transition case)
                highlightColor = '#FF8C00';
                strokeColor = 'rgba(255, 140, 0, 0.8)';
                glowColor = 'rgba(255, 140, 0, 0.4)';
            } else if (placeInfo.missingTokens !== undefined) {
                // Red for missing tokens (deadlock case)
                highlightColor = '#FF0000';
                strokeColor = 'rgba(255, 0, 0, 0.8)';
                glowColor = 'rgba(255, 0, 0, 0.4)';
            } else if (placeInfo.excessTokens !== undefined) {
                // Purple for excess tokens (improper termination case)
                highlightColor = '#8B008B';
                strokeColor = 'rgba(139, 0, 139, 0.8)';
                glowColor = 'rgba(139, 0, 139, 0.4)';
            }
            
            // Draw multiple highlight rings for emphasis
            for (let i = 0; i < 3; i++) {
                ctx.beginPath();
                ctx.arc(place.position.x, place.position.y, place.radius + 8 + (i * 4), 0, Math.PI * 2);
                ctx.strokeStyle = i === 0 ? strokeColor : glowColor;
                ctx.lineWidth = i === 0 ? 4 : 6 - i * 2;
                ctx.stroke();
            }

            // Add problem indicator text
            this.renderPlaceProblemInfo(ctx, place, placeInfo);
        } else {
            // Regular highlighting for trace elements
            ctx.beginPath();
            ctx.arc(place.position.x, place.position.y, place.radius + 8, 0, Math.PI * 2);
            ctx.strokeStyle = 'rgba(255, 107, 107, 0.6)';
            ctx.lineWidth = 6;
            ctx.stroke();
            
            ctx.beginPath();
            ctx.arc(place.position.x, place.position.y, place.radius + 4, 0, Math.PI * 2);
            ctx.strokeStyle = '#FF6B6B';
            ctx.lineWidth = 3;
            ctx.stroke();
        }
    }

    renderTransitionHighlight(ctx, transition, elementId) {
        // Check if this is a dead transition (handle tau_ prefix)
        let isDeadTransition = false;
        if (this.violationInfo && this.violationInfo.deadTransition) {
            const originalDeadTransitionId = this.mapTauTransitionId(this.violationInfo.deadTransition.transitionId);
            isDeadTransition = originalDeadTransitionId === elementId;
        }
        
        if (isDeadTransition) {
            // Dark red highlight for dead transitions with multiple rings
            for (let i = 0; i < 3; i++) {
                ctx.beginPath();
                ctx.rect(
                    transition.position.x - transition.width / 2 - 8 - (i * 4),
                    transition.position.y - transition.height / 2 - 8 - (i * 4),
                    transition.width + 16 + (i * 8),
                    transition.height + 16 + (i * 8)
                );
                ctx.strokeStyle = i === 0 ? 'rgba(139, 0, 0, 0.9)' : 'rgba(139, 0, 0, 0.4)';
                ctx.lineWidth = i === 0 ? 4 : 6 - i * 2;
                ctx.stroke();
            }

            // Add "DEAD" indicator with enhanced visibility
            ctx.font = 'bold 14px Arial';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            const text = 'DEAD';
            const textWidth = ctx.measureText(text).width;
            const textX = transition.position.x;
            const textY = transition.position.y - transition.height / 2 - 25;
            
            // Enhanced background for text
            ctx.fillStyle = 'rgba(139, 0, 0, 0.95)';
            ctx.fillRect(textX - textWidth/2 - 6, textY - 8, textWidth + 12, 16);
            
            // White border for text background
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
            ctx.lineWidth = 1;
            ctx.strokeRect(textX - textWidth/2 - 6, textY - 8, textWidth + 12, 16);
            
            // Text with shadow
            ctx.fillStyle = '#000000';
            ctx.fillText(text, textX + 1, textY + 1);
            ctx.fillStyle = '#FFFFFF';
            ctx.fillText(text, textX, textY);
        } else {
            // Regular highlighting for trace transitions
            for (let i = 0; i < 2; i++) {
                ctx.beginPath();
                ctx.rect(
                    transition.position.x - transition.width / 2 - 4 - (i * 4),
                    transition.position.y - transition.height / 2 - 4 - (i * 4),
                    transition.width + 8 + (i * 8),
                    transition.height + 8 + (i * 8)
                );
                ctx.strokeStyle = i === 0 ? '#4ECDC4' : 'rgba(78, 205, 196, 0.4)';
                ctx.lineWidth = i === 0 ? 3 : 6;
                ctx.stroke();
            }
        }
    }

    renderArcHighlight(ctx, renderer, arcId) {
        const arc = renderer.petriNet.arcs.get(arcId);
        if (!arc) return;
        
        const sourceElement = renderer.petriNet.places.get(arc.source) || 
                            renderer.petriNet.transitions.get(arc.source);
        const targetElement = renderer.petriNet.places.get(arc.target) || 
                            renderer.petriNet.transitions.get(arc.target);
        
        if (!sourceElement || !targetElement) return;
        
        const { start, end } = renderer.calculateArcEndpoints(sourceElement, targetElement);
        
        // Different arc colors for dead transitions vs traces
        let arcColor = '#FFE66D'; // Default yellow
        let arcColorFaded = 'rgba(255, 230, 109, 0.4)';
        
        if (this.violationInfo && this.violationInfo.violationType === "dead_transition") {
            arcColor = '#FF8C00'; // Orange for dead transition arcs
            arcColorFaded = 'rgba(255, 140, 0, 0.6)';
        }
        
        // Draw multiple arc highlights for emphasis
        for (let i = 0; i < 2; i++) {
            ctx.beginPath();
            ctx.moveTo(start.x, start.y);
            ctx.lineTo(end.x, end.y);
            ctx.strokeStyle = i === 0 ? arcColor : arcColorFaded;
            ctx.lineWidth = i === 0 ? 6 : 10;
            ctx.stroke();
        }
    }

    renderPlaceProblemInfo(ctx, place, placeInfo) {
        const x = place.position.x + place.radius + 15;
        const y = place.position.y - 10;
        
        let text = '';
        let bgColor = 'rgba(255, 0, 0, 0.95)'; // Default red
        let textColor = '#FFFFFF';
        
        if (placeInfo.missingTokens !== undefined) {
            text = `Missing: ${placeInfo.missingTokens}`;
            bgColor = 'rgba(255, 0, 0, 0.95)'; // Red for missing tokens
        } else if (placeInfo.excessTokens !== undefined) {
            text = `Excess: +${placeInfo.excessTokens}`;
            bgColor = 'rgba(139, 0, 139, 0.95)'; // Purple for excess tokens
        } else if (placeInfo.deficit !== undefined) {
            text = `Need: ${placeInfo.requiredTokens}`;
            bgColor = 'rgba(255, 140, 0, 0.95)'; // Orange for token deficit (dead transitions)
        } else if (placeInfo.maxFoundTokens !== undefined) {
            text = `Max: ${placeInfo.maxFoundTokens}/${placeInfo.requiredTokens}`;
            bgColor = 'rgba(255, 140, 0, 0.95)'; // Orange for insufficient capacity
        }

        if (text) {
            // Set font and measure text
            ctx.font = 'bold 11px Arial';
            ctx.textAlign = 'left';
            ctx.textBaseline = 'middle';
            const textMetrics = ctx.measureText(text);
            const textWidth = textMetrics.width;
            const padding = 8;
            const boxHeight = 20;
            
            // Draw shadow first
            ctx.fillStyle = 'rgba(0, 0, 0, 0.3)';
            ctx.fillRect(x + 2, y - boxHeight/2 + 2, textWidth + padding * 2, boxHeight);
            
            // Draw background
            ctx.fillStyle = bgColor;
            ctx.fillRect(x, y - boxHeight/2, textWidth + padding * 2, boxHeight);
            
            // Draw border
            ctx.strokeStyle = 'rgba(255, 255, 255, 0.9)';
            ctx.lineWidth = 2;
            ctx.strokeRect(x, y - boxHeight/2, textWidth + padding * 2, boxHeight);
            
            // Draw text
            ctx.fillStyle = textColor;
            ctx.fillText(text, x + padding, y);
        }
    }

    renderDataOverlays() {
        const ctx = this.mainRenderer.ctx;
        const renderer = this.mainRenderer;
        
        console.log("Rendering", this.dataOverlays.size, "data overlays");
        
        // Ensure we have a valid context
        if (!ctx || !renderer) {
            console.error("No valid context or renderer");
            return;
        }
        
        ctx.save();
        ctx.translate(renderer.panOffset.x, renderer.panOffset.y);
        ctx.scale(renderer.zoomFactor, renderer.zoomFactor);
        
        for (const [transitionId, overlay] of this.dataOverlays) {
            if (overlay.isPlace) {
                // Skip place overlays for now - they're handled in place highlighting
                continue;
            }
            
            const transition = renderer.petriNet.transitions.get(transitionId);
            if (!transition) continue;
            
            console.log("Rendering overlay for transition", transitionId, "type:", overlay.type);
            
            const x = transition.position.x + 50; // Offset to the right
            const y = transition.position.y - 60; // Offset above
            
            let text;
            if (overlay.type === 'deadTransition') {
                text = this.formatDeadTransitionOverlay(overlay.data);
            } else if (overlay.type === 'dataChanges') {
                text = this.formatDataChangesOverlay(overlay);
            } else if (overlay.type === 'dataValuation') {
                text = this.formatDataValuationOverlay(overlay);
            } else {
                text = this.formatDataOverlay(overlay);
            }
            
            const lines = text.split('\n');
            const lineHeight = 16;
            const padding = 10;
            
            ctx.font = '12px monospace';
            const maxWidth = Math.max(...lines.map(line => ctx.measureText(line).width));
            const boxWidth = Math.max(120, maxWidth + padding * 2); // Minimum width
            const boxHeight = lines.length * lineHeight + padding * 2;
            
            // Different background color based on overlay type
            if (overlay.type === 'deadTransition') {
                ctx.fillStyle = 'rgba(139, 0, 0, 0.95)'; // Dark red for dead transitions
                ctx.strokeStyle = '#8B0000';
            } else if (overlay.type === 'dataChanges') {
                ctx.fillStyle = 'rgba(46, 125, 50, 0.95)'; // Green for data changes
                ctx.strokeStyle = '#2E7D32';
            } else {
                ctx.fillStyle = 'rgba(46, 52, 64, 0.95)'; // Default dark blue
                ctx.strokeStyle = '#88C0D0';
            }
            
            // Draw shadow first
            ctx.fillStyle = 'rgba(0, 0, 0, 0.3)';
            ctx.fillRect(x + 3, y - boxHeight + 3, boxWidth, boxHeight);
            
            // Draw main box
            ctx.fillStyle = overlay.type === 'deadTransition' ? 'rgba(139, 0, 0, 0.95)' : 
                           (overlay.type === 'dataChanges' ? 'rgba(46, 125, 50, 0.95)' : 'rgba(46, 52, 64, 0.95)');
            ctx.fillRect(x, y - boxHeight, boxWidth, boxHeight);
            
            // Draw border
            ctx.lineWidth = 2;
            ctx.strokeRect(x, y - boxHeight, boxWidth, boxHeight);
            
            // Draw text
            ctx.fillStyle = '#ECEFF4';
            ctx.textAlign = 'left';
            
            lines.forEach((line, index) => {
                ctx.fillText(line, x + padding, y - boxHeight + padding + (index + 1) * lineHeight);
            });
        }

        // Render responsible variables with type information
        this.renderResponsibleVariables();
        
        ctx.restore();
        console.log("Data overlays rendering complete");
    }

    formatDeadTransitionOverlay(data) {
        const lines = [`DEAD: ${data.deadTransition.transitionLabel}`];
        
        // Add the main reason
        lines.push(`Reason: ${data.reason.replace('Dead transition: ', '')}`);
        
        // Add problematic places if any
        if (data.problematicPlaces && data.problematicPlaces.length > 0) {
            lines.push('');
            lines.push('Token Issues:');
            for (const place of data.problematicPlaces) {
                lines.push(`• ${place.placeName}: needs ${place.requiredTokens}, max ${place.maxFoundTokens || place.currentTokens}`);
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
        
        // Add suggested fix if available
        if (data.suggestedFix) {
            lines.push('');
            lines.push('Suggested Fix:');
            if (data.suggestedFix.type === 'add_tokens') {
                for (const action of data.suggestedFix.actions) {
                    lines.push(`• Add ${action.addTokens} tokens to ${action.placeName}`);
                }
            } else if (data.suggestedFix.type === 'satisfying_values') {
                for (const value of data.suggestedFix.values) {
                    lines.push(`• Set ${value.variable} = ${value.suggestedValue}`);
                }
            }
        }
        
        return lines.join('\n');
    }

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

    formatDataChangesOverlay(overlay) {
        const lines = ['Data Changes:'];
        
        if (overlay.changes && overlay.changes.length > 0) {
            for (const change of overlay.changes) {
                const symbol = change.changeType === 'created' ? '+' : 
                              (change.changeType === 'deleted' ? '-' : '→');
                lines.push(`${symbol} ${change.variable}: ${change.oldValue} → ${change.newValue}`);
            }
        } else {
            lines.push('No changes');
        }
        
        return lines.join('\n');
    }

    formatDataValuationOverlay(overlay) {
        const lines = ['Variables:'];
        
        if (overlay.valuation && Object.keys(overlay.valuation).length > 0) {
            for (const [varName, value] of Object.entries(overlay.valuation)) {
                lines.push(`${varName} = ${value}`);
            }
        } else {
            lines.push('No variables');
        }
        
        return lines.join('\n');
    }

    formatDataOverlay(overlay) {
        return this.formatDataChangesOverlay(overlay);
    }

    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

/**
 * Enhanced UI for the Suvorov & Lomazova DPN Soundness Verifier
 */
class EnhancedSuvorovLomazovaVerificationUI {
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
        if (document.getElementById('enhanced-sl-verification-styles')) return;
        const style = document.createElement('style');
        style.id = 'enhanced-sl-verification-styles';
        style.textContent = `
            /* Enhanced Verification Styles */
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

            .enhanced-analyze-btn {
                background: linear-gradient(135deg, #A3BE8C, #88C0D0) !important;
                color: #2E3440 !important;
                font-weight: 600 !important;
                padding: 6px 12px !important;
                border-radius: 5px !important;
                border: none !important;
                cursor: pointer !important;
            }

            .enhanced-analyze-btn:hover {
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

            .suggested-fix {
                background-color: rgba(163, 190, 140, 0.2);
                padding: 10px;
                border-radius: 4px;
                margin-bottom: 10px;
                border-left: 3px solid #A3BE8C;
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
                display: flex;
                gap: 10px;
                justify-content: flex-end;
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

            .trace-control-btn.persistent {
                background-color: #A3BE8C;
                color: #2E3440;
            }

            .trace-control-btn.persistent:hover {
                background-color: #B4CFB0;
            }
            
            .counterexample-header {
                display: flex;
                justify-content: space-between;
                align-items: center;
                margin-bottom: 8px;
            }

            .verification-algorithm-info {
                background-color: #4C566A;
                border-radius: 5px;
                padding: 15px;
                margin-bottom: 20px;
            }

            .verification-algorithm-info h4 {
                margin: 0 0 10px 0;
                color: #88C0D0;
            }

            .visualization-status {
                font-size: 11px;
                color: #88C0D0;
                margin-top: 5px;
                font-style: italic;
            }
        `;
        document.head.appendChild(style);
    }

    createVerificationSection() {
        const modelTab = document.querySelector('.sidebar-pane[data-tab="model"]');
        if (!modelTab || document.getElementById('enhanced-sl-verification-section')) return;
        const section = document.createElement('div');
        section.id = 'enhanced-sl-verification-section';
        section.className = 'sidebar-section';
        section.innerHTML = `
            <div class="section-header">
                <div class="section-title">
                    <span class="section-icon">🎯</span>
                    <h3>Verification</h3>
                </div>
            </div>
            <div class="section-content">
                <button id="btn-enhanced-sl-verify" class="button-primary" style="width:100%; background: linear-gradient(135deg, #A3BE8C, #88C0D0, #EBCB8B); color: #2E3440; font-weight: 600;">
                    🎯 Soundness Verification
                </button>
            </div>
        `;
        modelTab.appendChild(section);
        section.querySelector('#btn-enhanced-sl-verify').addEventListener('click', () => this.startVerification());
    }

    createVerificationModal() {
        if (document.getElementById('enhanced-sl-verification-modal')) return;
        const modal = document.createElement('div');
        modal.id = 'enhanced-sl-verification-modal';
        modal.className = 'verification-modal';
        modal.innerHTML = `
            <div class="verification-modal-content">
                <div class="verification-modal-header">
                    <h2>🎯 Soundness Verification Results</h2>
                    <button class="verification-close-btn" id="enhanced-sl-close-verification-modal">×</button>
                </div>
                <div class="enhanced-sl-modal-body" id="enhanced-sl-modal-body"></div>
            </div>`;
        document.body.appendChild(modal);
        modal.querySelector('#enhanced-sl-close-verification-modal').addEventListener('click', () => this.closeModal());
        modal.addEventListener('click', (e) => { if (e.target === modal) this.closeModal(); });
    }

    showModal() { 
        document.querySelector('#enhanced-sl-verification-modal').classList.add('show'); 
    }
    
    closeModal() { 
        document.querySelector('#enhanced-sl-verification-modal').classList.remove('show'); 
        // Don't automatically clear visualization when closing modal
    }

    async startVerification() {
        const verifyButton = document.querySelector('#btn-enhanced-sl-verify');
        const modalBody = document.querySelector('#enhanced-sl-modal-body');

        verifyButton.disabled = true;
        verifyButton.innerHTML = '<span class="verification-spinner"></span> Running Enhanced Algorithm...';
        this.showModal();
        modalBody.innerHTML = this.createProgressHTML();

        try {
            this.verifier = new EnhancedSuvorovLomazovaVerifier(this.app.api.petriNet);
            const result = await this.verifier.verify((progress, step) => {
                this.updateProgress(progress, step);
            });
            this.currentCounterexamples = result.counterexampleTraces || [];
            this.initializeTraceVisualizer();
            modalBody.innerHTML = this.createEnhancedResultsHTML(result);
        } catch (error) {
            modalBody.innerHTML = this.createErrorHTML(error);
        } finally {
            verifyButton.disabled = false;
            verifyButton.innerHTML = '🎯 Soundness Verification';
        }
    }

    createProgressHTML() {
        return `
            <div class="verification-algorithm-info">
                <h4>🎯 Enhanced Suvorov & Lomazova Algorithm</h4>
                <p style="color: #D8DEE9; margin: 0;">
                    Advanced data-aware soundness verification with detailed counterexample analysis and visualization.
                </p>
            </div>
            <div class="verification-progress">
                <div class="verification-progress-bar">
                    <div class="verification-progress-fill" id="enhanced-progress-fill" style="width: 0%"></div>
                </div>
                <div class="verification-step" id="enhanced-progress-step">
                    Initializing verification...
                </div>
            </div>
        `;
    }

    updateProgress(progress, step) {
        const progressFill = document.querySelector('#enhanced-progress-fill');
        const progressStep = document.querySelector('#enhanced-progress-step');
        
        if (progressFill) {
            progressFill.style.width = `${progress}%`;
        }
        
        if (progressStep) {
            progressStep.textContent = step;
        }
    }

    initializeTraceVisualizer() {
        console.log("Initializing FIXED trace visualizer");
        if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
            this.traceVisualizer = new EnhancedSuvorovLomazovaTraceVisualizationRenderer(this.app);
            console.log("FIXED Enhanced trace visualizer created");
            
            // Add a test method to the visualizer for debugging
            this.traceVisualizer.testHighlight = () => {
                console.log("Testing highlight functionality");
                this.traceVisualizer.isActive = true;
                this.traceVisualizer.highlightedElements.add("test");
                this.traceVisualizer.mainRenderer.render();
            };
        } else {
            console.warn("Cannot initialize trace visualizer - missing app.editor or app.editor.renderer");
        }
    }

    visualizeCounterexample(counterexampleIndex) {
        console.log("Visualizing counterexample index:", counterexampleIndex);
        console.log("Total counterexamples:", this.currentCounterexamples.length);
        console.log("Trace visualizer exists:", !!this.traceVisualizer);
        
        if (!this.traceVisualizer) {
            console.log("Trace visualizer not found, attempting to initialize");
            this.initializeTraceVisualizer();
        }
        
        if (!this.traceVisualizer || counterexampleIndex >= this.currentCounterexamples.length) {
            console.error("Cannot visualize - no visualizer or invalid index");
            return;
        }
        
        const counterexample = this.currentCounterexamples[counterexampleIndex];
        console.log("Counterexample to visualize:", counterexample);
        
        // Enable persistent highlights to prevent clearing when dialog closes
        this.traceVisualizer.setPersistentHighlights(true);
        this.traceVisualizer.visualizeCounterexample(counterexample);

        document.querySelectorAll('.enhanced-counterexample-item').forEach((item, idx) => {
            item.classList.toggle('active-counterexample', idx === counterexampleIndex);
        });
        this.isVisualizationActive = true;
        
        console.log("Visualization activated with persistent highlights");
    }

    clearCounterexampleVisualization() {
        if (this.traceVisualizer) {
            this.traceVisualizer.setPersistentHighlights(false);
            this.traceVisualizer.clearHighlights();
            this.isVisualizationActive = false;
        }
        document.querySelectorAll('.enhanced-counterexample-item').forEach(item => item.classList.remove('active-counterexample'));
    }

    togglePersistentVisualization() {
        if (this.traceVisualizer) {
            const currentState = this.traceVisualizer.persistentHighlights;
            this.traceVisualizer.setPersistentHighlights(!currentState);
            
            // Update button text to reflect state
            const toggleBtn = document.querySelector('#btn-toggle-persistent');
            if (toggleBtn) {
                toggleBtn.textContent = this.traceVisualizer.persistentHighlights ? "Unlock Highlights" : "Lock Highlights";
                toggleBtn.classList.toggle('persistent', this.traceVisualizer.persistentHighlights);
            }
        }
    }

    createEnhancedResultsHTML(result) {
        const statusClass = result.isSound ? 'sound' : 'unsound';
        const statusIcon = result.isSound ? '✅' : '❌';
        let propertiesHTML = result.properties.map(prop => {
            let counterexampleHTML = (!prop.satisfied && prop.counterexamples?.length > 0) 
                ? this.createEnhancedCounterexampleSection(prop.counterexamples, prop.name) 
                : '';
            return `<div class="verification-property">
                        <div class="verification-property-header">
                            <div class="verification-property-title">${prop.name}</div>
                            <div class="verification-property-status ${prop.satisfied ? 'pass' : 'fail'}">${prop.satisfied ? 'PASS' : 'FAIL'}</div>
                        </div>
                        <div class="verification-property-description">${prop.description}</div>
                        ${counterexampleHTML}
                    </div>`;
        }).join('');

        return `
            <div class="verification-algorithm-info">
                <h4>🎯 Enhanced Suvorov & Lomazova Algorithm</h4>
                <p style="color: #D8DEE9; margin: 0;">
                    Advanced formal verification with comprehensive counterexample analysis and intelligent visualization.
                </p>
            </div>
            <div class="verification-status ${statusClass}">
                <div class="verification-status-icon">${statusIcon}</div>
                <div>${result.isSound ? 'Formally Sound' : 'Formally Unsound'}</div>
            </div>
            <div class="verification-details">${propertiesHTML}</div>
            <div class="verification-timing">Enhanced verification completed in ${result.executionTime}ms</div>`;
    }

    createEnhancedCounterexampleSection(counterexamples, propertyName) {
        let itemsHTML = counterexamples.map((ce, index) => {
            const globalIndex = this.currentCounterexamples.indexOf(ce);
            return `<div class="enhanced-counterexample-item" data-property="${propertyName}" data-index="${globalIndex}">
                        <div class="counterexample-header">
                            <span class="counterexample-title">Counterexample ${index + 1}</span>
                            <div class="counterexample-actions">
                                <button class="enhanced-analyze-btn" onclick="window.enhancedFormalVerifierUI.visualizeCounterexample(${globalIndex})">
                                    🎯 Analyze & Visualize
                                </button>
                            </div>
                        </div>
                        <div class="enhanced-counterexample-details">
                            ${this.formatCounterexampleDetails(ce)}
                        </div>
                        <div class="visualization-status" id="viz-status-${globalIndex}">
                            Click "Analyze & Visualize" to see detailed trace with variable evolution boxes
                        </div>
                    </div>`;
        }).join('');

        return `<div class="enhanced-counterexample-section">
                    <h4>🔍 Detailed Counterexample Analysis (${counterexamples.length})</h4>
                    <div class="counterexample-controls">
                        <button class="trace-control-btn" id="btn-toggle-persistent" onclick="window.enhancedFormalVerifierUI.togglePersistentVisualization()">
                            Lock Highlights
                        </button>
                        <button class="trace-control-btn" onclick="window.enhancedFormalVerifierUI.clearCounterexampleVisualization()">
                            Clear All Highlights
                        </button>
                    </div>
                    <div class="enhanced-counterexample-list">
                        ${itemsHTML}
                    </div>
                </div>`;
    }

    formatCounterexampleDetails(ce) {
        let details = `<div class="violation-summary">
                          <strong>Violation:</strong> ${ce.reason}
                       </div>`;

        if (ce.detailedReason) {
            details += `<div class="detailed-reason">
                           <strong>Detailed Analysis:</strong><br>
                           ${ce.detailedReason}
                        </div>`;
        }

        if (ce.problematicPlaces && ce.problematicPlaces.length > 0) {
            details += `<div class="problematic-places">
                           <strong>Problematic Places:</strong><br>
                           ${ce.problematicPlaces.map(p => 
                               `• ${p.placeName}: ${this.formatPlaceProblem(p)}`
                           ).join('<br>')}
                        </div>`;
        }

        if (ce.responsibleVariables && ce.responsibleVariables.length > 0) {
            details += `<div class="responsible-variables">
                           <strong>Responsible Variables:</strong><br>
                           ${ce.responsibleVariables.map(v => 
                               `• ${v.variable} = ${this.formatVariableForCounterexample(v)} (${v.type || 'unknown'} type)${v.problem ? ` - ${v.problem}` : ''}`
                           ).join('<br>')}
                        </div>`;
        }

        if (ce.suggestedFix) {
            details += `<div class="suggested-fix">
                           <strong>Suggested Fix:</strong><br>
                           ${this.formatSuggestedFix(ce.suggestedFix)}
                        </div>`;
        }

        if (ce.trace && ce.trace.length > 0) {
            details += `<div class="execution-info"><strong>Execution steps:</strong> ${ce.trace.length} (with data evolution tracking)</div>`;
        }

        if (ce.deadTransition) {
            details += `<div class="dead-transition-info"><strong>Dead transition:</strong> ${ce.deadTransition.transitionLabel}</div>`;
        }

        return details;
    }

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

    formatSuggestedFix(suggestedFix) {
        if (suggestedFix.type === 'add_tokens') {
            return `${suggestedFix.description}:<br>${suggestedFix.actions.map(action => 
                `• Add ${action.addTokens} tokens to ${action.placeName}`
            ).join('<br>')}`;
        } else if (suggestedFix.type === 'satisfying_values') {
            return `${suggestedFix.description}:<br>${suggestedFix.values.map(value => 
                `• Set ${value.variable} = ${value.suggestedValue} (currently ${value.currentValue})`
            ).join('<br>')}`;
        } else if (suggestedFix.type === 'error') {
            return `${suggestedFix.description}: ${suggestedFix.error}`;
        }
        return 'No specific fix suggested';
    }

    createErrorHTML(error) {
        return `<div class="verification-status error">
                    <div class="verification-status-icon">⚠️</div>
                    <div>Enhanced verification error: ${error.message}</div>
                </div>`;
    }
}

// Initialization logic
document.addEventListener('DOMContentLoaded', () => {
    // Ensure this runs after the main app is initialized
    setTimeout(() => {
        if (window.petriApp && !window.enhancedFormalVerifierUI) {
            window.enhancedFormalVerifierUI = new EnhancedSuvorovLomazovaVerificationUI(window.petriApp);
            console.log("Enhanced Suvorov-Lomazova Verification System initialized with advanced visualization");
        }
    }, 1200);
});