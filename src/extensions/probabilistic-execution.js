/**
 * Probabilistic Execution Engine for Data Petri Nets (Refactored)
 * 
 * Implements the approach from "Data Petri Nets Meet Probabilistic Programming"
 * (Kuhn et al., BPM 2024) - https://doi.org/10.1007/978-3-031-70396-6_2
 * 
 * This refactored module generates and executes WebPPL code to properly resolve
 * DPN expressions following the formal Csim translation from Section 5.2:
 * 
 * Key Paper References:
 * - Section 3: Data Petri Nets with Probabilistic Schedulers (Definition 1-6)
 * - Section 4: The Probabilistic Programming Language PPL (Figure 2-4)
 * - Section 5: From DPNs to PPL Programs (Figure 5, Csim construction)
 * - Section 5.1: Setup and Conventions
 * - Section 5.2: Simulating Net Runs in PPL
 * - Section 5.3: Correctness (Theorem 1)
 * 
 * The engine supports two modes:
 * 1. Native Mode - Direct JavaScript execution (fast, for simple nets)
 * 2. WebPPL Mode - Full probabilistic programming (accurate, for DPNs with constraints)
 */

import { WebPPLCodeGenerator } from './webppl-code-generator.js';

/**
 * Seeded random number generator (Mulberry32)
 * Used for reproducible probabilistic simulations in Native Mode.
 * 
 * [Definition 3] Scheduler S: SN → Dist(TN) × (VN → Dist(ΔN))
 * The seed enables reproducible distributions for ST (transition selection)
 * and SV (variable sampling).
 * 
 * @param {number} seed - Initial seed value
 * @returns {function} A function that returns random numbers in [0, 1)
 */
function createSeededRandom(seed) {
    let state = seed;
    return function() {
        state |= 0;
        state = state + 0x6D2B79F5 | 0;
        let t = Math.imul(state ^ state >>> 15, 1 | state);
        t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
        return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
}

/**
 * [Definition 3] Uniform Draw - Implements ST scheduler for transition selection
 * 
 * @param {Array} items - Array of items to select from
 * @param {function} random - Random number generator function
 * @returns {*} Uniformly selected item
 */
function uniformDraw(items, random) {
    if (items.length === 0) return null;
    const index = Math.floor(random() * items.length);
    return items[index];
}

/**
 * [Definition 3] Weighted Draw - Alternative scheduler for transition selection
 * 
 * @param {Array} items - Array of items to select from
 * @param {Object} weights - Map of item -> weight
 * @param {function} random - Random number generator function
 * @returns {*} Weighted random selection
 */
function weightedDraw(items, weights, random) {
    if (items.length === 0) return null;
    
    const itemWeights = items.map(item => weights[item] || 1);
    const totalWeight = itemWeights.reduce((sum, w) => sum + w, 0);
    
    let randomValue = random() * totalWeight;
    for (let i = 0; i < items.length; i++) {
        randomValue -= itemWeights[i];
        if (randomValue <= 0) {
            return items[i];
        }
    }
    return items[items.length - 1];
}

/**
 * ProbabilisticExecutionEngine
 * 
 * Main class that provides probabilistic execution capabilities for DPNs.
 * Implements the simulation semantics from Section 5 of the paper.
 * 
 * [Figure 5] Csim structure:
 *   Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
 */
class ProbabilisticExecutionEngine {
    /**
     * Creates a new ProbabilisticExecutionEngine instance.
     * 
     * @param {Object} options - Configuration options
     * @param {number} options.seed - Random seed for reproducibility (default: Date.now())
     * @param {string} options.scheduler - Transition selection strategy: 'uniform' | 'weighted' (default: 'uniform')
     * @param {Object} options.transitionWeights - Weights for weighted scheduler
     * @param {Object} options.variableDistributions - SV distributions for variable sampling
     * @param {number} options.maxSteps - Maximum simulation steps (default: 10000)
     * @param {string} options.executionMode - 'native' | 'webppl' | 'auto' (default: 'auto')
     */
    constructor(options = {}) {
        // [Definition 3] Scheduler configuration
        this.seed = options.seed ?? Date.now();
        this.scheduler = options.scheduler ?? 'uniform';
        this.transitionWeights = options.transitionWeights ?? {};
        this.variableDistributions = options.variableDistributions ?? {};
        this.maxSteps = options.maxSteps ?? 10000;
        this.executionMode = options.executionMode ?? 'auto';
        
        // Initialize seeded random generator for native mode
        this.random = createSeededRandom(this.seed);
        
        // Initialize WebPPL code generator
        this.codeGenerator = new WebPPLCodeGenerator({
            schedulerType: this.scheduler,
            transitionWeights: this.transitionWeights,
            variableDistributions: this.variableDistributions,
            maxSteps: this.maxSteps
        });
        
        // Cache for generated WebPPL code
        this._webpplCodeCache = null;
        this._webpplCodeNetHash = null;
        
        // WebPPL module reference (lazy loaded)
        this._webppl = null;
    }

    /**
     * Reset the random generator with a new seed.
     * 
     * @param {number} seed - New seed value
     */
    reseed(seed) {
        this.seed = seed;
        this.random = createSeededRandom(seed);
    }

    /**
     * Get the WebPPL module (lazy load).
     * 
     * @returns {Promise<Object>} WebPPL module
     */
    async getWebPPL() {
        if (this._webppl) {
            return this._webppl;
        }
        
        try {
            // Dynamic import for browser compatibility
            const webppl = await import('webppl');
            this._webppl = webppl.default || webppl;
            return this._webppl;
        } catch (error) {
            console.warn('[PP Engine] WebPPL not available, falling back to native mode:', error.message);
            return null;
        }
    }

    /**
     * Determine the best execution mode for a given net.
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {string} 'native' | 'webppl'
     */
    determineExecutionMode(net) {
        if (this.executionMode !== 'auto') {
            return this.executionMode;
        }
        
        // Check if net has complex postconditions that need WebPPL
        const needsWebPPL = this.netRequiresWebPPL(net);
        return needsWebPPL ? 'webppl' : 'native';
    }

    /**
     * Check if a net requires WebPPL for proper execution.
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {boolean} True if WebPPL is needed
     */
    netRequiresWebPPL(net) {
        // Check if any transition has constraint-style postconditions
        for (const [id, transition] of net.transitions) {
            const postcondition = transition.postcondition || '';
            
            // Constraint patterns that require probabilistic inference
            if (postcondition.match(/[a-zA-Z_][a-zA-Z0-9_]*'\s*[<>=!]+/)) {
                // Has primed variable with comparison
                const hasInequality = postcondition.match(/'[^=]*[<>][^=]*/) ||
                                     postcondition.match(/'\s*[<>]/);
                if (hasInequality) {
                    return true; // Needs sampling + observe
                }
            }
            
            // Check for sampling keywords
            if (postcondition.match(/\b(sample|uniform|gaussian|bernoulli|categorical)\b/i)) {
                return true;
            }
        }
        
        return false;
    }

    /**
     * Generate WebPPL code for a net.
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @param {Object} options - Generation options
     * @returns {string} Generated WebPPL code
     */
    generateWebPPLCode(net, options = {}) {
        return this.codeGenerator.generateCode(net, options);
    }

    /**
     * [Section 5.1] frontier(M, α) = {t ∈ T | ∃β : (M,α)[(t,β)⟩}
     * 
     * Computes the frontier - set of all enabled transitions in current state.
     * 
     * [Definition 2] (Transition Enabling):
     * A step (t, β) is enabled in state (M, α) iff:
     * (i) β is defined for all variables in V(pre(t)) ∪ V(post(t))
     * (ii) β matches α on all unprimed variables  
     * (iii) For every p ∈ •t: M(p) ≥ l(p,t) (sufficient tokens)
     * (iv) β |= pre(t) ∧ post(t) (guards are satisfied)
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {Array<string>} Array of enabled transition IDs
     */
    getEnabledTransitions(net) {
        // Update enabled transitions based on token availability and guards
        net.updateEnabledTransitions();
        
        const enabled = [];
        for (const [id, transition] of net.transitions) {
            if (transition.isEnabled) {
                enabled.push(id);
            }
        }
        return enabled;
    }

    /**
     * [Definition 3] Select transition using scheduler ST
     * 
     * "P_S[M,α](t) = [t ∈ frontier(M,α)] · ST(t) / Σ_{t'∈frontier} ST(t')"
     * 
     * @param {Array<string>} enabledTransitions - Array of enabled transition IDs
     * @returns {string|null} Selected transition ID or null if none enabled
     */
    selectTransition(enabledTransitions) {
        if (enabledTransitions.length === 0) {
            return null;
        }
        
        // [Example 1] Use configured scheduler (uniform by default)
        if (this.scheduler === 'weighted' && Object.keys(this.transitionWeights).length > 0) {
            return weightedDraw(enabledTransitions, this.transitionWeights, this.random);
        }
        
        // [Definition 3] Default: Uniform scheduler ST = uniformDraw
        return uniformDraw(enabledTransitions, this.random);
    }

    /**
     * [Section 5.1] Check if current state is a goal state
     * 
     * "Examples of G include (beside deadlocked states) the set of all states 
     * where some final marking has been reached"
     * 
     * [Definition 6] Goal states G are necessary for computing termination
     * probability P_S^N(φ).
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {Object} Goal check result with {isGoal, reason, details}
     */
    checkGoalState(net) {
        const result = {
            isGoal: false,
            reason: null,
            details: {}
        };
        
        // [Section 5.1] Check if all places with finalMarking have reached it
        let hasAnyFinalMarking = false;
        let allFinalMarkingsReached = true;
        const finalMarkingStatus = {};
        
        for (const [id, place] of net.places) {
            if (place.finalMarking !== undefined && place.finalMarking !== null && place.finalMarking > 0) {
                hasAnyFinalMarking = true;
                const reached = place.tokens >= place.finalMarking;
                finalMarkingStatus[id] = {
                    expected: place.finalMarking,
                    actual: place.tokens,
                    reached: reached
                };
                if (!reached) {
                    allFinalMarkingsReached = false;
                }
            }
        }
        
        // If finalMarking is defined and all are reached, it's a goal state
        if (hasAnyFinalMarking && allFinalMarkingsReached) {
            result.isGoal = true;
            result.reason = 'final_marking_reached';
            result.details = finalMarkingStatus;
            return result;
        }
        
        // [Section 5.1] "G contains all deadlocked net states"
        const enabledTransitions = this.getEnabledTransitions(net);
        if (enabledTransitions.length === 0) {
            result.isGoal = true;
            result.reason = 'deadlock';
            result.details = { noEnabledTransitions: true };
        }
        
        return result;
    }

    /**
     * Validate that the net has a defined goal state (finalMarking).
     * 
     * [Section 5.1] Goal states G must be specified via finalMarking.
     * Without a defined goal, the simulation cannot determine when to terminate
     * for computing P_S^N(φ).
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @throws {Error} If no finalMarking is defined
     */
    validateGoalStateDefinition(net) {
        let hasAnyFinalMarking = false;
        
        for (const [id, place] of net.places) {
            if (place.finalMarking !== undefined && place.finalMarking !== null && place.finalMarking > 0) {
                hasAnyFinalMarking = true;
                break;
            }
        }
        
        if (!hasAnyFinalMarking) {
            throw new Error(
                `No finalMarking defined in the Petri net.\n` +
                `[Section 5.1 of the paper] Goal states G must be specified via the 'finalMarking' ` +
                `attribute on places.\n` +
                `Please add 'finalMarking: 1' (or appropriate value) to the place(s) that ` +
                `represent the final state.`
            );
        }
    }

    /**
     * [Section 5.2] Execute a single probabilistic step (Native Mode)
     * 
     * Implements one iteration of the Cloop from Figure 5:
     *   Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)
     * 
     * 1. Compute frontier (enabled transitions)
     * 2. Select transition using scheduler ST
     * 3. Fire selected transition (Cfire)
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {Promise<Object>} Step result with {fired, transitionId, status}
     */
    async stepNative(net) {
        // [Section 5.1] Check goal state first
        const goalCheck = this.checkGoalState(net);
        if (goalCheck.isGoal) {
            return {
                fired: false,
                transitionId: null,
                status: goalCheck.reason === 'deadlock' ? 'deadlock' : 'goal',
                goalDetails: goalCheck.details
            };
        }
        
        // [Section 5.1] Compute frontier(M, α)
        const enabledTransitions = this.getEnabledTransitions(net);
        
        if (enabledTransitions.length === 0) {
            // Should not reach here due to goal check, but safety fallback
            return {
                fired: false,
                transitionId: null,
                status: 'deadlock',
                goalDetails: { noEnabledTransitions: true }
            };
        }
        
        // [Definition 3] Select transition using scheduler ST
        const selectedTransition = this.selectTransition(enabledTransitions);
        
        // [Section 5.2] Cfire(t) - Fire the chosen transition
        // The actual firing handles token movement and variable updates
        let fireResult;
        if (typeof net.fireTransition === 'function') {
            // DataPetriNet.fireTransition is async
            fireResult = await net.fireTransition(selectedTransition);
        } else {
            fireResult = false;
        }
        
        if (fireResult) {
            // Update enabled transitions after firing
            net.updateEnabledTransitions();
        }
        
        return {
            fired: fireResult,
            transitionId: selectedTransition,
            status: 'active',
            enabledBefore: enabledTransitions.length
        };
    }

    /**
     * [Section 5.2] Execute a single probabilistic step
     * 
     * For step-by-step simulation, uses native mode for responsiveness.
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @returns {Promise<Object>} Step result with {fired, transitionId, status}
     */
    async step(net) {
        return this.stepNative(net);
    }

    /**
     * [Figure 5] Full simulation using WebPPL - Run until goal state
     * 
     * This method generates WebPPL code and executes it to get a complete
     * probabilistic run that satisfies the DPN semantics including:
     * - Proper handling of constraint postconditions via observe
     * - Correct sampling from scheduler distributions
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @param {Object} options - Simulation options
     * @returns {Promise<Object>} Simulation result with trace, final state, status
     */
    async runWebPPLSimulation(net, options = {}) {
        const webppl = await this.getWebPPL();
        
        if (!webppl) {
            console.warn('[PP Engine] WebPPL unavailable, falling back to native simulation');
            return this.runNativeSimulation(net, options);
        }
        
        // Generate WebPPL code
        const code = this.generateWebPPLCode(net, { includeComments: false });
        
        console.log('[PP Engine] Executing WebPPL simulation...');
        console.log('[PP Engine] Generated code:\n', code.substring(0, 500), '...');
        
        return new Promise((resolve, reject) => {
            try {
                webppl.run(code, (err, result) => {
                    if (err) {
                        console.error('[PP Engine] WebPPL execution error:', err);
                        reject(err);
                        return;
                    }
                    
                    // Convert WebPPL result to our format
                    const simulationResult = {
                        status: result.status || 'completed',
                        trace: (result.trace || []).map((tid, idx) => ({
                            step: idx + 1,
                            transitionId: tid,
                            transition: net.transitions.get(tid)?.label || tid
                        })),
                        traceLength: result.trace?.length || 0,
                        finalState: {
                            marking: result.state?.marking || {},
                            valuation: result.state?.valuation || {}
                        },
                        goalDetails: result.status === 'goal' ? result.state : null,
                        executionMode: 'webppl'
                    };
                    
                    // Apply the final state to the net
                    this.applyStateToNet(net, simulationResult.finalState);
                    
                    resolve(simulationResult);
                });
            } catch (error) {
                reject(error);
            }
        });
    }

    /**
     * [Figure 5] Full simulation using Native mode
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @param {Object} options - Simulation options
     * @returns {Promise<Object>} Simulation result
     */
    async runNativeSimulation(net, options = {}) {
        const validateGoal = options.validateGoal ?? true;
        const onStep = options.onStep ?? null;
        
        if (validateGoal) {
            this.validateGoalStateDefinition(net);
        }
        
        const trace = [];
        let stepCount = 0;
        let status = 'active';
        let goalDetails = null;
        
        while (stepCount < this.maxSteps) {
            const stepResult = await this.stepNative(net);
            
            if (stepResult.fired) {
                trace.push({
                    step: stepCount + 1,
                    transitionId: stepResult.transitionId,
                    transition: net.transitions.get(stepResult.transitionId)?.label || stepResult.transitionId
                });
                
                if (onStep) {
                    onStep(stepCount + 1, stepResult.transitionId, net);
                }
                
                stepCount++;
            } else {
                status = stepResult.status;
                goalDetails = stepResult.goalDetails;
                break;
            }
        }
        
        if (stepCount >= this.maxSteps) {
            status = 'max_steps_exceeded';
        }
        
        const finalMarking = {};
        for (const [id, place] of net.places) {
            finalMarking[id] = place.tokens;
        }
        
        const finalValuation = {};
        if (net.dataVariables && typeof net.getDataValuation === 'function') {
            Object.assign(finalValuation, net.getDataValuation());
        }
        
        return {
            status: status,
            trace: trace,
            traceLength: trace.length,
            finalState: {
                marking: finalMarking,
                valuation: finalValuation
            },
            goalDetails: goalDetails,
            executionMode: 'native'
        };
    }

    /**
     * Apply a state (marking and valuation) to a net.
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @param {Object} state - State with marking and valuation
     */
    applyStateToNet(net, state) {
        // Apply marking
        if (state.marking) {
            for (const [placeId, tokens] of Object.entries(state.marking)) {
                const place = net.places.get(placeId);
                if (place) {
                    place.tokens = tokens;
                }
            }
        }
        
        // Apply valuation
        if (state.valuation && typeof net.setDataValuation === 'function') {
            net.setDataValuation(state.valuation);
        }
        
        // Update enabled transitions
        net.updateEnabledTransitions();
    }

    /**
     * [Figure 5] Full simulation - Run until goal state or max steps
     * 
     * Automatically selects the best execution mode based on the net:
     * - Native mode: Fast, for simple nets without constraint postconditions
     * - WebPPL mode: Accurate, for DPNs with constraint postconditions
     * 
     * Implements the complete Csim program:
     *   Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
     * 
     * [Theorem 1] (Correctness):
     * "For every initial net state (M,α), executing the main loop of Csim
     * produces the same distribution over runs as the encoded net N under scheduler S."
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net instance
     * @param {Object} options - Simulation options
     * @param {boolean} options.validateGoal - Whether to validate finalMarking exists (default: true)
     * @param {function} options.onStep - Callback after each step: (stepNum, transitionId, net) => void
     * @param {boolean} options.forceWebPPL - Force WebPPL execution mode (default: false)
     * @returns {Promise<Object>} Simulation result with trace, final state, status
     */
    async runFullSimulation(net, options = {}) {
        const validateGoal = options.validateGoal ?? true;
        const forceWebPPL = options.forceWebPPL ?? false;
        
        // [Section 5.1] Validate goal state definition
        if (validateGoal) {
            this.validateGoalStateDefinition(net);
        }
        
        // Determine execution mode
        const mode = forceWebPPL ? 'webppl' : this.determineExecutionMode(net);
        
        console.log(`[PP Engine] Running full simulation in ${mode} mode`);
        
        if (mode === 'webppl') {
            try {
                return await this.runWebPPLSimulation(net, options);
            } catch (error) {
                console.warn('[PP Engine] WebPPL simulation failed, falling back to native:', error.message);
                return this.runNativeSimulation(net, options);
            }
        }
        
        return this.runNativeSimulation(net, options);
    }

    /**
     * Generate multiple simulation cases for event log creation.
     * 
     * [Definition 6] (Run Probability):
     * "For a goal set G and a set Runs_G of runs ending in G,
     * P_S^N(ρ) = L_S^N(ρ) / Σ_{ρ'∈Runs_G} L_S^N(ρ')"
     * 
     * This method generates N independent runs for statistical analysis.
     * 
     * @param {function} netFactory - Function that returns a fresh net clone for each case
     * @param {number} numCases - Number of cases to generate
     * @param {Object} options - Generation options
     * @param {boolean} options.validateGoal - Whether to validate finalMarking exists (default: true)
     * @param {function} options.onCaseStart - Callback when case starts: (caseNum) => void
     * @param {function} options.onCaseEnd - Callback when case ends: (caseNum, result) => void
     * @param {function} options.onStep - Callback after each step: (caseNum, stepNum, transitionId, net) => void
     * @param {boolean} options.useWebPPL - Force WebPPL mode for all cases (default: false)
     * @returns {Promise<Array>} Array of simulation results for each case
     */
    async generateCases(netFactory, numCases, options = {}) {
        const validateGoal = options.validateGoal ?? true;
        const onCaseStart = options.onCaseStart ?? null;
        const onCaseEnd = options.onCaseEnd ?? null;
        const onStep = options.onStep ?? null;
        const useWebPPL = options.useWebPPL ?? false;
        
        // Validate goal state on first net
        if (validateGoal) {
            const testNet = netFactory();
            this.validateGoalStateDefinition(testNet);
        }
        
        const cases = [];
        const baseSeed = this.seed;
        
        for (let caseNum = 1; caseNum <= numCases; caseNum++) {
            if (onCaseStart) {
                onCaseStart(caseNum);
            }
            
            // Create fresh net clone for this case
            const net = netFactory();
            
            // Reseed for each case to ensure reproducibility
            this.reseed(baseSeed + caseNum);
            
            // Run simulation for this case
            let result;
            if (useWebPPL) {
                result = await this.runWebPPLSimulation(net, { validateGoal: false });
            } else {
                result = await this.runNativeSimulation(net, {
                    validateGoal: false,
                    onStep: onStep ? (stepNum, transitionId, net) => onStep(caseNum, stepNum, transitionId, net) : null
                });
            }
            
            // Add case metadata
            result.caseId = caseNum;
            cases.push(result);
            
            if (onCaseEnd) {
                onCaseEnd(caseNum, result);
            }
        }
        
        return cases;
    }

    /**
     * Convert simulation results to XES-compatible event log format.
     * 
     * Transforms the trace from simulation results into events suitable
     * for process mining analysis.
     * 
     * @param {Array} cases - Array of simulation results from generateCases
     * @param {Object} options - Formatting options
     * @param {Date} options.startTimestamp - Base timestamp for first event
     * @param {number} options.avgDuration - Average duration between events (ms)
     * @param {string} options.format - 'lifecycle' | 'classic'
     * @returns {Array} XES-compatible event log
     */
    casesToEventLog(cases, options = {}) {
        const startTimestamp = options.startTimestamp ?? new Date();
        const avgDuration = options.avgDuration ?? 1000;
        const format = options.format ?? 'classic';
        
        const eventLog = [];
        let currentTime = new Date(startTimestamp);
        
        for (const caseResult of cases) {
            const caseId = `case_${caseResult.caseId}`;
            
            for (const step of caseResult.trace) {
                if (format === 'classic') {
                    eventLog.push({
                        'case:concept:name': caseId,
                        'concept:name': step.transition,
                        'time:timestamp': currentTime.toISOString()
                    });
                } else {
                    // Lifecycle format with start/complete
                    eventLog.push({
                        'case:concept:name': caseId,
                        'concept:name': step.transition,
                        'time:timestamp': currentTime.toISOString(),
                        'lifecycle:transition': 'start'
                    });
                    
                    currentTime = new Date(currentTime.getTime() + avgDuration);
                    
                    eventLog.push({
                        'case:concept:name': caseId,
                        'concept:name': step.transition,
                        'time:timestamp': currentTime.toISOString(),
                        'lifecycle:transition': 'complete'
                    });
                }
                
                currentTime = new Date(currentTime.getTime() + avgDuration);
            }
        }
        
        return eventLog;
    }
}

/**
 * WebPPL-based Constraint Solver
 * 
 * [Section 5.2] Implements the sample() + condition() pattern from the paper
 * "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024).
 * 
 * "Let V'(post(t)) = {u1,...,uk} be the variables that are potentially
 * modified by firing t. Then we have for each i ∈ {1,...,k}:
 *   ui := SV(ui)
 * followed by:
 *   condition(post(t))"
 * 
 * This ensures that sampled values satisfy the postcondition constraints.
 */
class WebPPLConstraintSolver {
    constructor(options = {}) {
        this.maxRetries = options.maxRetries ?? 100;
        this.defaultBounds = options.defaultBounds ?? { min: 0, max: 1000 };
        this._webppl = null;
    }

    /**
     * Get the WebPPL module (lazy load).
     * @returns {Promise<Object>} WebPPL module
     */
    async getWebPPL() {
        if (this._webppl) {
            return this._webppl;
        }
        
        try {
            const webppl = await import('webppl');
            this._webppl = webppl.default || webppl;
            return this._webppl;
        } catch (error) {
            console.warn('[WebPPL Solver] WebPPL not available:', error.message);
            return null;
        }
    }

    /**
     * [Section 5.2] Solve a constraint expression using WebPPL sample+observe
     * 
     * Generates a mini WebPPL program that:
     * 1. Samples values from uniform distributions (SV scheduler)
     * 2. Observes the postcondition constraint
     * 3. Returns the sampled values
     * 
     * @param {string} constraintExpression - The constraint expression (e.g., "x' > x && x' <= 100")
     * @param {Object} currentValues - Current variable values (α)
     * @param {Object} options - Solver options
     * @param {string} options.mode - 'int' | 'float' | 'auto' (default: 'auto')
     * @returns {Promise<{success: boolean, newValues: Object}>}
     */
    async solveConstraint(constraintExpression, currentValues, options = {}) {
        const mode = options.mode ?? 'auto';
        
        console.log('[WebPPL Solver] Solving constraint:', constraintExpression);
        console.log('[WebPPL Solver] Current values:', currentValues);

        // Parse the constraint to identify primed variables
        const primedVars = this.extractPrimedVariables(constraintExpression);
        
        if (primedVars.length === 0) {
            console.warn('[WebPPL Solver] No primed variables found in constraint');
            return { success: false, newValues: {} };
        }

        // Infer bounds from the constraint expression
        const varBounds = this.inferBoundsFromConstraint(constraintExpression, currentValues, primedVars);

        // Try WebPPL first
        const webppl = await this.getWebPPL();
        if (webppl) {
            try {
                const result = await this.solveWithWebPPL(
                    webppl, 
                    constraintExpression, 
                    currentValues, 
                    primedVars, 
                    varBounds,
                    mode
                );
                if (result.success) {
                    return result;
                }
            } catch (error) {
                console.warn('[WebPPL Solver] WebPPL execution failed:', error.message);
            }
        }

        // Fallback to rejection sampling in JavaScript
        console.log('[WebPPL Solver] Falling back to native rejection sampling');
        return this.solveWithRejectionSampling(constraintExpression, currentValues, primedVars, varBounds, mode);
    }

    /**
     * Extract primed variable names from constraint expression.
     * @private
     */
    extractPrimedVariables(expression) {
        const regex = /([a-zA-Z_][a-zA-Z0-9_]*)'/g;
        const matches = new Set();
        let match;
        while ((match = regex.exec(expression)) !== null) {
            matches.add(match[1]);
        }
        return Array.from(matches);
    }

    /**
     * Infer reasonable bounds for primed variables from the constraint.
     * 
     * [Section 5.2] "The distribution SV(v) is typically uniform over a 
     * reasonable domain inferred from the constraint."
     * 
     * @private
     */
    inferBoundsFromConstraint(expression, currentValues, primedVars) {
        const bounds = {};
        
        for (const varName of primedVars) {
            const currentVal = currentValues[varName];
            let min = this.defaultBounds.min;
            let max = this.defaultBounds.max;
            
            // Parse constraint patterns to infer tighter bounds
            // Pattern: x' > value or x' >= value
            const lowerPatterns = [
                new RegExp(`${varName}'\\s*>\\s*([\\d.]+|${varName})`),
                new RegExp(`${varName}'\\s*>=\\s*([\\d.]+|${varName})`),
                new RegExp(`([\\d.]+|${varName})\\s*<\\s*${varName}'`),
                new RegExp(`([\\d.]+|${varName})\\s*<=\\s*${varName}'`)
            ];
            
            for (const pattern of lowerPatterns) {
                const match = expression.match(pattern);
                if (match) {
                    const bound = match[1] === varName ? currentVal : parseFloat(match[1]);
                    if (!isNaN(bound)) {
                        min = Math.max(min, bound);
                    }
                }
            }
            
            // Pattern: x' < value or x' <= value
            const upperPatterns = [
                new RegExp(`${varName}'\\s*<\\s*([\\d.]+)`),
                new RegExp(`${varName}'\\s*<=\\s*([\\d.]+)`),
                new RegExp(`([\\d.]+)\\s*>\\s*${varName}'`),
                new RegExp(`([\\d.]+)\\s*>=\\s*${varName}'`)
            ];
            
            for (const pattern of upperPatterns) {
                const match = expression.match(pattern);
                if (match) {
                    const bound = parseFloat(match[1]);
                    if (!isNaN(bound)) {
                        max = Math.min(max, bound);
                    }
                }
            }
            
            // If current value is known, use it to inform bounds
            if (typeof currentVal === 'number' && !isNaN(currentVal)) {
                // Check if constraint references current value (e.g., x' > x)
                if (expression.includes(`${varName}' > ${varName}`) || 
                    expression.includes(`${varName}' >= ${varName}`)) {
                    min = Math.max(min, currentVal);
                }
                if (expression.includes(`${varName}' < ${varName}`) || 
                    expression.includes(`${varName}' <= ${varName}`)) {
                    max = Math.min(max, currentVal);
                }
            }
            
            // Ensure valid bounds
            if (min >= max) {
                // Expand bounds if they're invalid
                const center = (min + max) / 2;
                min = center - 100;
                max = center + 100;
            }
            
            bounds[varName] = { min, max };
        }
        
        return bounds;
    }

    /**
     * [Section 5.2] Generate and execute WebPPL code for constraint solving.
     * 
     * Implements the Cfire pattern:
     *   ui := sample(uniform(min, max))  // SV scheduler
     *   observe(post(t))                 // condition on postcondition
     * 
     * @private
     */
    async solveWithWebPPL(webppl, constraintExpression, currentValues, primedVars, varBounds, mode) {
        // Generate WebPPL code
        const code = this.generateWebPPLSolverCode(constraintExpression, currentValues, primedVars, varBounds, mode);
        
        console.log('[WebPPL Solver] Generated code:\n', code);
        
        return new Promise((resolve, reject) => {
            try {
                webppl.run(code, (err, result) => {
                    if (err) {
                        console.error('[WebPPL Solver] Execution error:', err);
                        resolve({ success: false, newValues: {} });
                        return;
                    }
                    
                    console.log('[WebPPL Solver] Result:', result);
                    
                    if (result && typeof result === 'object') {
                        // Convert result to newValues format
                        const newValues = {};
                        for (const varName of primedVars) {
                            if (result[varName] !== undefined) {
                                newValues[varName] = mode === 'int' 
                                    ? Math.floor(result[varName]) 
                                    : result[varName];
                            }
                        }
                        resolve({ success: true, newValues });
                    } else {
                        resolve({ success: false, newValues: {} });
                    }
                });
            } catch (error) {
                reject(error);
            }
        });
    }

    /**
     * Generate WebPPL code for constraint solving.
     * 
     * [Section 5.2] Following the paper's sample+observe pattern.
     * 
     * @private
     */
    generateWebPPLSolverCode(constraintExpression, currentValues, primedVars, varBounds, mode) {
        // Build current values as WebPPL variables
        const currentValLines = Object.entries(currentValues)
            .map(([name, value]) => {
                if (typeof value === 'string') {
                    return `var ${name} = "${value}";`;
                } else if (typeof value === 'boolean') {
                    return `var ${name} = ${value};`;
                } else {
                    return `var ${name} = ${value};`;
                }
            })
            .join('\n');
        
        // Build sampling statements for primed variables
        const samplingLines = primedVars.map(varName => {
            const bounds = varBounds[varName];
            // Use uniform distribution as SV scheduler
            return `var ${varName}_prime = sample(Uniform({a: ${bounds.min}, b: ${bounds.max}}));`;
        }).join('\n');
        
        // Translate constraint expression
        // Replace x' with x_prime for WebPPL
        let translatedConstraint = constraintExpression;
        for (const varName of primedVars) {
            const regex = new RegExp(`${varName}'`, 'g');
            translatedConstraint = translatedConstraint.replace(regex, `${varName}_prime`);
        }
        
        // Handle logical operators
        translatedConstraint = translatedConstraint
            .replace(/&&/g, ' && ')
            .replace(/\|\|/g, ' || ');
        
        // Build result object
        const resultObj = primedVars.map(varName => `"${varName}": ${varName}_prime`).join(', ');
        
        const code = `
// [Section 5.2] WebPPL Constraint Solver
// Current valuation α
${currentValLines}

// [Definition 3] SV scheduler: sample from uniform distribution
var solveFn = function() {
    ${samplingLines}
    
    // [Section 5.2] observe post(t) - condition on postcondition
    condition(${translatedConstraint});
    
    return {${resultObj}};
};

// Use rejection sampling (enumerate for small domains)
Infer({method: 'rejection', samples: 1}, solveFn)
`;
        
        return code;
    }

    /**
     * Fallback: Native JavaScript rejection sampling.
     * 
     * [Section 5.2] Implements the same sample+observe pattern without WebPPL.
     * 
     * @private
     */
    solveWithRejectionSampling(constraintExpression, currentValues, primedVars, varBounds, mode) {
        console.log('[WebPPL Solver] Native rejection sampling for:', constraintExpression);
        
        for (let attempt = 0; attempt < this.maxRetries; attempt++) {
            // Sample values for primed variables (SV scheduler)
            const sampledValues = {};
            for (const varName of primedVars) {
                const bounds = varBounds[varName];
                const range = bounds.max - bounds.min;
                let value = bounds.min + Math.random() * range;
                
                if (mode === 'int' || (mode === 'auto' && Number.isInteger(currentValues[varName]))) {
                    value = Math.floor(value);
                }
                
                sampledValues[varName] = value;
            }
            
            // Check if sampled values satisfy constraint (observe)
            if (this.checkConstraint(constraintExpression, currentValues, sampledValues)) {
                console.log('[WebPPL Solver] Found satisfying values after', attempt + 1, 'attempts:', sampledValues);
                return { success: true, newValues: sampledValues };
            }
        }
        
        console.warn('[WebPPL Solver] Failed to find satisfying values after', this.maxRetries, 'attempts');
        return { success: false, newValues: {} };
    }

    /**
     * Check if sampled values satisfy the constraint.
     * @private
     */
    checkConstraint(constraintExpression, currentValues, sampledValues) {
        try {
            // Build evaluation context
            let evalExpr = constraintExpression;
            
            // Replace primed variables with sampled values
            for (const [varName, value] of Object.entries(sampledValues)) {
                const regex = new RegExp(`${varName}'`, 'g');
                evalExpr = evalExpr.replace(regex, value.toString());
            }
            
            // Replace unprimed variables with current values
            for (const [varName, value] of Object.entries(currentValues)) {
                const regex = new RegExp(`\\b${varName}\\b(?!')`, 'g');
                if (typeof value === 'string') {
                    evalExpr = evalExpr.replace(regex, `"${value}"`);
                } else {
                    evalExpr = evalExpr.replace(regex, value.toString());
                }
            }
            
            // Evaluate
            const result = eval(evalExpr);
            return Boolean(result);
        } catch (error) {
            console.error('[WebPPL Solver] Constraint evaluation error:', error);
            return false;
        }
    }
}

// Global instance for use by dpn-model.js
let _globalConstraintSolver = null;

/**
 * Get the global WebPPL constraint solver instance.
 * @returns {WebPPLConstraintSolver}
 */
function getConstraintSolver() {
    if (!_globalConstraintSolver) {
        _globalConstraintSolver = new WebPPLConstraintSolver();
    }
    return _globalConstraintSolver;
}

/**
 * [Section 5.2] Solve constraint expression using WebPPL-based probabilistic approach.
 * 
 * Implements the paper's sample() + condition() pattern for constraint solving.
 * 
 * @param {string} constraintExpression - The constraint expression
 * @param {Object} currentValues - Current variable values
 * @param {string} mode - 'int' | 'float' | 'auto'
 * @returns {Promise<{success: boolean, newValues: Object}>}
 */
async function solveExpressionWithWebPPL(constraintExpression, currentValues, mode = 'auto') {
    const solver = getConstraintSolver();
    return solver.solveConstraint(constraintExpression, currentValues, { mode });
}

// Export for use in other modules
export { 
    ProbabilisticExecutionEngine, 
    createSeededRandom, 
    uniformDraw, 
    weightedDraw,
    WebPPLConstraintSolver,
    getConstraintSolver,
    solveExpressionWithWebPPL
};
