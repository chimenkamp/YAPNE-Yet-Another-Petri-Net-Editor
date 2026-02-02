/**
 * WebPPL Code Generator for Data Petri Nets
 * 
 * Implements the formal translation of DPNs to Probabilistic Programming Language (PPL)
 * as defined in "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
 * https://doi.org/10.1007/978-3-031-70396-6_2
 * 
 * Paper Reference - Key Sections:
 * - Section 3: Data Petri Nets with Probabilistic Schedulers (Definition 1-6)
 * - Section 4: The Probabilistic Programming Language PPL (Figure 2-4)
 * - Section 5: From DPNs to PPL Programs (Figure 5, Csim construction)
 * - Section 5.1: Setup and Conventions
 * - Section 5.2: Simulating Net Runs in PPL
 * - Section 5.3: Correctness (Theorem 1)
 * 
 * Translation Structure (Figure 5):
 *   Csim: Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
 * 
 * Where:
 * - Cinit: Initializes the marking M and valuation α (Section 5.2)
 * - Benabled(t): Guard checking if transition t is enabled (Definition 2)
 * - Cfire(t): Fires transition t, samples variables, observes postcondition (Section 5.2)
 * - isGoal: Boolean formula for goal states G (Section 5.1)
 */

/**
 * WebPPLCodeGenerator
 * 
 * Generates executable WebPPL code from a Data Petri Net model.
 * The generated code faithfully implements the DPN semantics and scheduler.
 */
class WebPPLCodeGenerator {
    /**
     * Creates a new WebPPLCodeGenerator.
     * 
     * @param {Object} options - Configuration options
     * @param {string} options.schedulerType - 'uniform' | 'weighted' (default: 'uniform')
     * @param {Object} options.transitionWeights - Weights for weighted scheduler
     * @param {Object} options.variableDistributions - Distributions for SV scheduler
     * @param {number} options.maxSteps - Maximum simulation steps (default: 10000)
     */
    constructor(options = {}) {
        this.schedulerType = options.schedulerType ?? 'uniform';
        this.transitionWeights = options.transitionWeights ?? {};
        this.variableDistributions = options.variableDistributions ?? {};
        this.maxSteps = options.maxSteps ?? 10000;
    }

    /**
     * Generate WebPPL code from a Petri Net or Data Petri Net.
     * 
     * [Section 5] The PPL program Csim simulates the runs by probabilistically
     * selecting and firing enabled transitions in a loop until a goal state
     * in G has been reached.
     * 
     * @param {PetriNet|DataPetriNet|Object} net - The Petri net (live instance or JSON)
     * @param {Object} options - Generation options
     * @param {boolean} options.includeComments - Include paper reference comments (default: true)
     * @param {string} options.mode - 'simulation' | 'inference' (default: 'simulation')
     * @returns {string} Generated WebPPL code
     */
    generateCode(net, options = {}) {
        const includeComments = options.includeComments ?? true;
        const mode = options.mode ?? 'simulation';
        
        // Normalize the net to a standard JSON structure
        const dpn = this.normalizeNet(net);
        
        // Validate goal state definition
        this.validateGoalState(dpn);
        
        // Build code sections
        const sections = [
            this.generateHeader(dpn, includeComments),
            this.generateInitialization(dpn, includeComments),
            this.generateGoalStateCheck(dpn, includeComments),
            this.generateEnablingFunctions(dpn, includeComments),
            this.generateFiringFunctions(dpn, includeComments),
            this.generateScheduler(dpn, includeComments),
            this.generateMainLoop(dpn, includeComments, mode)
        ];
        
        return sections.join('\n\n');
    }

    /**
     * Normalize a Petri net (live instance or JSON) to a standard structure.
     * 
     * [Definition 1] DPN = (P, T, F, l, A, V, Δ, pre, post)
     * 
     * @param {PetriNet|DataPetriNet|Object} net - Input net
     * @returns {Object} Normalized DPN structure
     */
    normalizeNet(net) {
        // Handle Map-based live instances
        if (net.places instanceof Map) {
            return this.normalizeFromMaps(net);
        }
        
        // Handle JSON-like objects with arrays
        if (Array.isArray(net.places)) {
            return this.normalizeFromJSON(net);
        }
        
        throw new Error('Unable to normalize net: unknown format');
    }

    /**
     * Normalize from Map-based live Petri Net instance.
     * @private
     */
    normalizeFromMaps(net) {
        const dpn = {
            name: net.name || 'DPN',
            places: [],
            transitions: [],
            arcs: [],
            dataVariables: []
        };
        
        // Convert places
        for (const [id, place] of net.places) {
            dpn.places.push({
                id: id,
                label: place.label || id,
                tokens: place.tokens ?? 0,
                finalMarking: place.finalMarking ?? 0
            });
        }
        
        // Convert transitions
        for (const [id, transition] of net.transitions) {
            dpn.transitions.push({
                id: id,
                label: transition.label || id,
                precondition: transition.precondition ?? '',
                postcondition: transition.postcondition ?? '',
                silent: transition.silent ?? false
            });
        }
        
        // Convert arcs
        for (const [id, arc] of net.arcs) {
            dpn.arcs.push({
                id: id,
                source: arc.source,
                target: arc.target,
                weight: arc.weight ?? 1,
                type: arc.type ?? 'regular'
            });
        }
        
        // Convert data variables
        if (net.dataVariables instanceof Map) {
            for (const [id, variable] of net.dataVariables) {
                dpn.dataVariables.push({
                    id: id,
                    name: variable.name || id,
                    type: variable.type || 'int',
                    currentValue: variable.currentValue ?? 0
                });
            }
        }
        
        return dpn;
    }

    /**
     * Normalize from JSON structure.
     * @private
     */
    normalizeFromJSON(net) {
        return {
            name: net.name || 'DPN',
            places: (net.places || []).map(p => ({
                id: p.id,
                label: p.label || p.id,
                tokens: p.tokens ?? 0,
                finalMarking: p.finalMarking ?? 0
            })),
            transitions: (net.transitions || []).map(t => ({
                id: t.id,
                label: t.label || t.id,
                precondition: t.precondition ?? '',
                postcondition: t.postcondition ?? '',
                silent: t.silent ?? false
            })),
            arcs: (net.arcs || []).map(a => ({
                id: a.id,
                source: a.source,
                target: a.target,
                weight: a.weight ?? 1,
                type: a.type ?? 'regular'
            })),
            dataVariables: (net.dataVariables || []).map(v => ({
                id: v.id,
                name: v.name || v.id,
                type: v.type || 'int',
                currentValue: v.currentValue ?? 0
            }))
        };
    }

    /**
     * Validate that the DPN has a defined goal state.
     * 
     * [Section 5.1] Goal states G must be specified via the 'finalMarking' attribute.
     * Without a defined goal, the simulation cannot determine when to terminate.
     * 
     * @param {Object} dpn - Normalized DPN
     * @throws {Error} If no finalMarking is defined
     */
    validateGoalState(dpn) {
        const hasGoal = dpn.places.some(p => p.finalMarking > 0);
        
        if (!hasGoal) {
            throw new Error(
                `No finalMarking defined in the DPN.\n` +
                `[Section 5.1] Goal states G must be specified via the 'finalMarking' attribute on places.\n` +
                `Please add 'finalMarking: 1' (or appropriate value) to the place(s) that represent the final state.`
            );
        }
    }

    /**
     * Generate header with metadata and imports.
     * @private
     */
    generateHeader(dpn, includeComments) {
        let header = '';
        
        if (includeComments) {
            header += `/**
 * WebPPL Program generated from DPN: ${dpn.name}
 * Following "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
 * 
 * [Definition 1] DPN = (P, T, F, l, A, V, Δ, pre, post)
 * - |P| = ${dpn.places.length} places
 * - |T| = ${dpn.transitions.length} transitions  
 * - |V| = ${dpn.dataVariables.length} data variables
 * 
 * Scheduler: ${this.schedulerType}
 * Max Steps: ${this.maxSteps}
 */\n`;
        }
        
        return header;
    }

    /**
     * Generate initialization code (Cinit).
     * 
     * [Section 5.2] Cinit initializes the net state:
     * - For every place p ∈ P, M(p) = initial tokens
     * - For every variable v ∈ V, α(v) = initial value
     * 
     * @private
     */
    generateInitialization(dpn, includeComments) {
        // Build initial marking M0
        const initialMarking = {};
        dpn.places.forEach(p => { initialMarking[p.id] = p.tokens; });
        
        // Build initial valuation α0
        const initialValuation = {};
        dpn.dataVariables.forEach(v => { initialValuation[v.name] = v.currentValue; });
        
        // Build final marking specification for goal state
        const finalMarkingSpec = {};
        dpn.places.forEach(p => {
            if (p.finalMarking > 0) {
                finalMarkingSpec[p.id] = p.finalMarking;
            }
        });
        
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Section 5.2] Cinit - Initialize the net state
 * 
 * Sets up the initial marking M0 and initial valuation α0.
 * [Definition 1] A net state is a pair (M, α) where:
 * - M: P → N is the marking (token distribution)
 * - α: V → Δ is the valuation (variable assignment)
 */\n`;
        }
        
        code += `var initialState = {
    marking: ${JSON.stringify(initialMarking, null, 4).replace(/\n/g, '\n    ')},
    valuation: ${JSON.stringify(initialValuation, null, 4).replace(/\n/g, '\n    ')}
};

var finalMarkingSpec = ${JSON.stringify(finalMarkingSpec)};

var maxSteps = ${this.maxSteps};`;
        
        return code;
    }

    /**
     * Generate goal state check function.
     * 
     * [Section 5.1] isGoal formula: conjunction of marking conditions
     * "Examples of G include the set of all states where some final marking
     * has been reached or a variable is above some threshold."
     * 
     * @private
     */
    generateGoalStateCheck(dpn, includeComments) {
        const finalPlaces = dpn.places.filter(p => p.finalMarking > 0);
        
        const goalConditions = finalPlaces.map(p => 
            `state.marking['${p.id}'] >= ${p.finalMarking}`
        );
        
        const goalExpr = goalConditions.length > 0 
            ? goalConditions.join(' && ') 
            : 'false';
        
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Section 5.1] isGoal - Check if current state is a goal state
 * 
 * Goal states G are defined by the finalMarking attribute on places.
 * [Definition 6] The probability P_S^N(φ) of satisfying φ is the sum
 * of probabilities of all runs reaching G that satisfy φ.
 */\n`;
        }
        
        code += `var isGoalState = function(state) {
    return ${goalExpr};
};`;
        
        return code;
    }

    /**
     * Generate transition enabling check functions.
     * 
     * [Definition 2] (Transition Enabling):
     * A step (t, β) is enabled in state (M, α) iff:
     * (i) β is defined for all variables in V(pre(t)) ∪ V(post(t))
     * (ii) β matches α on all unprimed variables
     * (iii) For every p ∈ •t: M(p) ≥ l(p,t) (sufficient tokens in preset)
     * (iv) β |= pre(t) ∧ post(t) (guards are satisfied)
     * 
     * Simplified: Benabled(t) = pre(t) ∧ ∧_{p∈•t} M(p) ≥ l(p,t)
     * 
     * @private
     */
    generateEnablingFunctions(dpn, includeComments) {
        const { transitions, arcs, dataVariables, places } = dpn;
        const placeIds = new Set(places.map(p => p.id));
        
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Definition 2] Benabled(t) - Check if transition t is enabled
 * 
 * Simplified form for simulation:
 * Benabled(t) = pre(t) ∧ ∧_{p∈•t} M(p) ≥ l(p,t)
 */\n`;
        }
        
        // Generate enabling check for each transition
        const enableChecks = transitions.map(t => {
            // Get preset •t (places with arcs TO this transition)
            const preset = arcs.filter(a => 
                a.target === t.id && placeIds.has(a.source) && a.type !== 'inhibitor'
            );
            
            // Token availability check: ∧_{p∈•t} M(p) ≥ l(p,t)
            const tokenChecks = preset.map(a => 
                `state.marking['${a.source}'] >= ${a.weight}`
            );
            const tokenCondition = tokenChecks.length > 0 ? tokenChecks.join(' && ') : 'true';
            
            // Precondition guard: pre(t)
            const guardCondition = this.translateExpression(t.precondition, dataVariables, 'state.valuation');
            
            return `    if (transitionId === '${t.id}') {
        var tokenCheck = ${tokenCondition};
        var guardCheck = ${guardCondition};
        return tokenCheck && guardCheck;
    }`;
        });
        
        code += `var isTransitionEnabled = function(state, transitionId) {
${enableChecks.join('\n')}
    return false;
};

var getEnabledTransitions = function(state) {
    var enabled = [];
${transitions.map(t => `    if (isTransitionEnabled(state, '${t.id}')) { enabled.push('${t.id}'); }`).join('\n')}
    return enabled;
};`;
        
        return code;
    }

    /**
     * Generate transition firing functions.
     * 
     * [Section 5.2] Cfire(t) performs:
     * 1. Token removal from preset: ∀p∈•t: M'(p) = M(p) - l(p,t)
     * 2. Token addition to postset: ∀p∈t•: M'(p) = M(p) + l(t,p)
     * 3. Variable sampling: v' := SV(v') for each v ∈ V'(post(t))
     * 4. Postcondition observation: observe post(t)
     * 5. Valuation update: α'(v) = v' for modified variables
     * 
     * @private
     */
    generateFiringFunctions(dpn, includeComments) {
        const { transitions, arcs, dataVariables, places } = dpn;
        const placeIds = places.map(p => p.id);
        const variableNames = dataVariables.map(v => v.name);
        const placeIdSet = new Set(placeIds);
        
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Section 5.2] Cfire(t) - Fire transition t
 * 
 * For transition t with preset •t and postset t•:
 * 1. Remove tokens from preset: ∀p∈•t: M'(p) = M(p) - l(p,t)
 * 2. Add tokens to postset: ∀p∈t•: M'(p) = M(p) + l(t,p)
 * 3. Sample new variable values from scheduler SV: v' := SV(v')
 * 4. Condition on postcondition: condition(post(t))
 * 5. Update valuation: α' with new variable values
 */\n`;
        }
        
        // Generate one fire function per transition
        const fireFunctions = transitions.map(t => {
            // Get preset •t = {p | (p,t) ∈ F} and postset t• = {p | (t,p) ∈ F}
            const preset = arcs.filter(a => a.target === t.id && placeIdSet.has(a.source));
            const postset = arcs.filter(a => a.source === t.id && placeIdSet.has(a.target));
            
            // Build new marking with token updates
            const markingEntries = placeIds.map(pid => {
                let delta = 0;
                const presetArc = preset.find(a => a.source === pid);
                if (presetArc && presetArc.type !== 'inhibitor' && presetArc.type !== 'read') {
                    delta -= presetArc.weight;
                }
                const postsetArc = postset.find(a => a.target === pid);
                if (postsetArc) {
                    delta += postsetArc.weight;
                }
                const op = delta >= 0 ? '+' : '';
                return `        '${pid}': state.marking['${pid}'] ${op} ${delta}`;
            });
            
            // Parse postcondition for variable updates
            const updates = this.parsePostconditionUpdates(t.postcondition, dataVariables);
            const updateMap = {};
            updates.forEach(u => { updateMap[u.variable] = u; });
            
            // Generate valuation entries
            let valuationCode;
            if (variableNames.length > 0) {
                const valuationEntries = variableNames.map(vn => {
                    const update = updateMap[vn];
                    if (update) {
                        if (update.isConstraint) {
                            // For constraints, sample from distribution and condition
                            return `        '${vn}': ${vn}_prime`;
                        } else {
                            // Deterministic assignment
                            return `        '${vn}': ${update.expression}`;
                        }
                    }
                    return `        '${vn}': state.valuation['${vn}']`;
                });
                valuationCode = `{\n${valuationEntries.join(',\n')}\n    }`;
            } else {
                valuationCode = '{}';
            }
            
            // Build sampling and condition statements for constraints
            // [Section 5.2] Following the paper's sample + condition pattern
            const constraintUpdates = updates.filter(u => u.isConstraint);
            let samplingCode = '';
            let conditionCode = '';
            
            if (constraintUpdates.length > 0) {
                // Generate var declarations with _prime suffix (aligned with internal execution)
                const samplingStatements = constraintUpdates.map(u => {
                    const distName = this.variableDistributions[u.variable] || 'uniform(0, 1000)';
                    return `    var ${u.variable}_prime = sample(${distName});`;
                });
                samplingCode = `\n${samplingStatements.join('\n')}\n`;
                
                // Generate condition statement for postcondition constraints
                const constraintExpr = this.translatePostconditionConstraint(t.postcondition, dataVariables, constraintUpdates);
                if (constraintExpr !== 'true') {
                    conditionCode = `\n    condition(${constraintExpr});\n`;
                }
            }
            
            const funcName = this.sanitizeId(t.id);
            
            return `var fire_${funcName} = function(state) {${samplingCode}${conditionCode}
    return {
        marking: {
${markingEntries.join(',\n')}
        },
        valuation: ${valuationCode}
    };
};`;
        });
        
        code += fireFunctions.join('\n\n');
        
        // Generate dispatcher function
        const dispatchCases = transitions.map(t => 
            `    if (transitionId === '${t.id}') { return fire_${this.sanitizeId(t.id)}(state); }`
        );
        
        code += `

var fireTransition = function(state, transitionId) {
${dispatchCases.join('\n')}
    return state;
};`;
        
        return code;
    }

    /**
     * Generate scheduler functions.
     * 
     * [Definition 3] DPN Scheduler S: SN → Dist(TN) × (VN → Dist(ΔN))
     * 
     * A scheduler S resolves nondeterminism by providing:
     * - ST: Distribution over enabled transitions
     * - SV: Distribution over variable updates for each variable
     * 
     * @private
     */
    generateScheduler(dpn, includeComments) {
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Definition 3] DPN Scheduler S
 * 
 * - ST: Distribution over enabled transitions
 * - SV: Distribution over variable updates
 * 
 * [Example 1] Uniform scheduler: ST = unif(1, |frontier(M,α)|)
 */\n`;
        }
        
        if (this.schedulerType === 'weighted' && Object.keys(this.transitionWeights).length > 0) {
            const weights = JSON.stringify(this.transitionWeights);
            code += `var transitionWeights = ${weights};

var selectTransition = function(enabledTransitions) {
    if (enabledTransitions.length === 0) return null;
    var weights = map(function(t) { return transitionWeights[t] || 1; }, enabledTransitions);
    var idx = discrete(weights);
    return enabledTransitions[idx];
};`;
        } else {
            code += `var selectTransition = function(enabledTransitions) {
    if (enabledTransitions.length === 0) return null;
    return uniformDraw(enabledTransitions);
};`;
        }
        
        return code;
    }

    /**
     * Generate main simulation loop.
     * 
     * [Figure 5] Main simulation loop - Cloop:
     *   do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
     * 
     * [Theorem 1] (Correctness):
     * "For every initial net state (M,α), executing the main loop of Csim
     * on s(M,α) produces the same distribution over runs as the encoded net N
     * under scheduler S."
     * 
     * @private
     */
    generateMainLoop(dpn, includeComments, mode) {
        let code = '';
        
        if (includeComments) {
            code += `/**
 * [Figure 5] Main simulation loop - Cloop
 * 
 * Structure: do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... ) od
 * 
 * [Theorem 1] (Correctness): Produces same distribution as DPN under scheduler S.
 */\n`;
        }
        
        code += `var simulationStep = function(state, trace, stepCount) {
    if (isGoalState(state)) {
        return { state: state, trace: trace, status: 'goal', steps: stepCount };
    }
    
    if (stepCount >= maxSteps) {
        return { state: state, trace: trace, status: 'max_steps', steps: stepCount };
    }
    
    var enabledTransitions = getEnabledTransitions(state);
    
    if (enabledTransitions.length === 0) {
        return { state: state, trace: trace, status: 'deadlock', steps: stepCount };
    }
    
    var chosenTransition = selectTransition(enabledTransitions);
    var newState = fireTransition(state, chosenTransition);
    var newTrace = trace.concat([chosenTransition]);
    
    return simulationStep(newState, newTrace, stepCount + 1);
};

var simulateDPN = function() {
    return simulationStep(initialState, [], 0);
};

simulateDPN()`;
        
        return code;
    }

    /**
     * Translate a DPN expression to WebPPL, replacing variable references.
     * 
     * [Section 5.1] "we denote by pre(t) the expression pre(t) in which
     * every variable v ∈ V has been replaced by v (underlined)"
     * 
     * @private
     */
    translateExpression(expr, dataVariables, statePrefix) {
        if (!expr || expr.trim() === '' || expr.trim() === ';') {
            return 'true';
        }
        
        let translated = expr.replace(/;/g, '').trim();
        
        // Replace logical operators
        translated = translated.replace(/&&/g, ' && ').replace(/\|\|/g, ' || ');
        
        // Sort variables by length descending to avoid partial replacements
        const sortedVars = [...dataVariables].sort((a, b) => b.name.length - a.name.length);
        
        sortedVars.forEach(v => {
            // Match variable name NOT followed by prime (')
            const regex = new RegExp(`\\b${v.name}\\b(?!')`, 'g');
            translated = translated.replace(regex, `${statePrefix}['${v.name}']`);
        });
        
        return translated || 'true';
    }

    /**
     * Translate postcondition constraint to WebPPL condition expression.
     * 
     * [Section 5.2] Uses the _prime naming convention aligned with internal execution.
     * Primed variables x' become x_prime, unprimed variables become state.valuation['x'].
     * 
     * @private
     */
    translatePostconditionConstraint(postcondition, dataVariables, constraintUpdates) {
        if (!postcondition || constraintUpdates.length === 0) {
            return 'true';
        }
        
        let translated = postcondition;
        
        // First: Replace primed variables with _prime suffix
        // This must happen before unprimed replacement to avoid nested substitution
        constraintUpdates.forEach(u => {
            const primedRegex = new RegExp(`\\b${u.variable}'`, 'g');
            translated = translated.replace(primedRegex, `${u.variable}_prime`);
        });
        
        // Second: Replace unprimed variables with state.valuation lookups
        // Sort by length descending to avoid partial replacements (e.g., 'x' matching in 'xy')
        const sortedVars = [...dataVariables].sort((a, b) => b.name.length - a.name.length);
        sortedVars.forEach(v => {
            // Match variable name NOT followed by prime (') and NOT already _prime
            const regex = new RegExp(`\\b${v.name}\\b(?!['_])`, 'g');
            translated = translated.replace(regex, `state.valuation['${v.name}']`);
        });
        
        // Remove assignment statements (keep only constraints)
        const parts = translated.split(/[;&]/);
        const constraints = parts
            .map(p => p.trim())
            .filter(p => p && !p.includes(':=') && !p.match(/^[a-zA-Z_][a-zA-Z0-9_]*_prime\s*=\s*/));
        
        return constraints.length > 0 ? constraints.join(' && ') : 'true';
    }

    /**
     * Parse postcondition into variable updates.
     * 
     * [Section 5.2] "Let V'(post(t)) = {u1,...,uk} be the variables that are
     * potentially modified by firing t"
     * 
     * Format: "v' = expr" where v' denotes the new value of variable v
     * 
     * @private
     */
    parsePostconditionUpdates(postcondition, dataVariables) {
        const updates = [];
        if (!postcondition || postcondition.trim() === '') {
            return updates;
        }
        
        const statements = postcondition.split(/[;&]/);
        
        for (const stmt of statements) {
            const trimmed = stmt.trim();
            if (!trimmed) continue;
            
            // Match "variable' = expression" for deterministic updates
            const assignmentMatch = trimmed.match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)$/);
            if (assignmentMatch) {
                const varName = assignmentMatch[1];
                const expression = assignmentMatch[2].trim();
                
                // Check if this is a constraint (contains comparison operators)
                const isConstraint = /[<>=!]/.test(expression) && !/^[^<>=!]+$/.test(expression);
                
                if (isConstraint) {
                    updates.push({
                        variable: varName,
                        expression: expression,
                        isConstraint: true
                    });
                } else {
                    // Translate the deterministic expression
                    const translatedExpr = this.translateExpression(expression, dataVariables, 'state.valuation');
                    updates.push({
                        variable: varName,
                        expression: translatedExpr,
                        isConstraint: false
                    });
                }
            }
            
            // Check for constraint-style postconditions like "x' >= 10 && x' <= 1000"
            const constraintMatch = trimmed.match(/([a-zA-Z_][a-zA-Z0-9_]*)'\s*([<>=!]+)\s*(.+)/);
            if (constraintMatch && !assignmentMatch) {
                const varName = constraintMatch[1];
                // This is a constraint that requires sampling
                const existingUpdate = updates.find(u => u.variable === varName);
                if (!existingUpdate) {
                    updates.push({
                        variable: varName,
                        expression: trimmed,
                        isConstraint: true
                    });
                }
            }
        }
        
        return updates;
    }

    /**
     * Sanitize ID for use as JavaScript function name.
     * @private
     */
    sanitizeId(id) {
        return id.replace(/[^a-zA-Z0-9_]/g, '_');
    }
}

export { WebPPLCodeGenerator };
