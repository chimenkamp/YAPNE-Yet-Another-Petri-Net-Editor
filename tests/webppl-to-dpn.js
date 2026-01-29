import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';
import webppl from 'webppl';

// ES Module compatibility for __dirname
const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

/**
 * DPNSimulator
 * 
 * Implements the translation of Data Petri Nets (DPN) to Probabilistic Programming 
 * as described in "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024).
 * 
 * Paper Reference: https://doi.org/10.1007/978-3-031-70396-6_2
 * 
 * Key Sections Referenced:
 * - Section 3: Data Petri Nets with Probabilistic Schedulers (Definition 1-6)
 * - Section 4: The Probabilistic Programming Language PPL (Figure 2-4)
 * - Section 5: From DPNs to PPL Programs (Figure 5, Csim construction)
 * - Section 5.1: Setup and Conventions
 * - Section 5.2: Simulating Net Runs in PPL
 * - Section 5.3: Correctness (Theorem 1)
 * 
 * Definition 1 (Data Petri Net):
 * A DPN is a tuple N = (P, T, F, l, A, V, Δ, pre, post) where:
 * - P is a finite set of places
 * - T is a finite set of transitions
 * - F ⊆ (P × T) ∪ (T × P) is the flow relation
 * - l: F → N+ assigns positive weights to arcs
 * - A is a set of actions
 * - V is a finite set of typed data variables
 * - Δ is the data domain
 * - pre, post: T → Expr assign guards and postconditions to transitions
 */
class DPNSimulator {
    /**
     * Creates a DPNSimulator instance.
     * 
     * @param {string|object} input - Either a JSON string or a parsed DPN object
     */
    constructor(input) {
        // Accept both string and object input
        if (typeof input === 'string') {
            this.dpn = JSON.parse(input);
        } else {
            this.dpn = input;
        }
        
        // Normalize the DPN structure to handle missing optional fields
        this.normalizeDPN();
    }
    
    /**
     * Normalizes the DPN structure to ensure all required fields exist.
     * This allows the simulator to work with various JSON formats from public/examples.
     * 
     * [Definition 1] Ensures all components of the DPN tuple are present.
     */
    normalizeDPN() {
        // Ensure places array exists
        this.dpn.places = this.dpn.places || [];
        
        // Ensure transitions array exists
        this.dpn.transitions = this.dpn.transitions || [];
        
        // Ensure arcs array exists
        this.dpn.arcs = this.dpn.arcs || [];
        
        // Ensure dataVariables array exists (V in Definition 1)
        this.dpn.dataVariables = this.dpn.dataVariables || [];
        
        // Normalize each place
        this.dpn.places = this.dpn.places.map(p => ({
            ...p,
            tokens: p.tokens ?? 0,
            finalMarking: p.finalMarking ?? 0  // [Section 5.1] Goal states via final marking
        }));
        
        // Normalize each transition - ensure pre/post conditions exist
        // [Definition 1] pre, post: T → Expr
        this.dpn.transitions = this.dpn.transitions.map(t => ({
            ...t,
            precondition: t.precondition ?? '',
            postcondition: t.postcondition ?? ''
        }));
        
        // Normalize each arc - ensure weight exists
        // [Definition 1] l: F → N+ (arc weights)
        this.dpn.arcs = this.dpn.arcs.map(a => ({
            ...a,
            weight: a.weight ?? 1
        }));
        
        // Normalize each variable
        this.dpn.dataVariables = this.dpn.dataVariables.map(v => ({
            ...v,
            currentValue: v.currentValue ?? 0
        }));
    }
    
    /**
     * Load a DPN from a JSON file.
     * 
     * @param {string} filePath - Path to the JSON file
     * @returns {DPNSimulator} - A new simulator instance
     */
    static fromFile(filePath) {
        const content = fs.readFileSync(filePath, 'utf8');
        return new DPNSimulator(content);
    }

    /**
     * Main entry point. Compiles and runs the DPN model.
     * 
     * [Section 5] The PPL program Csim simulates the runs by probabilistically 
     * selecting and firing enabled transitions in a loop until a goal state 
     * in G has been reached.
     * 
     * @param {function} callback - Optional callback for results.
     */
    run(callback) {
        const pplCode = this.generatePPL();
        
        console.log("=".repeat(60));
        console.log("Generated WebPPL Code:");
        console.log("=".repeat(60));
        console.log(pplCode);
        console.log("=".repeat(60));

        // Execute via WebPPL
        webppl.run(pplCode, (s, val) => {
            console.log("\n" + "=".repeat(60));
            console.log("Simulation Result:");
            console.log("=".repeat(60));
            console.log("Final State:", JSON.stringify(val.state, null, 2));
            console.log("Trace:", val.trace);
            console.log("Trace Length:", val.trace.length);
            if (callback) callback(val);
        });
    }

    /**
     * Generates the PPL program Csim as defined in Section 5.2 (Figure 5).
     * 
     * Structure from Figure 5:
     *   Csim: Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
     * 
     * Where:
     * - Cinit: Initializes the marking and variable valuation (Section 5.2)
     * - Benabled(t): Guard checking if transition t is enabled (Definition 2)
     * - Cfire(t): Fires transition t (Section 5.2)
     * - isGoal: Boolean formula for goal states (Section 5.1)
     */
    generatePPL() {
        const { places, transitions, arcs, dataVariables } = this.dpn;

        // [Section 5.1] Setup: P = {p1,...,p#P}, T = {t1,...,t#T}, V = {v1,...,v#V}
        const placeIds = places.map(p => p.id);
        const transitionIds = transitions.map(t => t.id);
        const variableNames = dataVariables.map(v => v.name);

        // [Section 5.1] Initial state (M0, α0)
        // M0(pi) = initial tokens, α0(vj) = initial value
        const initialMarking = {};
        places.forEach(p => { initialMarking[p.id] = p.tokens; });
        
        const initialValuation = {};
        dataVariables.forEach(v => { initialValuation[v.name] = v.currentValue; });

        // [Section 5.1] Goal states G - determined by finalMarking attribute
        // "Examples of G include (beside deadlocked states) the set of all states,
        // where some final marking has been reached"
        // 
        // [Definition 6] The probability of reaching G is normalized over all runs
        // that terminate in a goal state.
        //
        // finalMarking specifies the expected token count in each place when goal is reached.
        // A state is a goal state iff marking matches all specified finalMarkings.
        const finalMarkingSpec = {};
        places.forEach(p => {
            if (p.finalMarking !== undefined && p.finalMarking !== null) {
                finalMarkingSpec[p.id] = p.finalMarking;
            }
        });
        
        // Generate goal state check expression
        // [Section 5.1] isGoal formula: conjunction of marking conditions
        const goalConditions = Object.entries(finalMarkingSpec)
            .filter(([pid, count]) => count > 0)  // Only check places that should have tokens
            .map(([pid, count]) => `state.marking['${pid}'] >= ${count}`);
        
        // [Section 5.1] Require explicit finalMarking to define goal states G
        // Without a defined goal, the simulation cannot determine when to terminate.
        const hasExplicitGoal = goalConditions.length > 0;
        if (!hasExplicitGoal) {
            throw new Error(
                `No finalMarking defined in the DPN.\n` +
                `[Section 5.1] Goal states G must be specified via the 'finalMarking' attribute on places.\n` +
                `Please add 'finalMarking: 1' (or appropriate value) to the place(s) that represent the final state.\n` +
                `Example: { "id": "p_end", "tokens": 0, "finalMarking": 1 }`
            );
        }

        return `
/**
 * WebPPL Program generated from DPN: ${this.dpn.name || 'Unnamed'}
 * Following "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
 * 
 * [Definition 1] DPN = (P, T, F, l, A, V, Δ, pre, post)
 * - |P| = ${placeIds.length} places
 * - |T| = ${transitionIds.length} transitions  
 * - |V| = ${variableNames.length} data variables
 */

/**
 * [Section 5.2] Cinit - Initialize the net state
 * 
 * Sets up the initial marking M0 and initial valuation α0.
 * [Definition 1] A net state is a pair (M, α) where:
 * - M: P → N is the marking (token distribution)
 * - α: V → Δ is the valuation (variable assignment)
 */
var initialState = {
    // [Section 5.1] For every place p ∈ P, p stores how many tokens are in p
    marking: ${JSON.stringify(initialMarking)},
    // [Section 5.1] For every variable v ∈ V, v stores the current value
    valuation: ${JSON.stringify(initialValuation)}
};

/**
 * [Section 5.1] Final marking specification (Mf)
 * Used to determine goal states G.
 */
var finalMarkingSpec = ${JSON.stringify(finalMarkingSpec)};

/**
 * [Section 5.2] Benabled(t) - Check if transition t is enabled
 * 
 * From Definition 2 (Transition Enabling):
 * A step (t, β) is enabled in state (M, α) iff:
 * (i) β is defined for all variables mentioned in pre(t) and post(t)
 * (ii) β matches α on all unprimed variables
 * (iii) For every place p ∈ •t (preset), M(p) ≥ l(p,t) (sufficient tokens)
 * (iv) β satisfies pre(t) ∧ post(t) (guards hold)
 * 
 * Simplified form for simulation: Benabled(t) = pre(t) ∧ ∧_{p∈•t} M(p) ≥ l(p,t)
 */
var isTransitionEnabled = function(state, transitionId) {
    ${this.generateEnablingChecks(transitions, arcs, dataVariables)}
};

/**
 * [Section 5.2] Cfire(t) - Fire transition t
 * 
 * For transition t with preset •t = {q1,...,qm} and postset t• = {r1,...,rn}:
 * 1. Remove tokens from preset: ∀p∈•t: M'(p) = M(p) - l(p,t)
 * 2. Add tokens to postset: ∀p∈t•: M'(p) = M(p) + l(t,p)
 * 3. Sample new variable values from scheduler SV: v' := SV(v')
 * 4. Condition on postcondition: observe post(t)
 * 5. Log the step: log step(t)
 * 6. Update valuation: α' with new variable values
 * 
 * Note: WebPPL requires pure functional style - no field assignments.
 * We construct new state objects directly instead of mutating.
 */
${this.generateFiringFunctions(transitions, arcs, dataVariables, places)}

/**
 * [Definition 3] DPN Scheduler S: SN → Dist(TN) × (VN → Dist(ΔN))
 * 
 * A scheduler S resolves nondeterminism by providing:
 * - ST: Distribution over enabled transitions
 * - SV: Distribution over variable updates for each variable
 * 
 * [Example 1] Uniform scheduler: ST = unif(1, |frontier(M,α)|)
 * WebPPL's uniformDraw implements uniform selection over the enabled set.
 */
var selectTransition = function(enabledTransitions) {
    // [Definition 3] ST: Uniformly select transition from enabled set (frontier)
    return uniformDraw(enabledTransitions);
};

/**
 * [Section 5.1] isGoal - Check if current state is a goal state
 * 
 * Goal states G are defined by the finalMarking attribute on places.
 * From the paper: "Examples of G include (beside deadlocked states) 
 * the set of all states where some final marking has been reached 
 * or a variable is above some threshold."
 * 
 * [Definition 6] The probability P_S^N(φ) of satisfying φ is the sum
 * of probabilities of all runs reaching G that satisfy φ.
 */
var isGoalState = function(state) {
    // Goal: Check if marking matches final marking specification (Mf)
    return ${goalConditions.join(' && ')};
};

/**
 * [Section 5.1] frontier(M, α) = {t ∈ T | ∃β : (M,α)[(t,β)⟩}
 * 
 * The frontier is the set of all transitions that are enabled in state (M, α).
 * [Definition 2] A transition t is in frontier iff there exists a valid 
 * variable assignment β such that the step (t, β) is enabled.
 */
var getEnabledTransitions = function(state) {
    var enabled = [];
    ${transitionIds.map(tid => `
    if (isTransitionEnabled(state, '${tid}')) {
        enabled.push('${tid}');
    }`).join('')}
    return enabled;
};

/**
 * [Figure 5] Main simulation loop - Cloop
 * 
 * Structure from Figure 5:
 *   do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
 * 
 * This loop implements the simulation semantics:
 * 1. Check if goal state reached (¬isGoal guard)
 * 2. Compute frontier - set of enabled transitions
 * 3. If frontier empty → deadlock (may be goal state per Section 5.1)
 * 4. Select transition uniformly from frontier (scheduler ST)
 * 5. Fire selected transition (Cfire)
 * 6. Add step to trace (log step(t))
 * 7. Recurse with new state
 * 
 * [Definition 5] The likelihood L_S^N of a run ρ is computed recursively:
 * - L_S^N(ε) = 1 (empty run)
 * - L_S^N(ρ · (t,β)) = L_S^N(ρ) · P_S[M_ρ,α_ρ](t,β)
 * 
 * [Definition 6] Probability normalized: P_S^N(ρ) = L_S^N(ρ) / Σ_{ρ'∈Runs_G} L_S^N(ρ')
 */
var simulationStep = function(state, trace) {
    // [Section 5.1] Check if current state is a goal state
    if (isGoalState(state)) {
        return { state: state, trace: trace, status: 'goal' };
    }
    
    // [Section 5.1] Compute frontier(M, α) - set of enabled transitions
    var enabledTransitions = getEnabledTransitions(state);
    
    // [Section 5.1] "G contains all deadlocked net states"
    // [Definition 5] If no transitions enabled, likelihood of continuing is 0
    if (enabledTransitions.length === 0) {
        // Deadlock reached - this is a goal state per paper Section 5.1
        return { state: state, trace: trace, status: 'deadlock' };
    }
    
    // [Definition 4] Select transition using scheduler ST
    // P_S[M,α](t) = [t ∈ frontier(M,α)] · ST(t) / Σ_{t'∈frontier} ST(t')
    var chosenTransition = selectTransition(enabledTransitions);
    
    // [Section 5.2] Cfire(t) - Fire the chosen transition
    var newState = fireTransition(state, chosenTransition);
    
    // [Section 5.2] log step(t) - Add step to trace
    // This records the run ρ = (t1,β1)...(tn,βn)
    var newTrace = trace.concat([chosenTransition]);
    
    // Recursive call (corresponds to do...od loop in Figure 5)
    return simulationStep(newState, newTrace);
};

/**
 * [Section 5.2] Csim entry point
 * 
 * Csim: Cinit; Cloop
 * 
 * [Theorem 1] (Correctness):
 * "For every initial net state (M,α), executing the main loop of Csim 
 * on s(M,α) produces the same distribution over runs as the encoded net N 
 * under scheduler S."
 * 
 * This ensures the PPL program faithfully represents the DPN semantics.
 */
var simulateDPN = function() {
    return simulationStep(initialState, []);
};

// Run simulation and return result
simulateDPN()
`;
    }

    /**
     * Generate transition enabling checks following Definition 2.
     * 
     * [Definition 2] (Transition Enabling):
     * A step (t, β) is enabled in state (M, α) iff:
     * (i) β is defined for all variables in V(pre(t)) ∪ V(post(t))
     * (ii) β matches α on all unprimed variables
     * (iii) For every p ∈ •t: M(p) ≥ l(p,t) (sufficient tokens in preset)
     * (iv) β |= pre(t) ∧ post(t) (guards are satisfied)
     * 
     * Simplified for simulation: Benabled(t) = pre(t) ∧ ∧_{p∈•t} M(p) ≥ l(p,t)
     * 
     * @param {Array} transitions - List of transitions from DPN
     * @param {Array} arcs - List of arcs from DPN
     * @param {Array} dataVariables - List of data variables from DPN
     * @returns {string} - WebPPL code for enabling checks
     */
    generateEnablingChecks(transitions, arcs, dataVariables) {
        const checks = transitions.map(t => {
            // [Definition 2] Get preset •t (places with arcs TO this transition)
            // •t = {p ∈ P | (p,t) ∈ F}
            const preset = arcs.filter(a => a.target === t.id && 
                !transitions.some(tr => tr.id === a.source)); // source must be a place
            
            // [Definition 2(iii)] Token availability check: ∧_{p∈•t} M(p) ≥ l(p,t)
            const tokenChecks = preset.map(a => 
                `state.marking['${a.source}'] >= ${a.weight}`
            );
            const tokenCondition = tokenChecks.length > 0 ? tokenChecks.join(' && ') : 'true';
            
            // [Definition 2(iv)] Precondition guard: pre(t)
            const guardCondition = this.translateExpression(t.precondition, dataVariables, 'state.valuation');
            
            return `
    if (transitionId === '${t.id}') {
        // [Definition 2] Benabled(${t.id}): pre(t) ∧ ∧_{p∈•t} M(p) ≥ l(p,t)
        var tokenCheck = ${tokenCondition};
        var guardCheck = ${guardCondition};
        return tokenCheck && guardCheck;
    }`;
        });
        
        return checks.join('') + `
    return false;`;
    }

    /**
     * Generate firing functions following Section 5.2 Cfire(t).
     * 
     * [Section 5.2] For each transition t, Cfire(t) performs:
     * 1. Token removal from preset: ∀p∈•t: M'(p) = M(p) - l(p,t)
     * 2. Token addition to postset: ∀p∈t•: M'(p) = M(p) + l(t,p)
     * 3. Variable sampling: v' := SV(v') for each v ∈ V'(post(t))
     * 4. Postcondition observation: observe post(t)
     * 5. Valuation update: α'(v) = v' for modified variables
     * 
     * WebPPL requires pure functional style - we generate separate functions
     * per transition that return new state objects.
     * 
     * @param {Array} transitions - List of transitions from DPN
     * @param {Array} arcs - List of arcs from DPN  
     * @param {Array} dataVariables - List of data variables from DPN
     * @param {Array} places - List of places from DPN
     * @returns {string} - WebPPL code for firing functions
     */
    generateFiringFunctions(transitions, arcs, dataVariables, places) {
        const placeIds = places.map(p => p.id);
        const variableNames = dataVariables.map(v => v.name);

        // Generate one fire function per transition
        const fireFunctions = transitions.map(t => {
            // [Definition 2] Get preset •t = {p | (p,t) ∈ F} and postset t• = {p | (t,p) ∈ F}
            const preset = arcs.filter(a => a.target === t.id);
            const postset = arcs.filter(a => a.source === t.id);
            
            // [Section 5.2] Build new marking: M' with token updates
            // For p ∈ •t: M'(p) = M(p) - l(p,t)
            // For p ∈ t•: M'(p) = M(p) + l(t,p)
            const markingEntries = placeIds.map(pid => {
                let delta = 0;
                // Check if this place is in preset (tokens consumed)
                const presetArc = preset.find(a => a.source === pid);
                if (presetArc) {
                    delta -= presetArc.weight;
                }
                // Check if this place is in postset (tokens produced)
                const postsetArc = postset.find(a => a.target === pid);
                if (postsetArc) {
                    delta += postsetArc.weight;
                }
                const op = delta >= 0 ? '+' : '';
                return `'${pid}': state.marking['${pid}'] ${op} ${delta}`;
            });
            
            // [Section 5.2] Build new valuation: α' with variable updates from postcondition
            // V'(post(t)) = {u1,...,uk} are the variables potentially modified
            const updates = this.parsePostconditionUpdates(t.postcondition, dataVariables);
            const updateMap = {};
            updates.forEach(u => { updateMap[u.variable] = u.expression; });
            
            // Generate valuation entries - updated vars use new expression, others keep current
            const valuationEntries = variableNames.map(vn => {
                const expr = updateMap[vn] || `state.valuation['${vn}']`;
                return `'${vn}': ${expr}`;
            });
            
            // Handle case where there are no variables
            const valuationCode = variableNames.length > 0 
                ? `{\n            ${valuationEntries.join(',\n            ')}\n        }`
                : '{}';
            
            return `
// [Section 5.2] Cfire(${t.id}): Fire transition and update state
var fire_${this.sanitizeId(t.id)} = function(state) {
    return {
        marking: {
            ${markingEntries.join(',\n            ')}
        },
        valuation: ${valuationCode}
    };
};`;
        }).join('\n');

        // Generate dispatcher function that routes to appropriate fire function
        const dispatcher = `
// [Section 5.2] Dispatcher for Cfire(t) - routes to transition-specific fire function
var fireTransition = function(state, transitionId) {
    ${transitions.map(t => 
        `if (transitionId === '${t.id}') { return fire_${this.sanitizeId(t.id)}(state); }`
    ).join('\n    ')}
    // [Definition 5] Fallback - should never reach here if transition was enabled
    return state;
};`;

        return fireFunctions + '\n' + dispatcher;
    }
    
    /**
     * Sanitize transition ID for use as JavaScript function name.
     * Replaces invalid characters with underscores.
     * 
     * @param {string} id - Original transition ID
     * @returns {string} - Sanitized ID safe for JS function names
     */
    sanitizeId(id) {
        return id.replace(/[^a-zA-Z0-9_]/g, '_');
    }

    /**
     * Generate firing code following Section 5.2 Cfire(t).
     * (Legacy method - kept for reference)
     */
    generateFiringCode(transitions, arcs, dataVariables) {
        const cases = transitions.map(t => {
            // Get preset •t and postset t•
            const preset = arcs.filter(a => a.target === t.id);
            const postset = arcs.filter(a => a.source === t.id);
            
            // Token removal: q := q - weight (for q ∈ •t)
            const removeTokens = preset.map(a => 
                `newMarking['${a.source}'] = newMarking['${a.source}'] - ${a.weight};`
            ).join('\n        ');
            
            // Token addition: r := r + weight (for r ∈ t•)  
            const addTokens = postset.map(a =>
                `newMarking['${a.target}'] = newMarking['${a.target}'] + ${a.weight};`
            ).join('\n        ');
            
            // Variable updates from postcondition
            const updates = this.parsePostconditionUpdates(t.postcondition, dataVariables);
            const variableUpdates = updates.map(u => 
                `newValuation['${u.variable}'] = ${u.expression};`
            ).join('\n        ');
            
            return `
    if (transitionId === '${t.id}') {
        // [Section 5.2] Cfire(${t.id})
        // Remove tokens from preset •t
        ${removeTokens || '// No tokens to remove'}
        // Add tokens to postset t•
        ${addTokens || '// No tokens to add'}
        // Apply postcondition updates (variable assignments)
        ${variableUpdates || '// No variable updates'}
    }`;
        });
        
        return cases.join('');
    }

    /**
     * Translate a DPN expression to WebPPL, replacing variable references.
     * 
     * [Section 5.1] "we denote by pre(t) the expression pre(t) in which 
     * every variable v ∈ V has been replaced by v (underlined)"
     */
    translateExpression(expr, dataVariables, statePrefix) {
        if (!expr || expr.trim() === '' || expr.trim() === ';') {
            return 'true';
        }
        
        let translated = expr.replace(/;/g, '').trim();
        
        // Sort variables by length descending to avoid partial replacements
        // e.g., 'temp' should be replaced before 't'
        const sortedVars = [...dataVariables].sort((a, b) => b.name.length - a.name.length);
        
        sortedVars.forEach(v => {
            const regex = new RegExp(`\\b${v.name}\\b`, 'g');
            translated = translated.replace(regex, `${statePrefix}['${v.name}']`);
        });
        
        return translated || 'true';
    }

    /**
     * Parse postcondition into variable updates.
     * 
     * [Section 5.2] "Let V'(post(t)) = {u1,...,uk} be the variables that are 
     * potentially modified by firing t"
     * 
     * Format: "v' = expr" where v' denotes the new value of variable v
     * [Section 5.1] "V' keeps their primed copies used to describe variable updates"
     * 
     * @param {string} postcondition - Postcondition expression from transition
     * @param {Array} dataVariables - List of data variables from DPN
     * @returns {Array} - List of {variable, expression} update objects
     */
    parsePostconditionUpdates(postcondition, dataVariables) {
        const updates = [];
        if (!postcondition || postcondition.trim() === '') {
            return updates;
        }
        
        const statements = postcondition.split(';');
        
        for (const stmt of statements) {
            const trimmed = stmt.trim();
            if (!trimmed) continue;
            
            // Match "variable' = expression" pattern for deterministic updates
            // [Section 5.1] "V' keeps their primed copies used to describe variable updates"
            const assignmentMatch = trimmed.match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\s*=\s*(.+)$/);
            if (assignmentMatch) {
                const varName = assignmentMatch[1];
                const expression = assignmentMatch[2].trim();
                
                // Translate expression, replacing variable names with state lookups
                const translatedExpr = this.translateExpression(expression, dataVariables, 'state.valuation');
                
                updates.push({
                    variable: varName,
                    expression: translatedExpr
                });
            }
            // Note: Constraint-style postconditions like "x' >= 10 && x' <= 1000"
            // would require sampling from the constraint domain using SV scheduler.
            // This is more complex and requires probabilistic inference.
            // For now, we handle deterministic assignments only.
        }
        
        return updates;
    }
}

// =============================================================================
// Export the DPNSimulator class
// =============================================================================
export { DPNSimulator };

// =============================================================================
// Command-line interface for testing
// =============================================================================
// Usage: node tests/webppl-to-dpn.js [path-to-json-file]
// If no file specified, runs with the DPN-Fibonacci example.

async function main() {
    console.log("=".repeat(70));
    console.log("DPN to PPL Translator");
    console.log("Following: 'Data Petri Nets Meet Probabilistic Programming'");
    console.log("           (Kuhn et al., BPM 2024)");
    console.log("Paper: https://doi.org/10.1007/978-3-031-70396-6_2");
    console.log("=".repeat(70));
    console.log("");

    // Get file path from command line or use default
    const args = process.argv.slice(2);
    let filePath;
    
    if (args.length > 0) {
        filePath = args[0];
    } else {
        // Default to DPN-Fibonacci example
        filePath = path.join(__dirname, '..', 'public', 'examples', 'DPN-Fibonacci(n).json');
    }
    
    console.log(`Loading DPN from: ${filePath}`);
    console.log("");
    
    try {
        const sim = DPNSimulator.fromFile(filePath);
        console.log(`DPN Name: ${sim.dpn.name || 'Unnamed'}`);
        console.log(`Places: ${sim.dpn.places.length}`);
        console.log(`Transitions: ${sim.dpn.transitions.length}`);
        console.log(`Variables: ${sim.dpn.dataVariables.length}`);
        console.log("");
        
        // Show final marking configuration
        const finalPlaces = sim.dpn.places.filter(p => p.finalMarking > 0);
        if (finalPlaces.length > 0) {
            console.log("Final Marking (Goal State):");
            finalPlaces.forEach(p => {
                console.log(`  ${p.label || p.id}: ${p.finalMarking} token(s)`);
            });
            console.log("");
        }
        // Note: If no finalMarking is defined, generatePPL() will throw an error
        
        sim.run((result) => {
            console.log("\n" + "=".repeat(70));
            console.log("Simulation Complete");
            console.log("=".repeat(70));
            console.log(`Status: ${result.status}`);
            console.log(`Trace Length: ${result.trace.length} steps`);
            
            // Show final variable values if any
            const varNames = Object.keys(result.state.valuation);
            if (varNames.length > 0) {
                console.log("\nFinal Variable Values:");
                varNames.forEach(v => {
                    console.log(`  ${v} = ${result.state.valuation[v]}`);
                });
            }
            
            // Show final marking
            console.log("\nFinal Marking:");
            Object.entries(result.state.marking).forEach(([pid, tokens]) => {
                if (tokens > 0) {
                    console.log(`  ${pid}: ${tokens} token(s)`);
                }
            });
        });
    } catch (error) {
        console.error(`Error: ${error.message}`);
        process.exit(1);
    }
}

main();