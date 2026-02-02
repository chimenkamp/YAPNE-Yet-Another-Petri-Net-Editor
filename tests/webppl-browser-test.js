/**
 * WebPPL Browser Integration Test
 * 
 * Tests that WebPPL is properly loaded and can execute probabilistic programs.
 * Run in browser console or import this module.
 * 
 * References:
 * - Paper: "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
 * - Section 5.2: Simulating Net Runs in PPL
 */

/**
 * Test 1: Verify WebPPL is available
 */
export function testWebPPLAvailable() {
    if (typeof window !== 'undefined' && window.webppl) {
        console.log('✅ WebPPL is available:', window.webppl.version || 'loaded');
        return true;
    } else {
        console.error('❌ WebPPL is not available. Run: npm run bundle:webppl');
        return false;
    }
}

/**
 * Test 2: Run a simple WebPPL program
 */
export function testSimpleProgram() {
    return new Promise((resolve, reject) => {
        if (!window.webppl) {
            reject(new Error('WebPPL not available'));
            return;
        }

        const code = `
            var x = sample(Uniform({a: 0, b: 10}));
            var y = sample(Uniform({a: 0, b: 10}));
            condition(x + y > 5);
            x + y
        `;

        console.log('Running simple WebPPL program...');
        
        window.webppl.run(code, (err, result) => {
            if (err) {
                console.error('❌ WebPPL execution error:', err);
                reject(err);
            } else {
                console.log('✅ WebPPL result:', result);
                resolve(result);
            }
        });
    });
}

/**
 * Test 3: Run a DPN-style simulation (simplified)
 * This mimics the Csim structure from Section 5.2
 */
export function testDPNSimulation() {
    return new Promise((resolve, reject) => {
        if (!window.webppl) {
            reject(new Error('WebPPL not available'));
            return;
        }

        // Simplified DPN: Two places, one transition
        // Models a counter incrementing until reaching goal
        const code = `
            // [Section 5.2] Cinit - Initial state
            var initialState = {
                marking: { 'p1': 1, 'p2': 0 },
                valuation: { 'counter': 0 }
            };
            var maxSteps = 100;

            // [Definition 2] isGoalState - Check if p2 has a token
            var isGoalState = function(state) {
                return state.marking['p2'] >= 1;
            };

            // [Definition 2] Benabled(t1) - Check if t1 is enabled
            var isTransitionEnabled = function(state, tid) {
                if (tid === 't1') {
                    return state.marking['p1'] >= 1 && state.valuation['counter'] < 5;
                }
                if (tid === 't2') {
                    return state.marking['p1'] >= 1 && state.valuation['counter'] >= 5;
                }
                return false;
            };

            var getEnabledTransitions = function(state) {
                var enabled = [];
                if (isTransitionEnabled(state, 't1')) { enabled.push('t1'); }
                if (isTransitionEnabled(state, 't2')) { enabled.push('t2'); }
                return enabled;
            };

            // [Definition 3] Scheduler ST - Uniform selection
            var selectTransition = function(enabled) {
                if (enabled.length === 0) return null;
                return uniformDraw(enabled);
            };

            // [Section 5.2] Cfire(t) - Fire transition
            var fireTransition = function(state, tid) {
                if (tid === 't1') {
                    // Increment counter
                    return {
                        marking: { 'p1': 1, 'p2': 0 },
                        valuation: { 'counter': state.valuation['counter'] + 1 }
                    };
                }
                if (tid === 't2') {
                    // Move token to p2
                    return {
                        marking: { 'p1': 0, 'p2': 1 },
                        valuation: state.valuation
                    };
                }
                return state;
            };

            // [Figure 5] Main simulation loop - Cloop
            var simulationStep = function(state, trace, stepCount) {
                if (isGoalState(state)) {
                    return { state: state, trace: trace, status: 'goal', steps: stepCount };
                }
                if (stepCount >= maxSteps) {
                    return { state: state, trace: trace, status: 'max_steps', steps: stepCount };
                }
                var enabled = getEnabledTransitions(state);
                if (enabled.length === 0) {
                    return { state: state, trace: trace, status: 'deadlock', steps: stepCount };
                }
                var chosen = selectTransition(enabled);
                var newState = fireTransition(state, chosen);
                // [Section 5.2] "log step(t)" - Record fired transition
                return simulationStep(newState, trace.concat([chosen]), stepCount + 1);
            };

            var simulateDPN = function() {
                return simulationStep(initialState, [], 0);
            };

            simulateDPN()
        `;

        console.log('Running DPN simulation via WebPPL...');
        
        window.webppl.run(code, (err, result) => {
            if (err) {
                console.error('❌ DPN simulation error:', err);
                reject(err);
            } else {
                console.log('✅ DPN simulation result:');
                console.log('  Status:', result.status);
                console.log('  Steps:', result.steps);
                console.log('  Trace:', result.trace);
                console.log('  Final State:', result.state);
                resolve(result);
            }
        });
    });
}

/**
 * Test 4: Test Infer for probabilistic inference
 * This demonstrates the inference capability needed for Theorem 1
 */
export function testInference() {
    return new Promise((resolve, reject) => {
        if (!window.webppl) {
            reject(new Error('WebPPL not available'));
            return;
        }

        const code = `
            // [Theorem 1] Use Infer to compute distribution over outcomes
            var model = function() {
                var coin = flip(0.5);
                var die = randomInteger(6) + 1;
                condition(coin || die > 3);
                return { coin: coin, die: die };
            };

            var dist = Infer({ method: 'rejection', samples: 1000 }, model);
            sample(dist)
        `;

        console.log('Running inference test via WebPPL...');
        
        window.webppl.run(code, (err, result) => {
            if (err) {
                console.error('❌ Inference error:', err);
                reject(err);
            } else {
                console.log('✅ Inference result:', result);
                resolve(result);
            }
        });
    });
}

/**
 * Run all tests
 */
export async function runAllTests() {
    console.log('=== WebPPL Browser Integration Tests ===\n');
    
    const results = {
        available: false,
        simple: false,
        dpn: false,
        inference: false
    };

    // Test 1: Availability
    results.available = testWebPPLAvailable();
    if (!results.available) {
        console.error('\n❌ WebPPL not available. Stopping tests.');
        return results;
    }

    // Test 2: Simple program
    try {
        await testSimpleProgram();
        results.simple = true;
    } catch (e) {
        console.error('Simple program test failed:', e);
    }

    // Test 3: DPN simulation
    try {
        await testDPNSimulation();
        results.dpn = true;
    } catch (e) {
        console.error('DPN simulation test failed:', e);
    }

    // Test 4: Inference
    try {
        await testInference();
        results.inference = true;
    } catch (e) {
        console.error('Inference test failed:', e);
    }

    console.log('\n=== Test Results ===');
    console.log('WebPPL Available:', results.available ? '✅' : '❌');
    console.log('Simple Program:', results.simple ? '✅' : '❌');
    console.log('DPN Simulation:', results.dpn ? '✅' : '❌');
    console.log('Inference:', results.inference ? '✅' : '❌');

    return results;
}

// Auto-run tests when loaded if in browser
if (typeof window !== 'undefined') {
    window.webpplTests = {
        testWebPPLAvailable,
        testSimpleProgram,
        testDPNSimulation,
        testInference,
        runAllTests
    };
    
    console.log('WebPPL tests loaded. Run window.webpplTests.runAllTests() in console.');
}
