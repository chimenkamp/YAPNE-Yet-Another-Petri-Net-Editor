/**
 * Z3 Integration Helper
 * Provides utility functions and ensures proper Z3 integration across all components
 */

class Z3IntegrationHelper {
    constructor() {
        this.z3Ready = false;
        this.z3Instance = null;
        this.readyCallbacks = [];
    }

    /**
     * Initialize Z3 and notify all waiting components
     */
    async initialize() {
        try {
            this.z3Instance = await initZ3();
            this.z3Ready = true;
            
            console.log('✅ Z3 SMT Solver initialized successfully');
            
            // Notify all waiting callbacks
            this.readyCallbacks.forEach(callback => {
                try {
                    callback(this.z3Instance);
                } catch (error) {
                    console.error('Error in Z3 ready callback:', error);
                }
            });
            
            this.readyCallbacks = [];
            
            // Create global SMT solver instance
            if (!window.globalSMTSolver) {
                window.globalSMTSolver = new SMTSolver();
            }
            
            return true;
        } catch (error) {
            console.error('❌ Failed to initialize Z3 SMT Solver:', error);
            this.z3Ready = false;
            return false;
        }
    }

    /**
     * Register a callback to be called when Z3 is ready
     * @param {Function} callback - Function to call when Z3 is ready
     */
    onReady(callback) {
        if (this.z3Ready) {
            callback(this.z3Instance);
        } else {
            this.readyCallbacks.push(callback);
        }
    }

    /**
     * Check if Z3 is ready
     * @returns {boolean}
     */
    isReady() {
        return this.z3Ready;
    }

    /**
     * Get the Z3 instance (null if not ready)
     * @returns {object|null}
     */
    getZ3Instance() {
        return this.z3Instance;
    }

    /**
     * Test Z3 functionality with a simple example
     * @returns {Promise<boolean>}
     */
    async testZ3() {
        if (!this.z3Ready) {
            console.warn('Z3 not ready for testing');
            return false;
        }

        try {
            const solver = new SMTSolver();
            
            // Test basic satisfiability
            const result1 = await solver.isSatisfiable('x > 0 && x < 10');
            console.log('Test 1 (x > 0 && x < 10):', result1 ? 'SAT' : 'UNSAT');
            
            // Test unsatisfiable formula
            const result2 = await solver.isSatisfiable('x > 10 && x < 5');
            console.log('Test 2 (x > 10 && x < 5):', result2 ? 'SAT' : 'UNSAT');
            
            // Test solving for specific values
            const solution = await solver.solve('x > 5 && x < 15 && y == x + 2');
            console.log('Test 3 solution:', solution);
            
            return result1 && !result2 && solution !== null;
        } catch (error) {
            console.error('Z3 test failed:', error);
            return false;
        }
    }

    /**
     * Create a new SMT solver instance
     * @returns {SMTSolver}
     */
    createSolver() {
        return new SMTSolver();
    }

    /**
     * Create a new Expression solver instance
     * @param {Object} valuation - Current variable valuation
     * @returns {ExpressionSolver}
     */
    createExpressionSolver(valuation) {
        return new ExpressionSolver(valuation);
    }

    /**
     * Create a new LTL Expression solver instance
     * @param {Object} valuation - Current variable valuation
     * @returns {LTLExpressionSolver}
     */
    createLTLExpressionSolver(valuation) {
        return new LTLExpressionSolver(valuation);
    }
}

// Create global instance
window.z3Helper = new Z3IntegrationHelper();

// Auto-initialize when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
    if (typeof initZ3 === 'function') {
        window.z3Helper.initialize().then((success) => {
            if (success) {
                // Run a quick test
                window.z3Helper.testZ3().then((testPassed) => {
                    if (testPassed) {
                        console.log('✅ Z3 integration test passed');
                        
                        // Dispatch event for other components
                        const event = new CustomEvent('z3-ready', {
                            detail: { z3Helper: window.z3Helper }
                        });
                        document.dispatchEvent(event);
                    } else {
                        console.warn('⚠️ Z3 integration test failed');
                    }
                });
            }
        });
    } else {
        console.error('❌ initZ3 function not found. Make sure Z3 is properly loaded.');
    }
});

/**
 * Utility function to replace old SMT solver calls
 * @param {string} formula - Formula to check
 * @returns {Promise<boolean>}
 */
window.checkSatisfiability = async function(formula) {
    if (window.globalSMTSolver) {
        return await window.globalSMTSolver.isSatisfiable(formula);
    } else {
        console.warn('Global SMT solver not ready, using basic check');
        return formula !== 'false';
    }
};

/**
 * Utility function for constraint solving
 * @param {string} constraints - Constraint string
 * @param {Object} currentValues - Current variable values
 * @returns {Promise<Object|null>}
 */
window.solveConstraints = async function(constraints, currentValues) {
    try {
        const solver = new ExpressionSolver(currentValues || {});
        return await solver.solve(constraints);
    } catch (error) {
        console.error('Constraint solving failed:', error);
        return null;
    }
};

console.log('Z3 Integration Helper loaded');