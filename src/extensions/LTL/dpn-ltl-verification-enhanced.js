/**
 * Final Integration Script for Enhanced LTL Verification
 * 
 * This script provides the complete integration of the enhanced LTL verification
 * system with your existing Data Petri Net application.
 */

/**
 * Enhanced LTL Verification Integration Manager
 */
class EnhancedLTLVerificationIntegration {
    constructor() {
        this.isInitialized = false;
        this.ltlManager = null;
        this.verificationExtension = null;
        this.expressionSolver = null;
        this.debugMode = false;
    }

    /**
     * Initialize the enhanced LTL verification system
     * @param {Object} petriApp - The Petri net application instance
     * @returns {Promise<boolean>} Success status
     */
    async initialize(petriApp) {
        try {
            this.log('Initializing Enhanced LTL Verification System...');

            // Check dependencies
            if (!this.checkDependencies()) {
                throw new Error('Missing required dependencies');
            }

            // Initialize LTL integration manager
            this.ltlManager = new LTLIntegrationManager();
            this.ltlManager.initialize({
                atomEvaluator: this.createAtomEvaluator(petriApp)
            });

            // Initialize expression solver
            this.expressionSolver = new ExpressionSolver({});

            // Initialize verification UI extension
            this.verificationExtension = new LTLVerificationExtension(petriApp);

            // Set up event handlers
            this.setupEventHandlers(petriApp);

            // Enhance the existing DPN model with constraint solving
            this.enhanceDataPetriNetModel();

            this.isInitialized = true;
            this.log('Enhanced LTL Verification System initialized successfully');

            return true;
        } catch (error) {
            console.error('Failed to initialize Enhanced LTL Verification:', error);
            return false;
        }
    }

    /**
     * Check if all required dependencies are available
     * @returns {boolean} Dependencies status
     */
    checkDependencies() {
        const required = [
            'LTLIntegrationManager',
            'LTLVerificationExtension', 
            'LTLExpressionSolver',
            'DataAwareLTLEvaluator'
        ];
    
        const missing = required.filter(dep => typeof window[dep] === 'undefined');
        
        if (missing.length > 0) {
            console.error('Missing dependencies:', missing);
            return false;
        }

        return true;
    }

    /**
     * Create an atom evaluator for the LTL system
     * @param {Object} petriApp - The Petri net application
     * @returns {Function} Atom evaluator function
     */
    createAtomEvaluator(petriApp) {
        return (atomValue, input) => {
            try {
                // Check if it's a place reference
                if (input.marking && input.marking[atomValue] !== undefined) {
                    return input.marking[atomValue] > 0;
                }

                // Check if it's a data variable reference
                if (input.valuation && input.valuation[atomValue] !== undefined) {
                    return Boolean(input.valuation[atomValue]);
                }

                // Try to evaluate as a constraint
                if (atomValue.includes('>') || atomValue.includes('<') || atomValue.includes('=')) {
                    return this.evaluateConstraintAtom(atomValue, input);
                }

                this.log(`Unknown atom: ${atomValue}`);
                return false;
            } catch (error) {
                console.error(`Error evaluating atom ${atomValue}:`, error);
                return false;
            }
        };
    }

    /**
     * Evaluate a constraint atom
     * @param {string} atomValue - The constraint expression
     * @param {Object} input - Input context with marking and valuation
     * @returns {boolean} Constraint result
     */
    evaluateConstraintAtom(atomValue, input) {
        const constraintMatch = atomValue.match(/^([a-zA-Z_][a-zA-Z0-9_]*)\s*([<>=!]+)\s*(.+)$/);
        
        if (!constraintMatch) {
            return false;
        }

        const [, variable, operator, valueStr] = constraintMatch;
        const currentValue = input.valuation[variable];

        if (currentValue === undefined) {
            this.log(`Variable ${variable} not found in valuation`);
            return false;
        }

        // Parse target value
        let targetValue;
        if (/^".*"$/.test(valueStr.trim())) {
            targetValue = valueStr.trim().slice(1, -1);
        } else if (!isNaN(valueStr.trim())) {
            targetValue = parseFloat(valueStr.trim());
        } else {
            targetValue = valueStr.trim();
        }

        return this.evaluateComparison(currentValue, operator.trim(), targetValue);
    }

    /**
     * Evaluate a comparison operation
     * @param {*} left - Left operand
     * @param {string} operator - Comparison operator
     * @param {*} right - Right operand
     * @returns {boolean} Comparison result
     */
    evaluateComparison(left, operator, right) {
        const numLeft = typeof left === 'number' ? left : parseFloat(left);
        const numRight = typeof right === 'number' ? right : parseFloat(right);

        if (!isNaN(numLeft) && !isNaN(numRight)) {
            switch (operator) {
                case '>': return numLeft > numRight;
                case '<': return numLeft < numRight;
                case '>=': return numLeft >= numRight;
                case '<=': return numLeft <= numRight;
                case '==': case '=': return Math.abs(numLeft - numRight) < 1e-10;
                case '!=': return Math.abs(numLeft - numRight) >= 1e-10;
                default: return false;
            }
        } else {
            switch (operator) {
                case '==': case '=': return left == right;
                case '!=': return left != right;
                default: return false;
            }
        }
    }

    /**
     * Set up event handlers for the integration
     * @param {Object} petriApp - The Petri net application
     */
    setupEventHandlers(petriApp) {
        // Listen for Petri net state changes
        if (petriApp.api && typeof petriApp.api.addEventListener === 'function') {
            petriApp.api.addEventListener('transitionFired', (event) => {
                this.onTransitionFired(event);
            });

            petriApp.api.addEventListener('dataVariableChanged', (event) => {
                this.onDataVariableChanged(event);
            });
        }

        // Listen for verification requests
        document.addEventListener('ltl-verification-request', (event) => {
            this.handleVerificationRequest(event.detail);
        });
    }

    /**
     * Handle transition fired events
     * @param {Object} event - Transition fired event
     */
    onTransitionFired(event) {
        if (this.debugMode) {
            this.log('Transition fired:', event.transitionId);
        }
    }

    /**
     * Handle data variable changed events
     * @param {Object} event - Data variable changed event
     */
    onDataVariableChanged(event) {
        if (this.debugMode) {
            this.log('Data variable changed:', event.variableId, event.newValue);
        }
    }

    /**
     * Handle LTL verification requests
     * @param {Object} request - Verification request details
     */
    async handleVerificationRequest(request) {
        try {
            this.log('Handling LTL verification request:', request.formula);
            
            const result = await this.verifyFormula(request.formula, request.options);
            
            // Dispatch result event
            const resultEvent = new CustomEvent('ltl-verification-result', {
                detail: result
            });
            document.dispatchEvent(resultEvent);
            
        } catch (error) {
            console.error('LTL verification request failed:', error);
        }
    }

    /**
     * Verify an LTL formula
     * @param {string} formula - The LTL formula to verify
     * @param {Object} options - Verification options
     * @returns {Promise<Object>} Verification result
     */
    async verifyFormula(formula, options = {}) {
        if (!this.isInitialized) {
            throw new Error('LTL verification system not initialized');
        }

        try {
            // Parse the formula
            const ast = this.ltlManager.parseFormula(formula);
            
            // Create verifier
            const petriNet = options.petriNet || this.getCurrentPetriNet();
            const verifier = new EnhancedLTLVerifier(petriNet, ast);
            
            // Run verification
            const result = await verifier.verify((progress, step) => {
                this.log(`Verification progress: ${progress}% - ${step}`);
            });
            
            return result;
        } catch (error) {
            console.error('Formula verification failed:', error);
            throw error;
        }
    }

    /**
     * Get the current Petri net instance
     * @returns {Object} Current Petri net
     */
    getCurrentPetriNet() {
        if (window.petriApp && window.petriApp.api && window.petriApp.api.petriNet) {
            return window.petriApp.api.petriNet;
        }
        throw new Error('No active Petri net found');
    }

    /**
     * Enhance the Data Petri Net model with improved constraint solving
     */
    enhanceDataPetriNetModel() {
        // Check if DataAwareTransition is available
        if (typeof DataAwareTransition !== 'undefined') {
            // Enhance the evaluatePostcondition method
            const originalEvaluatePostcondition = DataAwareTransition.prototype.evaluatePostcondition;
            
            DataAwareTransition.prototype.evaluatePostcondition = function(valuation) {
                try {
                    // Try the enhanced solver first
                    if (this.postcondition && this.postcondition.trim()) {
                        const solver = new ExpressionSolver(valuation);
                        const result = solver.solve(this.postcondition);
                        
                        // Validate that result contains valid updates
                        if (this.validatePostconditionResult(result, valuation)) {
                            return result;
                        }
                    }
                    
                    // Fallback to original implementation
                    return originalEvaluatePostcondition.call(this, valuation);
                } catch (error) {
                    console.error(`Enhanced postcondition evaluation failed for transition ${this.id}:`, error);
                    return originalEvaluatePostcondition.call(this, valuation);
                }
            };

            // Add validation method
            DataAwareTransition.prototype.validatePostconditionResult = function(result, originalValuation) {
                // Check that all required variables are present
                for (const varName of Object.keys(originalValuation)) {
                    if (result[varName] === undefined) {
                        return false;
                    }
                }
                
                // Check that types are preserved
                for (const [varName, newValue] of Object.entries(result)) {
                    const originalValue = originalValuation[varName];
                    if (originalValue !== null && typeof originalValue !== typeof newValue) {
                        return false;
                    }
                }
                
                return true;
            };

            this.log('Enhanced Data Petri Net model with improved constraint solving');
        }
    }

    /**
     * Enable or disable debug mode
     * @param {boolean} enabled - Debug mode status
     */
    setDebugMode(enabled) {
        this.debugMode = enabled;
        this.log(`Debug mode ${enabled ? 'enabled' : 'disabled'}`);
    }

    /**
     * Log a message (only if debug mode is enabled)
     * @param {...any} args - Log arguments
     */
    log(...args) {
        if (this.debugMode) {
            console.log('[Enhanced LTL]', ...args);
        }
    }

    /**
     * Get system status and statistics
     * @returns {Object} System status
     */
    getStatus() {
        return {
            initialized: this.isInitialized,
            debugMode: this.debugMode,
            hasLTLManager: !!this.ltlManager,
            hasVerificationExtension: !!this.verificationExtension,
            hasExpressionSolver: !!this.expressionSolver,
            dependencies: this.checkDependencies()
        };
    }

    /**
     * Clean up and dispose of resources
     */
    dispose() {
        if (this.verificationExtension && typeof this.verificationExtension.dispose === 'function') {
            this.verificationExtension.dispose();
        }
        
        this.ltlManager = null;
        this.verificationExtension = null;
        this.expressionSolver = null;
        this.isInitialized = false;
        
        this.log('Enhanced LTL Verification System disposed');
    }
}

/**
 * Auto-initialization function
 */
function initializeEnhancedLTLVerification() {
    // Create global integration instance
    if (!window.enhancedLtlVerification) {
        window.enhancedLtlVerification = new EnhancedLTLVerificationIntegration();
    }

    // Wait for the Petri net application to be ready
    const checkAndInitialize = async () => {
        if (window.petriApp && window.dataPetriNetIntegration) {
            console.log('Initializing Enhanced LTL Verification System...');
            
            const success = await window.enhancedLtlVerification.initialize(window.petriApp);
            
            if (success) {
                console.log('✅ Enhanced LTL Verification System ready');
                
                // Optional: Enable debug mode in development
                if (window.location.hostname === 'localhost' || window.location.hostname === '127.0.0.1') {
                    window.LTLVerificationUtils.setDebugMode(true);
                }
                
                // Dispatch ready event
                const readyEvent = new CustomEvent('enhanced-ltl-ready', {
                    detail: window.LTLVerificationUtils.getStatus()
                });
                document.dispatchEvent(readyEvent);
            } else {
                console.error('❌ Failed to initialize Enhanced LTL Verification System');
            }
        } else {
            // Retry after a short delay
            // setTimeout(checkAndInitialize, 500);
        }
    };

    // Start initialization
    checkAndInitialize();
}

/**
 * DOM ready handler
 */
if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', () => {
        setTimeout(initializeEnhancedLTLVerification, 1500);
    });
} else {
    // DOM already loaded
    setTimeout(initializeEnhancedLTLVerification, 100);
}

/**
 * Utility functions for external use
 */
window.LTLVerificationUtils = {
    /**
     * Quick formula validation
     * @param {string} formula - Formula to validate
     * @param {Array} availableAtoms - Available atoms
     * @returns {Object} Validation result
     */
    validateFormula(formula, availableAtoms = []) {
        try {
            const parser = new EnhancedLTLParser(availableAtoms);
            return parser.parse(formula);
        } catch (error) {
            return { valid: false, error: error.message };
        }
    },

    /**
     * Get current system status
     * @returns {Object} System status
     */
    getStatus() {
        // return window.enhancedLtlVerification ? 
        //     window.LTLVerificationUtils.getStatus() : 
        //     { initialized: false };
        return true
    },

    /**
     * Enable debug mode
     * @param {boolean} enabled - Debug status
     */
    setDebugMode(enabled) {
        // if (window.enhancedLtlVerification) {
        //     window.LTLVerificationUtils.setDebugMode(enabled);
        // }
    },

    /**
     * Manually trigger verification
     * @param {string} formula - Formula to verify
     * @param {Object} options - Verification options
     * @returns {Promise<Object>} Verification result
     */
    async verifyFormula(formula, options = {}) {
        if (!window.enhancedLtlVerification || !window.enhancedLtlVerification.isInitialized) {
            throw new Error('Enhanced LTL Verification System not ready');
        }
        
        return window.enhancedLtlVerification.verifyFormula(formula, options);
    }
};

// Export for module systems
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        EnhancedLTLVerificationIntegration,
        initializeEnhancedLTLVerification
    };
}

console.log('Enhanced LTL Verification Integration Script loaded');