/**
 * Probabilistic Execution Integration for Data Petri Nets
 * 
 * Integrates the Probabilistic Execution Engine with the Petri Net Editor application.
 * Implements the approach from "Data Petri Nets Meet Probabilistic Programming"
 * (Kuhn et al., BPM 2024) - https://doi.org/10.1007/978-3-031-70396-6_2
 * 
 * This module extends the existing simulation and event log generation features
 * to use probabilistic programming semantics:
 * - Step simulation uses uniform scheduler ST for transition selection
 * - Full playout runs until goal state (finalMarking) or deadlock
 * - Event log generation produces N probabilistic traces
 * 
 * Key Paper Concepts:
 * - [Definition 3] Uniform scheduler ST for transition selection
 * - [Section 5.1] Goal states G via finalMarking attribute
 * - [Figure 5] Csim loop structure
 */

import { ProbabilisticExecutionEngine } from './probabilistic-execution.js';

/**
 * ProbabilisticExecutionIntegration
 * 
 * Extends the PetriNetApp with probabilistic execution capabilities.
 * 
 * [Figure 5] Implements Csim from the paper:
 *   Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
 */
class ProbabilisticExecutionIntegration {
    /**
     * Initialize the Probabilistic Execution Integration
     * 
     * @param {PetriNetApp} app - Reference to the main application
     */
    constructor(app) {
        this.app = app;
        
        // [Definition 3] Initialize the probabilistic execution engine
        // Default: uniform scheduler ST for transition selection
        this.engine = new ProbabilisticExecutionEngine({
            seed: Date.now(),
            scheduler: 'uniform',
            maxSteps: 10000
        });
        
        // Store reference globally for debugging and external access
        window.probabilisticEngine = this.engine;
        
        // Extend the app with probabilistic methods
        this.extendApp();
        
        console.log("[PP Integration] Probabilistic Execution Engine initialized");
        console.log("[PP Integration] Using uniform scheduler (Definition 3 from paper)");
    }

    /**
     * Trigger variable history update after firing
     * Calls the updateVariableHistory function if available (from variable-tracking.js)
     * 
     * @param {string} transitionLabel - Label of the fired transition
     */
    triggerVariableHistoryUpdate(transitionLabel) {
        // Call the global updateVariableHistory function from variable-tracking.js
        if (typeof window.updateVariableHistoryForPP === 'function') {
            window.updateVariableHistoryForPP(`After firing: ${transitionLabel}`);
        }
        
        // Also update the data values display
        if (typeof window.updateDataValuesDisplayForPP === 'function') {
            window.updateDataValuesDisplayForPP();
        }
    }

    /**
     * Extend the PetriNetApp with probabilistic execution methods.
     * Overrides and extends existing simulation methods.
     */
    extendApp() {
        const app = this.app;
        const engine = this.engine;
        const integration = this;

        // Store original methods for fallback (not used anymore - PP-only approach)
        // const originalStepSimulation = app.stepSimulation.bind(app);
        // const originalStartAutoRun = app.startAutoRun.bind(app);
        const originalStopAutoRun = app.stopAutoRun.bind(app);

        /**
         * [Section 5.2] Probabilistic step simulation
         * 
         * Instead of firing all enabled transitions simultaneously,
         * this uses the paper's approach:
         * 1. Compute frontier (enabled transitions)
         * 2. Select ONE transition using scheduler ST (uniform by default)
         * 3. Fire selected transition
         * 
         * This correctly implements the Cloop from Figure 5.
         */
        app.stepSimulationProbabilistic = async function() {
            const net = this.api.petriNet;
            
            // Capture initial state on first step
            if (!this.simulationStarted) {
                this.captureInitialState();
            }
            
            // [Section 5.2] Execute a single probabilistic step
            const result = await engine.step(net);
            
            if (result.fired) {
                // Update display after successful firing
                if (this.api.editor) {
                    this.api.editor.render();
                }
                this.updateTokensDisplay();
                this.updateSelectedElementProperties();
                
                // Get transition label for logging and variable tracking
                const transition = net.transitions.get(result.transitionId);
                const transitionLabel = transition?.label || result.transitionId;
                
                // [Variable Tracking] Update variable history and display
                integration.triggerVariableHistoryUpdate(transitionLabel);
                
                // Log the fired transition
                console.log(`[PP Step] Fired: ${transitionLabel} ` +
                           `(selected from ${result.enabledBefore} enabled transitions)`);
            } else {
                // Simulation ended - goal or deadlock
                const message = result.status === 'goal' 
                    ? "Goal state reached (finalMarking satisfied)"
                    : "Deadlock - no enabled transitions";
                console.log(`[PP Step] ${message}`);
                alert(message);
            }
            
            return result;
        };

        /**
         * [Definition 3] Step simulation using probabilistic approach
         * 
         * Always uses probabilistic step - PP-only approach
         * Uses scheduler ST for transition selection
         */
        app.stepSimulation = async function() {
            // Always use probabilistic step (PP-only approach)
            return await this.stepSimulationProbabilistic();
        };

        /**
         * [Figure 5] Full probabilistic simulation (playout)
         * 
         * Runs the complete Csim program until goal state or deadlock.
         * Requires finalMarking to be defined to know when to stop.
         * 
         * @param {Object} options - Simulation options
         * @returns {Promise<Object>} Simulation result with trace and final state
         */
        app.runFullSimulationProbabilistic = async function(options = {}) {
            const net = this.api.petriNet;
            
            // Capture initial state
            if (!this.simulationStarted) {
                this.captureInitialState();
            }
            
            try {
                // [Section 5.1] Validate that finalMarking is defined
                engine.validateGoalStateDefinition(net);
                
                // [Figure 5] Run full simulation
                const result = await engine.runFullSimulation(net, {
                    validateGoal: false, // Already validated
                    onStep: (stepNum, transitionId, net) => {
                        // Update display after each step
                        if (this.api.editor) {
                            this.api.editor.render();
                        }
                        this.updateTokensDisplay();
                        
                        // [Variable Tracking] Update variable history
                        const transition = net.transitions.get(transitionId);
                        const transitionLabel = transition?.label || transitionId;
                        integration.triggerVariableHistoryUpdate(transitionLabel);
                    }
                });
                
                // Final display update
                if (this.api.editor) {
                    this.api.editor.render();
                }
                this.updateTokensDisplay();
                this.updateSelectedElementProperties();
                
                // Log results
                console.log(`[PP Full Simulation] Status: ${result.status}`);
                console.log(`[PP Full Simulation] Trace length: ${result.traceLength} steps`);
                console.log(`[PP Full Simulation] Trace: ${result.trace.map(s => s.transition).join(' → ')}`);
                
                // Show result to user
                const statusMsg = result.status === 'goal' 
                    ? "Goal state reached!" 
                    : result.status === 'deadlock'
                    ? "Deadlock reached"
                    : `Simulation stopped: ${result.status}`;
                
                alert(`${statusMsg}\nSteps: ${result.traceLength}\nTrace: ${result.trace.map(s => s.transition).join(' → ')}`);
                
                return result;
            } catch (error) {
                console.error('[PP Full Simulation] Error:', error.message);
                alert(error.message);
                throw error;
            }
        };

        /**
         * [Figure 5] Auto-run using probabilistic steps
         * 
         * Implements Cloop with interval-based execution
         * Always uses PP approach (uniform scheduler)
         */
        app.startAutoRun = function() {
            // Stop any existing auto-run
            this.stopAutoRun();
            
            // Capture initial state on first auto-run
            if (!this.simulationStarted) {
                this.captureInitialState();
            }
            
            // [Figure 5] Start probabilistic auto-run
            this.autoRunInterval = window.setInterval(async () => {
                const net = this.api.petriNet;
                const result = await engine.step(net);
                
                if (result.fired) {
                    // Update display
                    if (this.api.editor) {
                        this.api.editor.render();
                    }
                    this.updateTokensDisplay();
                    this.updateSelectedElementProperties();
                    
                    // [Variable Tracking] Update variable history
                    const transition = net.transitions.get(result.transitionId);
                    const transitionLabel = transition?.label || result.transitionId;
                    integration.triggerVariableHistoryUpdate(transitionLabel);
                } else {
                    // Goal or deadlock reached - stop auto-run
                    this.stopAutoRun();
                    
                    const message = result.status === 'goal'
                        ? "Auto-run stopped: Goal state reached"
                        : "Auto-run stopped: Deadlock (no enabled transitions)";
                    
                    console.log(`[PP Auto-run] ${message}`);
                    alert(message);
                    
                    const autoRunButton = document.getElementById("btn-auto-run");
                    if (autoRunButton) {
                        autoRunButton.textContent = "Auto Run";
                    }
                }
            }, this.autoRunDelay);
        };

        /**
         * Configure the probabilistic execution engine
         * 
         * @param {Object} options - Engine configuration
         * @param {number} options.seed - Random seed for reproducibility
         * @param {string} options.scheduler - 'uniform' or 'weighted'
         * @param {Object} options.transitionWeights - Weights for weighted scheduler
         * @param {number} options.maxSteps - Maximum simulation steps
         * @param {string} options.executionMode - 'native' | 'webppl' | 'auto'
         * @param {Object} options.variableDistributions - SV distributions
         */
        app.configureProabilisticEngine = function(options = {}) {
            if (options.seed !== undefined) {
                engine.reseed(options.seed);
            }
            if (options.scheduler !== undefined) {
                engine.scheduler = options.scheduler;
            }
            if (options.transitionWeights !== undefined) {
                engine.transitionWeights = options.transitionWeights;
            }
            if (options.maxSteps !== undefined) {
                engine.maxSteps = options.maxSteps;
            }
            if (options.executionMode !== undefined) {
                engine.executionMode = options.executionMode;
            }
            if (options.variableDistributions !== undefined) {
                engine.variableDistributions = options.variableDistributions;
            }
            
            console.log('[PP Config] Engine reconfigured:', {
                seed: engine.seed,
                scheduler: engine.scheduler,
                maxSteps: engine.maxSteps,
                executionMode: engine.executionMode
            });
        };

        /**
         * Get the probabilistic execution engine instance
         * @returns {ProbabilisticExecutionEngine} The engine instance
         */
        app.getProbabilisticEngine = function() {
            return engine;
        };

        /**
         * Check if the current net has reached a goal state
         * 
         * [Section 5.1] Goal states G via finalMarking
         * 
         * @returns {Object} Goal state check result
         */
        app.checkGoalState = function() {
            return engine.checkGoalState(this.api.petriNet);
        };

        /**
         * Generate WebPPL code for the current Petri net.
         * 
         * [Section 5] Generates the Csim program following the paper's translation.
         * 
         * @param {Object} options - Generation options
         * @param {boolean} options.includeComments - Include paper reference comments
         * @returns {string} Generated WebPPL code
         */
        app.generateWebPPLCode = function(options = {}) {
            return engine.generateWebPPLCode(this.api.petriNet, options);
        };

        /**
         * Check if WebPPL mode is recommended for the current net.
         * 
         * @returns {boolean} True if WebPPL is recommended
         */
        app.recommendsWebPPLMode = function() {
            return engine.netRequiresWebPPL(this.api.petriNet);
        };

        /**
         * Show WebPPL code in a dialog.
         * 
         * [Section 5] Displays the generated Csim program for inspection.
         */
        app.showWebPPLCodeDialog = function() {
            integration.showWebPPLCodeDialog();
        };

        // Set up the "View WebPPL Code" button handler
        integration.setupWebPPLViewerButton();

        /**
         * Run a full WebPPL-based simulation.
         * 
         * [Theorem 1] Produces same distribution as DPN under scheduler S.
         * 
         * @param {Object} options - Simulation options
         * @returns {Promise<Object>} Simulation result
         */
        app.runWebPPLSimulation = async function(options = {}) {
            const net = this.api.petriNet;
            
            // Capture initial state
            if (!this.simulationStarted) {
                this.captureInitialState();
            }
            
            try {
                const result = await engine.runWebPPLSimulation(net, options);
                
                // Update display
                if (this.api.editor) {
                    this.api.editor.render();
                }
                this.updateTokensDisplay();
                this.updateSelectedElementProperties();
                
                console.log('[PP WebPPL] Simulation completed:', result.status);
                return result;
            } catch (error) {
                console.error('[PP WebPPL] Error:', error.message);
                throw error;
            }
        };
    }

    /**
     * Set up the "View WebPPL Code" button handler
     */
    setupWebPPLViewerButton() {
        const btn = document.getElementById('btn-view-webppl');
        if (btn) {
            btn.addEventListener('click', () => {
                this.showWebPPLCodeDialog();
            });
            console.log('[PP Integration] WebPPL Viewer button initialized');
        } else {
            // Button might not exist yet, try again later
            setTimeout(() => this.setupWebPPLViewerButton(), 500);
        }
    }

    /**
     * Show WebPPL code in a modal dialog.
     * 
     * [Section 5] Displays the generated Csim program for inspection.
     * The code follows the paper's translation from DPN to WebPPL.
     */
    showWebPPLCodeDialog() {
        try {
            // Generate the WebPPL code
            const code = this.app.generateWebPPLCode({ includeComments: true });
            
            // Check if dialog already exists
            let dialog = document.getElementById('webppl-code-dialog');
            if (dialog) {
                dialog.remove();
            }
            
            // Create the modal dialog
            dialog = document.createElement('div');
            dialog.id = 'webppl-code-dialog';
            dialog.className = 'modal-overlay';
            dialog.innerHTML = `
                <div class="modal-container" style="max-width: 900px; max-height: 85vh; display: flex; flex-direction: column; width: 90%;">
                    <div class="modal-header">
                        <h2>📜 WebPPL Code (Csim Translation)</h2>
                        <button class="close-btn modal-close" title="Close">&times;</button>
                    </div>
                    <div class="modal-body" style="flex: 1; overflow: hidden; display: flex; flex-direction: column; padding: 0;">
                        <div style="padding: 10px 15px; background: #2E3440; border-bottom: 1px solid #434C5E; font-size: 12px; color: #D8DEE9;">
                            <strong>Reference:</strong> "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)<br>
                            <em>This code implements the Csim translation from Section 5.2 of the paper.</em>
                        </div>
                        <pre id="webppl-code-content" style="flex: 1; overflow: auto; margin: 0; padding: 15px; font-family: 'Consolas', 'Monaco', 'Courier New', monospace; font-size: 13px; line-height: 1.5; background: #1e1e1e; color: #d4d4d4; white-space: pre; tab-size: 2; min-height: 300px;"></pre>
                    </div>
                    <div class="modal-footer">
                        <button id="webppl-copy-btn" class="blue" title="Copy to clipboard">📋 Copy Code</button>
                        <button id="webppl-download-btn" title="Download as file">💾 Download</button>
                        <button id="webppl-close-btn">Close</button>
                    </div>
                </div>
            `;
            
            document.body.appendChild(dialog);
            
            // Set the code content with syntax highlighting hints
            const codeContent = document.getElementById('webppl-code-content');
            codeContent.textContent = code;
            
            // Apply basic syntax highlighting
            this.applyWebPPLSyntaxHighlighting(codeContent);
            
            // Set up button handlers
            const closeBtn = dialog.querySelector('.modal-close');
            const closeBtnFooter = document.getElementById('webppl-close-btn');
            const copyBtn = document.getElementById('webppl-copy-btn');
            const downloadBtn = document.getElementById('webppl-download-btn');
            
            const closeDialog = () => {
                dialog.classList.add('hidden');
                setTimeout(() => dialog.remove(), 300);
            };
            
            closeBtn.addEventListener('click', closeDialog);
            closeBtnFooter.addEventListener('click', closeDialog);
            
            // Close on overlay click
            dialog.addEventListener('click', (e) => {
                if (e.target === dialog) {
                    closeDialog();
                }
            });
            
            // Close on Escape key
            const escHandler = (e) => {
                if (e.key === 'Escape') {
                    closeDialog();
                    document.removeEventListener('keydown', escHandler);
                }
            };
            document.addEventListener('keydown', escHandler);
            
            // Copy to clipboard
            copyBtn.addEventListener('click', async () => {
                try {
                    await navigator.clipboard.writeText(code);
                    const originalText = copyBtn.textContent;
                    copyBtn.textContent = '✓ Copied!';
                    setTimeout(() => {
                        copyBtn.textContent = originalText;
                    }, 2000);
                } catch (err) {
                    console.error('Failed to copy:', err);
                    alert('Failed to copy to clipboard. Please select and copy manually.');
                }
            });
            
            // Download as file
            downloadBtn.addEventListener('click', () => {
                const blob = new Blob([code], { type: 'text/plain' });
                const url = URL.createObjectURL(blob);
                const a = document.createElement('a');
                a.href = url;
                a.download = 'dpn-simulation.wppl';
                document.body.appendChild(a);
                a.click();
                document.body.removeChild(a);
                URL.revokeObjectURL(url);
            });
            
            console.log('[PP Integration] WebPPL code dialog opened');
            
        } catch (error) {
            console.error('[PP Integration] Error generating WebPPL code:', error);
            alert('Error generating WebPPL code:\n' + error.message);
        }
    }

    /**
     * Apply basic syntax highlighting to WebPPL code
     * 
     * @param {HTMLElement} element - The pre element containing the code
     */
    applyWebPPLSyntaxHighlighting(element) {
        const code = element.textContent;
        
        // Simple syntax highlighting using spans
        let highlighted = code
            // Comments (// and /** */)
            .replace(/(\/\/.*$)/gm, '<span style="color: #6a9955;">$1</span>')
            .replace(/(\/\*\*[\s\S]*?\*\/)/g, '<span style="color: #6a9955;">$1</span>')
            // Keywords
            .replace(/\b(var|const|let|function|return|if|else|while|do|for|true|false|null|undefined)\b/g, 
                '<span style="color: #569cd6;">$1</span>')
            // WebPPL functions
            .replace(/\b(flip|uniform|gaussian|sample|factor|observe|Infer|Enumerate|SMC|MCMC|condition)\b/g,
                '<span style="color: #dcdcaa;">$1</span>')
            // Numbers
            .replace(/\b(\d+\.?\d*)\b/g, '<span style="color: #b5cea8;">$1</span>')
            // Strings
            .replace(/("(?:[^"\\]|\\.)*")/g, '<span style="color: #ce9178;">$1</span>')
            .replace(/('(?:[^'\\]|\\.)*')/g, '<span style="color: #ce9178;">$1</span>');
        
        element.innerHTML = highlighted;
    }

    /**
     * Check if the net has any finalMarking defined
     * 
     * @param {PetriNet|DataPetriNet} net - The Petri net to check
     * @returns {boolean} True if at least one place has finalMarking > 0
     */
    hasFinalMarkingDefined(net) {
        for (const [id, place] of net.places) {
            if (place.finalMarking !== undefined && place.finalMarking !== null && place.finalMarking > 0) {
                return true;
            }
        }
        return false;
    }
}

/**
 * Initialize the Probabilistic Execution Integration
 * 
 * @param {PetriNetApp} app - The main application instance
 * @returns {ProbabilisticExecutionIntegration} The integration instance
 */
function initializeProbabilisticExecution(app) {
    const integration = new ProbabilisticExecutionIntegration(app);
    window.probabilisticIntegration = integration;
    return integration;
}

export { ProbabilisticExecutionIntegration, initializeProbabilisticExecution };