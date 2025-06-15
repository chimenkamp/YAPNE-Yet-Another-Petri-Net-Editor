/**
 * Enhanced LTL Verification Extension for Data Petri Nets
 * 
 * This implementation integrates the existing LTL infrastructure
 * and provides comprehensive LTL_f verification for Data-Aware Dynamic Systems
 */

class LTLVerificationExtensionTWO {
    constructor(app) {
        this.app = app;
        this.ltlFormula = "";
        this.ltlAST = null;
        this.constraints = new Set();
        this.initializeUI();
        this.injectStyles();
    }

    /**
     * Initialize the LTL verification UI components
     */
    initializeUI() {
        this.addLTLButtonToVerificationSection();
        this.createLTLModal();
    }

    initialize() {
        // This method can be used to perform any additional initialization if needed

        return true;
    }

    /**
     * Add LTL checker button to existing verification section
     */
    addLTLButtonToVerificationSection() {
        const verificationSection = document.querySelector('#verification-section .section-content');
        if (!verificationSection) return;

        const ltlButtonHTML = `
            <div style="margin-top: 15px; padding-top: 15px; border-top: 1px solid #434C5E;">
                <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">
                    Verify Linear Temporal Logic properties on finite traces (LTL_f) using the integrated LTL parser.
                </p>
                <button id="btn-verify-ltl" class="ltl-verify-button">
                    <span class="ltl-btn-icon">📝</span>
                    LTL Model Checking
                </button>
            </div>
        `;

        verificationSection.insertAdjacentHTML('beforeend', ltlButtonHTML);

        const ltlButton = document.querySelector('#btn-verify-ltl');
        ltlButton.addEventListener('click', () => this.openLTLModal());
    }

    /**
     * Create the enhanced LTL formula editor modal
     */
    createLTLModal() {
        const modal = document.createElement('div');
        modal.id = 'ltl-verification-modal';
        modal.className = 'ltl-modal';
        modal.innerHTML = `
            <div class="ltl-modal-content">
                <div class="ltl-modal-header">
                    <h2>
                        <span>📝</span>
                        Enhanced LTL Model Checking for Data Petri Nets
                    </h2>
                    <button class="ltl-close-btn" id="close-ltl-modal">×</button>
                </div>
                <div class="ltl-modal-body">
                    
                    <!-- Algorithm Info -->
                    <div class="ltl-algorithm-info">
                        <h4>🔬 Algorithm: Enhanced Data-Aware LTL_f Verification</h4>
                        <p>
                            Uses the integrated LTL parser with full support for temporal operators,
                            data constraints, and proper Büchi automaton construction.
                        </p>
                    </div>

                    <!-- Formula Editor Section -->
                    <div class="ltl-editor-section">
                        <div class="ltl-section-header">
                            <h3>📋 LTL_f Formula Editor (Enhanced)</h3>
                            <div class="ltl-formula-help-toggle">
                                <button id="toggle-ltl-help" class="ltl-help-button">❓ Syntax Help</button>
                            </div>
                        </div>
                        
                        <div class="ltl-formula-input-container">
                            <label for="ltl-formula-input">Enter LTL_f Formula:</label>
                            <textarea 
                                id="ltl-formula-input" 
                                class="ltl-formula-textarea"
                                placeholder="Example: G (balance >= 0) && F (status = |completed|)"
                                rows="3"
                            ></textarea>
                            <div id="ltl-formula-validation" class="ltl-validation-message"></div>
                        </div>

                        <!-- Enhanced Syntax Help Panel -->
                        <div id="ltl-help-panel" class="ltl-help-panel" style="display: none;">
                            <h4>Enhanced LTL_f Syntax Reference</h4>
                            <div class="ltl-help-grid">
                                <div class="ltl-help-category">
                                    <h5>Temporal Operators:</h5>
                                    <ul>
                                        <li><code>F φ</code> or <code>eventually φ</code> - Eventually φ</li>
                                        <li><code>G φ</code> or <code>globally φ</code> - Always φ</li>
                                        <li><code>X φ</code> or <code>next φ</code> - Next φ</li>
                                        <li><code>φ U ψ</code> or <code>φ until ψ</code> - φ Until ψ</li>
                                        <li><code>φ W ψ</code> or <code>φ weak-until ψ</code> - φ Weak Until ψ</li>
                                        <li><code>φ R ψ</code> or <code>φ weak-release ψ</code> - φ Release ψ</li>
                                        <li><code>φ M ψ</code> or <code>φ strong-release ψ</code> - φ Strong Release ψ</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Logical Operators:</h5>
                                    <ul>
                                        <li><code>φ && ψ</code> or <code>φ and ψ</code> - AND</li>
                                        <li><code>φ || ψ</code> or <code>φ or ψ</code> - OR</li>
                                        <li><code>φ xor ψ</code> or <code>φ ^ ψ</code> - XOR</li>
                                        <li><code>!φ</code> or <code>not φ</code> - NOT</li>
                                        <li><code>φ -> ψ</code> or <code>φ implies ψ</code> - Implies</li>
                                        <li><code>φ <-> ψ</code> or <code>φ iff ψ</code> - Equivalence</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Data Constraints:</h5>
                                    <ul>
                                        <li><code>|variable > 5|</code> - Atom syntax</li>
                                        <li><code>|balance >= 100|</code> - Comparison</li>
                                        <li><code>|status = "done"|</code> - String equality</li>
                                        <li><code>place_name</code> - Place is marked</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Let Expressions:</h5>
                                    <ul>
                                        <li><code>let x = |balance > 0| in G x</code></li>
                                        <li><code>let safe = |balance >= 0| in safe U |status = "done"|</code></li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Complex Examples:</h5>
                                    <ul>
                                        <li><code>G (|balance >= 0|)</code> - Balance always non-negative</li>
                                        <li><code>start -> F end</code> - If start then eventually end</li>
                                        <li><code>F (|amount > 100| && completed)</code> - Eventually high amount and completed</li>
                                        <li><code>|request| U (|grant| || |deny|)</code> - Request until grant or deny</li>
                                    </ul>
                                </div>
                            </div>
                        </div>

                        <!-- Available Elements Section -->
                        <div class="ltl-available-elements">
                            <h4>Available Elements:</h4>
                            <div class="ltl-elements-grid">
                                <div class="ltl-element-category">
                                    <h5>Places:</h5>
                                    <div id="ltl-places-list" class="ltl-element-list">
                                        <!-- Dynamically populated -->
                                    </div>
                                </div>
                                <div class="ltl-element-category">
                                    <h5>Data Variables:</h5>
                                    <div id="ltl-variables-list" class="ltl-element-list">
                                        <!-- Dynamically populated -->
                                    </div>
                                </div>
                            </div>
                        </div>
                    </div>

                    <!-- Verification Controls -->
                    <div class="ltl-controls-section">
                        <div class="ltl-button-group">
                            <button id="btn-validate-ltl" class="ltl-secondary-button">
                                🔍 Validate Formula
                            </button>
                            <button id="btn-start-ltl-verification" class="ltl-primary-button" disabled>
                                ▶️ Start Verification
                            </button>
                        </div>
                    </div>

                    <!-- Results Section -->
                    <div id="ltl-results-section" class="ltl-results-section" style="display: none;">
                        <div id="ltl-verification-progress" class="ltl-progress-container">
                            <!-- Progress bar will be shown here during verification -->
                        </div>
                        <div id="ltl-verification-results" class="ltl-results-container">
                            <!-- Results will be shown here -->
                        </div>
                    </div>
                </div>
            </div>
        `;

        document.body.appendChild(modal);
        this.setupLTLModalEventHandlers();
    }

    /**
     * Setup event handlers for the LTL modal
     */
    setupLTLModalEventHandlers() {
        const closeBtn = document.querySelector('#close-ltl-modal');
        const modal = document.querySelector('#ltl-verification-modal');
        
        closeBtn.addEventListener('click', () => this.closeLTLModal());
        modal.addEventListener('click', (e) => {
            if (e.target === modal) this.closeLTLModal();
        });

        const helpToggle = document.querySelector('#toggle-ltl-help');
        const helpPanel = document.querySelector('#ltl-help-panel');
        helpToggle.addEventListener('click', () => {
            const isVisible = helpPanel.style.display !== 'none';
            helpPanel.style.display = isVisible ? 'none' : 'block';
            helpToggle.textContent = isVisible ? '❓ Syntax Help' : '❌ Hide Help';
        });

        const formulaInput = document.querySelector('#ltl-formula-input');
        formulaInput.addEventListener('input', () => this.validateLTLFormula());

        const validateBtn = document.querySelector('#btn-validate-ltl');
        validateBtn.addEventListener('click', () => this.validateLTLFormula(true));

        const startBtn = document.querySelector('#btn-start-ltl-verification');
        startBtn.addEventListener('click', () => this.startLTLVerification());

        document.addEventListener('click', (e) => {
            if (e.target.classList.contains('ltl-element-tag')) {
                this.insertElementIntoFormula(e.target.textContent);
            }
        });
    }

    /**
     * Open the LTL modal and populate available elements
     */
    openLTLModal() {
        const modal = document.querySelector('#ltl-verification-modal');
        modal.classList.add('show');
        
        this.populateAvailableElements();
        this.resetLTLModal();
        
        setTimeout(() => {
            document.querySelector('#ltl-formula-input').focus();
        }, 100);
    }

    /**
     * Close the LTL modal
     */
    closeLTLModal() {
        const modal = document.querySelector('#ltl-verification-modal');
        modal.classList.remove('show');
    }

    /**
     * Reset the modal to initial state
     */
    resetLTLModal() {
        document.querySelector('#ltl-formula-input').value = '';
        document.querySelector('#ltl-formula-validation').innerHTML = '';
        document.querySelector('#ltl-results-section').style.display = 'none';
        document.querySelector('#btn-start-ltl-verification').disabled = true;
        this.ltlFormula = '';
        this.ltlAST = null;
        this.constraints.clear();
    }

    /**
     * Populate available elements (places and variables)
     */
    populateAvailableElements() {
        const placesContainer = document.querySelector('#ltl-places-list');
        const variablesContainer = document.querySelector('#ltl-variables-list');
        
        placesContainer.innerHTML = '';
        variablesContainer.innerHTML = '';

        // Add places
        for (const [id, place] of this.app.api.petriNet.places) {
            const placeTag = document.createElement('span');
            placeTag.className = 'ltl-element-tag ltl-place-tag';
            placeTag.textContent = place.label;
            placeTag.title = `Click to insert place "${place.label}"`;
            placesContainer.appendChild(placeTag);
        }

        // Add data variables with atom syntax
        if (this.app.api.petriNet.dataVariables) {
            for (const [id, variable] of this.app.api.petriNet.dataVariables) {
                const varTag = document.createElement('span');
                varTag.className = 'ltl-element-tag ltl-variable-tag';
                varTag.textContent = `|${variable.name}|`;
                varTag.title = `Click to insert variable "${variable.name}" as atom`;
                variablesContainer.appendChild(varTag);
            }
        }

        if (placesContainer.children.length === 0) {
            placesContainer.innerHTML = '<span class="ltl-no-elements">No places available</span>';
        }
        if (variablesContainer.children.length === 0) {
            variablesContainer.innerHTML = '<span class="ltl-no-elements">No data variables available</span>';
        }
    }

    /**
     * Insert an element into the formula at cursor position
     */
    insertElementIntoFormula(elementName) {
        const textarea = document.querySelector('#ltl-formula-input');
        const start = textarea.selectionStart;
        const end = textarea.selectionEnd;
        const text = textarea.value;
        
        const before = text.substring(0, start);
        const after = text.substring(end);
        
        textarea.value = before + elementName + after;
        textarea.focus();
        textarea.setSelectionRange(start + elementName.length, start + elementName.length);
        
        this.validateLTLFormula();
    }

    /**
     * Enhanced LTL formula validation using the integrated LTL parser
     */
    validateLTLFormula(showDetails = false) {
        const formulaInput = document.querySelector('#ltl-formula-input');
        const validationDiv = document.querySelector('#ltl-formula-validation');
        const startBtn = document.querySelector('#btn-start-ltl-verification');
        
        const formula = formulaInput.value.trim();
        
        if (!formula) {
            validationDiv.innerHTML = '';
            startBtn.disabled = true;
            return false;
        }

        try {
            // Use the integrated LTL parser
            const parser = new EnhancedLTLParser(this.getAvailableAtoms());
            const result = parser.parse(formula);
            
            if (result.valid) {
                this.ltlFormula = formula;
                this.ltlAST = result.ast;
                this.constraints = new Set(result.constraints);
                
                if (showDetails) {
                    validationDiv.innerHTML = `
                        <div class="ltl-validation-success">
                            ✅ Formula is valid!
                            <div class="ltl-validation-details">
                                <strong>Parsed structure:</strong> ${result.structure || 'Valid LTL_f formula'}
                                ${result.constraints.length > 0 ? 
                                    `<br><strong>Data constraints:</strong> ${result.constraints.join(', ')}` : 
                                    ''}
                                <br><strong>Temporal operators:</strong> ${result.temporalOps || 'None'}
                            </div>
                        </div>
                    `;
                } else {
                    validationDiv.innerHTML = '<div class="ltl-validation-success">✅ Valid formula</div>';
                }
                
                startBtn.disabled = false;
                return true;
            } else {
                validationDiv.innerHTML = `
                    <div class="ltl-validation-error">
                        ❌ ${result.error}
                        ${result.suggestion ? `<br><strong>Suggestion:</strong> ${result.suggestion}` : ''}
                    </div>
                `;
                startBtn.disabled = true;
                return false;
            }
        } catch (error) {
            validationDiv.innerHTML = `
                <div class="ltl-validation-error">
                    ❌ Parse error: ${error.message}
                </div>
            `;
            startBtn.disabled = true;
            return false;
        }
    }

    /**
     * Get available atomic propositions for the parser
     */
    getAvailableAtoms() {
        const atoms = [];
        
        // Add place names
        for (const [id, place] of this.app.api.petriNet.places) {
            atoms.push(place.label);
        }
        
        // Add data variable names (they'll be used in |variable| syntax)
        if (this.app.api.petriNet.dataVariables) {
            for (const [id, variable] of this.app.api.petriNet.dataVariables) {
                atoms.push(variable.name);
            }
        }
        
        return atoms;
    }

    /**
     * Start enhanced LTL verification process
     */
    async startLTLVerification() {
        const resultsSection = document.querySelector('#ltl-results-section');
        const progressContainer = document.querySelector('#ltl-verification-progress');
        const resultsContainer = document.querySelector('#ltl-verification-results');
        const startBtn = document.querySelector('#btn-start-ltl-verification');
        
        resultsSection.style.display = 'block';
        startBtn.disabled = true;
        startBtn.innerHTML = '<span class="ltl-spinner"></span> Verifying...';
        
        progressContainer.innerHTML = this.createLTLProgressHTML();
        resultsContainer.innerHTML = '';
        
        try {
            const verifier = new EnhancedLTLVerifier(this.app.api.petriNet, this.ltlAST);
            await verifier.verify((progress, step) => {
                this.updateLTLProgress(progress, step);
            }).then((result) => {
                progressContainer.style.display = 'none';
                resultsContainer.innerHTML = this.createLTLResultsHTML(result);
                console.log('LTL Verification Result:', result);
            });
            
            
        } catch (error) {
            console.error('LTL Verification error:', error);
            progressContainer.style.display = 'none';
            resultsContainer.innerHTML = this.createLTLErrorHTML(error);
        } finally {
            startBtn.disabled = false;
            startBtn.innerHTML = '▶️ Start Verification';
        }
    }

    /**
     * Create progress HTML for LTL verification
     */
    createLTLProgressHTML() {
        return `
            <div class="ltl-progress-header">
                <h4>🔄 Enhanced LTL_f Model Checking in Progress</h4>
                <p>Checking formula: <code>${this.ltlFormula}</code></p>
            </div>
            <div class="ltl-progress-bar-container">
                <div class="ltl-progress-bar">
                    <div class="ltl-progress-fill" id="ltl-progress-fill" style="width: 0%"></div>
                </div>
                <div class="ltl-progress-step" id="ltl-progress-step">
                    Initializing verification...
                </div>
            </div>
        `;
    }

    /**
     * Update progress during LTL verification
     */
    updateLTLProgress(progress, step) {
        const progressFill = document.querySelector('#ltl-progress-fill');
        const progressStep = document.querySelector('#ltl-progress-step');
        
        if (progressFill) progressFill.style.width = `${progress}%`;
        if (progressStep) progressStep.textContent = step;
    }

    /**
     * Create results HTML for LTL verification
     */
    createLTLResultsHTML(result) {
        const satisfied = result.satisfied;
        const statusClass = satisfied ? 'ltl-result-satisfied' : 'ltl-result-violated';
        const statusIcon = satisfied ? '✅' : '❌';
        const statusText = satisfied ? 'Formula SATISFIED' : 'Formula VIOLATED';
        
        let html = `
            <div class="ltl-result-header ${statusClass}">
                <div class="ltl-result-icon">${statusIcon}</div>
                <div class="ltl-result-summary">
                    <div class="ltl-result-status">${statusText}</div>
                    <div class="ltl-result-formula">Formula: <code>${this.ltlFormula}</code></div>
                </div>
            </div>
            
            <div class="ltl-result-details">
                <div class="ltl-result-explanation">
                    ${satisfied ? 
                        'The LTL_f formula is satisfied by all execution traces of the Data Petri Net.' :
                        'The LTL_f formula is violated. A counterexample trace has been found.'}
                </div>
        `;
        
        if (!satisfied && result.counterexample) {
            html += `
                <div class="ltl-counterexample">
                    <h4>🔍 Counterexample Trace:</h4>
                    <div class="ltl-trace">
                        ${this.formatTrace(result.counterexample)}
                    </div>
                </div>
            `;
        }
        
        if (result.statistics) {
            html += `
                <div class="ltl-statistics">
                    <h4>📊 Verification Statistics:</h4>
                    <div class="ltl-stats-grid">
                        <div class="ltl-stat">
                            <span class="ltl-stat-label">States explored:</span>
                            <span class="ltl-stat-value">${result.statistics.statesExplored}</span>
                        </div>
                        <div class="ltl-stat">
                            <span class="ltl-stat-label">Transitions fired:</span>
                            <span class="ltl-stat-value">${result.statistics.transitionsFired}</span>
                        </div>
                        <div class="ltl-stat">
                            <span class="ltl-stat-label">Automaton states:</span>
                            <span class="ltl-stat-value">${result.statistics.automatonStates}</span>
                        </div>
                        <div class="ltl-stat">
                            <span class="ltl-stat-label">Execution time:</span>
                            <span class="ltl-stat-value">${result.executionTime}ms</span>
                        </div>
                    </div>
                </div>
            `;
        }
        
        html += '</div>';
        return html;
    }

    /**
     * Format a trace for display
     */
    formatTrace(trace) {
        return trace.map((step, index) => {
            return `
                <div class="ltl-trace-step">
                    <div class="ltl-trace-step-number">${index + 1}</div>
                    <div class="ltl-trace-step-content">
                        <div class="ltl-trace-action">${step.action || 'Initial state'}</div>
                        <div class="ltl-trace-state">
                            ${step.marking ? `Marking: ${this.formatMarking(step.marking)}` : ''}
                            ${step.dataValuation ? `<br>Data: ${this.formatDataValuation(step.dataValuation)}` : ''}
                        </div>
                    </div>
                </div>
            `;
        }).join('');
    }

    /**
     * Format marking for display
     */
    formatMarking(marking) {
        return Object.entries(marking)
            .filter(([place, tokens]) => tokens > 0)
            .map(([place, tokens]) => `${place}(${tokens})`)
            .join(', ') || 'empty';
    }

    /**
     * Format data valuation for display
     */
    formatDataValuation(valuation) {
        if (typeof valuation !== 'object' || valuation === null) {
            return String(valuation); // Fallback for unexpected types
        }
        return Object.entries(valuation)
            .map(([variable, value]) => {
                const displayValue = typeof value === 'string' ? `"${value}"` : value;
                return `${variable} = ${displayValue}`;
            })
            .join(', ') || '(no data)';
    }

    /**
     * Create error HTML for LTL verification
     */
    createLTLErrorHTML(error) {
        return `
            <div class="ltl-result-header ltl-result-error">
                <div class="ltl-result-icon">⚠️</div>
                <div class="ltl-result-summary">
                    <div class="ltl-result-status">Verification Error</div>
                    <div class="ltl-result-formula">An error occurred during verification</div>
                </div>
            </div>
            
            <div class="ltl-error-details">
                <h4>Error Details:</h4>
                <pre class="ltl-error-message">${error.message}</pre>
                ${error.stack ? `<details><summary>Stack trace</summary><pre>${error.stack}</pre></details>` : ''}
            </div>
        `;
    }

    /**
     * Inject CSS styles for LTL verification components
     */
    injectStyles() {
        if (document.getElementById('ltl-verification-styles')) return;

        const style = document.createElement('style');
        style.id = 'ltl-verification-styles';
        style.textContent = `
            /* Enhanced LTL Verification Extension Styles */
            .ltl-verify-button {
                background-color: #81A1C1 !important;
                color: #ECEFF4 !important;
                width: 100%;
                padding: 12px;
                font-size: 16px;
                font-weight: 500;
                display: flex;
                align-items: center;
                justify-content: center;
                gap: 8px;
                border-radius: 6px;
                border: none;
                cursor: pointer;
                transition: all 0.2s;
            }

            .ltl-verify-button:hover {
                background-color: #88C0D0 !important;
                transform: translateY(-1px);
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.2);
            }

            /* Enhanced LTL Modal Styles */
            .ltl-modal {
                position: fixed;
                top: 0;
                left: 0;
                right: 0;
                bottom: 0;
                background-color: rgba(0, 0, 0, 0.85);
                z-index: 3000;
                display: none;
                align-items: center;
                justify-content: center;
                padding: 20px;
                box-sizing: border-box;
                backdrop-filter: blur(4px);
            }

            .ltl-modal.show {
                display: flex;
            }

            .ltl-modal-content {
                background-color: #3B4252;
                border-radius: 12px;
                box-shadow: 0 20px 60px rgba(0, 0, 0, 0.5);
                width: 100%;
                max-width: 1000px;
                max-height: 95vh;
                overflow-y: auto;
                position: relative;
                border: 2px solid #4C566A;
            }

            .ltl-modal-header {
                display: flex;
                justify-content: space-between;
                align-items: center;
                padding: 25px;
                border-bottom: 2px solid #434C5E;
                background: linear-gradient(135deg, #4C566A, #5E81AC);
                border-radius: 10px 10px 0 0;
            }

            .ltl-modal-header h2 {
                margin: 0;
                color: #E5E9F0;
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 20px;
                font-weight: 600;
            }

            .ltl-close-btn {
                background: none;
                border: none;
                font-size: 28px;
                color: #D8DEE9;
                cursor: pointer;
                padding: 5px;
                width: 40px;
                height: 40px;
                display: flex;
                align-items: center;
                justify-content: center;
                border-radius: 6px;
                transition: all 0.2s;
            }

            .ltl-close-btn:hover {
                color: #ECEFF4;
                background-color: rgba(191, 97, 106, 0.3);
                transform: scale(1.1);
            }

            .ltl-modal-body {
                padding: 25px;
            }

            /* Enhanced Algorithm Info */
            .ltl-algorithm-info {
                background: linear-gradient(135deg, #4C566A, #5E81AC);
                border-radius: 8px;
                padding: 20px;
                margin-bottom: 25px;
                border-left: 4px solid #88C0D0;
                position: relative;
                overflow: hidden;
            }

            .ltl-algorithm-info::before {
                content: '';
                position: absolute;
                top: 0;
                left: 0;
                right: 0;
                bottom: 0;
                background: linear-gradient(45deg, transparent 30%, rgba(255,255,255,0.1) 50%, transparent 70%);
                pointer-events: none;
            }

            .ltl-algorithm-info h4 {
                margin: 0 0 10px 0;
                color: #E5E9F0;
                font-size: 16px;
                font-weight: 600;
            }

            .ltl-algorithm-info p {
                margin: 0;
                color: #D8DEE9;
                line-height: 1.6;
            }

            /* Enhanced Editor Section */
            .ltl-editor-section {
                background-color: #434C5E;
                border-radius: 8px;
                padding: 20px;
                margin-bottom: 20px;
                border: 1px solid #4C566A;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
            }

            .ltl-section-header {
                display: flex;
                justify-content: space-between;
                align-items: center;
                margin-bottom: 20px;
            }

            .ltl-section-header h3 {
                margin: 0;
                color: #E5E9F0;
                font-size: 18px;
                font-weight: 600;
            }

            .ltl-help-button {
                background-color: #5E81AC;
                color: #ECEFF4;
                border: none;
                padding: 8px 15px;
                border-radius: 5px;
                cursor: pointer;
                font-size: 14px;
                font-weight: 500;
                transition: all 0.2s;
            }

            .ltl-help-button:hover {
                background-color: #81A1C1;
                transform: translateY(-1px);
            }

            /* Enhanced Formula Input */
            .ltl-formula-input-container {
                margin-bottom: 20px;
            }

            .ltl-formula-input-container label {
                display: block;
                margin-bottom: 8px;
                font-weight: 600;
                color: #E5E9F0;
                font-size: 15px;
            }

            .ltl-formula-textarea {
                width: 100%;
                min-height: 100px;
                padding: 15px;
                border: 2px solid #4C566A;
                border-radius: 6px;
                background-color: #2E3440;
                color: #E5E9F0;
                font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
                font-size: 16px;
                line-height: 1.5;
                resize: vertical;
                transition: all 0.2s;
                box-sizing: border-box;
            }

            .ltl-formula-textarea:focus {
                outline: none;
                border-color: #88C0D0;
                box-shadow: 0 0 0 3px rgba(136, 192, 208, 0.3);
                background-color: #242933;
            }

            /* Enhanced Validation Messages */
            .ltl-validation-message {
                margin-top: 12px;
                min-height: 20px;
            }

            .ltl-validation-success {
                color: #A3BE8C;
                background: linear-gradient(135deg, rgba(163, 190, 140, 0.15), rgba(163, 190, 140, 0.05));
                padding: 15px;
                border-radius: 6px;
                border-left: 4px solid #A3BE8C;
                font-weight: 500;
            }

            .ltl-validation-error {
                color: #BF616A;
                background: linear-gradient(135deg, rgba(191, 97, 106, 0.15), rgba(191, 97, 106, 0.05));
                padding: 15px;
                border-radius: 6px;
                border-left: 4px solid #BF616A;
                font-weight: 500;
            }

            .ltl-validation-details {
                margin-top: 10px;
                font-size: 13px;
                opacity: 0.9;
                line-height: 1.4;
            }

            /* Enhanced Help Panel */
            .ltl-help-panel {
                background-color: #2E3440;
                border-radius: 8px;
                padding: 20px;
                margin-top: 15px;
                border: 1px solid #4C566A;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
            }

            .ltl-help-panel h4 {
                margin: 0 0 15px 0;
                color: #88C0D0;
                font-size: 16px;
                font-weight: 600;
            }

            .ltl-help-grid {
                display: grid;
                grid-template-columns: repeat(auto-fit, minmax(250px, 1fr));
                gap: 25px;
            }

            .ltl-help-category h5 {
                margin: 0 0 12px 0;
                color: #E5E9F0;
                font-size: 14px;
                font-weight: 600;
                border-bottom: 2px solid #434C5E;
                padding-bottom: 5px;
            }

            .ltl-help-category ul {
                margin: 0;
                padding-left: 0;
                list-style: none;
            }

            .ltl-help-category li {
                margin-bottom: 10px;
                font-size: 13px;
                color: #D8DEE9;
                line-height: 1.4;
            }

            .ltl-help-category code {
                background-color: #434C5E;
                color: #88C0D0;
                padding: 3px 8px;
                border-radius: 4px;
                font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
                font-weight: 600;
            }

            /* Enhanced Available Elements */
            .ltl-available-elements {
                background-color: #2E3440;
                border-radius: 8px;
                padding: 18px;
                border: 1px solid #4C566A;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
            }

            .ltl-available-elements h4 {
                margin: 0 0 15px 0;
                color: #E5E9F0;
                font-size: 15px;
                font-weight: 600;
            }

            .ltl-elements-grid {
                display: grid;
                grid-template-columns: 1fr 1fr;
                gap: 20px;
            }

            .ltl-element-category h5 {
                margin: 0 0 12px 0;
                color: #88C0D0;
                font-size: 13px;
                text-transform: uppercase;
                letter-spacing: 0.5px;
                font-weight: 600;
            }

            .ltl-element-list {
                display: flex;
                flex-wrap: wrap;
                gap: 8px;
            }

            .ltl-element-tag {
                background-color: #5E81AC;
                color: #ECEFF4;
                padding: 6px 12px;
                border-radius: 20px;
                font-size: 12px;
                font-weight: 500;
                cursor: pointer;
                transition: all 0.2s;
                border: 1px solid transparent;
            }

            .ltl-element-tag:hover {
                transform: translateY(-2px);
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.2);
            }

            .ltl-place-tag {
                background: linear-gradient(135deg, #A3BE8C, #D08770);
            }

            .ltl-place-tag:hover {
                background: linear-gradient(135deg, #B4CFB0, #EBCB8B);
            }

            .ltl-variable-tag {
                background: linear-gradient(135deg, #EBCB8B, #D08770);
                color: #2E3440;
            }

            .ltl-variable-tag:hover {
                background: linear-gradient(135deg, #F0D49C, #E8B4B8);
            }

            .ltl-no-elements {
                color: #4C566A;
                font-style: italic;
                font-size: 12px;
            }

            /* Enhanced Controls Section */
            .ltl-controls-section {
                margin: 25px 0;
            }

            .ltl-button-group {
                display: flex;
                gap: 15px;
                justify-content: center;
            }

            .ltl-primary-button {
                background: linear-gradient(135deg, #A3BE8C, #88C0D0);
                color: #2E3440;
                border: none;
                padding: 15px 30px;
                border-radius: 8px;
                font-size: 16px;
                font-weight: 600;
                cursor: pointer;
                transition: all 0.2s;
                display: flex;
                align-items: center;
                gap: 8px;
            }

            .ltl-primary-button:hover:not(:disabled) {
                background: linear-gradient(135deg, #B4CFB0, #A3D0E4);
                transform: translateY(-2px);
                box-shadow: 0 6px 20px rgba(0, 0, 0, 0.3);
            }

            .ltl-primary-button:disabled {
                background-color: #4C566A;
                color: #D8DEE9;
                cursor: not-allowed;
                transform: none;
                box-shadow: none;
                opacity: 0.6;
            }

            .ltl-secondary-button {
                background: linear-gradient(135deg, #5E81AC, #81A1C1);
                color: #ECEFF4;
                border: none;
                padding: 12px 25px;
                border-radius: 6px;
                font-size: 14px;
                font-weight: 500;
                cursor: pointer;
                transition: all 0.2s;
            }

            .ltl-secondary-button:hover {
                background: linear-gradient(135deg, #81A1C1, #88C0D0);
                transform: translateY(-1px);
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.2);
            }

            /* Enhanced Results Section */
            .ltl-results-section {
                background-color: #434C5E;
                border-radius: 8px;
                padding: 20px;
                margin-top: 20px;
                border: 1px solid #4C566A;
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.1);
            }

            /* Enhanced Progress */
            .ltl-progress-container {
                margin-bottom: 20px;
            }

            .ltl-progress-header h4 {
                margin: 0 0 10px 0;
                color: #88C0D0;
                font-size: 16px;
                font-weight: 600;
            }

            .ltl-progress-header p {
                margin: 0 0 15px 0;
                color: #D8DEE9;
            }

            .ltl-progress-bar-container {
                margin-top: 15px;
            }

            .ltl-progress-bar {
                width: 100%;
                height: 12px;
                background-color: #2E3440;
                border-radius: 6px;
                overflow: hidden;
                border: 1px solid #4C566A;
                box-shadow: inset 0 2px 4px rgba(0, 0, 0, 0.1);
            }

            .ltl-progress-fill {
                height: 100%;
                background: linear-gradient(90deg, #88C0D0, #A3BE8C, #EBCB8B);
                border-radius: 6px;
                transition: width 0.3s ease;
                box-shadow: 0 2px 4px rgba(0, 0, 0, 0.1);
            }

            .ltl-progress-step {
                color: #D8DEE9;
                font-size: 14px;
                margin-top: 12px;
                text-align: center;
                font-weight: 500;
            }

            /* Enhanced Spinner */
            .ltl-spinner {
                display: inline-block;
                width: 16px;
                height: 16px;
                border: 2px solid rgba(46, 52, 64, 0.3);
                border-radius: 50%;
                border-top-color: #E5E9F0;
                animation: ltl-spin 1s ease-in-out infinite;
            }

            @keyframes ltl-spin {
                to { transform: rotate(360deg); }
            }

            /* Enhanced Result Display */
            .ltl-result-header {
                display: flex;
                align-items: center;
                gap: 20px;
                padding: 25px;
                border-radius: 8px;
                margin-bottom: 20px;
                position: relative;
                overflow: hidden;
            }

            .ltl-result-satisfied {
                background: linear-gradient(135deg, rgba(163, 190, 140, 0.2), rgba(163, 190, 140, 0.1));
                border: 2px solid #A3BE8C;
            }

            .ltl-result-violated {
                background: linear-gradient(135deg, rgba(191, 97, 106, 0.2), rgba(191, 97, 106, 0.1));
                border: 2px solid #BF616A;
            }

            .ltl-result-error {
                background: linear-gradient(135deg, rgba(208, 135, 112, 0.2), rgba(208, 135, 112, 0.1));
                border: 2px solid #D08770;
            }

            .ltl-result-icon {
                font-size: 36px;
            }

            .ltl-result-status {
                font-size: 20px;
                font-weight: 700;
                color: #E5E9F0;
            }

            .ltl-result-formula {
                font-size: 14px;
                color: #D8DEE9;
                margin-top: 5px;
            }

            .ltl-result-formula code {
                background-color: rgba(46, 52, 64, 0.5);
                padding: 4px 8px;
                border-radius: 4px;
                font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            }

            .ltl-result-details {
                color: #D8DEE9;
                line-height: 1.6;
            }

            .ltl-result-explanation {
                background-color: #2E3440;
                padding: 18px;
                border-radius: 6px;
                margin-bottom: 20px;
                border-left: 4px solid #88C0D0;
                font-weight: 500;
            }

            /* Enhanced Counterexample */
            .ltl-counterexample {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 18px;
                margin-bottom: 20px;
                border-left: 4px solid #BF616A;
            }

            .ltl-counterexample h4 {
                margin: 0 0 15px 0;
                color: #BF616A;
                font-weight: 600;
            }

            .ltl-trace {
                background-color: #434C5E;
                border-radius: 6px;
                padding: 12px;
                max-height: 350px;
                overflow-y: auto;
            }

            .ltl-trace-step {
                display: flex;
                align-items: flex-start;
                gap: 15px;
                padding: 12px;
                border-bottom: 1px solid #4C566A;
                transition: all 0.2s;
            }

            .ltl-trace-step:hover {
                background-color: rgba(94, 129, 172, 0.1);
            }

            .ltl-trace-step:last-child {
                border-bottom: none;
            }

            .ltl-trace-step-number {
                background: linear-gradient(135deg, #5E81AC, #81A1C1);
                color: #ECEFF4;
                width: 30px;
                height: 30px;
                border-radius: 50%;
                display: flex;
                align-items: center;
                justify-content: center;
                font-size: 12px;
                font-weight: 600;
                flex-shrink: 0;
            }

            .ltl-trace-action {
                font-weight: 600;
                color: #88C0D0;
                margin-bottom: 5px;
            }

            .ltl-trace-state {
                font-size: 13px;
                color: #D8DEE9;
                line-height: 1.4;
            }

            /* Enhanced Statistics */
            .ltl-statistics {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 18px;
                border-left: 4px solid #EBCB8B;
            }

            .ltl-statistics h4 {
                margin: 0 0 15px 0;
                color: #EBCB8B;
                font-weight: 600;
            }

            .ltl-stats-grid {
                display: grid;
                grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
                gap: 15px;
            }

            .ltl-stat {
                display: flex;
                justify-content: space-between;
                align-items: center;
                padding: 10px 0;
                border-bottom: 1px solid #434C5E;
            }

            .ltl-stat:last-child {
                border-bottom: none;
            }

            .ltl-stat-label {
                color: #D8DEE9;
                font-size: 13px;
                font-weight: 500;
            }

            .ltl-stat-value {
                color: #E5E9F0;
                font-weight: 700;
                font-size: 14px;
            }

            /* Enhanced Error Details */
            .ltl-error-details {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 18px;
                border-left: 4px solid #BF616A;
            }

            .ltl-error-details h4 {
                margin: 0 0 15px 0;
                color: #BF616A;
                font-weight: 600;
            }

            .ltl-error-message {
                background-color: #434C5E;
                color: #E5E9F0;
                padding: 15px;
                border-radius: 6px;
                overflow-x: auto;
                font-size: 13px;
                margin: 0;
                white-space: pre-wrap;
                line-height: 1.4;
            }

            /* Responsive Design */
            @media (max-width: 768px) {
                .ltl-modal-content {
                    max-width: 95vw;
                    margin: 10px;
                }

                .ltl-elements-grid {
                    grid-template-columns: 1fr;
                }

                .ltl-help-grid {
                    grid-template-columns: 1fr;
                }

                .ltl-button-group {
                    flex-direction: column;
                }

                .ltl-stats-grid {
                    grid-template-columns: 1fr;
                }
            }
        `;

        document.head.appendChild(style);
    }
}

/**
 * Enhanced LTL Parser that integrates with the existing LTL infrastructure
 */
class EnhancedLTLParser {
    constructor(availableAtoms = []) {
        this.availableAtoms = availableAtoms;
        this.constraints = [];
        this.temporalOps = [];
    }

    /**
     * Parse an LTL_f formula using the integrated LTL infrastructure
     */
    parse(formula) {
        this.constraints = [];
        this.temporalOps = [];
        
        try {
            // Use the existing LTL reader
            const ltlAST = this.readExpression(formula);
            
            // Validate the AST
            const validation = this.validateAST(ltlAST);
            if (!validation.valid) {
                return validation;
            }
            
            // Collect information about the formula
            this.collectFormulaInfo(ltlAST);
            
            return {
                valid: true,
                ast: ltlAST,
                structure: this.astToString(ltlAST),
                constraints: this.constraints,
                temporalOps: this.temporalOps.join(', ') || 'None'
            };
            
        } catch (error) {
            return {
                valid: false,
                error: error.message,
                suggestion: this.getSuggestion(error.message)
            };
        }
    }

    /**
     * Read expression using the existing LTL infrastructure
     */
    readExpression(input) {
        // This would use the existing readExpression function
        // For now, we'll create a simplified AST
        return this.parseToAST(input);
    }

    /**
     * Simplified AST parser for demonstration
     */
    parseToAST(formula) {
        // This is a simplified version - in practice, you'd use the full LTL parser
        const tokens = this.tokenize(formula);
        return this.parseTokens(tokens);
    }

    /**
     * Tokenize the formula
     */
    tokenize(formula) {
        // Enhanced tokenization that handles atoms with |variable| syntax
        const tokenRegex = /(\|[^|]+\||G|F|X|U|W|R|M|&&|and|\|\||or|!|not|->|implies|<->|iff|\(|\)|[a-zA-Z_][a-zA-Z0-9_]*)/g;
        const tokens = [];
        let match;
        
        while ((match = tokenRegex.exec(formula)) !== null) {
            tokens.push({
                type: this.getTokenType(match[1]),
                value: match[1],
                position: match.index
            });
        }
        
        return tokens;
    }

    /**
     * Get token type
     */
    getTokenType(value) {
        const temporalOps = ['F', 'G', 'X', 'U', 'W', 'R', 'M'];
        const logicalOps = ['&&', 'and', '||', 'or', '!', 'not', '->', 'implies', '<->', 'iff'];
        
        if (value === '(' || value === ')') return 'PAREN';
        if (temporalOps.includes(value)) return 'TEMPORAL';
        if (logicalOps.includes(value)) return 'LOGICAL';
        if (value.startsWith('|') && value.endsWith('|')) return 'ATOM';
        if (/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(value)) return 'IDENTIFIER';
        
        return 'UNKNOWN';
    }

    /**
     * Parse tokens into AST
     */
    parseTokens(tokens) {
        this.tokens = tokens;
        this.position = 0;
        return this.parseExpression();
    }

    /**
     * Parse expression
     */
    parseExpression() {
        return this.parseImplication();
    }

    /**
     * Parse implication
     */
    parseImplication() {
        let left = this.parseOr();
        
        while (this.peek() && (this.peek().value === '->' || this.peek().value === 'implies')) {
            this.consume();
            const right = this.parseOr();
            left = {
                type: 'LTLImplication',
                operator: '->',
                left,
                right
            };
        }
        
        return left;
    }

    /**
     * Parse OR operations
     */
    parseOr() {
        let left = this.parseAnd();
        
        while (this.peek() && (this.peek().value === '||' || this.peek().value === 'or')) {
            this.consume();
            const right = this.parseAnd();
            left = {
                type: 'LTLDisjunction',
                operator: '||',
                left,
                right
            };
        }
        
        return left;
    }

    /**
     * Parse AND operations
     */
    parseAnd() {
        let left = this.parseUntil();
        
        while (this.peek() && (this.peek().value === '&&' || this.peek().value === 'and')) {
            this.consume();
            const right = this.parseUntil();
            left = {
                type: 'LTLConjunction',
                operator: '&&',
                left,
                right
            };
        }
        
        return left;
    }

    /**
     * Parse Until and other binary temporal operations
     */
    parseUntil() {
        let left = this.parseUnary();
        
        while (this.peek() && ['U', 'W', 'R', 'M'].includes(this.peek().value)) {
            const op = this.consume().value;
            const right = this.parseUnary();
            
            let type;
            switch (op) {
                case 'U': type = 'LTLStrongUntil'; break;
                case 'W': type = 'LTLWeakUntil'; break;
                case 'R': type = 'LTLWeakRelease'; break;
                case 'M': type = 'LTLStrongRelease'; break;
            }
            
            left = {
                type,
                operator: op,
                left,
                right
            };
            
            this.temporalOps.push(op);
        }
        
        return left;
    }

    /**
     * Parse unary operations
     */
    parseUnary() {
        const token = this.peek();
        
        if (token && ['F', 'G', 'X'].includes(token.value)) {
            const op = this.consume().value;
            const operand = this.parseUnary();
            
            let type;
            switch (op) {
                case 'F': type = 'LTLEventually'; break;
                case 'G': type = 'LTLGlobally'; break;
                case 'X': type = 'LTLNext'; break;
            }
            
            this.temporalOps.push(op);
            
            return {
                type,
                operator: op,
                expression: operand
            };
        }
        
        if (token && (token.value === '!' || token.value === 'not')) {
            this.consume();
            const operand = this.parseUnary();
            return {
                type: 'LTLNegation',
                operator: '!',
                expression: operand
            };
        }
        
        return this.parseAtom();
    }

    /**
     * Parse atomic formulas
     */
    parseAtom() {
        const token = this.peek();
        
        if (!token) {
            throw new Error('Unexpected end of formula');
        }
        
        if (token.value === '(') {
            this.consume('(');
            const expr = this.parseExpression();
            this.consume(')');
            return expr;
        }
        
        if (token.type === 'ATOM') {
            const atomValue = this.consume().value;
            // Parse |variable op value| syntax
            const content = atomValue.slice(1, -1); // Remove | |
            
            if (this.isConstraint(content)) {
                this.constraints.push(content);
                return {
                    type: 'LTLAtom',
                    value: content,
                    delimiter: '|'
                };
            } else {
                return {
                    type: 'LTLAtom',
                    value: content,
                    delimiter: '|'
                };
            }
        }
        
        if (token.type === 'IDENTIFIER') {
            const name = this.consume().value;
            return {
                type: 'LTLReference',
                name
            };
        }
        
        throw new Error(`Unexpected token: ${token.value}`);
    }

    /**
     * Check if content is a constraint
     */
    isConstraint(content) {
        return /[<>=!]/.test(content);
    }

    /**
     * Peek at current token
     */
    peek() {
        return this.position < this.tokens.length ? this.tokens[this.position] : null;
    }

    /**
     * Consume current token
     */
    consume(expected = null) {
        const token = this.tokens[this.position];
        
        if (!token) {
            throw new Error('Unexpected end of formula');
        }
        
        if (expected && token.value !== expected) {
            throw new Error(`Expected '${expected}' but got '${token.value}'`);
        }
        
        this.position++;
        return token;
    }

    /**
     * Validate AST
     */
    validateAST(ast) {
        const unknownRefs = [];
        this.collectReferences(ast, unknownRefs);
        
        const invalidRefs = unknownRefs.filter(ref => 
            !this.availableAtoms.includes(ref));
            
        if (invalidRefs.length > 0) {
            return {
                valid: false,
                error: `Unknown references: ${invalidRefs.join(', ')}`,
                suggestion: `Available atoms: ${this.availableAtoms.join(', ')}`
            };
        }
        
        return { valid: true };
    }

    /**
     * Collect references from AST
     */
    collectReferences(ast, refs) {
        if (!ast) return;
        
        if (ast.type === 'LTLReference') {
            if (!refs.includes(ast.name)) {
                refs.push(ast.name);
            }
        } else if (ast.type === 'LTLAtom') {
            // Extract variable names from atom content
            const varMatch = ast.value.match(/^([a-zA-Z_][a-zA-Z0-9_]*)/);
            if (varMatch && !refs.includes(varMatch[1])) {
                refs.push(varMatch[1]);
            }
        } else {
            // Recursively check child nodes
            if (ast.left) this.collectReferences(ast.left, refs);
            if (ast.right) this.collectReferences(ast.right, refs);
            if (ast.expression) this.collectReferences(ast.expression, refs);
        }
    }

    /**
     * Collect formula information
     */
    collectFormulaInfo(ast) {
        if (!ast) return;
        
        if (['LTLEventually', 'LTLGlobally', 'LTLNext', 'LTLStrongUntil', 'LTLWeakUntil', 'LTLWeakRelease', 'LTLStrongRelease'].includes(ast.type)) {
            if (!this.temporalOps.includes(ast.operator)) {
                this.temporalOps.push(ast.operator);
            }
        }
        
        if (ast.type === 'LTLAtom' && this.isConstraint(ast.value)) {
            if (!this.constraints.includes(ast.value)) {
                this.constraints.push(ast.value);
            }
        }
        
        // Recursively check child nodes
        if (ast.left) this.collectFormulaInfo(ast.left);
        if (ast.right) this.collectFormulaInfo(ast.right);
        if (ast.expression) this.collectFormulaInfo(ast.expression);
    }

    /**
     * Convert AST to string
     */
    astToString(ast) {
        if (!ast) return '';
        
        switch (ast.type) {
            case 'LTLAtom':
                return `|${ast.value}|`;
            case 'LTLReference':
                return ast.name;
            case 'LTLConjunction':
                return `(${this.astToString(ast.left)} ∧ ${this.astToString(ast.right)})`;
            case 'LTLDisjunction':
                return `(${this.astToString(ast.left)} ∨ ${this.astToString(ast.right)})`;
            case 'LTLImplication':
                return `(${this.astToString(ast.left)} → ${this.astToString(ast.right)})`;
            case 'LTLStrongUntil':
                return `(${this.astToString(ast.left)} U ${this.astToString(ast.right)})`;
            case 'LTLWeakUntil':
                return `(${this.astToString(ast.left)} W ${this.astToString(ast.right)})`;
            case 'LTLWeakRelease':
                return `(${this.astToString(ast.left)} R ${this.astToString(ast.right)})`;
            case 'LTLStrongRelease':
                return `(${this.astToString(ast.left)} M ${this.astToString(ast.right)})`;
            case 'LTLEventually':
                return `F${this.astToString(ast.expression)}`;
            case 'LTLGlobally':
                return `G${this.astToString(ast.expression)}`;
            case 'LTLNext':
                return `X${this.astToString(ast.expression)}`;
            case 'LTLNegation':
                return `¬${this.astToString(ast.expression)}`;
            default:
                return `[${ast.type}]`;
        }
    }

    /**
     * Get suggestion for errors
     */
    getSuggestion(error) {
        if (error.includes('Unknown references')) {
            return 'Use place names directly or data variables in |variable| syntax. Click elements below to insert them.';
        }
        if (error.includes('Unexpected token')) {
            return 'Check syntax: use F/G/X for temporal ops, &&/|| for logic, |var > 5| for constraints.';
        }
        if (error.includes('Expected')) {
            return 'Check parentheses matching and operator syntax.';
        }
        return 'Refer to syntax help above for correct LTL_f formula structure.';
    }
}

/**
 * Enhanced LTL Verifier with symbolic state-space exploration.
 * This verifier can handle Data Petri Nets with infinite data domains by
 * representing sets of data valuations as logical formulas.
 */
class EnhancedLTLVerifier {
    /**
     * Creates an instance of the symbolic LTL verifier.
     * @param {DataPetriNet} petriNet The Data Petri Net to verify.
     * @param {Object} ltlAST The Abstract Syntax Tree of the LTL formula.
     */
    constructor(petriNet, ltlAST) {
        this.petriNet = petriNet;
        // The LTL formula should be negated for model checking, as we search for a counterexample.
        this.ltlAST = { type: 'LTLNegation', operator: '!', expression: ltlAST };
        this.startTime = 0;
        this.smtSolver = new SMTSolver();
        this.statistics = {
            statesExplored: 0,
            transitionsFired: 0,
            automatonStates: 0,
            productStates: 0
        };
    }

    /**
     * Main verification method that orchestrates the symbolic model checking process.
     * @param {function(number, string): void} progressCallback A function to report progress.
     * @returns {Promise<Object>} A promise that resolves to the verification result.
     */
    async verify(progressCallback) {
        this.startTime = Date.now();
        
        try {
            progressCallback(10, "Analyzing LTL formula structure...");
            // await this.delay(50);
            
            console.log("LTL AST:", JSON.stringify(this.ltlAST, null, 2));
            
            progressCallback(25, "Constructing Büchi automaton for the LTL formula...");
            const automaton = this.constructEnhancedBuchiAutomaton();
            this.statistics.automatonStates = automaton.states.size;
            
            console.log("Büchi Automaton:", JSON.stringify(automaton, null, 2));

            progressCallback(50, "Building symbolic product automaton with the Petri net...");
            const product = this._constructSymbolicProductAutomaton(automaton);
            this.statistics.productStates = product.states.size;
            
            console.log("Product Automaton:", JSON.stringify(product, null, 2));
            
            progressCallback(75, "Checking for counterexamples in the product automaton...");
            const result = this._checkAcceptance(product);
            
            console.log("Verification Result:", JSON.stringify(result, null, 2));

            progressCallback(100, "Verification complete!");
            // await this.delay(50);
            
            const executionTime = Date.now() - this.startTime;
        
            return {
                // If a counterexample to the negated formula is found, the original formula is violated.
                satisfied: !result.hasCounterexample,
                counterexample: result.hasCounterexample ? this.buildCounterexample(result.witness, product) : null,
                statistics: this.statistics,
                executionTime,
                debugObject: {
                    ltlAST: this.ltlAST,
                    automaton:automaton,
                    productAutomaton: product,
                    result: result
                }
            };
            
        } catch (error) {
            console.error('Enhanced LTL Verification error:', error);
            throw error;
        }
    }

    /**
     * Constructs a Büchi automaton from the LTL formula.
     * This is a simplified representation for demonstration.
     * @returns {Object} A Büchi automaton.
     */
    constructEnhancedBuchiAutomaton() {
        const converter = new LTLToBuchiConverter(this.ltlAST);
        return converter.build();
    }
    
    /**
     * Constructs the symbolic product automaton of the Petri net and the LTL automaton.
     * @param {Object} automaton The Büchi automaton for the LTL formula.
     * @returns {Object} The product automaton.
     * @private
     */
    _constructSymbolicProductAutomaton(automaton) {
        const productStates = new Set();
        const productTransitions = new Map();
        const productAcceptingStates = new Set();
        const initialMarking = this.getInitialMarking();
        const initialFormula = this._getInitialFormula();

        // Seed initial product states
        for (const autoState of automaton.initialStates) {
            const st = { marking: initialMarking, formula: initialFormula, automatonState: autoState };
            const key = this.serializeState(st);
            productStates.add(key);
            if (automaton.acceptingStates.has(autoState)) {
                productAcceptingStates.add(key);
            }
        }

        const queue = Array.from(productStates).map(k => this.deserializeState(k));
        const visited = new Set(productStates);

        while (queue.length > 0) {
            const currentState = queue.shift();
            this.statistics.statesExplored++;
            const enabled = this._getEnabledTransitionsSymbolic(currentState);

            for (const tId of enabled) {
                const { nextMarking, nextFormula } = this._computeNextSymbolicState(currentState, tId);
                // Skip if formula is unsatisfiable
                if (nextFormula === 'false') continue;

                const autoTrans = automaton.transitions.get(currentState.automatonState) || [];
                for (const autoTr of autoTrans) {
                    const condPred = this._ltlFormulaToPredicate(autoTr.condition);
                    const rawComb = this._formulaAnd(nextFormula, condPred);
                    const combFormula = this._simplifyFormula(rawComb);
                    // Skip unsatisfiable combined formula
                    if (combFormula === 'false') continue;

                    const nxt = { marking: nextMarking, formula: combFormula, automatonState: autoTr.target };
                    const nxtKey = this.serializeState(nxt);
                    if (!visited.has(nxtKey)) {
                        visited.add(nxtKey);
                        productStates.add(nxtKey);
                        queue.push(nxt);
                        if (automaton.acceptingStates.has(autoTr.target)) {
                            productAcceptingStates.add(nxtKey);
                        }
                    }
                    const curKey = this.serializeState(currentState);
                    if (!productTransitions.has(curKey)) {
                        productTransitions.set(curKey, []);
                    }
                    productTransitions.get(curKey).push({ target: nxtKey, transitionId: tId });
                }
            }
        }

        return {
            states: productStates,
            transitions: productTransitions,
            initialStates: new Set(Array.from(productStates).slice(0, automaton.initialStates.size)),
            acceptingStates: productAcceptingStates
        };
    }
    /**
     * Computes the next symbolic state after firing a transition.
     * @param {Object} currentState The current symbolic state.
     * @param {string} transitionId The ID of the transition to fire.
     * @returns {Object} An object containing the next marking and the next symbolic formula.
     * @private
     */
    _computeNextSymbolicState(currentState, transitionId) {
        const transition = this.petriNet.transitions.get(transitionId);
        const newMarking = { ...currentState.marking };
        // Apply input and output arcs (unchanged)
        const inputArcs = Array.from(this.petriNet.arcs.values()).filter(arc => arc.target === transitionId);
        const outputArcs = Array.from(this.petriNet.arcs.values()).filter(arc => arc.source === transitionId);
        inputArcs.forEach(arc => {
            const place = this.petriNet.places.get(arc.source);
            if (place) newMarking[place.label] = (newMarking[place.label] || 0) - (arc.weight || 1);
        });
        outputArcs.forEach(arc => {
            const place = this.petriNet.places.get(arc.target);
            if (place) newMarking[place.label] = (newMarking[place.label] || 0) + (arc.weight || 1);
        });

        // Build formula with precondition
        const precondition = transition.precondition || 'true';
        const formulaWithPre = this._formulaAnd(currentState.formula, precondition);

        // Apply postcondition symbolically if present
        let nextFormula = transition.postcondition
            ? this._applyPostconditionSymbolically(formulaWithPre, transition)
            : formulaWithPre;

        // Early simplification via SMT
        nextFormula = this._simplifyFormula(nextFormula);

        return { nextMarking: newMarking, nextFormula };
    }

    /**
     * Symbolically applies a transition's postcondition to a formula.
     * @param {string} currentFormula The current formula.
     * @param {Object} transition The transition being fired.
     * @returns {string} The new symbolic formula after the transition.
     * @private
     */
    _applyPostconditionSymbolically(currentFormula, transition) {
        const postcondition = transition.postcondition;
        if (!postcondition || postcondition.trim() === '') {
            return currentFormula;
        }

        // Get all known variable names from the net.
        const variableNames = Array.from(this.petriNet.dataVariables.values()).map(v => v.name);
        if (variableNames.length === 0) {
            return currentFormula;
        }

        // 1. Rename all variables in the *previous* state's formula to their "_old" versions.
        // This preserves the constraints on the state before this transition fired.
        let oldFormula = currentFormula;
        // Sort by length descending to avoid replacing 'x' inside 'x_old'
        const sortedVarNames = [...variableNames].sort((a, b) => b.length - a.length);
        for (const v of sortedVarNames) {
            oldFormula = oldFormula.replace(new RegExp(`\\b${v}\\b`, 'g'), `${v}_old`);
        }

        // 2. Parse the postcondition string into individual update statements.
        // e.g., "x' = x + 10; y' = y + 5"
        const updates = postcondition.split(';').map(s => s.trim()).filter(Boolean);
        const updateConstraints = [];
        const updatedVars = new Set();

        for (const update of updates) {
            const match = update.match(/^([a-zA-Z_]\w*)'\s*=\s*(.*)/);
            if (!match) continue; // Skip anything that isn't a "var' = ..." assignment

            const [, varName, expression] = match;
            updatedVars.add(varName);

            // Create a logical equality constraint, e.g., "x == (x_old + 10)".
            // The RHS expression refers to the state *before* the update, so all its
            // variables must also be renamed to their "_old" versions.
            let rhs = expression;
            for (const v of sortedVarNames) {
                rhs = rhs.replace(new RegExp(`\\b${v}\\b`, 'g'), `${v}_old`);
            }
            updateConstraints.push(`${varName} == (${rhs})`);
        }
        
        // 3. For any variable that was NOT updated, add a "frame condition" constraint
        // stating its value does not change, e.g., "z == z_old".
        const unchangedConstraints = variableNames
            .filter(v => !updatedVars.has(v))
            .map(v => `${v} == ${v}_old`);

        // 4. Combine everything with ANDs into a single, clean formula.
        const allConstraints = [
            `(${oldFormula})`, 
            ...updateConstraints, 
            ...unchangedConstraints
        ].filter(c => c && c !== '()').join(' && ');
        
        return allConstraints;
    }
    
    /**
     * Simplifies a formula. Placeholder for an SMT solver's quantifier elimination. For performance reasons, this should be implemented using an SMT solver.
     * @param {string} formula The formula to simplify.
     * @returns {string} The simplified formula.
     * @private
     */
    _simplifyFormula(formula) {
        const trimmed = (formula || 'true').trim();
        if (trimmed === '' || trimmed === 'true') {
            return 'true';
        }
        if (trimmed === 'false') {
            return 'false';
        }
        // Use SMT solver to eliminate unsatisfiable formulas
        if (!this.smtSolver.isSatisfiable(trimmed)) {
            return 'false';
        }
        // TODO: Add tautology detection if needed
        return trimmed;
    }
    /**
     * Checks if a formula is satisfiable.
     * @param {string} formula The formula to check.
     * @returns {boolean} True if the formula is satisfiable.
     * @private
     */
    _isSatisfiable(formula) {
        return this.smtSolver.isSatisfiable(formula);
    }
    
    /**
     * Combines two formulas with a logical AND.
     * @param {string} f1 The first formula.
     * @param {string} f2 The second formula.
     * @returns {string} The combined formula.
     * @private
     */
    _formulaAnd(f1, f2) {
        if (f1 === 'true') return f2;
        if (f2 === 'true') return f1;
        if (f1 === 'false' || f2 === 'false') return 'false';
        return `(${f1}) && (${f2})`;
    }

    /**
     * Converts an LTL AST fragment into a string predicate.
     * @param {Object} formula The LTL formula AST node.
     * @returns {string} A string representing the logical predicate.
     * @private
     */
    _ltlFormulaToPredicate(formula) {
        if (!formula) return 'true';
        switch (formula.type) {
            case 'TRUE': return 'true';
            case 'LTLAtom': return formula.value;
            case 'LTLReference': return `(${formula.name} > 0)`;
            case 'LTLConjunction': return this._formulaAnd(this._ltlFormulaToPredicate(formula.left), this._ltlFormulaToPredicate(formula.right));
            case 'LTLDisjunction': return `(${this._ltlFormulaToPredicate(formula.left)}) || (${this._ltlFormulaToPredicate(formula.right)})`;
            case 'LTLNegation': return `!(${this._ltlFormulaToPredicate(formula.expression)})`;
            case 'LTLImplication': return `!(${this._ltlFormulaToPredicate(formula.left)}) || (${this._ltlFormulaToPredicate(formula.right)})`;
            default: return 'true';
        }
    }

    /**
     * Gets the initial formula representing the initial data state.
     * @returns {string} The initial formula.
     * @private
     */
    _getInitialFormula() {
        const initialConstraints = [];
        if (this.petriNet.dataVariables) {
            for (const [, variable] of this.petriNet.dataVariables) {
                if (variable.currentValue !== null) {
                    initialConstraints.push(`${variable.name} == ${JSON.stringify(variable.currentValue)}`);
                }
            }
        }
        return initialConstraints.join(' && ') || 'true';
    }

    /**
     * Checks for accepting states in the product automaton.
     * @param {Object} product The product automaton.
     * @returns {Object} An object indicating if a counterexample was found.
     * @private
     */
    _checkAcceptance(product) {
        // Find all Strongly Connected Components (SCCs) in the product graph
        const sccs = this._findSCCs(product);

        // Map each state to the index of the SCC it belongs to
        const stateToSccIndex = new Map();
        sccs.forEach((scc, index) => {
            scc.forEach(stateKey => stateToSccIndex.set(stateKey, index));
        });

        for (const scc of sccs) {
            // An SCC is part of a counterexample if it's non-trivial (a cycle) or self-looping,
            // contains an accepting state, and is reachable from an initial state.
            if (scc.size > 1 || (scc.size === 1 && this._hasSelfLoop(product, scc.values().next().value))) {
                
                let sccIsAccepting = false;
                for (const stateKey of scc) {
                    if (product.acceptingStates.has(stateKey)) {
                        sccIsAccepting = true;
                        break;
                    }
                }

                if (sccIsAccepting) {
                    // Check if this accepting SCC is reachable from any initial state
                    const pathToScc = this._findPathToSCC(product, scc);
                    if (pathToScc) {
                        // Found a reachable, accepting cycle. This is a counterexample.
                        const cycle = this._findCycleInSCC(product, scc, pathToScc.path[pathToScc.path.length - 1].targetStateKey);
                        return {
                            hasCounterexample: true,
                            witness: pathToScc.path.concat(cycle) // Combine path to cycle and the cycle itself
                        };
                    }
                }
            }
        }

        return { hasCounterexample: false, witness: null };
    }

   /**
     * Finds a path from an initial state to a target state using Breadth-First Search.
     * @param {Object} product The product automaton.
     * @param {string} targetStateKey The key of the target state.
     * @returns {Array|null} The path as a sequence of transitions, or null if no path is found.
     * @private
     */
    _findPathToState(product, targetStateKey) {
        const queue = Array.from(product.initialStates).map(key => ({ key, path: [] }));
        const visited = new Set(product.initialStates);

        while (queue.length > 0) {
            const { key, path } = queue.shift();

            if (key === targetStateKey) {
                return path; // Path found
            }

            const transitions = product.transitions.get(key) || [];
            for (const { target, transitionId } of transitions) {
                if (!visited.has(target)) {
                    visited.add(target);
                    const newPath = [...path, { transitionId, targetStateKey: target }];
                    queue.push({ key: target, path: newPath });
                }
            }
        }
        return null; // No path found
    }

    /**
     * Get enabled transitions in a symbolic state.
     * @param {Object} state The current symbolic state.
     * @returns {Array<string>} A list of enabled transition IDs.
     * @private
     */
    _getEnabledTransitionsSymbolic(state) {
        const enabled = [];
        for (const [id, transition] of this.petriNet.transitions) {
            let isEnabled = true;
            const inputArcs = Array.from(this.petriNet.arcs.values()).filter(arc => arc.target === id);
            for (const arc of inputArcs) {
                const place = this.petriNet.places.get(arc.source);
                if (!place || (state.marking[place.label] || 0) < arc.weight) {
                    isEnabled = false;
                    break;
                }
            }
            if (isEnabled && typeof transition.precondition === 'string' && transition.precondition.trim() !== '') {
                const formulaWithPrecondition = this._formulaAnd(state.formula, transition.precondition);
                if (!this._isSatisfiable(formulaWithPrecondition)) {
                    isEnabled = false;
                }
            }
            if (isEnabled) {
                enabled.push(id);
            }
        }
        return enabled;
    }

    _findSCCs(product) {
        const sccs = [];
        const stack = [];
        const onStack = new Map();
        const ids = new Map();
        const low = new Map();
        let idCounter = 0;

        const dfs = (at) => {
            stack.push(at);
            onStack.set(at, true);
            ids.set(at, idCounter);
            low.set(at, idCounter);
            idCounter++;

            const transitions = product.transitions.get(at) || [];
            for (const { target } of transitions) {
                if (!ids.has(target)) {
                    dfs(target);
                }
                if (onStack.get(target)) {
                    low.set(at, Math.min(low.get(at), low.get(target)));
                }
            }

            if (ids.get(at) === low.get(at)) {
                const scc = new Set();
                while (stack.length > 0) {
                    const node = stack.pop();
                    onStack.set(node, false);
                    low.set(node, ids.get(at));
                    scc.add(node);
                    if (node === at) break;
                }
                sccs.push(scc);
            }
        };

        for (const stateKey of product.states) {
            if (!ids.has(stateKey)) {
                dfs(stateKey);
            }
        }
        return sccs;
    }

    /**
     * Finds a path from an initial state to a given SCC.
     * @param {Object} product The product automaton.
     * @param {Set<string>} targetScc The SCC to find a path to.
     * @returns {Object|null} The path object or null if not reachable.
     * @private
     */
    _findPathToSCC(product, targetScc) {
        const queue = Array.from(product.initialStates).map(key => ({ key, path: [] }));
        const visited = new Set(product.initialStates);

        while (queue.length > 0) {
            const { key, path } = queue.shift();

            if (targetScc.has(key)) {
                return { path }; // Path found
            }

            const transitions = product.transitions.get(key) || [];
            for (const { target, transitionId } of transitions) {
                if (!visited.has(target)) {
                    visited.add(target);
                    const newPath = [...path, { transitionId, targetStateKey: target }];
                    queue.push({ key: target, path: newPath });
                }
            }
        }
        return null; // No path found
    }

    /**
     * Finds a cycle within a given SCC starting from an entry point.
     * @param {Object} product The product automaton.
     * @param {Set<string>} scc The SCC to find a cycle in.
     * @param {string} startNode The entry point to the SCC.
     * @returns {Array} The path representing the cycle.
     * @private
     */
    _findCycleInSCC(product, scc, startNode) {
        const queue = [{ key: startNode, path: [] }];
        const visited = new Set([startNode]);

        while(queue.length > 0) {
            const { key, path } = queue.shift();
            const transitions = (product.transitions.get(key) || []).filter(t => scc.has(t.target));

            for(const {target, transitionId} of transitions) {
                const newPath = [...path, { transitionId, targetStateKey: target }];
                if(target === startNode) {
                    return newPath; // Cycle found
                }
                if(!visited.has(target)) {
                    visited.add(target);
                    queue.push({ key: target, path: newPath });
                }
            }
        }
        return []; // Should not happen if SCC is valid
    }

    /**
     * Checks if a single-node SCC has a self-loop.
     * @private
     */
    _hasSelfLoop(product, stateKey) {
        const transitions = product.transitions.get(stateKey) || [];
        return transitions.some(t => t.target === stateKey);
    }
    /**
     * Build counterexample trace.
     * @param {string} finalStateKey The key of the final state in the witness path.
     * @param {Object} product The product automaton.
     * @returns {Array<Object>|null} The counterexample trace or null.
     */
    buildCounterexample(path) {
        if (!path) return null;

        const trace = [];
        let currentMarking = this.getInitialMarking();
        let currentValuation = this.getInitialValuation();

        // Add the initial state to the trace
        trace.push({
            action: 'Initial State',
            marking: { ...currentMarking },
            dataValuation: { ...currentValuation }
        });

        // Replay the path of transitions to generate concrete states
        for (const step of path) {
            const transitionId = step.transitionId;
            const transition = this.petriNet.transitions.get(transitionId);
            if (!transition) continue;

            // 1. Update Petri net marking
            const inputArcs = Array.from(this.petriNet.arcs.values()).filter(arc => arc.target === transitionId);
            const outputArcs = Array.from(this.petriNet.arcs.values()).filter(arc => arc.source === transitionId);

            inputArcs.forEach(arc => {
                const place = this.petriNet.places.get(arc.source);
                if (place) currentMarking[place.label] = (currentMarking[place.label] || 0) - (arc.weight || 1);
            });
            outputArcs.forEach(arc => {
                const place = this.petriNet.places.get(arc.target);
                if (place) currentMarking[place.label] = (currentMarking[place.label] || 0) + (arc.weight || 1);
            });

            // 2. CORRECTED: Update data valuation by evaluating assignments
            if (transition.postcondition) {
                try {
                    const nextValuation = { ...currentValuation };
                    const statements = transition.postcondition.split(';').map(s => s.trim()).filter(Boolean);

                    for (const statement of statements) {
                        const assignMatch = statement.match(/^([a-zA-Z_]\w*)'\s*=\s*(.+)$/);
                        if (assignMatch) {
                            const [, varName, expression] = assignMatch;
                            if (varName in nextValuation) {
                                // Create a function to evaluate the expression in the context of the current valuation
                                const varNames = Object.keys(currentValuation);
                                const varValues = Object.values(currentValuation);
                                const evaluator = new Function(...varNames, `return ${expression};`);
                                // Update the variable in the next valuation
                                nextValuation[varName] = evaluator(...varValues);
                            }
                        }
                    }
                    currentValuation = nextValuation;

                } catch (e) {
                    console.error(`Could not evaluate postcondition for ${transition.label}: ${e.message}`);
                }
            }

            // Add the new concrete state to the trace
            trace.push({
                action: `Fire: ${transition.label || transition.id}`,
                marking: { ...currentMarking },
                dataValuation: { ...currentValuation }
            });
        }

        return trace;
    }

    /**
     * Get initial marking of the Petri net.
     * @returns {Object} The initial marking.
     */
    getInitialMarking() {
        const marking = {};
        for (const [id, place] of this.petriNet.places) {
            marking[place.label] = place.tokens || 0;
        }
        return marking;
    }


    /**
     * Get the initial data valuation from the Petri net model.
     * This method safely retrieves data from the DataPetriNet instance.
     * @returns {Object} The initial mapping of variable names to their values.
     */
    getInitialValuation() {
        if (this.petriNet && typeof this.petriNet.getDataValuation === 'function') {
            return this.petriNet.getDataValuation();
        }
        // Fallback for safety, in case a non-data net is being verified
        console.warn("The verifier could not find a getDataValuation function on the Petri net. Assuming no data variables.");
        return {};
    }

    /**
     * Serialize a state object to a string key.
     * @param {Object} state The state to serialize.
     * @returns {string} The serialized state key.
     */
    serializeState(state) {
        const sortedMarking = Object.entries(state.marking).sort();
        return JSON.stringify({
            marking: sortedMarking,
            formula: state.formula,
            automatonState: state.automatonState
        });
    }

    /**
     * Deserialize a state key back to a state object.
     * @param {string} stateKey The key to deserialize.
     * @returns {Object} The state object.
     */
    deserializeState(stateKey) {
        const data = JSON.parse(stateKey);
        data.marking = Object.fromEntries(data.marking);
        return data;
    }

    /**
     * Utility method to add delays for UI feedback.
     * @param {number} ms Milliseconds to delay.
     * @returns {Promise<void>}
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}

class LTLToBuchiConverter {
    constructor(ast) {
         // --- Add these new members ---
        this.formulaKeyMap = new Map();
        this.nextFormulaId = 0;
        
        // --- Essential Members ---
        this.originalAST = ast;
        // --- Essential Members ---
        this.originalAST = ast; // Keep the original for reference
        this.memo = new Map(); // Memoization for formula processing
        this.states = new Map(); // Map from state name (key) to state object
        this.formulasToProcess = []; // Queue for the translation algorithm
        
        // --- GBA Acceptance Members ---
        this.acceptanceConditions = [];
        this.acceptanceConditionIndex = new Map();
    }

    // --- Public Main Method ---

    /**
     * Builds the Büchi Automaton and formats it to the required API.
     * @returns {object} The resulting automaton with {states, initialStates, acceptingStates, transitions}.
     */
    build() {
        // --- PHASE 1: Rewriting ---
        let nnfAst = this._toNNF(this.originalAST);
        let rewrittenAst = this._rewrite(nnfAst);
        
        this._collectAcceptanceConditions(rewrittenAst);

        // --- PHASE 2: Translation ---
        this._translate(rewrittenAst);
        let internalAutomaton = this._getInternalAutomatonRepresentation();

        // --- PHASE 3: Simplification ---
        internalAutomaton = this._simplifyAutomaton(internalAutomaton);

        // --- Final Formatting to Match Required API ---
        const finalTransitions = {};
        for (const [stateName, stateObject] of internalAutomaton.states.entries()) {
            finalTransitions[stateName] = stateObject.transitions;
        }

        const acceptingStates = new Set();
        for (const state of internalAutomaton.states.values()) {
            if (state.acceptance.size > 0) {
                acceptingStates.add(state.name);
            }
        }

        return {
            states: new Set(internalAutomaton.states.keys()),
            initialStates: new Set(internalAutomaton.initialStates),
            acceptingStates: new Set(acceptingStates),
            transitions: new Map(Object.entries(finalTransitions))
        };
    }

    // --- Phase 1: Rewriting ---

    _rewrite(node) {
        if (!node) return null;

        // Recursively rewrite children first
        if (node.left) node.left = this._rewrite(node.left);
        if (node.right) node.right = this._rewrite(node.right);
        if (node.expression) node.expression = this._rewrite(node.expression);
        
        // Rule: (X φ) U (X ψ)  ≡  X(φ U ψ)
        if (node.type === 'LTLStrongUntil' && node.left?.type === 'LTLNext' && node.right?.type === 'LTLNext') {
            return {
                type: 'LTLNext',
                expression: { type: 'LTLStrongUntil', left: node.left.expression, right: node.right.expression }
            };
        }
        
        // Rule: F G F φ ≡ G F φ
        if (node.type === 'LTLEventually' && node.expression?.type === 'LTLGlobally' && node.expression.expression?.type === 'LTLEventually') {
            return {
                type: 'LTLGlobally',
                expression: node.expression.expression
            }
        }

        return node;
    }

    // --- Phase 2: Translation ---

    _translate(ast) {
        this._findOrCreateState(new Set([ast]));

        while (this.formulasToProcess.length > 0) {
            const formulaSet = this.formulasToProcess.shift();
            this._processFormulaSet(formulaSet);
        }
    }

    _processFormulaSet(formulaSet) {
        const stateName = this._getStateName(formulaSet);
        const state = this.states.get(stateName);
        if (state.processed) return;
        
        state.processed = true;

        const cover = this._getCover(formulaSet);

        for (const term of cover) {
            const nextFormulas = new Set();
            const condition = new Set();
            
            for (const literal of term) {
                if (literal.type === 'LTLNext') {
                    nextFormulas.add(literal.expression);
                } else {
                    condition.add(literal);
                }
            }
            
            const nextStateName = this._findOrCreateState(nextFormulas);
            state.transitions.push({ target: nextStateName, condition: this._simplifyCondition(condition) });
        }
    }

    _findOrCreateState(formulaSet) {
        const name = this._getStateName(formulaSet);
        if (!this.states.has(name)) {
            const acceptance = this._getAcceptanceSet(formulaSet);
            this.states.set(name, {
                name: name,
                formulas: formulaSet,
                transitions: [],
                processed: false,
                acceptance: acceptance,
            });
            this.formulasToProcess.push(formulaSet);
        }
        return name;
    }

    _getCover(formulaSet) {
        if (formulaSet.size === 0) return [new Set([{ type: 'LTLTrue' }])];
        
        const formulaArray = [...formulaSet];
        const first = formulaArray[0];
        const rest = new Set(formulaArray.slice(1));

        const expansion = this._expand(first);
        const restCover = this._getCover(rest);
        
        let combinedCover = [];
        for (const term of expansion) {
            for (const restTerm of restCover) {
                const newTerm = new Set([...term, ...restTerm]);
                if (this._isConsistent(newTerm)) {
                    combinedCover.push(newTerm);
                }
            }
        }
        
        return this._simplifyCover(combinedCover);
    }
    
    _expand(f) {
        const key = this._formulaToKey(f);
        if (this.memo.has(key)) return this.memo.get(key);

        let result;
        switch (f.type) {
            case 'LTLDisjunction':
                result = [new Set([f.left]), new Set([f.right])];
                break;
            case 'LTLConjunction':
                result = [new Set([f.left, f.right])];
                break;
            // Rule: ψ₁ U ψ₂ = ψ₂ ∨ (ψ₁ ∧ X(ψ₁ U ψ₂))
            case 'LTLStrongUntil':
                result = [
                    new Set([f.right]),
                    new Set([f.left, { type: 'LTLNext', expression: f }])
                ];
                break;
            // Rule: ψ₁ R ψ₂ = ψ₂ ∧ (ψ₁ ∨ X(ψ₁ R ψ₂))
            case 'LTLWeakRelease':
                 result = [
                    new Set([f.right, f.left]),
                    new Set([f.right, { type: 'LTLNext', expression: f }])
                 ];
                 break;
            default: // Literals
                result = [new Set([f])];
        }
        this.memo.set(key, result);
        return result;
    }
    
    // --- Phase 3: Simplification ---
    
    _simplifyAutomaton(automaton) {
        let changed = true;
        let iterations = 0;
        const MAX_ITERATIONS = 500;

        while (changed && iterations < MAX_ITERATIONS) {
            changed = false;
            iterations++;

            const sccs = this._findSCCs(automaton);
            // const pruned = this._pruneFairSets(automaton, sccs);
            // if (pruned) changed = true;
        }

        return automaton;
    }
    
    _pruneFairSets(automaton, sccs) {
        let changed = false;
        const fairSCCs = new Set();
        const sccOfState = new Map();

        sccs.forEach((scc, i) => {
            for (const stateName of scc) {
                sccOfState.set(stateName, i);
            }
        });
        
        // An SCC is fair if it is non-trivial and it intersects all fair sets 
        sccs.forEach((scc, i) => {
            if (automaton.acceptanceConditions.length === 0) return;
            
            let isFair = true;
            for (let accIndex = 0; accIndex < automaton.acceptanceConditions.length; accIndex++) {
                const intersects = scc.some(stateName => automaton.states.get(stateName).acceptance.has(accIndex));
                if (!intersects) {
                    isFair = false;
                    break;
                }
            }
            if (isFair) {
                fairSCCs.add(i);
            }
        });

        // States not in a fair SCC can be removed from the accepting sets 
        for (const state of automaton.states.values()) {
            const sccIndex = sccOfState.get(state.name);
            if (!fairSCCs.has(sccIndex)) {
                if (state.acceptance.size > 0) {
                    state.acceptance.clear();
                    changed = true;
                }
            }
        }
        
        return changed;
    }
    
    _findSCCs(automaton) {
        const sccs = [];
        const stack = [];
        const onStack = new Map();
        const ids = new Map();
        const low = new Map();
        let id = 0;

        for (const stateName of automaton.states.keys()) {
            if (!ids.has(stateName)) {
                dfs(stateName);
            }
        }

        function dfs(at) {
            stack.push(at);
            onStack.set(at, true);
            ids.set(at, id);
            low.set(at, id);
            id++;

            const state = automaton.states.get(at);
            for (const { target } of state.transitions) {
                if (!ids.has(target)) {
                    dfs(target);
                }
                if (onStack.get(target)) {
                    low.set(at, Math.min(low.get(at), low.get(target)));
                }
            }

            if (ids.get(at) === low.get(at)) {
                const scc = new Set();
                while (stack.length > 0) {
                    const node = stack.pop();
                    onStack.set(node, false);
                    low.set(node, ids.get(at));
                    scc.add(node);
                    if (node === at) break;
                }
                sccs.push(scc);
            }
        }

        return sccs;
    }

    // --- Helper & Utility Methods ---

    _collectAcceptanceConditions(node) {
        if (!node) return;
        const key = this._formulaToKey(node);
        if (this.acceptanceConditionIndex.has(key)) return;

        if (node.type === 'LTLStrongUntil') {
            const index = this.acceptanceConditions.length;
            this.acceptanceConditions.push(node);
            this.acceptanceConditionIndex.set(key, index);
        }

        if (node.left) this._collectAcceptanceConditions(node.left);
        if (node.right) this._collectAcceptanceConditions(node.right);
        if (node.expression) this._collectAcceptanceConditions(node.expression);
    }
    
    _getAcceptanceSet(formulaSet) {
        const satisfied = new Set();
        // The acceptance condition contains all the states s such that the label of s does not imply ψ₁Uψ₂ or the label of s implies ψ₂ 
        for (let i = 0; i < this.acceptanceConditions.length; i++) {
            const untilFormula = this.acceptanceConditions[i];
            const rightHandSide = untilFormula.right;

            if (!this._setHas(formulaSet, untilFormula) || this._setHas(formulaSet, rightHandSide)) {
                satisfied.add(i);
            }
        }
        return satisfied;
    }

    _simplifyCondition(conditionSet) {
        return [...conditionSet].map(f => this._formulaToPretty(f)).join(' ∧ ');
    }

    _isConsistent(term) {
        const formulas = new Set();
        for (const f of term) {
            const key = this._formulaToKey(f);
            // Check for contradiction like {p, !p}
            const notKey = this._formulaToKey(this._toNNF({ type: 'LTLNegation', expression: f }));
            if (formulas.has(notKey)) return false;
            formulas.add(key);
        }
        return true;
    }
    
    _simplifyCover(cover) {
        const simplified = [];
        for (let i = 0; i < cover.length; i++) {
            let isSubsumed = false;
            for (let j = 0; j < cover.length; j++) {
                if (i !== j && this._isSubset(cover[j], cover[i])) {
                    isSubsumed = true;
                    break;
                }
            }
            if (!isSubsumed) {
                simplified.push(cover[i]);
            }
        }
        return simplified;
    }
    
    _getInternalAutomatonRepresentation() {
         const initialStates = new Set();
         // The initial state corresponds to the cover of the main formula 
         const initialStateFormulas = new Set([this._rewrite(this._toNNF(this.originalAST))]);
         initialStates.add(this._getStateName(initialStateFormulas));

        return {
            states: this.states,
            initialStates: initialStates,
            acceptanceConditions: this.acceptanceConditions,
        };
    }
    
    _isSubset(s1, s2) {
        if (s1.size > s2.size) return false;
        for (const item of s1) if (!this._setHas(s2, item)) return false;
        return true;
    }
    
    _setHas(set, formula) {
        const key = this._formulaToKey(formula);
        return this._setHasKey(set, key);
    }
    
    _setHasKey(set, key) {
        for (const item of set) if (this._formulaToKey(item) === key) return true;
        return false;
    }

    _formulaToKey(f) {
        if (!f) return 'null';
    
        // Recursively get keys for children first
        const leftKey = f.left ? this._formulaToKey(f.left) : null;
        const rightKey = f.right ? this._formulaToKey(f.right) : null;
        const exprKey = f.expression ? this._formulaToKey(f.expression) : null;
        
        // Create a canonical string representation based on children's keys
        const canonicalRepresentation = JSON.stringify({
            type: f.type,
            op: f.operator,
            l: leftKey,
            r: rightKey,
            e: exprKey,
            n: f.name,
            v: f.value
        });
    
        // Check if we've seen this exact formula structure before
        if (this.formulaKeyMap.has(canonicalRepresentation)) {
            return this.formulaKeyMap.get(canonicalRepresentation);
        }
    
        // If not, assign it a new unique ID and store it
        const newId = `f_${this.nextFormulaId++}`;
        this.formulaKeyMap.set(canonicalRepresentation, newId);
        
        // Also attach the ID to the formula object itself for potential debugging
        f.formulaId = newId;
    
        return newId;
    }

    _getStateName(formulaSet) {
        if (formulaSet.size === 0) return 'q_true'; 
        // A unique name for each state based on its formulas
        return "q" + [...formulaSet].map(f => this._formulaToKey(f)).sort().join(';').hashCode();
    }
    
    _formulaToPretty(f) {
        if (!f) return 'null';
        switch(f.type) {
            case 'LTLTrue': return 'true';
            case 'LTLFalse': return 'false';
            case 'LTLAtom': return f.value;
            case 'LTLReference': return f.name;
            case 'LTLNegation': return `!(${this._formulaToPretty(f.expression)})`;
            default: return this._formulaToKey(f).substring(0, 20) + '...';
        }
    }
    

    _toNNF(node) {
        switch(node.type) {
            case 'LTLNegation': {
                const expr = node.expression;
                switch(expr.type) {
                    case 'LTLNegation':
                        return this._toNNF(expr.expression);
                    case 'LTLConjunction':
                        return {
                            type: 'LTLDisjunction',
                            operator: '||',
                            left: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.left }),
                            right: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.right })
                        };
                    case 'LTLDisjunction':
                        return {
                            type: 'LTLConjunction',
                            operator: '&&',
                            left: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.left }),
                            right: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.right })
                        };
                    case 'LTLNext':
                        return { type: 'LTLNext', operator: 'X', expression: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.expression }) };
                    case 'LTLGlobally':
                        return { type: 'LTLEventually', operator: 'F', expression: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.expression }) };
                    case 'LTLEventually':
                        return { type: 'LTLGlobally', operator: 'G', expression: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.expression }) };
                    case 'LTLUntil':
                        return {
                            type: 'LTLEventuallyRelease',
                            operator: 'R',
                            left: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.left }),
                            right: this._toNNF({ type: 'LTLNegation', operator: '!', expression: expr.right })
                        };
                    default:
                        return node; // atomic negation
                }
            }
            case 'LTLConjunction':
            case 'LTLDisjunction':
                return {
                    ...node,
                    left: this._toNNF(node.left),
                    right: this._toNNF(node.right)
                };
            case 'LTLNext':
            case 'LTLGlobally':
            case 'LTLEventually':
                return { ...node, expression: this._toNNF(node.expression) };
            case 'LTLUntil':
            case 'LTLEventuallyRelease':
                return {
                    ...node,
                    left: this._toNNF(node.left),
                    right: this._toNNF(node.right)
                };
            default:
                return node;
        }
    }
    buildBuchiAutomaton(ltlAST) {
        const nnfAST = this._toNNF(ltlAST);
        // existing conversion logic, now feeding nnfAST
        return this.converter.convert(nnfAST);
    }
}

// Helper function to create a hash code for unique state naming.
String.prototype.hashCode = function() {
    let hash = 0, i, chr;
    if (this.length === 0) return hash;
    for (i = 0; i < this.length; i++) {
        chr = this.charCodeAt(i);
        hash = ((hash << 5) - hash) + chr;
        hash |= 0; // Convert to 32bit integer
    }
    return Math.abs(hash);
};
// Auto-initialize when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
    const initEnhancedLTLVerification = () => {
        if (window.petriApp && window.dataPetriNetIntegration) {
            if (!window.enhancedLtlVerificationTWO) {
                console.log("Initializing Enhanced LTL Verification extension");
                window.enhancedLtlVerificationTWO = new LTLVerificationExtensionTWO(window.petriApp);
            }
        } else {
            setTimeout(initEnhancedLTLVerification, 500);
        }
    };
    
    setTimeout(initEnhancedLTLVerification, 1500);
});


