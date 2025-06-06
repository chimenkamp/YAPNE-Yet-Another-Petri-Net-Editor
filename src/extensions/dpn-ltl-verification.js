/**
 * LTL Verification Extension for Data Petri Nets
 * 
 * Implements LTL_f verification for Data-Aware Dynamic Systems based on:
 * "Linear-Time Verification of Data-Aware Dynamic Systems with Arithmetic"
 * by Paolo Felli, Marco Montali, Sarah Winkler
 */

class LTLVerificationExtension {
    constructor(app) {
        this.app = app;
        this.ltlFormula = "";
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

    /**
     * Add LTL checker button to existing verification section
     */
    addLTLButtonToVerificationSection() {
        const verificationSection = document.querySelector('#verification-section .section-content');
        if (!verificationSection) return;

        // Add separator and LTL button
        const ltlButtonHTML = `
            <div style="margin-top: 15px; padding-top: 15px; border-top: 1px solid #434C5E;">
                <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">
                    Verify Linear Temporal Logic properties on finite traces (LTL_f).
                </p>
                <button id="btn-verify-ltl" class="ltl-verify-button">
                    <span class="ltl-btn-icon">📝</span>
                    LTL Model Checking
                </button>
            </div>
        `;

        verificationSection.insertAdjacentHTML('beforeend', ltlButtonHTML);

        // Add event listener
        const ltlButton = document.querySelector('#btn-verify-ltl');
        ltlButton.addEventListener('click', () => this.openLTLModal());
    }

    /**
     * Create the LTL formula editor modal
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
                        LTL Model Checking for Data Petri Nets
                    </h2>
                    <button class="ltl-close-btn" id="close-ltl-modal">×</button>
                </div>
                <div class="ltl-modal-body">
                    
                    <!-- Algorithm Info -->
                    <div class="ltl-algorithm-info">
                        <h4>🔬 Algorithm: Data-Aware LTL_f Verification</h4>
                        <p>
                            Based on Felli, Montali & Winkler's approach for checking LTL_f properties 
                            on Data-Aware Dynamic Systems with finite summary.
                        </p>
                    </div>

                    <!-- Formula Editor Section -->
                    <div class="ltl-editor-section">
                        <div class="ltl-section-header">
                            <h3>📋 LTL_f Formula Editor</h3>
                            <div class="ltl-formula-help-toggle">
                                <button id="toggle-ltl-help" class="ltl-help-button">❓ Syntax Help</button>
                            </div>
                        </div>
                        
                        <div class="ltl-formula-input-container">
                            <label for="ltl-formula-input">Enter LTL_f Formula:</label>
                            <textarea 
                                id="ltl-formula-input" 
                                class="ltl-formula-textarea"
                                placeholder="Example: ◇(sold ∧ amount > 100) ∨ □(balance ≥ 0)"
                                rows="3"
                            ></textarea>
                            <div id="ltl-formula-validation" class="ltl-validation-message"></div>
                        </div>

                        <!-- Syntax Help Panel (initially hidden) -->
                        <div id="ltl-help-panel" class="ltl-help-panel" style="display: none;">
                            <h4>LTL_f Syntax Reference</h4>
                            <div class="ltl-help-grid">
                                <div class="ltl-help-category">
                                    <h5>Temporal Operators:</h5>
                                    <ul>
                                        <li><code>◇φ</code> or <code>F φ</code> - Eventually φ (Future)</li>
                                        <li><code>□φ</code> or <code>G φ</code> - Always φ (Globally)</li>
                                        <li><code>○φ</code> or <code>X φ</code> - Next φ</li>
                                        <li><code>φ U ψ</code> - φ Until ψ</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Logical Operators:</h5>
                                    <ul>
                                        <li><code>∧</code> or <code>&</code> - AND</li>
                                        <li><code>∨</code> or <code>|</code> - OR</li>
                                        <li><code>¬</code> or <code>!</code> - NOT</li>
                                        <li><code>→</code> or <code>-></code> - Implies</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Data Constraints:</h5>
                                    <ul>
                                        <li><code>variable > value</code></li>
                                        <li><code>variable = value</code></li>
                                        <li><code>variable ≤ value</code></li>
                                        <li><code>place_name</code> - Place is marked</li>
                                    </ul>
                                </div>
                                <div class="ltl-help-category">
                                    <h5>Examples:</h5>
                                    <ul>
                                        <li><code>◇(end ∧ balance > 0)</code></li>
                                        <li><code>□(account_balance ≥ 0)</code></li>
                                        <li><code>start → ◇end</code></li>
                                        <li><code>request U (grant ∨ deny)</code></li>
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

                    <!-- Results Section (initially hidden) -->
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
        // Close modal handlers
        const closeBtn = document.querySelector('#close-ltl-modal');
        const modal = document.querySelector('#ltl-verification-modal');
        
        closeBtn.addEventListener('click', () => this.closeLTLModal());
        modal.addEventListener('click', (e) => {
            if (e.target === modal) this.closeLTLModal();
        });

        // Help toggle
        const helpToggle = document.querySelector('#toggle-ltl-help');
        const helpPanel = document.querySelector('#ltl-help-panel');
        helpToggle.addEventListener('click', () => {
            const isVisible = helpPanel.style.display !== 'none';
            helpPanel.style.display = isVisible ? 'none' : 'block';
            helpToggle.textContent = isVisible ? '❓ Syntax Help' : '❌ Hide Help';
        });

        // Formula input validation
        const formulaInput = document.querySelector('#ltl-formula-input');
        formulaInput.addEventListener('input', () => this.validateLTLFormula());

        // Validation button
        const validateBtn = document.querySelector('#btn-validate-ltl');
        validateBtn.addEventListener('click', () => this.validateLTLFormula(true));

        // Start verification button
        const startBtn = document.querySelector('#btn-start-ltl-verification');
        startBtn.addEventListener('click', () => this.startLTLVerification());

        // Element click handlers for easy insertion
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
        
        // Focus on formula input
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
        this.constraints.clear();
    }

    /**
     * Populate available elements (places and variables)
     */
    populateAvailableElements() {
        const placesContainer = document.querySelector('#ltl-places-list');
        const variablesContainer = document.querySelector('#ltl-variables-list');
        
        // Clear existing content
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

        // Add data variables
        if (this.app.api.petriNet.dataVariables) {
            for (const [id, variable] of this.app.api.petriNet.dataVariables) {
                const varTag = document.createElement('span');
                varTag.className = 'ltl-element-tag ltl-variable-tag';
                varTag.textContent = variable.name;
                varTag.title = `Click to insert variable "${variable.name}"`;
                variablesContainer.appendChild(varTag);
            }
        }

        // Show message if no elements
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
     * Validate the LTL formula
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
            const parser = new LTLParser();
            const result = parser.parse(formula, this.getAvailableAtoms());
            
            if (result.valid) {
                this.ltlFormula = formula;
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
        
        // Add data variable names
        if (this.app.api.petriNet.dataVariables) {
            for (const [id, variable] of this.app.api.petriNet.dataVariables) {
                atoms.push(variable.name);
            }
        }
        
        return atoms;
    }

    /**
     * Start LTL verification process
     */
    async startLTLVerification() {
        const resultsSection = document.querySelector('#ltl-results-section');
        const progressContainer = document.querySelector('#ltl-verification-progress');
        const resultsContainer = document.querySelector('#ltl-verification-results');
        const startBtn = document.querySelector('#btn-start-ltl-verification');
        
        // Show results section and progress
        resultsSection.style.display = 'block';
        startBtn.disabled = true;
        startBtn.innerHTML = '<span class="ltl-spinner"></span> Verifying...';
        
        // Show progress
        progressContainer.innerHTML = this.createLTLProgressHTML();
        resultsContainer.innerHTML = '';
        
        try {
            // Create verifier and run verification
            const verifier = new LTLVerifier(this.app.api.petriNet, this.ltlFormula);
            const result = await verifier.verify((progress, step) => {
                this.updateLTLProgress(progress, step);
            });
            
            // Hide progress, show results
            progressContainer.style.display = 'none';
            resultsContainer.innerHTML = this.createLTLResultsHTML(result);
            
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
                <h4>🔄 LTL_f Model Checking in Progress</h4>
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
                            ${step.dataValuation ? `Data: ${this.formatDataValuation(step.dataValuation)}` : ''}
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
        return Object.entries(valuation)
            .map(([variable, value]) => `${variable}=${value}`)
            .join(', ') || 'no data';
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
            /* LTL Verification Extension Styles */
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
            }

            .ltl-verify-button:hover {
                background-color: #88C0D0 !important;
            }

            /* LTL Modal Styles */
            .ltl-modal {
                position: fixed;
                top: 0;
                left: 0;
                right: 0;
                bottom: 0;
                background-color: rgba(0, 0, 0, 0.8);
                z-index: 3000;
                display: none;
                align-items: center;
                justify-content: center;
                padding: 20px;
                box-sizing: border-box;
            }

            .ltl-modal.show {
                display: flex;
            }

            .ltl-modal-content {
                background-color: #3B4252;
                border-radius: 12px;
                box-shadow: 0 10px 40px rgba(0, 0, 0, 0.4);
                width: 100%;
                max-width: 900px;
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
                background-color: #4C566A;
                border-radius: 10px 10px 0 0;
            }

            .ltl-modal-header h2 {
                margin: 0;
                color: #E5E9F0;
                display: flex;
                align-items: center;
                gap: 12px;
                font-size: 20px;
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
            }

            .ltl-modal-body {
                padding: 25px;
            }

            /* Algorithm Info */
            .ltl-algorithm-info {
                background: linear-gradient(135deg, #4C566A, #5E81AC);
                border-radius: 8px;
                padding: 20px;
                margin-bottom: 25px;
                border-left: 4px solid #88C0D0;
            }

            .ltl-algorithm-info h4 {
                margin: 0 0 10px 0;
                color: #E5E9F0;
                font-size: 16px;
            }

            .ltl-algorithm-info p {
                margin: 0;
                color: #D8DEE9;
                line-height: 1.5;
            }

            /* Editor Section */
            .ltl-editor-section {
                background-color: #434C5E;
                border-radius: 8px;
                padding: 20px;
                margin-bottom: 20px;
                border: 1px solid #4C566A;
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
            }

            .ltl-help-button {
                background-color: #5E81AC;
                color: #ECEFF4;
                border: none;
                padding: 8px 15px;
                border-radius: 5px;
                cursor: pointer;
                font-size: 14px;
                transition: background-color 0.2s;
            }

            .ltl-help-button:hover {
                background-color: #81A1C1;
            }

            /* Formula Input */
            .ltl-formula-input-container {
                margin-bottom: 20px;
            }

            .ltl-formula-input-container label {
                display: block;
                margin-bottom: 8px;
                font-weight: 500;
                color: #E5E9F0;
                font-size: 15px;
            }

            .ltl-formula-textarea {
                width: 100%;
                min-height: 80px;
                padding: 15px;
                border: 2px solid #4C566A;
                border-radius: 6px;
                background-color: #2E3440;
                color: #E5E9F0;
                font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
                font-size: 16px;
                line-height: 1.4;
                resize: vertical;
                transition: border-color 0.2s;
                box-sizing: border-box;
            }

            .ltl-formula-textarea:focus {
                outline: none;
                border-color: #88C0D0;
                box-shadow: 0 0 0 3px rgba(136, 192, 208, 0.3);
            }

            /* Validation Messages */
            .ltl-validation-message {
                margin-top: 10px;
                min-height: 20px;
            }

            .ltl-validation-success {
                color: #A3BE8C;
                background-color: rgba(163, 190, 140, 0.1);
                padding: 12px;
                border-radius: 5px;
                border-left: 4px solid #A3BE8C;
            }

            .ltl-validation-error {
                color: #BF616A;
                background-color: rgba(191, 97, 106, 0.1);
                padding: 12px;
                border-radius: 5px;
                border-left: 4px solid #BF616A;
            }

            .ltl-validation-details {
                margin-top: 8px;
                font-size: 13px;
                opacity: 0.9;
            }

            /* Help Panel */
            .ltl-help-panel {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 20px;
                margin-top: 15px;
                border: 1px solid #4C566A;
            }

            .ltl-help-panel h4 {
                margin: 0 0 15px 0;
                color: #88C0D0;
                font-size: 16px;
            }

            .ltl-help-grid {
                display: grid;
                grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
                gap: 20px;
            }

            .ltl-help-category h5 {
                margin: 0 0 10px 0;
                color: #E5E9F0;
                font-size: 14px;
                border-bottom: 1px solid #434C5E;
                padding-bottom: 5px;
            }

            .ltl-help-category ul {
                margin: 0;
                padding-left: 0;
                list-style: none;
            }

            .ltl-help-category li {
                margin-bottom: 8px;
                font-size: 13px;
                color: #D8DEE9;
            }

            .ltl-help-category code {
                background-color: #434C5E;
                color: #88C0D0;
                padding: 2px 6px;
                border-radius: 3px;
                font-family: 'Consolas', 'Monaco', 'Courier New', monospace;
            }

            /* Available Elements */
            .ltl-available-elements {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 15px;
                border: 1px solid #4C566A;
            }

            .ltl-available-elements h4 {
                margin: 0 0 15px 0;
                color: #E5E9F0;
                font-size: 15px;
            }

            .ltl-elements-grid {
                display: grid;
                grid-template-columns: 1fr 1fr;
                gap: 20px;
            }

            .ltl-element-category h5 {
                margin: 0 0 10px 0;
                color: #88C0D0;
                font-size: 13px;
                text-transform: uppercase;
                letter-spacing: 0.5px;
            }

            .ltl-element-list {
                display: flex;
                flex-wrap: wrap;
                gap: 6px;
            }

            .ltl-element-tag {
                background-color: #5E81AC;
                color: #ECEFF4;
                padding: 4px 10px;
                border-radius: 15px;
                font-size: 12px;
                cursor: pointer;
                transition: all 0.2s;
                border: 1px solid transparent;
            }

            .ltl-element-tag:hover {
                background-color: #81A1C1;
                transform: translateY(-1px);
                box-shadow: 0 2px 5px rgba(0, 0, 0, 0.2);
            }

            .ltl-place-tag {
                background-color: #A3BE8C;
            }

            .ltl-place-tag:hover {
                background-color: #B4CFB0;
            }

            .ltl-variable-tag {
                background-color: #EBCB8B;
                color: #2E3440;
            }

            .ltl-variable-tag:hover {
                background-color: #F0D49C;
            }

            .ltl-no-elements {
                color: #4C566A;
                font-style: italic;
                font-size: 12px;
            }

            /* Controls Section */
            .ltl-controls-section {
                margin: 25px 0;
            }

            .ltl-button-group {
                display: flex;
                gap: 15px;
                justify-content: center;
            }

            .ltl-primary-button {
                background-color: #A3BE8C;
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
                background-color: #B4CFB0;
                transform: translateY(-2px);
                box-shadow: 0 4px 12px rgba(0, 0, 0, 0.2);
            }

            .ltl-primary-button:disabled {
                background-color: #4C566A;
                color: #D8DEE9;
                cursor: not-allowed;
                transform: none;
                box-shadow: none;
            }

            .ltl-secondary-button {
                background-color: #5E81AC;
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
                background-color: #81A1C1;
            }

            /* Results Section */
            .ltl-results-section {
                background-color: #434C5E;
                border-radius: 8px;
                padding: 20px;
                margin-top: 20px;
                border: 1px solid #4C566A;
            }

            /* Progress */
            .ltl-progress-container {
                margin-bottom: 20px;
            }

            .ltl-progress-header h4 {
                margin: 0 0 10px 0;
                color: #88C0D0;
                font-size: 16px;
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
                height: 8px;
                background-color: #2E3440;
                border-radius: 4px;
                overflow: hidden;
                border: 1px solid #4C566A;
            }

            .ltl-progress-fill {
                height: 100%;
                background: linear-gradient(90deg, #88C0D0, #A3BE8C);
                border-radius: 4px;
                transition: width 0.3s ease;
            }

            .ltl-progress-step {
                color: #D8DEE9;
                font-size: 14px;
                margin-top: 12px;
                text-align: center;
            }

            /* Spinner */
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

            /* Result Display */
            .ltl-result-header {
                display: flex;
                align-items: center;
                gap: 20px;
                padding: 20px;
                border-radius: 8px;
                margin-bottom: 20px;
            }

            .ltl-result-satisfied {
                background-color: rgba(163, 190, 140, 0.2);
                border: 2px solid #A3BE8C;
            }

            .ltl-result-violated {
                background-color: rgba(191, 97, 106, 0.2);
                border: 2px solid #BF616A;
            }

            .ltl-result-error {
                background-color: rgba(208, 135, 112, 0.2);
                border: 2px solid #D08770;
            }

            .ltl-result-icon {
                font-size: 32px;
            }

            .ltl-result-status {
                font-size: 18px;
                font-weight: 600;
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
                padding: 15px;
                border-radius: 6px;
                margin-bottom: 20px;
                border-left: 4px solid #88C0D0;
            }

            /* Counterexample */
            .ltl-counterexample {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 15px;
                margin-bottom: 20px;
                border-left: 4px solid #BF616A;
            }

            .ltl-counterexample h4 {
                margin: 0 0 15px 0;
                color: #BF616A;
            }

            .ltl-trace {
                background-color: #434C5E;
                border-radius: 5px;
                padding: 10px;
                max-height: 300px;
                overflow-y: auto;
            }

            .ltl-trace-step {
                display: flex;
                align-items: flex-start;
                gap: 15px;
                padding: 10px;
                border-bottom: 1px solid #4C566A;
            }

            .ltl-trace-step:last-child {
                border-bottom: none;
            }

            .ltl-trace-step-number {
                background-color: #5E81AC;
                color: #ECEFF4;
                width: 25px;
                height: 25px;
                border-radius: 50%;
                display: flex;
                align-items: center;
                justify-content: center;
                font-size: 12px;
                font-weight: 600;
                flex-shrink: 0;
            }

            .ltl-trace-action {
                font-weight: 500;
                color: #88C0D0;
                margin-bottom: 5px;
            }

            .ltl-trace-state {
                font-size: 13px;
                color: #D8DEE9;
            }

            /* Statistics */
            .ltl-statistics {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 15px;
                border-left: 4px solid #EBCB8B;
            }

            .ltl-statistics h4 {
                margin: 0 0 15px 0;
                color: #EBCB8B;
            }

            .ltl-stats-grid {
                display: grid;
                grid-template-columns: repeat(auto-fit, minmax(150px, 1fr));
                gap: 15px;
            }

            .ltl-stat {
                display: flex;
                justify-content: space-between;
                align-items: center;
                padding: 8px 0;
                border-bottom: 1px solid #434C5E;
            }

            .ltl-stat:last-child {
                border-bottom: none;
            }

            .ltl-stat-label {
                color: #D8DEE9;
                font-size: 13px;
            }

            .ltl-stat-value {
                color: #E5E9F0;
                font-weight: 600;
            }

            /* Error Details */
            .ltl-error-details {
                background-color: #2E3440;
                border-radius: 6px;
                padding: 15px;
                border-left: 4px solid #BF616A;
            }

            .ltl-error-details h4 {
                margin: 0 0 15px 0;
                color: #BF616A;
            }

            .ltl-error-message {
                background-color: #434C5E;
                color: #E5E9F0;
                padding: 15px;
                border-radius: 5px;
                overflow-x: auto;
                font-size: 13px;
                margin: 0;
                white-space: pre-wrap;
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
 * LTL Parser for Data Petri Nets
 * Parses LTL_f formulas with data constraints
 */
class LTLParser {
    constructor() {
        this.tokens = [];
        this.position = 0;
        this.availableAtoms = [];
        this.constraints = [];
    }

    /**
     * Parse an LTL_f formula
     */
    parse(formula, availableAtoms = []) {
        this.availableAtoms = availableAtoms;
        this.constraints = [];
        
        try {
            // Normalize the formula
            const normalizedFormula = this.normalizeFormula(formula);
            
            // Tokenize
            this.tokens = this.tokenize(normalizedFormula);
            this.position = 0;
            
            // Parse the formula
            const ast = this.parseFormula();
            
            // Validate atoms and collect constraints
            const validationResult = this.validateAST(ast);
            
            if (!validationResult.valid) {
                return validationResult;
            }
            
            return {
                valid: true,
                ast: ast,
                structure: this.astToString(ast),
                constraints: this.constraints
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
     * Normalize formula by replacing Unicode operators with ASCII equivalents
     */
    normalizeFormula(formula) {
        return formula
            .replace(/◇/g, 'F')      // Eventually
            .replace(/□/g, 'G')      // Globally  
            .replace(/○/g, 'X')      // Next
            .replace(/∧/g, '&')      // AND
            .replace(/∨/g, '|')      // OR
            .replace(/¬/g, '!')      // NOT
            .replace(/→/g, '->')     // Implies
            .replace(/≤/g, '<=')     // Less than or equal
            .replace(/≥/g, '>=')     // Greater than or equal
            .replace(/≠/g, '!=')     // Not equal
            .trim();
    }

    /**
     * Tokenize the formula
     */
    tokenize(formula) {
        const tokenRegex = /(\(|\)|F|G|X|U|&|\||!|->|<=|>=|!=|==|<|>|=|\w+|\d+(?:\.\d+)?)/g;
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
     * Determine token type
     */
    getTokenType(value) {
        const temporalOps = ['F', 'G', 'X', 'U'];
        const logicalOps = ['&', '|', '!', '->'];
        const comparisonOps = ['<', '>', '<=', '>=', '=', '!=', '=='];
        
        if (value === '(' || value === ')') return 'PAREN';
        if (temporalOps.includes(value)) return 'TEMPORAL';
        if (logicalOps.includes(value)) return 'LOGICAL';
        if (comparisonOps.includes(value)) return 'COMPARISON';
        if (/^\d+(\.\d+)?$/.test(value)) return 'NUMBER';
        if (/^\w+$/.test(value)) return 'IDENTIFIER';
        
        return 'UNKNOWN';
    }

    /**
     * Parse the main formula
     */
    parseFormula() {
        return this.parseImplication();
    }

    /**
     * Parse implication (lowest precedence)
     */
    parseImplication() {
        let left = this.parseOr();
        
        while (this.peek() && this.peek().value === '->') {
            this.consume('->');
            const right = this.parseOr();
            left = { type: 'IMPLIES', left, right };
        }
        
        return left;
    }

    /**
     * Parse OR operations
     */
    parseOr() {
        let left = this.parseAnd();
        
        while (this.peek() && this.peek().value === '|') {
            this.consume('|');
            const right = this.parseAnd();
            left = { type: 'OR', left, right };
        }
        
        return left;
    }

    /**
     * Parse AND operations
     */
    parseAnd() {
        let left = this.parseUntil();
        
        while (this.peek() && this.peek().value === '&') {
            this.consume('&');
            const right = this.parseUntil();
            left = { type: 'AND', left, right };
        }
        
        return left;
    }

    /**
     * Parse Until operations
     */
    parseUntil() {
        let left = this.parseUnary();
        
        while (this.peek() && this.peek().value === 'U') {
            this.consume('U');
            const right = this.parseUnary();
            left = { type: 'UNTIL', left, right };
        }
        
        return left;
    }

    /**
     * Parse unary operations (temporal and logical)
     */
    parseUnary() {
        const token = this.peek();
        
        if (token && (token.value === 'F' || token.value === 'G' || token.value === 'X')) {
            const op = this.consume().value;
            const operand = this.parseUnary();
            return { type: op, operand };
        }
        
        if (token && token.value === '!') {
            this.consume('!');
            const operand = this.parseUnary();
            return { type: 'NOT', operand };
        }
        
        return this.parseAtom();
    }

    /**
     * Parse atomic formulas (constraints, propositions, parentheses)
     */
    parseAtom() {
        const token = this.peek();
        
        if (!token) {
            throw new Error('Unexpected end of formula');
        }
        
        if (token.value === '(') {
            this.consume('(');
            const formula = this.parseFormula();
            this.consume(')');
            return formula;
        }
        
        if (token.type === 'IDENTIFIER') {
            return this.parseConstraintOrAtom();
        }
        
        throw new Error(`Unexpected token: ${token.value}`);
    }

    /**
     * Parse a constraint or atomic proposition
     */
    parseConstraintOrAtom() {
        const identifier = this.consume().value;
        const nextToken = this.peek();
        
        if (nextToken && nextToken.type === 'COMPARISON') {
            // This is a constraint
            const operator = this.consume().value;
            const rightToken = this.peek();
            
            if (!rightToken) {
                throw new Error(`Expected value after ${operator}`);
            }
            
            let value;
            if (rightToken.type === 'NUMBER') {
                value = parseFloat(this.consume().value);
            } else if (rightToken.type === 'IDENTIFIER') {
                value = this.consume().value;
            } else {
                throw new Error(`Invalid constraint value: ${rightToken.value}`);
            }
            
            const constraint = { type: 'CONSTRAINT', variable: identifier, operator, value };
            this.constraints.push(`${identifier} ${operator} ${value}`);
            return constraint;
        } else {
            // This is an atomic proposition
            return { type: 'ATOM', name: identifier };
        }
    }

    /**
     * Peek at the current token without consuming it
     */
    peek() {
        return this.position < this.tokens.length ? this.tokens[this.position] : null;
    }

    /**
     * Consume the current token
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
     * Validate the AST and check for unknown atoms
     */
    validateAST(ast) {
        const unknownAtoms = [];
        this.collectAtoms(ast, unknownAtoms);
        
        const invalidAtoms = unknownAtoms.filter(atom => 
            !this.availableAtoms.includes(atom)
        );
        
        if (invalidAtoms.length > 0) {
            return {
                valid: false,
                error: `Unknown atoms: ${invalidAtoms.join(', ')}`,
                suggestion: `Available atoms: ${this.availableAtoms.join(', ')}`
            };
        }
        
        return { valid: true };
    }

    /**
     * Collect all atoms from the AST
     */
    collectAtoms(ast, atoms) {
        if (!ast) return;
        
        if (ast.type === 'ATOM') {
            if (!atoms.includes(ast.name)) {
                atoms.push(ast.name);
            }
        } else if (ast.type === 'CONSTRAINT') {
            if (!atoms.includes(ast.variable)) {
                atoms.push(ast.variable);
            }
        } else {
            // Recursively check child nodes
            if (ast.left) this.collectAtoms(ast.left, atoms);
            if (ast.right) this.collectAtoms(ast.right, atoms);
            if (ast.operand) this.collectAtoms(ast.operand, atoms);
        }
    }

    /**
     * Convert AST back to string representation
     */
    astToString(ast) {
        if (!ast) return '';
        
        switch (ast.type) {
            case 'ATOM':
                return ast.name;
            case 'CONSTRAINT':
                return `${ast.variable} ${ast.operator} ${ast.value}`;
            case 'AND':
                return `(${this.astToString(ast.left)} ∧ ${this.astToString(ast.right)})`;
            case 'OR':
                return `(${this.astToString(ast.left)} ∨ ${this.astToString(ast.right)})`;
            case 'IMPLIES':
                return `(${this.astToString(ast.left)} → ${this.astToString(ast.right)})`;
            case 'UNTIL':
                return `(${this.astToString(ast.left)} U ${this.astToString(ast.right)})`;
            case 'F':
                return `◇${this.astToString(ast.operand)}`;
            case 'G':
                return `□${this.astToString(ast.operand)}`;
            case 'X':
                return `○${this.astToString(ast.operand)}`;
            case 'NOT':
                return `¬${this.astToString(ast.operand)}`;
            default:
                return `[${ast.type}]`;
        }
    }

    /**
     * Get suggestion for common errors
     */
    getSuggestion(error) {
        if (error.includes('Unknown atoms')) {
            return 'Click on available places and variables below to insert them into your formula.';
        }
        if (error.includes('Unexpected token')) {
            return 'Check the syntax. Use F for eventually, G for always, X for next, U for until.';
        }
        if (error.includes('Expected')) {
            return 'Make sure all parentheses are properly matched and operators have operands.';
        }
        return 'Check the syntax reference above for correct LTL_f formula structure.';
    }
}

/**
 * LTL Verifier implementing the algorithm from the paper
 */
/**
 * Complete Fixed LTL Verifier with proper display formatting and temporal operator handling
 */
class LTLVerifier {
    constructor(petriNet, formula) {
        this.petriNet = petriNet;
        this.formula = formula;
        this.parser = new LTLParser();
        this.startTime = 0;
        this.statistics = {
            statesExplored: 0,
            transitionsFired: 0,
            automatonStates: 0,
            productStates: 0
        };
    }

    /**
     * Main verification method - CORRECTED LOGIC
     */
    async verify(progressCallback) {
        this.startTime = Date.now();
        
        try {
            progressCallback(10, "Parsing LTL formula...");
            await this.delay(100);
            
            // Parse the formula
            const availableAtoms = this.getAvailableAtoms();
            const parseResult = this.parser.parse(this.formula, availableAtoms);
            
            if (!parseResult.valid) {
                throw new Error(`Formula parsing failed: ${parseResult.error}`);
            }
            
            console.log("Parsed formula AST:", parseResult.ast);
            
            progressCallback(25, "Constructing Büchi automaton for negated formula...");
            await this.delay(200);
            
            // CRITICAL FIX: Construct automaton for ¬φ (negation of original formula)
            const negatedFormula = { type: 'NOT', operand: parseResult.ast };
            const automaton = this.constructBuchiAutomaton(negatedFormula);
            this.statistics.automatonStates = automaton.states.size;
            
            console.log("Automaton states:", automaton.states.size);
            console.log("Automaton accepting states:", automaton.acceptingStates.size);
            
            progressCallback(50, "Building product automaton...");
            await this.delay(300);
            
            // Construct product of Petri net and automaton for ¬φ
            const product = this.constructProductAutomaton(automaton);
            this.statistics.productStates = product.states.size;
            
            console.log("Product states:", product.states.size);
            console.log("Product accepting states:", product.acceptingStates.size);
            
            progressCallback(75, "Checking for accepting cycles...");
            await this.delay(400);
            
            // Check for accepting runs
            const result = this.checkBuchiAcceptance(product);
            
            console.log("Has accepting run (for ¬φ):", result.hasAcceptingRun);
            console.log("Final result (φ satisfied):", !result.hasAcceptingRun);
            
            progressCallback(100, "Verification complete!");
            await this.delay(100);
            
            const executionTime = Date.now() - this.startTime;
            
            // CRITICAL FIX: Invert the result logic
            // If we find an accepting run in product with ¬φ, then φ is VIOLATED
            // If no accepting run in product with ¬φ, then φ is SATISFIED
            return {
                satisfied: !result.hasAcceptingRun,  // INVERTED!
                counterexample: result.hasAcceptingRun ? this.buildCounterexample(result.witness) : null,
                witness: result.hasAcceptingRun ? null : result.witness,
                statistics: this.statistics,
                executionTime
            };
            
        } catch (error) {
            console.error("LTL Verification error:", error);
            throw error;
        }
    }

    /**
     * Improved Büchi automaton construction
     */
    constructBuchiAutomaton(formula) {
        const states = new Set();
        const initialStates = new Set();
        const acceptingStates = new Set();
        const transitions = new Map();
        let stateCounter = 0;
        
        // Create state names
        const createState = () => `q${stateCounter++}`;
        
        // Recursive construction based on formula structure
        const buildAutomaton = (subformula) => {
            console.log("Building automaton for:", subformula.type, subformula);
            
            switch (subformula.type) {
                case 'ATOM':
                case 'CONSTRAINT':
                    return this.buildAtomicAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'NOT':
                    return this.buildNegationAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'AND':
                    return this.buildConjunctionAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'OR':
                    return this.buildDisjunctionAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'F': // Finally
                    return this.buildFinallyAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'G': // Globally  
                    return this.buildGloballyAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'X': // Next
                    return this.buildNextAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'UNTIL':
                    return this.buildUntilAutomaton(subformula, createState, states, transitions, acceptingStates);
                    
                case 'IMPLIES':
                    // A -> B is equivalent to !A | B
                    const impliesAsOr = {
                        type: 'OR',
                        left: { type: 'NOT', operand: subformula.left },
                        right: subformula.right
                    };
                    return buildAutomaton(impliesAsOr);
                    
                default:
                    console.warn(`Unsupported formula type: ${subformula.type}, treating as atomic`);
                    return this.buildAtomicAutomaton(subformula, createState, states, transitions, acceptingStates);
            }
        };
        
        const { initial, accepting } = buildAutomaton(formula);
        initialStates.add(initial);
        if (accepting) acceptingStates.add(accepting);
        
        return {
            states,
            initialStates,
            acceptingStates,
            transitions,
            alphabet: this.getFormulaAlphabet(formula)
        };
    }

    /**
     * Build automaton for atomic proposition
     */
    buildAtomicAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q1);
        
        // q0 --[formula]--> q1
        // q1 --[true]--> q1
        transitions.set(q0, [
            { target: q1, condition: formula },
            { target: q0, condition: { type: 'NOT', operand: formula } }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Build automaton for negation
     */
    buildNegationAutomaton(formula, createState, states, transitions, acceptingStates) {
        const operand = formula.operand;
        
        if (operand.type === 'ATOM' || operand.type === 'CONSTRAINT') {
            const q0 = createState();
            const q1 = createState();
            
            states.add(q0);
            states.add(q1);
            acceptingStates.add(q1);
            
            const negatedCondition = { type: 'NOT', operand };
            
            transitions.set(q0, [
                { target: q1, condition: negatedCondition },
                { target: q0, condition: operand }
            ]);
            transitions.set(q1, [
                { target: q1, condition: { type: 'TRUE' } }
            ]);
            
            return { initial: q0, accepting: q1 };
        } else if (operand.type === 'F') {
            // ¬F φ = G ¬φ
            const globallyNegated = {
                type: 'G',
                operand: { type: 'NOT', operand: operand.operand }
            };
            return this.buildGloballyAutomaton(globallyNegated, createState, states, transitions, acceptingStates);
        } else if (operand.type === 'G') {
            // ¬G φ = F ¬φ
            const finallyNegated = {
                type: 'F',
                operand: { type: 'NOT', operand: operand.operand }
            };
            return this.buildFinallyAutomaton(finallyNegated, createState, states, transitions, acceptingStates);
        } else {
            // For complex negations, use generic approach
            const inner = this.buildGenericAutomaton(operand, createState, states, transitions, acceptingStates);
            return inner;
        }
    }

    /**
     * Build automaton for F φ (Eventually)
     */
    buildFinallyAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q1);
        
        const phi = formula.operand;
        
        // q0 --[¬φ]--> q0 (wait for φ)
        // q0 --[φ]--> q1 (φ becomes true)
        // q1 --[true]--> q1 (φ was satisfied)
        transitions.set(q0, [
            { target: q0, condition: { type: 'NOT', operand: phi } },
            { target: q1, condition: phi }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Build automaton for G φ (Globally)
     */
    buildGloballyAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q0); // q0 is accepting (φ always holds)
        
        const phi = formula.operand;
        
        // q0 --[φ]--> q0 (φ continues to hold)
        // q0 --[¬φ]--> q1 (φ violated)
        // q1 --[true]--> q1 (sink - φ was violated)
        transitions.set(q0, [
            { target: q0, condition: phi },
            { target: q1, condition: { type: 'NOT', operand: phi } }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q0 };
    }

    /**
     * Build automaton for X φ (Next)
     */
    buildNextAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        const q2 = createState();
        
        states.add(q0);
        states.add(q1);
        states.add(q2);
        acceptingStates.add(q2);
        
        const phi = formula.operand;
        
        // q0 --[true]--> q1 (first step)
        // q1 --[φ]--> q2 (φ holds in next state)
        // q1 --[¬φ]--> sink (φ doesn't hold in next state)
        // q2 --[true]--> q2 (requirement satisfied)
        transitions.set(q0, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        transitions.set(q1, [
            { target: q2, condition: phi },
            { target: q0, condition: { type: 'NOT', operand: phi } }
        ]);
        transitions.set(q2, [
            { target: q2, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q2 };
    }

    /**
     * Build automaton for φ U ψ (Until)
     */
    buildUntilAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        const q2 = createState();
        
        states.add(q0);
        states.add(q1);
        states.add(q2);
        acceptingStates.add(q1);
        
        const phi = formula.left;
        const psi = formula.right;
        
        const phiAndNotPsi = {
            type: 'AND',
            left: phi,
            right: { type: 'NOT', operand: psi }
        };
        
        const notPhiAndNotPsi = {
            type: 'AND',
            left: { type: 'NOT', operand: phi },
            right: { type: 'NOT', operand: psi }
        };
        
        transitions.set(q0, [
            { target: q0, condition: phiAndNotPsi },
            { target: q1, condition: psi },
            { target: q2, condition: notPhiAndNotPsi }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        transitions.set(q2, [
            { target: q2, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Build automaton for conjunction
     */
    buildConjunctionAutomaton(formula, createState, states, transitions, acceptingStates) {
        // For A ∧ B, both must be true
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q1);
        
        transitions.set(q0, [
            { target: q1, condition: formula },
            { target: q0, condition: { type: 'NOT', operand: formula } }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Build automaton for disjunction
     */
    buildDisjunctionAutomaton(formula, createState, states, transitions, acceptingStates) {
        // For A ∨ B, either can be true
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q1);
        
        transitions.set(q0, [
            { target: q1, condition: formula },
            { target: q0, condition: { type: 'NOT', operand: formula } }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Generic automaton builder for complex formulas
     */
    buildGenericAutomaton(formula, createState, states, transitions, acceptingStates) {
        const q0 = createState();
        const q1 = createState();
        
        states.add(q0);
        states.add(q1);
        acceptingStates.add(q1);
        
        transitions.set(q0, [
            { target: q1, condition: formula },
            { target: q0, condition: { type: 'NOT', operand: formula } }
        ]);
        transitions.set(q1, [
            { target: q1, condition: { type: 'TRUE' } }
        ]);
        
        return { initial: q0, accepting: q1 };
    }

    /**
     * Get alphabet (atomic propositions) from formula
     */
    getFormulaAlphabet(formula) {
        const atoms = new Set();
        
        const extract = (f) => {
            if (!f) return;
            
            switch (f.type) {
                case 'ATOM':
                    atoms.add(f.name);
                    break;
                case 'CONSTRAINT':
                    atoms.add(f.variable);
                    break;
                case 'AND':
                case 'OR':
                case 'UNTIL':
                case 'IMPLIES':
                    extract(f.left);
                    extract(f.right);
                    break;
                case 'NOT':
                case 'F':
                case 'G':
                case 'X':
                    extract(f.operand);
                    break;
            }
        };
        
        extract(formula);
        return Array.from(atoms);
    }

    /**
     * Construct product automaton
     */
    constructProductAutomaton(automaton) {
        const productStates = new Set();
        const productTransitions = new Map();
        const productAcceptingStates = new Set();
        const initialMarking = this.getInitialMarking();
        const initialValuation = this.getInitialValuation();
        
        // Create initial product states for each automaton initial state
        const initialProductStates = [];
        for (const autoState of automaton.initialStates) {
            const initialProductState = {
                marking: initialMarking,
                valuation: initialValuation,
                automatonState: autoState
            };
            const stateKey = this.serializeState(initialProductState);
            productStates.add(stateKey);
            initialProductStates.push(stateKey);
            
            if (automaton.acceptingStates.has(autoState)) {
                productAcceptingStates.add(stateKey);
            }
        }
        
        // BFS to construct reachable product states
        const queue = [...initialProductStates.map(key => this.deserializeState(key))];
        const visited = new Set(initialProductStates);
        
        let maxStates = 10000; // Prevent infinite loops
        let stateCount = 0;
        
        while (queue.length > 0 && stateCount < maxStates) {
            const currentState = queue.shift();
            const currentKey = this.serializeState(currentState);
            this.statistics.statesExplored++;
            stateCount++;
            
            // Get enabled transitions in current Petri net state
            const enabledTransitions = this.getEnabledTransitions(currentState);
            
            for (const transitionId of enabledTransitions) {
                const nextPetriState = this.fireTransitionInState(currentState, transitionId);
                
                if (nextPetriState) {
                    // Check automaton transitions
                    const automatonTransitions = automaton.transitions.get(currentState.automatonState) || [];
                    
                    for (const autoTransition of automatonTransitions) {
                        if (this.evaluateAutomatonCondition(autoTransition.condition, nextPetriState)) {
                            const nextProductState = {
                                marking: nextPetriState.marking,
                                valuation: nextPetriState.valuation,
                                automatonState: autoTransition.target
                            };
                            
                            const nextKey = this.serializeState(nextProductState);
                            
                            if (!visited.has(nextKey)) {
                                visited.add(nextKey);
                                productStates.add(nextKey);
                                queue.push(nextProductState);
                                
                                if (automaton.acceptingStates.has(autoTransition.target)) {
                                    productAcceptingStates.add(nextKey);
                                }
                            }
                            
                            // Add transition
                            if (!productTransitions.has(currentKey)) {
                                productTransitions.set(currentKey, []);
                            }
                            productTransitions.get(currentKey).push({
                                target: nextKey,
                                transitionId,
                                targetState: nextProductState
                            });
                        }
                    }
                }
            }
        }
        
        return {
            states: productStates,
            transitions: productTransitions,
            initialStates: new Set(initialProductStates),
            acceptingStates: productAcceptingStates
        };
    }

    /**
     * CORRECTED: Check for accepting runs - returns whether accepting run exists
     */
    checkBuchiAcceptance(product) {
        // Find strongly connected components
        const sccs = this.findStronglyConnectedComponents(product);
        
        // Check each SCC for accepting states and reachability
        for (const scc of sccs) {
            const hasAcceptingState = scc.some(state => 
                product.acceptingStates.has(state));
                
            if (hasAcceptingState) {
                // Check if SCC is reachable from any initial state
                for (const initialState of product.initialStates) {
                    const pathToSCC = this.findPathToSCC(product, initialState, scc);
                    if (pathToSCC) {
                        // Found accepting run
                        const cycle = this.findCycleInSCC(product, scc);
                        return { 
                            hasAcceptingRun: true,
                            witness: {
                                prefix: pathToSCC,
                                cycle: cycle
                            }
                        };
                    }
                }
            }
        }
        
        // No accepting run found
        return {
            hasAcceptingRun: false,
            witness: null
        };
    }

    /**
     * Enhanced formula evaluation in state - FIXED for temporal operators
     */
    evaluateFormulaInState(formula, state, trace = null, position = 0) {
        if (!formula) return true;
        
        switch (formula.type) {
            case 'TRUE':
                return true;
                
            case 'FALSE':
                return false;
                
            case 'ATOM':
                // Check if place is marked
                return (state.marking[formula.name] || 0) > 0;
                
            case 'CONSTRAINT':
                // Evaluate data constraint
                const varValue = state.valuation[formula.variable];
                if (varValue === undefined) {
                    console.warn(`Variable ${formula.variable} not found in valuation:`, state.valuation);
                    return false;
                }
                const result = this.evaluateConstraint(varValue, formula.operator, formula.value);
                console.log(`Constraint ${formula.variable} ${formula.operator} ${formula.value}: ${varValue} => ${result}`);
                return result;
                
            case 'AND':
                return this.evaluateFormulaInState(formula.left, state, trace, position) && 
                       this.evaluateFormulaInState(formula.right, state, trace, position);
                       
            case 'OR':
                return this.evaluateFormulaInState(formula.left, state, trace, position) || 
                       this.evaluateFormulaInState(formula.right, state, trace, position);
                       
            case 'NOT':
                return !this.evaluateFormulaInState(formula.operand, state, trace, position);
                
            case 'IMPLIES':
                const left = this.evaluateFormulaInState(formula.left, state, trace, position);
                const right = this.evaluateFormulaInState(formula.right, state, trace, position);
                return !left || right; // ¬left ∨ right
                
            // Temporal operators should NOT be evaluated here - they're handled by the automaton
            case 'F':
            case 'G': 
            case 'X':
            case 'UNTIL':
                console.warn(`Temporal operator ${formula.type} should be handled by automaton, not direct evaluation`);
                return false;
                
            default:
                console.warn(`Unknown formula type in evaluation: ${formula.type}`);
                return false;
        }
    }

    /**
     * Evaluate automaton condition
     */
    evaluateAutomatonCondition(condition, state) {
        return this.evaluateFormulaInState(condition, state);
    }

    /**
     * Get available atomic propositions
     */
    getAvailableAtoms() {
        const atoms = [];
        
        // Add place names
        for (const [id, place] of this.petriNet.places) {
            atoms.push(place.label);
        }
        
        // Add data variable names  
        if (this.petriNet.dataVariables) {
            for (const [id, variable] of this.petriNet.dataVariables) {
                atoms.push(variable.name);
            }
        }
        
        return atoms;
    }

    /**
     * Get initial marking - FIXED to use place labels
     */
    getInitialMarking() {
        const marking = {};
        for (const [id, place] of this.petriNet.places) {
            marking[place.label] = place.tokens || 0;
        }
        return marking;
    }

    /**
     * Get initial data valuation - FIXED to use variable names
     */
    getInitialValuation() {
        const valuation = {};
        if (this.petriNet.dataVariables) {
            for (const [id, variable] of this.petriNet.dataVariables) {
                valuation[variable.name] = variable.getValue ? variable.getValue() : (variable.value || 0);
            }
        }
        return valuation;
    }

    /**
     * Serialize state to string
     */
    serializeState(state) {
        return JSON.stringify({
            marking: state.marking,
            valuation: state.valuation,
            automatonState: state.automatonState
        });
    }

    /**
     * Deserialize state from string
     */
    deserializeState(stateKey) {
        return JSON.parse(stateKey);
    }

    /**
     * Format marking for display - FIXED to show place names properly
     */
    formatMarking(marking) {
        const markedPlaces = Object.entries(marking)
            .filter(([place, tokens]) => tokens > 0)
            .map(([place, tokens]) => `${place}(${tokens})`);
        
        if (markedPlaces.length === 0) return 'empty';
        return markedPlaces.join(', ');
    }

    /**
     * Format data valuation for display - FIXED to show variable names properly  
     */
    formatDataValuation(valuation) {
        const variables = Object.entries(valuation)
            .map(([variable, value]) => `${variable}=${value}`);
            
        if (variables.length === 0) return 'no data';
        return variables.join(', ');
    }

    /**
     * Evaluate constraint - ENHANCED with better type handling
     */
    evaluateConstraint(value, operator, target) {
        // Convert to numbers if possible
        const numValue = typeof value === 'number' ? value : parseFloat(value);
        const numTarget = typeof target === 'number' ? target : parseFloat(target);
        
        // Use numeric comparison if both are valid numbers
        if (!isNaN(numValue) && !isNaN(numTarget)) {
            switch (operator) {
                case '>': return numValue > numTarget;
                case '<': return numValue < numTarget;
                case '>=': return numValue >= numTarget;
                case '<=': return numValue <= numTarget;
                case '=': case '==': return numValue === numTarget;
                case '!=': return numValue !== numTarget;
                default: return false;
            }
        } else {
            // Use string comparison
            switch (operator) {
                case '=': case '==': return value == target;
                case '!=': return value != target;
                default: return false;
            }
        }
    }

    /**
     * Get enabled transitions in state
     */
    getEnabledTransitions(state) {
        const enabled = [];
        
        for (const [id, transition] of this.petriNet.transitions) {
            if (this.isTransitionEnabledInState(id, state)) {
                enabled.push(id);
            }
        }
        
        return enabled;
    }

    /**
     * Check if transition is enabled in state
     */
    isTransitionEnabledInState(transitionId, state) {
        // Check token prerequisites
        const inputArcs = Array.from(this.petriNet.arcs.values())
            .filter(arc => arc.target === transitionId);
        
        for (const arc of inputArcs) {
            const place = this.petriNet.places.get(arc.source);
            if (!place) continue;
            const tokens = state.marking[place.label] || 0;
            if (tokens < (arc.weight || 1)) {
                return false;
            }
        }
        
        // Check data precondition
        const transition = this.petriNet.transitions.get(transitionId);
        if (transition && typeof transition.evaluatePrecondition === 'function') {
            return transition.evaluatePrecondition(state.valuation);
        }
        
        return true;
    }

    /**
     * Fire transition in state - FIXED to use proper place labels
     */
    fireTransitionInState(state, transitionId) {
        if (!this.isTransitionEnabledInState(transitionId, state)) {
            return null;
        }
        
        const newMarking = { ...state.marking };
        const newValuation = { ...state.valuation };
        
        // Update marking
        const inputArcs = Array.from(this.petriNet.arcs.values())
            .filter(arc => arc.target === transitionId);
        const outputArcs = Array.from(this.petriNet.arcs.values())
            .filter(arc => arc.source === transitionId);
        
        for (const arc of inputArcs) {
            const place = this.petriNet.places.get(arc.source);
            if (place) {
                newMarking[place.label] = (newMarking[place.label] || 0) - (arc.weight || 1);
            }
        }
        
        for (const arc of outputArcs) {
            const place = this.petriNet.places.get(arc.target);
            if (place) {
                newMarking[place.label] = (newMarking[place.label] || 0) + (arc.weight || 1);
            }
        }
        
        // Update data valuation
        const transition = this.petriNet.transitions.get(transitionId);
        if (transition && typeof transition.evaluatePostcondition === 'function') {
            const updates = transition.evaluatePostcondition(state.valuation);
            Object.assign(newValuation, updates);
        }
        
        this.statistics.transitionsFired++;
        
        return {
            marking: newMarking,
            valuation: newValuation
        };
    }

    /**
     * Find strongly connected components using Tarjan's algorithm
     */
    findStronglyConnectedComponents(graph) {
        const sccs = [];
        const stack = [];
        const indices = new Map();
        const lowlinks = new Map();
        const onStack = new Set();
        let index = 0;
        
        const strongConnect = (v) => {
            indices.set(v, index);
            lowlinks.set(v, index);
            index++;
            stack.push(v);
            onStack.add(v);
            
            const transitions = graph.transitions.get(v) || [];
            for (const transition of transitions) {
                const w = transition.target;
                if (!indices.has(w)) {
                    strongConnect(w);
                    lowlinks.set(v, Math.min(lowlinks.get(v), lowlinks.get(w)));
                } else if (onStack.has(w)) {
                    lowlinks.set(v, Math.min(lowlinks.get(v), indices.get(w)));
                }
            }
            
            if (lowlinks.get(v) === indices.get(v)) {
                const scc = [];
                let w;
                do {
                    w = stack.pop();
                    onStack.delete(w);
                    scc.push(w);
                } while (w !== v);
                if (scc.length > 0) {
                    sccs.push(scc);
                }
            }
        };
        
        for (const state of graph.states) {
            if (!indices.has(state)) {
                strongConnect(state);
            }
        }
        
        return sccs;
    }

    /**
     * Find path from initial state to SCC
     */
    findPathToSCC(product, initialState, scc) {
        const sccSet = new Set(scc);
        const queue = [{ state: initialState, path: [initialState] }];
        const visited = new Set([initialState]);
        
        while (queue.length > 0) {
            const { state, path } = queue.shift();
            
            if (sccSet.has(state)) {
                return path;
            }
            
            const transitions = product.transitions.get(state) || [];
            for (const transition of transitions) {
                if (!visited.has(transition.target)) {
                    visited.add(transition.target);
                    queue.push({
                        state: transition.target,
                        path: [...path, transition.target]
                    });
                }
            }
        }
        
        return null;
    }

    /**
     * Find a cycle within an SCC
     */
    findCycleInSCC(product, scc) {
        const sccSet = new Set(scc);
        
        for (const startState of scc) {
            const visited = new Set();
            const stack = [{ state: startState, path: [startState] }];
            
            while (stack.length > 0) {
                const { state, path } = stack.pop();
                
                if (path.length > 1 && state === startState) {
                    return path;
                }
                
                if (!visited.has(state)) {
                    visited.add(state);
                    
                    const transitions = product.transitions.get(state) || [];
                    for (const transition of transitions) {
                        if (sccSet.has(transition.target)) {
                            stack.push({
                                state: transition.target,
                                path: [...path, transition.target]
                            });
                        }
                    }
                }
            }
        }
        
        return null;
    }

    /**
     * Build counterexample trace from witness - ENHANCED with better formatting
     */
    buildCounterexample(witness) {
        if (!witness) return null;
        
        const trace = [];
        
        // Add prefix path
        if (witness.prefix) {
            witness.prefix.forEach((stateKey, index) => {
                const state = this.deserializeState(stateKey);
                trace.push({
                    step: index,
                    action: index === 0 ? 'Initial state' : `Transition to step ${index}`,
                    marking: state.marking,
                    dataValuation: state.valuation,
                    automatonState: state.automatonState
                });
            });
        }
        
        // Add cycle (if it exists and is different from prefix)
        if (witness.cycle && witness.cycle.length > 1) {
            const cycleStart = trace.length;
            witness.cycle.slice(1).forEach((stateKey, index) => {
                const state = this.deserializeState(stateKey);
                trace.push({
                    step: cycleStart + index,
                    action: `Cycle step ${index + 1}`,
                    marking: state.marking,
                    dataValuation: state.valuation,
                    automatonState: state.automatonState
                });
            });
        }
        
        return trace;
    }

    /**
     * Utility delay method
     */
    delay(ms) {
        return new Promise(resolve => setTimeout(resolve, ms));
    }
}
// Auto-initialize when DOM is ready and DPN integration is available
document.addEventListener('DOMContentLoaded', () => {
    const initLTLVerification = () => {
        if (window.petriApp && window.dataPetriNetIntegration) {
            if (!window.ltlVerification) {
                console.log("Initializing LTL Verification extension");
                window.ltlVerification = new LTLVerificationExtension(window.petriApp);
            }
        } else {
            // Retry after a short delay
            setTimeout(initLTLVerification, 500);
        }
    };
    
    // Wait for other extensions to load
    setTimeout(initLTLVerification, 1500);
});