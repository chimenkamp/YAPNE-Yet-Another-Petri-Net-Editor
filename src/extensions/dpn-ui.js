import { DataAwareTransition } from './dpn-model.js';

/**
 * Expression Editor Dialog - A sophisticated dialog for creating/editing pre and postconditions
 * with button-based insertion of operators, variables, and primed variables.
 */
class ExpressionEditorDialog {
  /**
   * Create an expression editor dialog
   * @param {Object} options - Configuration options
   * @param {string} options.type - 'precondition' or 'postcondition'
   * @param {string} options.currentExpression - Current expression value
   * @param {Array<{name: string, type: string}>} options.variables - Available variables
   * @param {Function} options.onSave - Callback when expression is saved
   * @param {Function} options.onValidate - Validation function
   */
  constructor(options) {
    this.type = options.type || 'precondition';
    this.currentExpression = options.currentExpression || '';
    this.variables = options.variables || [];
    this.onSave = options.onSave || (() => {});
    this.onValidate = options.onValidate || (() => ({ valid: true }));
    this.dialog = null;
    this.textarea = null;
  }

  /**
   * Get operators for the expression type
   */
  getOperators() {
    if (this.type === 'precondition') {
      return {
        comparison: [
          { label: '>', value: ' > ', description: 'Greater than' },
          { label: '<', value: ' < ', description: 'Less than' },
          { label: '>=', value: ' >= ', description: 'Greater or equal' },
          { label: '<=', value: ' <= ', description: 'Less or equal' },
          { label: '===', value: ' === ', description: 'Strict equal' },
          { label: '!==', value: ' !== ', description: 'Strict not equal' },
          { label: '==', value: ' == ', description: 'Equal' },
          { label: '!=', value: ' != ', description: 'Not equal' }
        ],
        logical: [
          { label: '&&', value: ' && ', description: 'Logical AND' },
          { label: '||', value: ' || ', description: 'Logical OR' },
          { label: '!', value: '!', description: 'Logical NOT' }
        ],
        arithmetic: [
          { label: '+', value: ' + ', description: 'Add' },
          { label: '-', value: ' - ', description: 'Subtract' },
          { label: '*', value: ' * ', description: 'Multiply' },
          { label: '/', value: ' / ', description: 'Divide' },
          { label: '%', value: ' % ', description: 'Modulo' }
        ],
        grouping: [
          { label: '( )', value: '()', description: 'Parentheses', cursorOffset: -1 }
        ],
        values: [
          { label: 'true', value: 'true', description: 'Boolean true' },
          { label: 'false', value: 'false', description: 'Boolean false' }
        ]
      };
    } else {
      // Postcondition operators
      return {
        assignment: [
          { label: "=' =", value: "' = ", description: 'Assignment (primed)', insertPrimed: true },
          { label: ';', value: '; ', description: 'Statement separator' }
        ],
        comparison: [
          { label: '>', value: ' > ', description: 'Greater than (constraint)' },
          { label: '<', value: ' < ', description: 'Less than (constraint)' },
          { label: '>=', value: ' >= ', description: 'Greater or equal (constraint)' },
          { label: '<=', value: ' <= ', description: 'Less or equal (constraint)' },
          { label: '==', value: ' == ', description: 'Equal (constraint)' }
        ],
        arithmetic: [
          { label: '+', value: ' + ', description: 'Add' },
          { label: '-', value: ' - ', description: 'Subtract' },
          { label: '*', value: ' * ', description: 'Multiply' },
          { label: '/', value: ' / ', description: 'Divide' },
          { label: '%', value: ' % ', description: 'Modulo' }
        ],
        logical: [
          { label: '&&', value: ' && ', description: 'Logical AND (for constraints)' },
          { label: '||', value: ' || ', description: 'Logical OR (for constraints)' }
        ],
        grouping: [
          { label: '( )', value: '()', description: 'Parentheses', cursorOffset: -1 }
        ]
      };
    }
  }

  /**
   * Insert text at cursor position in textarea
   */
  insertAtCursor(text, cursorOffset = 0) {
    if (!this.textarea) return;
    
    const start = this.textarea.selectionStart;
    const end = this.textarea.selectionEnd;
    const value = this.textarea.value;
    
    this.textarea.value = value.substring(0, start) + text + value.substring(end);
    
    // Set cursor position
    const newPos = start + text.length + cursorOffset;
    this.textarea.setSelectionRange(newPos, newPos);
    this.textarea.focus();
    
    // Trigger validation
    this.validateExpression();
  }

  /**
   * Validate the current expression
   */
  validateExpression() {
    const expression = this.textarea.value;
    const validationResult = this.onValidate(expression);
    
    const validationStatus = this.dialog.querySelector('#expr-validation-status');
    const validationMessage = this.dialog.querySelector('#expr-validation-message');
    
    if (validationResult.valid) {
      validationStatus.className = 'expr-validation-status valid';
      validationStatus.textContent = '✓ Valid';
      validationMessage.textContent = '';
      this.dialog.querySelector('#btn-save-expression').disabled = false;
    } else {
      validationStatus.className = 'expr-validation-status invalid';
      validationStatus.textContent = '✗ Invalid';
      validationMessage.textContent = validationResult.error || 'Invalid expression';
      this.dialog.querySelector('#btn-save-expression').disabled = true;
    }
  }

  /**
   * Create the dialog HTML
   */
  createDialogHTML() {
    const operators = this.getOperators();
    const isPrecondition = this.type === 'precondition';
    
    // Generate operator buttons HTML
    const generateOperatorSection = (title, ops, className) => {
      if (!ops || ops.length === 0) return '';
      return `
        <div class="expr-operator-section">
          <label>${title}</label>
          <div class="expr-operator-buttons ${className}">
            ${ops.map(op => `
              <button type="button" class="expr-operator-btn" 
                      data-value="${this.escapeHtml(op.value)}" 
                      data-offset="${op.cursorOffset || 0}"
                      title="${this.escapeHtml(op.description)}">
                ${this.escapeHtml(op.label)}
              </button>
            `).join('')}
          </div>
        </div>
      `;
    };

    // Generate variable buttons HTML
    const generateVariableButtons = (primed = false) => {
      if (this.variables.length === 0) {
        return '<p class="expr-no-vars">No variables defined</p>';
      }
      return this.variables.map(v => `
        <button type="button" class="expr-variable-btn" 
                data-value="${primed ? v.name + "'" : v.name}"
                title="${v.type}: ${v.name}${primed ? "' (new value)" : ' (current value)'}">
          ${primed ? v.name + "'" : v.name}
          <span class="expr-var-type">${v.type}</span>
        </button>
      `).join('');
    };

    return `
      <div class="modal-container expr-editor-modal">
        <div class="modal-header">
          <h2>${isPrecondition ? 'Edit Precondition (Guard)' : 'Edit Postcondition (Updates)'}</h2>
          <button class="close-btn">&times;</button>
        </div>
        <div class="modal-body expr-editor-body">
          <!-- Two Column Layout -->
          <div class="expr-two-column-layout">
            <!-- Left Column: Fixed Expression Input -->
            <div class="expr-left-column">
              <!-- Help Section -->
              <div class="expr-help-section">
                <div class="expr-help-toggle">
                  <button type="button" id="btn-toggle-help" class="expr-help-btn">
                    <span class="expr-help-icon">?</span> Quick Help
                  </button>
                </div>
                <div class="expr-help-content" id="expr-help-content" style="display: none;">
                  ${isPrecondition ? `
                    <p><strong>Precondition (Guard):</strong> A boolean expression that must be <code>true</code> for the transition to be enabled.</p>
                    <p><strong>Examples:</strong></p>
                    <ul>
                      <li><code>counter > 0</code> - Enable when counter is positive</li>
                      <li><code>x >= 5 && y < 10</code> - Enable when x ≥ 5 AND y < 10</li>
                      <li><code>status === "ready"</code> - Enable when status equals "ready"</li>
                    </ul>
                  ` : `
                    <p><strong>Postcondition (Updates):</strong> Defines how variables change when the transition fires.</p>
                    <p><strong>Direct Assignment:</strong> Use <code>variable' = expression;</code></p>
                    <p><strong>Constraint-based:</strong> Use <code>variable' > expr; variable' < expr;</code> (solver finds valid value)</p>
                    <p><strong>Examples:</strong></p>
                    <ul>
                      <li><code>counter' = counter + 1;</code> - Increment counter</li>
                      <li><code>x' = x * 2; y' = y - 1;</code> - Double x and decrement y</li>
                      <li><code>n' > n; n' < n + 10;</code> - n increases by 1-9 (random)</li>
                    </ul>
                  `}
                </div>
              </div>

              <!-- Expression Input -->
              <div class="expr-input-section">
                <label for="expr-textarea">Expression</label>
                <textarea id="expr-textarea" class="expr-textarea" rows="8" 
                          placeholder="${isPrecondition ? 'e.g., counter > 0 && status === \"ready\"' : 'e.g., counter\' = counter + 1;'}">${this.escapeHtml(this.currentExpression)}</textarea>
                <div class="expr-validation">
                  <span id="expr-validation-status" class="expr-validation-status"></span>
                  <span id="expr-validation-message" class="expr-validation-message"></span>
                </div>
              </div>
            </div>

            <!-- Right Column: Scrollable Buttons -->
            <div class="expr-right-column">
              <!-- Variables Section -->
              <div class="expr-variables-section">
                <div class="expr-section-header">
                  <h4>Variables</h4>
                </div>
                <div class="expr-variables-grid">
                  <div class="expr-var-column">
                    <label>Current Values</label>
                    <div class="expr-variable-buttons">
                      ${generateVariableButtons(false)}
                    </div>
                  </div>
                  ${!isPrecondition ? `
                    <div class="expr-var-column">
                      <label>New Values (Primed)</label>
                      <div class="expr-variable-buttons primed">
                        ${generateVariableButtons(true)}
                      </div>
                    </div>
                  ` : ''}
                </div>
              </div>

              <!-- Operators Section -->
              <div class="expr-operators-section">
                <div class="expr-section-header">
                  <h4>Operators</h4>
                </div>
                <div class="expr-operators-grid">
                  ${!isPrecondition ? generateOperatorSection('Assignment', operators.assignment, 'assignment') : ''}
                  ${generateOperatorSection('Comparison', operators.comparison, 'comparison')}
                  ${generateOperatorSection('Arithmetic', operators.arithmetic, 'arithmetic')}
                  ${generateOperatorSection('Logical', operators.logical, 'logical')}
                  ${generateOperatorSection('Grouping', operators.grouping, 'grouping')}
                  ${isPrecondition ? generateOperatorSection('Values', operators.values, 'values') : ''}
                </div>
              </div>

              <!-- Quick Templates -->
              <div class="expr-templates-section">
                <div class="expr-section-header">
                  <h4>Quick Templates</h4>
                </div>
                <div class="expr-template-buttons">
                  ${isPrecondition ? `
                    <button type="button" class="expr-template-btn" data-template="var > 0">var > 0</button>
                    <button type="button" class="expr-template-btn" data-template="var === value">var === value</button>
                    <button type="button" class="expr-template-btn" data-template="var1 > var2">var1 > var2</button>
                    <button type="button" class="expr-template-btn" data-template="cond1 && cond2">cond1 && cond2</button>
                    <button type="button" class="expr-template-btn" data-template="cond1 || cond2">cond1 || cond2</button>
                  ` : `
                    <button type="button" class="expr-template-btn" data-template="var' = var + 1;">var' = var + 1;</button>
                    <button type="button" class="expr-template-btn" data-template="var' = var - 1;">var' = var - 1;</button>
                    <button type="button" class="expr-template-btn" data-template="var' = 0;">var' = 0;</button>
                    <button type="button" class="expr-template-btn" data-template="var' > var; var' < var + 10;">var' ∈ (var, var+10)</button>
                    <button type="button" class="expr-template-btn" data-template="var' >= 0; var' <= 100;">var' ∈ [0, 100]</button>
                  `}
                </div>
              </div>
            </div>
          </div>
        </div>
        <div class="modal-footer">
          <button id="btn-clear-expression" type="button" class="expr-btn-secondary">Clear</button>
          <div class="expr-footer-right">
            <button id="btn-cancel-expression" type="button">Cancel</button>
            <button id="btn-save-expression" type="button" class="expr-btn-primary">Save</button>
          </div>
        </div>
      </div>
    `;
  }

  /**
   * Escape HTML special characters
   */
  escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  /**
   * Show the dialog
   */
  show() {
    // Create dialog element
    this.dialog = document.createElement('div');
    this.dialog.className = 'modal-overlay expr-editor-overlay';
    this.dialog.id = 'expression-editor-dialog';
    this.dialog.innerHTML = this.createDialogHTML();
    
    document.body.appendChild(this.dialog);
    
    // Get textarea reference
    this.textarea = this.dialog.querySelector('#expr-textarea');
    
    // Set up event listeners
    this.setupEventListeners();
    
    // Initial validation
    this.validateExpression();
    
    // Focus the textarea
    this.textarea.focus();
  }

  /**
   * Set up event listeners for the dialog
   */
  setupEventListeners() {
    // Close button
    this.dialog.querySelector('.close-btn').addEventListener('click', () => this.close());
    
    // Cancel button
    this.dialog.querySelector('#btn-cancel-expression').addEventListener('click', () => this.close());
    
    // Save button
    this.dialog.querySelector('#btn-save-expression').addEventListener('click', () => {
      this.onSave(this.textarea.value);
      this.close();
    });
    
    // Clear button
    this.dialog.querySelector('#btn-clear-expression').addEventListener('click', () => {
      this.textarea.value = '';
      this.textarea.focus();
      this.validateExpression();
    });
    
    // Help toggle
    this.dialog.querySelector('#btn-toggle-help').addEventListener('click', () => {
      const helpContent = this.dialog.querySelector('#expr-help-content');
      const isVisible = helpContent.style.display !== 'none';
      helpContent.style.display = isVisible ? 'none' : 'block';
    });
    
    // Textarea input for validation
    this.textarea.addEventListener('input', () => this.validateExpression());
    
    // Operator buttons
    this.dialog.querySelectorAll('.expr-operator-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        const value = btn.getAttribute('data-value');
        const offset = parseInt(btn.getAttribute('data-offset') || '0', 10);
        this.insertAtCursor(value, offset);
      });
    });
    
    // Variable buttons
    this.dialog.querySelectorAll('.expr-variable-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        const value = btn.getAttribute('data-value');
        this.insertAtCursor(value);
      });
    });
    
    // Template buttons
    this.dialog.querySelectorAll('.expr-template-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        const template = btn.getAttribute('data-template');
        this.insertAtCursor(template);
      });
    });
    
    // Click outside to close
    this.dialog.addEventListener('click', (e) => {
      if (e.target === this.dialog) {
        this.close();
      }
    });
    
    // Keyboard shortcuts
    this.dialog.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') {
        this.close();
      } else if (e.key === 'Enter' && e.ctrlKey) {
        // Ctrl+Enter to save
        const saveBtn = this.dialog.querySelector('#btn-save-expression');
        if (!saveBtn.disabled) {
          this.onSave(this.textarea.value);
          this.close();
        }
      }
    });
  }

  /**
   * Close the dialog
   */
  close() {
    if (this.dialog && this.dialog.parentNode) {
      document.body.removeChild(this.dialog);
    }
    this.dialog = null;
    this.textarea = null;
  }
}

class DataPetriNetUI {
  /**
   * Initialize the Data Petri Net UI extensions
   * @param {PetriNetApp} app - Reference to the main application
   */
  constructor(app) {
    this.app = app;
    
    // Store the original transition properties method to extend it later
    this.originalShowTransitionProperties = app.showTransitionProperties;
    
    // Initialize UI components
    this.initializeUI();
  }

  /**
   * Initialize UI components
   */
  initializeUI() {
    // Add data variables panel to the sidebar
    this.addDataVariablesPanel();
    
    // Use the existing data values display in index.html
    this.configureDataValuesDisplay();
    
    // Extend the transition properties panel to include data conditions
    this.extendTransitionPropertiesPanel();
    
    // Add help button for data expressions
    this.addDataExpressionHelpButton();
    
    // Extend editor modes to support data transitions
    this.extendEditorModes();
  }

  /**
   * Add the data variables management panel to the sidebar
   */
  addDataVariablesPanel() {
    const sidebar = document.querySelector('#data-variables-content-conatiner');
    if (!sidebar) return;
    
    // Create the data variables panel
    const dataVariablesPanel = document.createElement('div');
    dataVariablesPanel.className = 'data-variables-panel';
    dataVariablesPanel.innerHTML = `
      <div id="data-variables-content">
        <p>No data variables defined.</p>
      </div>
      <div class="toolbar-group">
        <button id="btn-add-data-variable">Add Variable</button>

      </div>
    `;
    
    // Append the panel to the sidebar
    const propertiesPanel = sidebar.querySelector('.properties-panel');
    if (propertiesPanel) {
      sidebar.insertBefore(dataVariablesPanel, propertiesPanel.nextSibling);
    } else {
      sidebar.appendChild(dataVariablesPanel);
    }
    
    // Add event listeners for buttons
    const addBtn = document.getElementById('btn-add-data-variable');
    if (addBtn) {
      addBtn.addEventListener('click', () => this.showAddVariableDialog());
    }
    
    const validateBtn = document.getElementById('btn-validate-expressions');
    if (validateBtn) {
      validateBtn.addEventListener('click', () => this.validateAllExpressions());
    }
    
    // Update the data variables display
    this.updateDataVariablesDisplay();
  }

  /**
   * Configure the existing data values display
   * Instead of creating a new one, we'll use the one in the HTML
   */
  configureDataValuesDisplay() {
    // Update the data values display with current values
    this.updateDataValuesDisplay();
  }

  /**
   * Extend the transition properties panel to include data conditions
   */
  extendTransitionPropertiesPanel() {
    // Override the transition properties display method
    this.app.showTransitionProperties = (id) => {
      // Call the original method first
      this.originalShowTransitionProperties.call(this.app, id);
      
      // Get the transition
      const transition = this.app.api.petriNet.transitions.get(id);
      if (!transition) return;
      
      // Check if it's a data-aware transition
      const isDataAware = typeof transition.evaluatePrecondition === 'function';
      
      // Get the properties panel
      const propertiesPanel = this.app.propertiesPanel;
      if (!propertiesPanel) return;
      
      // Extend the panel for data-aware transitions
      if (isDataAware) {
        // Check if transition is silent - disable data condition fields
        const isSilent = transition.silent || false;
        
        // Check if data condition fields already exist to prevent duplication
        if (!propertiesPanel.querySelector('#precondition-display')) {
          // Find insertion point for data conditions
          const buttonGroup = propertiesPanel.querySelector('.form-group button');
          const insertPoint = buttonGroup ? buttonGroup.closest('.form-group') : null;
          
          const disabledAttr = isSilent ? 'disabled' : '';
          const disabledStyle = isSilent ? 'style="opacity: 0.5; pointer-events: none;"' : '';
          
          // Format the display of expressions (truncate if too long)
          const formatExpression = (expr) => {
            if (!expr || expr.trim() === '') return '<span class="expr-empty">Not set</span>';
            const truncated = expr.length > 50 ? expr.substring(0, 47) + '...' : expr;
            return `<code class="expr-preview">${this.escapeHtml(truncated)}</code>`;
          };
          
          // HTML for data conditions with expression editor buttons
          const dataConditionsHtml = `
            <div class="form-group expr-field-group" ${disabledStyle}>
              <label>Precondition (Guard)</label>
              <div class="expr-display-container">
                <div class="expr-display" id="precondition-display">
                  ${formatExpression(transition.precondition)}
                </div>
                <div class="expr-actions">
                  <button id="btn-edit-precondition" type="button" class="expr-edit-btn" ${disabledAttr} title="Edit with Expression Editor">
                    ✏️ Edit
                  </button>
                  ${transition.precondition ? `<button id="btn-clear-precondition" type="button" class="expr-clear-btn" ${disabledAttr} title="Clear expression">✕</button>` : ''}
                </div>
              </div>
              <small>Boolean expression that must be true for the transition to be enabled</small>
            </div>
            <div class="form-group expr-field-group" ${disabledStyle}>
              <label>Postcondition (Updates)</label>
              <div class="expr-display-container">
                <div class="expr-display" id="postcondition-display">
                  ${formatExpression(transition.postcondition)}
                </div>
                <div class="expr-actions">
                  <button id="btn-edit-postcondition" type="button" class="expr-edit-btn" ${disabledAttr} title="Edit with Expression Editor">
                    ✏️ Edit
                  </button>
                  ${transition.postcondition ? `<button id="btn-clear-postcondition" type="button" class="expr-clear-btn" ${disabledAttr} title="Clear expression">✕</button>` : ''}
                </div>
              </div>
              <small>Format: variable' = expression; (use ' for new values)</small>
            </div>
          `;
          
          // Add the data conditions HTML
          if (insertPoint) {
            // Insert before a specific element
            insertPoint.insertAdjacentHTML('beforebegin', dataConditionsHtml);
          } else {
            // Append to the end
            propertiesPanel.insertAdjacentHTML('beforeend', dataConditionsHtml);
          }
        }
        
        // Get variable names for the expression editor
        const getVariables = () => {
          return Array.from(this.app.api.petriNet.dataVariables.values())
            .map(v => ({ name: v.name, type: v.type }));
        };
        
        // Add event listener for precondition edit button
        const editPreconditionBtn = document.getElementById('btn-edit-precondition');
        if (editPreconditionBtn && !isSilent) {
          editPreconditionBtn.addEventListener('click', () => {
            this.showExpressionEditor({
              type: 'precondition',
              currentExpression: transition.precondition || '',
              transitionId: id
            });
          });
        }
        
        // Add event listener for postcondition edit button
        const editPostconditionBtn = document.getElementById('btn-edit-postcondition');
        if (editPostconditionBtn && !isSilent) {
          editPostconditionBtn.addEventListener('click', () => {
            this.showExpressionEditor({
              type: 'postcondition',
              currentExpression: transition.postcondition || '',
              transitionId: id
            });
          });
        }
        
        // Add event listeners for clear buttons
        const clearPreconditionBtn = document.getElementById('btn-clear-precondition');
        if (clearPreconditionBtn && !isSilent) {
          clearPreconditionBtn.addEventListener('click', () => {
            this.app.api.setTransitionPrecondition(id, '');
            this.app.showTransitionProperties(id);
            this.app.updateTransitionStatus(id);
          });
        }
        
        const clearPostconditionBtn = document.getElementById('btn-clear-postcondition');
        if (clearPostconditionBtn && !isSilent) {
          clearPostconditionBtn.addEventListener('click', () => {
            this.app.api.setTransitionPostcondition(id, '');
            this.app.showTransitionProperties(id);
            this.app.updateTransitionStatus(id);
          });
        }
      } else {
        // For non-data transitions, add a button to convert them
        // Check if convert button already exists to prevent duplication
        if (!propertiesPanel.querySelector('#btn-convert-to-data-transition')) {
          const convertButtonHTML = `
            <div class="form-group">
              <button id="btn-convert-to-data-transition" type="button">Convert to Data Transition</button>
            </div>
          `;
          propertiesPanel.insertAdjacentHTML('beforeend', convertButtonHTML);
          
          // Add event listener for the convert button
          const convertButton = document.getElementById('btn-convert-to-data-transition');
          if (convertButton) {
            convertButton.addEventListener('click', () => this.convertToDataTransition(id));
          }
        }
      }
    };
  }

  /**
   * Show the expression editor dialog
   * @param {Object} options - Options for the editor
   * @param {string} options.type - 'precondition' or 'postcondition'
   * @param {string} options.currentExpression - Current expression value
   * @param {string} options.transitionId - ID of the transition being edited
   */
  showExpressionEditor(options) {
    const variables = Array.from(this.app.api.petriNet.dataVariables.values())
      .map(v => ({ name: v.name, type: v.type }));
    
    const variableNames = variables.map(v => v.name);
    
    const editor = new ExpressionEditorDialog({
      type: options.type,
      currentExpression: options.currentExpression,
      variables: variables,
      onValidate: (expression) => {
        if (options.type === 'precondition') {
          return this.app.api.validatePrecondition(expression, variableNames);
        } else {
          return this.app.api.validatePostcondition(expression, variableNames);
        }
      },
      onSave: (expression) => {
        if (options.type === 'precondition') {
          this.app.api.setTransitionPrecondition(options.transitionId, expression);
        } else {
          this.app.api.setTransitionPostcondition(options.transitionId, expression);
        }
        // Refresh the properties panel
        this.app.showTransitionProperties(options.transitionId);
        this.app.updateTransitionStatus(options.transitionId);
      }
    });
    
    editor.show();
  }

  /**
   * Escape HTML special characters
   */
  escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  /**
   * Add a help button for data expressions
   */
  addDataExpressionHelpButton() {
    // The help button is added in the extended transition properties panel
  }

  /**
   * Extend editor modes to support data transitions
   */
  extendEditorModes() {
    // Find the vertical toolbar
    const toolbar = document.querySelector('.vertical-toolbar .toolbar-group');
    if (!toolbar) return;
    
    // Find the add transition button to add our button after it
    const addTransitionBtn = document.getElementById('btn-add-transition');
    if (addTransitionBtn) {
      // Create the data transition button
      const dataTransitionBtn = document.createElement('button');
      dataTransitionBtn.id = 'btn-add-data-transition';
      dataTransitionBtn.title = 'Add data transition';
      dataTransitionBtn.innerHTML = '⊞'; // Different symbol for data transition
      dataTransitionBtn.className = '';
      
      // Add it after the regular transition button
      addTransitionBtn.insertAdjacentElement('afterend', dataTransitionBtn);
      
      // Add click event handler
      dataTransitionBtn.addEventListener('click', () => {
        this.app.editor.setMode('addDataTransition');
        this.updateActiveButton('btn-add-data-transition');
      });
      
      // Extend the editor with data transition mode
      this.extendEditorWithDataTransitionMode();
    }
  }

  /**
   * Update the active state of toolbar buttons (copied from PetriNetApp)
   * @param {string} activeId - ID of the active button
   */
  updateActiveButton(activeId) {
    const buttons = [
      'btn-select',
      'btn-add-place',
      'btn-add-transition',
      'btn-add-data-transition',
      'btn-add-arc'
    ];
    
    buttons.forEach(id => {
      const button = document.getElementById(id);
      if (button) {
        button.classList.toggle('active', id === activeId);
      }
    });
  }

  /**
   * Extend the editor to handle the data transition mode
   */
  extendEditorWithDataTransitionMode() {
    // Get the original mouse down handler
    const originalHandleMouseDown = this.app.editor.eventListeners.get('mousedown');
    
    // Create a new mouse down handler
    const newMouseDownHandler = (event) => {
      // If not in data transition mode, delegate to original handler
      if (this.app.editor.mode !== 'addDataTransition') {
        return originalHandleMouseDown(event);
      }
      
      // Handle creating a data transition
      const rect = this.app.editor.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;
      
      // Convert to world coordinates
      const worldPos = this.app.editor.renderer.screenToWorld(x, y);
      
      // Apply snap to grid if enabled
      if (this.app.editor.snapToGrid) {
        worldPos.x = Math.round(worldPos.x / this.app.editor.gridSize) * this.app.editor.gridSize;
        worldPos.y = Math.round(worldPos.y / this.app.editor.gridSize) * this.app.editor.gridSize;
      }
      
      // Create the data transition
      const id = this.app.api.createDataTransition(
        worldPos.x, 
        worldPos.y, 
        `DT${this.app.api.petriNet.transitions.size + 1}`
      );
      
      // Select the newly created transition
      this.app.editor.selectElement(id, 'transition');
      this.app.editor.render();
    };
    
    // Replace the mouse down handler
    this.app.editor.canvas.removeEventListener('mousedown', originalHandleMouseDown);
    this.app.editor.canvas.addEventListener('mousedown', newMouseDownHandler);
    this.app.editor.eventListeners.set('mousedown', newMouseDownHandler);
  }

  /**
   * Update the data variables display
   */
  updateDataVariablesDisplay() {
    const container = document.getElementById('data-variables-content');
    if (!container) return;
    
    // Check if there are any data variables
    if (this.app.api.petriNet.dataVariables && this.app.api.petriNet.dataVariables.size > 0) {
      // Create a table to display the variables
      let html = `
        <table class="data-variables-table">
          <tr>
            <th>Name</th>
            <th>Type</th>
            <th>Value</th>
            <th>Actions</th>
          </tr>
      `;
      
      // Add each variable to the table
      for (const [id, variable] of this.app.api.petriNet.dataVariables) {
        html += `
          <tr>
            <td>${variable.name}</td>
            <td>${variable.type}</td>
            <td>${variable.currentValue !== null ? variable.currentValue : '(null)'}</td>
            <td>
              <button class="btn-edit-variable" data-id="${id}">Edit</button>
              <button class="btn-delete-variable" data-id="${id}">Delete</button>
            </td>
          </tr>
        `;
      }
      
      html += '</table>';
      container.innerHTML = html;
      
      // Add event listeners for the edit buttons
      const editButtons = container.querySelectorAll('.btn-edit-variable');
      editButtons.forEach(button => {
        button.addEventListener('click', () => {
          const id = button.getAttribute('data-id');
          this.showEditVariableDialog(id);
        });
      });
      
      // Add event listeners for the delete buttons
      const deleteButtons = container.querySelectorAll('.btn-delete-variable');
      deleteButtons.forEach(button => {
        button.addEventListener('click', () => {
          const id = button.getAttribute('data-id');
          if (confirm('Are you sure you want to delete this variable?')) {
            this.app.api.removeDataVariable(id);
            this.updateDataVariablesDisplay();
            this.updateDataValuesDisplay();
          }
        });
      });
    } else {
      container.innerHTML = '<p>No data variables defined.</p>';
    }
  }

  /**
   * Update the data values display in the simulation panel
   */
  updateDataValuesDisplay() {
    const container = document.getElementById('data-values-content');
    if (!container) return;
    
    // Check if there are any data variables
    if (this.app.api.petriNet.dataVariables && this.app.api.petriNet.dataVariables.size > 0) {
      // Create a table to display the values
      let html = `
        <table class="data-values-table">
          <tr>
            <th>Variable</th>
            <th>Value</th>
            <th>Edit</th>
          </tr>
      `;
      
      // Add each variable to the table
      for (const [id, variable] of this.app.api.petriNet.dataVariables) {
        html += `
          <tr>
            <td>${variable.name}</td>
            <td>${variable.currentValue !== null ? variable.currentValue : '(null)'}</td>
            <td>
              <button class="btn-edit-value" data-id="${id}">Set</button>
            </td>
          </tr>
        `;
      }
      
      html += '</table>';
      container.innerHTML = html;
      
      // Add event listeners for the edit buttons
      const editButtons = container.querySelectorAll('.btn-edit-value');
      editButtons.forEach(button => {
        button.addEventListener('click', () => {
          const id = button.getAttribute('data-id');
          this.showEditValueDialog(id);
        });
      });
    } else {
      container.innerHTML = '<p>No data variables defined.</p>';
    }
  }

/**
 * Show dialog to add a new data variable
 */
showAddVariableDialog() {
  // Create the dialog
  const dialogId = 'add-variable-dialog';
  const dialog = document.createElement('div');
  dialog.className = 'modal-overlay';
  dialog.id = dialogId;
  
  dialog.innerHTML = `
    <div class="modal-container">
      <div class="modal-header">
        <h2>Add Data Variable</h2>
        <button class="close-btn">&times;</button>
      </div>
      <div class="modal-body">
        <div class="form-group">
          <label for="variable-name">Name</label>
          <input type="text" id="variable-name" required>
          <small>Use a valid identifier (letters, numbers, underscore)</small>
        </div>
        <div class="form-group">
          <label for="variable-type">Type</label>
          <select id="variable-type">
            <option value="int">Integer</option>
            <option value="float">Float</option>
            <option value="string">String</option>
            <option value="boolean">Boolean</option>
          </select>
        </div>
        <div class="form-group">
          <label for="variable-initial-value">Initial Value</label>
          <div id="initial-value-container">
            <input type="number" id="variable-initial-value" step="1" placeholder="Enter an integer">
          </div>
        </div>
        <div class="form-group">
          <label for="variable-description">Description</label>
          <textarea id="variable-description" rows="2"></textarea>
        </div>
      </div>
      <div class="modal-footer">
        <button id="btn-save-variable">Save</button>
        <button id="btn-cancel-variable">Cancel</button>
      </div>
    </div>
  `;
  
  document.body.appendChild(dialog);
  
  // Function to update the initial value input based on selected type
  const updateInitialValueInput = (type) => {
    const container = document.getElementById('initial-value-container');
    let inputHtml = '';
    
    switch(type) {
      case 'int':
        inputHtml = '<input type="number" id="variable-initial-value" step="1" placeholder="Enter an integer">';
        break;
      case 'float':
        inputHtml = '<input type="number" id="variable-initial-value" step="any" placeholder="Enter a decimal number">';
        break;
      case 'string':
        inputHtml = '<input type="text" id="variable-initial-value" placeholder="Enter text">';
        break;
      case 'boolean':
        inputHtml = `
          <select id="variable-initial-value">
            <option value="">Select a value</option>
            <option value="true">true</option>
            <option value="false">false</option>
          </select>
        `;
        break;
    }
    
    container.innerHTML = inputHtml;
  };
  
  // Add event listener for type change
  const typeSelect = document.getElementById('variable-type');
  typeSelect.addEventListener('change', (e) => {
    updateInitialValueInput(e.target.value);
  });
  
  // Initialize with default type (int)
  updateInitialValueInput('int');
  
  // Add event listeners for the buttons
  const closeButton = dialog.querySelector('.close-btn');
  closeButton.addEventListener('click', () => {
    document.body.removeChild(dialog);
  });
  
  const cancelButton = dialog.querySelector('#btn-cancel-variable');
  cancelButton.addEventListener('click', () => {
    document.body.removeChild(dialog);
  });
  
  const saveButton = dialog.querySelector('#btn-save-variable');
  saveButton.addEventListener('click', () => {
    // Get the form values
    const name = document.getElementById('variable-name').value;
    const type = document.getElementById('variable-type').value;
    const initialValueElement = document.getElementById('variable-initial-value');
    const initialValueStr = initialValueElement.value;
    const description = document.getElementById('variable-description').value;
    
    // Validate the name
    if (!name) {
      alert('Variable name is required');
      return;
    }
    
    // Check if it's a valid identifier
    if (!/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name)) {
      alert('Variable name must be a valid identifier (start with letter or underscore, contain only letters, numbers, or underscores)');
      return;
    }
    
    // Check for duplicate names
    for (const [, variable] of this.app.api.petriNet.dataVariables) {
      if (variable.name === name) {
        alert(`A variable with name "${name}" already exists`);
        return;
      }
    }
    
    // Parse the initial value based on the type
    let initialValue = null;
    if (initialValueStr) {
      try {
        if (type === 'int') {
          initialValue = parseInt(initialValueStr, 10);
          if (isNaN(initialValue)) {
            throw new Error('Not a valid integer');
          }
        } else if (type === 'float') {
          initialValue = parseFloat(initialValueStr);
          if (isNaN(initialValue)) {
            throw new Error('Not a valid float');
          }
        } else if (type === 'boolean') {
          if (initialValueStr === 'true') {
            initialValue = true;
          } else if (initialValueStr === 'false') {
            initialValue = false;
          } else {
            throw new Error('Boolean must be true or false');
          }
        } else { // string
          initialValue = initialValueStr;
        }
      } catch (error) {
        alert(`Invalid initial value: ${error.message}`);
        return;
      }
    }
    
    // Create the variable
    this.app.api.createDataVariable(name, type, initialValue, description);
    
    // Close the dialog
    document.body.removeChild(dialog);
    
    // Update displays
    this.updateDataVariablesDisplay();
    this.updateDataValuesDisplay();
  });
}

  /**
   * Show dialog to edit an existing data variable
   * @param {string} id - ID of the variable to edit
   */
  showEditVariableDialog(id) {
    // Get the variable
    const variable = this.app.api.getDataVariable(id);
    if (!variable) return;
    
    // Create the dialog
    const dialogId = 'edit-variable-dialog';
    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay';
    dialog.id = dialogId;
    
    dialog.innerHTML = `
      <div class="modal-container">
        <div class="modal-header">
          <h2>Edit Data Variable</h2>
          <button class="close-btn">&times;</button>
        </div>
        <div class="modal-body">
          <div class="form-group">
            <label for="variable-name">Name</label>
            <input type="text" id="variable-name" value="${variable.name}" required>
            <small>Use a valid identifier (letters, numbers, underscore)</small>
          </div>
          <div class="form-group">
            <label for="variable-type">Type</label>
            <select id="variable-type">
              <option value="int" ${variable.type === 'int' ? 'selected' : ''}>Integer</option>
              <option value="float" ${variable.type === 'float' ? 'selected' : ''}>Float</option>
              <option value="string" ${variable.type === 'string' ? 'selected' : ''}>String</option>
              <option value="boolean" ${variable.type === 'boolean' ? 'selected' : ''}>Boolean</option>
            </select>
          </div>
          <div class="form-group">
            <label for="variable-value">Current Value</label>
            <input type="text" id="variable-value" value="${variable.currentValue !== null ? variable.currentValue : ''}">
          </div>
          <div class="form-group">
            <label for="variable-description">Description</label>
            <textarea id="variable-description" rows="2">${variable.description || ''}</textarea>
          </div>
        </div>
        <div class="modal-footer">
          <button id="btn-save-variable">Save</button>
          <button id="btn-cancel-variable">Cancel</button>
        </div>
      </div>
    `;
    
    document.body.appendChild(dialog);
    
    // Add event listeners for the buttons
    const closeButton = dialog.querySelector('.close-btn');
    closeButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
    
    const cancelButton = dialog.querySelector('#btn-cancel-variable');
    cancelButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
    
    const saveButton = dialog.querySelector('#btn-save-variable');
    saveButton.addEventListener('click', () => {
      // Get the form values
      const name = document.getElementById('variable-name').value;
      const type = document.getElementById('variable-type').value;
      const valueStr = document.getElementById('variable-value').value;
      const description = document.getElementById('variable-description').value;
      
      // Validate the name
      if (!name) {
        alert('Variable name is required');
        return;
      }
      
      // Check if it's a valid identifier
      if (!/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name)) {
        alert('Variable name must be a valid identifier (start with letter or underscore, contain only letters, numbers, or underscores)');
        return;
      }
      
      // Check for duplicate names (excluding this variable)
      for (const [varId, v] of this.app.api.petriNet.dataVariables) {
        if (varId !== id && v.name === name) {
          alert(`A variable with name "${name}" already exists`);
          return;
        }
      }
      
      // Parse the value based on the type
      let parsedValue = null;
      if (valueStr) {
        try {
          if (type === 'int') {
            parsedValue = parseInt(valueStr, 10);
            if (isNaN(parsedValue)) {
              throw new Error('Not a valid integer');
            }
          } else if (type === 'float') {
            parsedValue = parseFloat(valueStr);
            if (isNaN(parsedValue)) {
              throw new Error('Not a valid float');
            }
          } else if (type === 'boolean') {
            if (valueStr.toLowerCase() === 'true') {
              parsedValue = true;
            } else if (valueStr.toLowerCase() === 'false') {
              parsedValue = false;
            } else {
              throw new Error('Boolean must be true or false');
            }
          } else { // string
            parsedValue = valueStr;
          }
        } catch (error) {
          alert(`Invalid value: ${error.message}`);
          return;
        }
      }
      
      // Update the variable
      variable.name = name;
      variable.type = type;
      variable.currentValue = parsedValue;
      variable.description = description;
      
      // Close the dialog
      document.body.removeChild(dialog);
      
      // Update displays
      this.updateDataVariablesDisplay();
      this.updateDataValuesDisplay();
      
      // Update enabled transitions
      this.app.api.petriNet.updateEnabledTransitions();
      if (this.app.editor) {
        this.app.editor.render();
      }
    });
  }

  /**
   * Show dialog to edit a variable's value during simulation
   * @param {string} id - ID of the variable to edit
   */
  showEditValueDialog(id) {
    // Get the variable
    const variable = this.app.api.getDataVariable(id);
    if (!variable) return;
    
    // Create the dialog
    const dialogId = 'edit-value-dialog';
    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay';
    dialog.id = dialogId;
    
    dialog.innerHTML = `
      <div class="modal-container">
        <div class="modal-header">
          <h2>Edit ${variable.name} Value</h2>
          <button class="close-btn">&times;</button>
        </div>
        <div class="modal-body">
          <div class="form-group">
            <label for="variable-value">New Value</label>
            <input type="text" id="variable-value" value="${variable.currentValue !== null ? variable.currentValue : ''}">
            <small>Type: ${variable.type}</small>
          </div>
        </div>
        <div class="modal-footer">
          <button id="btn-save-value">Save</button>
          <button id="btn-cancel-value">Cancel</button>
        </div>
      </div>
    `;
    
    document.body.appendChild(dialog);
    
    // Add event listeners for the buttons
    const closeButton = dialog.querySelector('.close-btn');
    closeButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
    
    const cancelButton = dialog.querySelector('#btn-cancel-value');
    cancelButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
    
    const saveButton = dialog.querySelector('#btn-save-value');
    saveButton.addEventListener('click', () => {
      // Get the value
      const valueStr = document.getElementById('variable-value').value;
      
      // Parse the value based on the type
      let parsedValue = null;
      if (valueStr) {
        try {
          if (variable.type === 'int') {
            parsedValue = parseInt(valueStr, 10);
            if (isNaN(parsedValue)) {
              throw new Error('Not a valid integer');
            }
          } else if (variable.type === 'float') {
            parsedValue = parseFloat(valueStr);
            if (isNaN(parsedValue)) {
              throw new Error('Not a valid float');
            }
          } else if (variable.type === 'boolean') {
            if (valueStr.toLowerCase() === 'true') {
              parsedValue = true;
            } else if (valueStr.toLowerCase() === 'false') {
              parsedValue = false;
            } else {
              throw new Error('Boolean must be true or false');
            }
          } else { // string
            parsedValue = valueStr;
          }
        } catch (error) {
          alert(`Invalid value: ${error.message}`);
          return;
        }
      }
      
      // Update the variable value
      this.app.api.updateDataVariableValue(id, parsedValue);
      
      // Close the dialog
      document.body.removeChild(dialog);
      
      // Update display
      this.updateDataValuesDisplay();
      
      // Update transition properties panel if a transition is selected
      if (this.app.selectedElement && this.app.selectedElement.type === 'transition') {
        this.app.showTransitionProperties(this.app.selectedElement.id);
      }
    });
  }

  /**
   * Show help for data expressions
   */
  showDataExpressionHelp() {
    // Get the variable names to display in the help
    const variableNames = Array.from(this.app.api.petriNet.dataVariables.values())
      .map(v => v.name);
    
    // Create the dialog
    const dialogId = 'data-expression-help-dialog';
    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay';
    dialog.id = dialogId;
    
    dialog.innerHTML = `
      <div class="modal-container">
        <div class="modal-header">
          <h2>Data Expression Help</h2>
          <button class="close-btn">&times;</button>
        </div>
        <div class="modal-body">
          <h3>Precondition (Guard)</h3>
          <p>A JavaScript expression that evaluates to true or false. If true, the transition is enabled (if token conditions are also met).</p>
          <h4>Available Variables</h4>
          <p>${variableNames.length > 0 ? variableNames.join(', ') : 'No variables defined'}</p>
          <h4>Examples</h4>
          <ul>
            <li><code>counter > 0</code> - Enable if counter is positive</li>
            <li><code>status === "ready" && count <= 10</code> - Enable if status is "ready" and count is at most 10</li>
            <li><code>x > 5 || y < 0</code> - Enable if either x > 5 or y < 0</li>
          </ul>
          
          <h3>Postcondition (Data Change)</h3>
          <p>Defines how variables change when a transition fires. Use <code>variable' = expression</code> format.</p>
          <p>Multiple assignments should be separated by semicolons.</p>
          <h4>Examples</h4>
          <ul>
            <li><code>counter' = counter + 1;</code> - Increment counter</li>
            <li><code>status' = "processing"; timer' = 0;</code> - Set status to "processing" and reset timer</li>
            <li><code>x' = x * 2; y' = y - 1;</code> - Double x and decrement y</li>
          </ul>
          
          <h3>Data Types</h3>
          <ul>
            <li><strong>Integer:</strong> Whole numbers (e.g., 42, -7, 0)</li>
            <li><strong>Float:</strong> Decimal numbers (e.g., 3.14, -2.5, 1.0)</li>
            <li><strong>String:</strong> Text values (use quotes: "hello", "processing")</li>
            <li><strong>Boolean:</strong> true or false values</li>
          </ul>
          
          <h3>Notes</h3>
          <ul>
            <li>Use a prime symbol (<code>'</code>) after variable names in postconditions to indicate the updated value.</li>
            <li>You can reference other variables in expressions (e.g., <code>total' = x + y;</code>).</li>
            <li>You can use the current and new values in the same expression (e.g., <code>x' = x + 1; y' = x' * 2;</code>).</li>
            <li>For constraint-based assignments, use expressions like <code>x' > 0 && x' < 100;</code> to let the solver find valid values.</li>
          </ul>
        </div>
        <div class="modal-footer">
          <button id="btn-close-help">Close</button>
        </div>
      </div>
    `;
    
    document.body.appendChild(dialog);
    
    // Add event listeners for the buttons
    const closeButton = dialog.querySelector('.close-btn');
    closeButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
    
    const closeHelpButton = dialog.querySelector('#btn-close-help');
    closeHelpButton.addEventListener('click', () => {
      document.body.removeChild(dialog);
    });
  }

  /**
   * Convert a standard transition to a data-aware transition
   * @param {string} id - ID of the transition to convert
   */
  convertToDataTransition(id) {
    // Get the original transition
    const oldTransition = this.app.api.petriNet.transitions.get(id);
    if (!oldTransition) return;
    
    // Create a new data-aware transition with the same properties
    const dataTransition = new DataAwareTransition(
      id,
      { x: oldTransition.position.x, y: oldTransition.position.y },
      oldTransition.label,
      oldTransition.priority,
      oldTransition.delay,
      "", // empty precondition
      ""  // empty postcondition
    );
    
    // Replace the transition in the Petri net
    this.app.api.petriNet.transitions.set(id, dataTransition);
    
    // Update enabled transitions
    this.app.api.petriNet.updateEnabledTransitions();
    
    // Show the properties panel for the new transition
    this.app.showTransitionProperties(id);
    
    // Render the editor
    if (this.app.editor) {
      this.app.editor.render();
    }
  }

  /**
   * Validate all expressions in transitions
   */
  validateAllExpressions() {
    // Get variable names for validation
    const variableNames = Array.from(this.app.api.petriNet.dataVariables.values())
      .map(v => v.name);
    
    let hasErrors = false;
    let resultMessage = "Expression Validation Results:\n\n";
    
    // Check each transition
    for (const [id, transition] of this.app.api.petriNet.transitions) {
      // Skip non-data transitions
      if (typeof transition.evaluatePrecondition !== 'function') continue;
      
      // Validate precondition
      if (transition.precondition && transition.precondition.trim() !== "") {
        const preResult = this.app.api.validatePrecondition(
          transition.precondition, 
          variableNames
        );
        
        if (!preResult.valid) {
          hasErrors = true;
          resultMessage += `Transition "${transition.label}" (${id}):\n`;
          resultMessage += `  Precondition Error: ${preResult.error}\n`;
        }
      }
      
      // Validate postcondition
      if (transition.postcondition && transition.postcondition.trim() !== "") {
        const postResult = this.app.api.validatePostcondition(
          transition.postcondition, 
          variableNames
        );
        
        if (!postResult.valid) {
          hasErrors = true;
          resultMessage += `Transition "${transition.label}" (${id}):\n`;
          resultMessage += `  Postcondition Error: ${postResult.error}\n`;
        }
      }
    }
    
    // Show the validation results
    if (hasErrors) {
      alert(resultMessage);
    } else {
      alert("All expressions are valid!");
    }
  }
}

export { DataPetriNetUI, ExpressionEditorDialog };