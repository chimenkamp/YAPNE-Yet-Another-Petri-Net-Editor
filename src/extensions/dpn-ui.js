
class DataPetriNetUI {
    /**
     * Initialize the Data Petri Net UI extensions
     * @param {PetriNetApp} app - Reference to the main application
     */
    constructor(app) {
      this.app = app;
      

      this.originalShowTransitionProperties = app.showTransitionProperties;
      

      this.initializeUI();
    }
  
    /**
     * Initialize UI components
     */
    initializeUI() {

      this.addDataVariablesPanel();
      

      this.addDataValuesDisplay();
      

      this.extendTransitionPropertiesPanel();
      

      this.addDataExpressionHelpButton();
      

      this.extendEditorModes();
    }
  
    /**
     * Add the data variables management panel to the sidebar
     */
    addDataVariablesPanel() {
      const sidebar = document.querySelector('#data-variables-content-conatiner');
      if (!sidebar) return;
      

      const dataVariablesPanel = document.createElement('div');
      dataVariablesPanel.className = 'data-variables-panel';
      dataVariablesPanel.innerHTML = `
        <div id="data-variables-content">
          <p>No data variables defined.</p>
        </div>
        <div class="toolbar-group">
          <button id="btn-add-data-variable">Add Variable</button>
          <button id="btn-validate-expressions">Validate Expressions</button>
        </div>
      `;
      

      const propertiesPanel = sidebar.querySelector('.properties-panel');
      if (propertiesPanel) {
        sidebar.insertBefore(dataVariablesPanel, propertiesPanel.nextSibling);
      } else {
        sidebar.appendChild(dataVariablesPanel);
      }
      

      const addBtn = document.getElementById('btn-add-data-variable');
      if (addBtn) {
        addBtn.addEventListener('click', () => this.showAddVariableDialog());
      }
      
      const validateBtn = document.getElementById('btn-validate-expressions');
      if (validateBtn) {
        validateBtn.addEventListener('click', () => this.validateAllExpressions());
      }
      

      this.updateDataVariablesDisplay();
    }
  
    /**
     * Add data values display to the simulation section
     */
    addDataValuesDisplay() {
      const simulationPanel = document.querySelector('.simulation-controls');
      if (!simulationPanel) return;
      

      const dataValuesDisplay = document.createElement('div');
      dataValuesDisplay.className = 'data-values-display';
      dataValuesDisplay.innerHTML = `
        <h4>Data Values</h4>
        <div id="data-values-content">
          <p>No data variables defined.</p>
        </div>
      `;
      

      const tokensDisplay = simulationPanel.querySelector('.tokens-display');
      if (tokensDisplay) {
        simulationPanel.insertBefore(dataValuesDisplay, tokensDisplay.nextSibling);
      } else {
        simulationPanel.appendChild(dataValuesDisplay);
      }
      

      this.updateDataValuesDisplay();
    }
  
    /**
     * Extend the transition properties panel to include data conditions
     */
    extendTransitionPropertiesPanel() {

      this.app.showTransitionProperties = (id) => {

        this.originalShowTransitionProperties.call(this.app, id);
        

        const transition = this.app.api.petriNet.transitions.get(id);
        if (!transition) return;
        

        const isDataAware = typeof transition.evaluatePrecondition === 'function';
        

        const propertiesPanel = this.app.propertiesPanel;
        if (!propertiesPanel) return;
        

        if (isDataAware) {

          const buttonGroup = propertiesPanel.querySelector('.form-group button');
          const insertPoint = buttonGroup ? buttonGroup.closest('.form-group') : null;
          

          const dataConditionsHtml = `
            <div class="form-group">
              <label for="transition-precondition">Precondition (Guard)</label>
              <textarea id="transition-precondition" rows="3">${transition.precondition || ''}</textarea>
              <small>JavaScript expression using variable names</small>
            </div>
            <div class="form-group">
              <label for="transition-postcondition">Postcondition (Updates)</label>
              <textarea id="transition-postcondition" rows="3">${transition.postcondition || ''}</textarea>
              <small>Format: x' = expression; y' = expression;</small>
            </div>
            <div class="form-group">
              <button id="btn-help-data-expressions" type="button">Help with Expressions</button>
            </div>
          `;
          

          if (insertPoint) {

            insertPoint.insertAdjacentHTML('beforebegin', dataConditionsHtml);
          } else {

            propertiesPanel.insertAdjacentHTML('beforeend', dataConditionsHtml);
          }
          

          const preconditionInput = document.getElementById('transition-precondition');
          if (preconditionInput) {
            preconditionInput.addEventListener('input', (e) => {

              try {
                this.app.api.setTransitionPrecondition(id, e.target.value);
              } catch (error) {
                preconditionInput.style.borderColor = 'red';
              }
              

              this.app.updateTransitionStatus(id);
            });
          }
          
          const postconditionInput = document.getElementById('transition-postcondition');
          if (postconditionInput) {
            postconditionInput.addEventListener('input', (e) => {
              try {
                this.app.api.setTransitionPostcondition(id, e.target.value);
              } catch (error) {
                postconditionInput.style.borderColor = 'red';
              }
              this.app.updateTransitionStatus(id);
            });
          }
          

          const helpButton = document.getElementById('btn-help-data-expressions');
          if (helpButton) {
            helpButton.addEventListener('click', () => this.showDataExpressionHelp());
          }
        } else {

          const convertButtonHTML = `
            <div class="form-group">
              <button id="btn-convert-to-data-transition" type="button">Convert to Data Transition</button>
            </div>
          `;
          propertiesPanel.insertAdjacentHTML('beforeend', convertButtonHTML);
          

          const convertButton = document.getElementById('btn-convert-to-data-transition');
          if (convertButton) {
            convertButton.addEventListener('click', () => this.convertToDataTransition(id));
          }
        }
      };
    }
  
    /**
     * Add a help button for data expressions
     */
    addDataExpressionHelpButton() {

    }
  
    /**
     * Extend editor modes to support data transitions
     */
    extendEditorModes() {

      const toolbar = document.querySelector('.vertical-toolbar .toolbar-group');
      if (!toolbar) return;
      

      const addTransitionBtn = document.getElementById('btn-add-transition');
      if (addTransitionBtn) {
        const dataTransitionBtn = document.createElement('button');
        dataTransitionBtn.id = 'btn-add-data-transition';
        dataTransitionBtn.title = 'Add data transition';
        dataTransitionBtn.innerHTML = '⊞'; // Different symbol for data transition
        dataTransitionBtn.className = '';
        

        addTransitionBtn.insertAdjacentElement('afterend', dataTransitionBtn);
        

        dataTransitionBtn.addEventListener('click', () => {
          this.app.editor.setMode('addDataTransition');
          this.updateActiveButton('btn-add-data-transition');
        });
        

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

      const originalHandleMouseDown = this.app.editor.eventListeners.get('mousedown');
      

      const newMouseDownHandler = (event) => {

        if (this.app.editor.mode !== 'addDataTransition') {
          return originalHandleMouseDown(event);
        }
        

        const rect = this.app.editor.canvas.getBoundingClientRect();
        const x = event.clientX - rect.left;
        const y = event.clientY - rect.top;
        

        const worldPos = this.app.editor.renderer.screenToWorld(x, y);
        

        if (this.app.editor.snapToGrid) {
          worldPos.x = Math.round(worldPos.x / this.app.editor.gridSize) * this.app.editor.gridSize;
          worldPos.y = Math.round(worldPos.y / this.app.editor.gridSize) * this.app.editor.gridSize;
        }
        

        const id = this.app.api.createDataTransition(
          worldPos.x, 
          worldPos.y, 
          `DT${this.app.api.petriNet.transitions.size + 1}`
        );
        

        this.app.editor.selectElement(id, 'transition');
        this.app.editor.render();
      };
      

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
      

      if (this.app.api.petriNet.dataVariables && this.app.api.petriNet.dataVariables.size > 0) {

        let html = `
          <table class="data-variables-table">
            <tr>
              <th>Name</th>
              <th>Type</th>
              <th>Value</th>
              <th>Actions</th>
            </tr>
        `;
        

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
        

        const editButtons = container.querySelectorAll('.btn-edit-variable');
        editButtons.forEach(button => {
          button.addEventListener('click', () => {
            const id = button.getAttribute('data-id');
            this.showEditVariableDialog(id);
          });
        });
        
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
      

      if (this.app.api.petriNet.dataVariables && this.app.api.petriNet.dataVariables.size > 0) {

        let html = `
          <table class="data-values-table">
            <tr>
              <th>Variable</th>
              <th>Value</th>
              <th>Edit</th>
            </tr>
        `;
        

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
                <option value="number">Number</option>
                <option value="string">String</option>
                <option value="boolean">Boolean</option>
              </select>
            </div>
            <div class="form-group">
              <label for="variable-initial-value">Initial Value</label>
              <input type="text" id="variable-initial-value">
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

        const name = document.getElementById('variable-name').value;
        const type = document.getElementById('variable-type').value;
        const initialValueStr = document.getElementById('variable-initial-value').value;
        const description = document.getElementById('variable-description').value;
        

        if (!name) {
          alert('Variable name is required');
          return;
        }
        

        if (!/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name)) {
          alert('Variable name must be a valid identifier (start with letter or underscore, contain only letters, numbers, or underscores)');
          return;
        }
        

        for (const [, variable] of this.app.api.petriNet.dataVariables) {
          if (variable.name === name) {
            alert(`A variable with name "${name}" already exists`);
            return;
          }
        }
        

        let initialValue = null;
        if (initialValueStr) {
          try {
            if (type === 'number') {
              initialValue = Number(initialValueStr);
              if (isNaN(initialValue)) {
                throw new Error('Not a valid number');
              }
            } else if (type === 'boolean') {
              if (initialValueStr.toLowerCase() === 'true') {
                initialValue = true;
              } else if (initialValueStr.toLowerCase() === 'false') {
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
        

        this.app.api.createDataVariable(name, type, initialValue, description);
        

        document.body.removeChild(dialog);
        

        this.updateDataVariablesDisplay();
        this.updateDataValuesDisplay();
      });
    }
  
    /**
     * Show dialog to edit an existing data variable
     * @param {string} id - ID of the variable to edit
     */
    showEditVariableDialog(id) {

      const variable = this.app.api.getDataVariable(id);
      if (!variable) return;
      

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
                <option value="number" ${variable.type === 'number' ? 'selected' : ''}>Number</option>
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

        const name = document.getElementById('variable-name').value;
        const type = document.getElementById('variable-type').value;
        const valueStr = document.getElementById('variable-value').value;
        const description = document.getElementById('variable-description').value;
        

        if (!name) {
          alert('Variable name is required');
          return;
        }
        

        if (!/^[a-zA-Z_][a-zA-Z0-9_]*$/.test(name)) {
          alert('Variable name must be a valid identifier (start with letter or underscore, contain only letters, numbers, or underscores)');
          return;
        }
        

        for (const [varId, v] of this.app.api.petriNet.dataVariables) {
          if (varId !== id && v.name === name) {
            alert(`A variable with name "${name}" already exists`);
            return;
          }
        }
        

        let parsedValue = null;
        if (valueStr) {
          try {
            if (type === 'number') {
              parsedValue = Number(valueStr);
              if (isNaN(parsedValue)) {
                throw new Error('Not a valid number');
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
        

        variable.name = name;
        variable.type = type;
        variable.currentValue = parsedValue;
        variable.description = description;
        

        document.body.removeChild(dialog);
        

        this.updateDataVariablesDisplay();
        this.updateDataValuesDisplay();
        

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

      const variable = this.app.api.getDataVariable(id);
      if (!variable) return;
      

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

        const valueStr = document.getElementById('variable-value').value;
        

        let parsedValue = null;
        if (valueStr) {
          try {
            if (variable.type === 'number') {
              parsedValue = Number(valueStr);
              if (isNaN(parsedValue)) {
                throw new Error('Not a valid number');
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
        

        this.app.api.updateDataVariableValue(id, parsedValue);
        

        document.body.removeChild(dialog);
        

        this.updateDataValuesDisplay();
        

        if (this.app.selectedElement && this.app.selectedElement.type === 'transition') {
          this.app.showTransitionProperties(this.app.selectedElement.id);
        }
      });
    }
  
    /**
     * Show help for data expressions
     */
    showDataExpressionHelp() {

      const variableNames = Array.from(this.app.api.petriNet.dataVariables.values())
        .map(v => v.name);
      

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
            
            <h3>Notes</h3>
            <ul>
              <li>Use a prime symbol (<code>'</code>) after variable names in postconditions to indicate the updated value.</li>
              <li>You can reference other variables in expressions (e.g., <code>total' = x + y;</code>).</li>
              <li>You can use the current and new values in the same expression (e.g., <code>x' = x + 1; y' = x' * 2;</code>).</li>
            </ul>
          </div>
          <div class="modal-footer">
            <button id="btn-close-help">Close</button>
          </div>
        </div>
      `;
      
      document.body.appendChild(dialog);
      

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

      const oldTransition = this.app.api.petriNet.transitions.get(id);
      if (!oldTransition) return;
      

      const dataTransition = new DataAwareTransition(
        id,
        { x: oldTransition.position.x, y: oldTransition.position.y },
        oldTransition.label,
        oldTransition.priority,
        oldTransition.delay,
        "", // empty precondition
        ""  // empty postcondition
      );
      

      this.app.api.petriNet.transitions.set(id, dataTransition);
      

      this.app.api.petriNet.updateEnabledTransitions();
      

      this.app.showTransitionProperties(id);
      

      if (this.app.editor) {
        this.app.editor.render();
      }
    }
  
    /**
     * Validate all expressions in transitions
     */
    validateAllExpressions() {

      const variableNames = Array.from(this.app.api.petriNet.dataVariables.values())
        .map(v => v.name);
      
      let hasErrors = false;
      let resultMessage = "Expression Validation Results:\n\n";
      

      for (const [id, transition] of this.app.api.petriNet.transitions) {

        if (typeof transition.evaluatePrecondition !== 'function') continue;
        

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
      

      if (hasErrors) {
        alert(resultMessage);
      } else {
        alert("All expressions are valid!");
      }
    }
  }