/**
 * PNML Importer Extension with Improved BPMN Layout Algorithm
 * Based on "A Simple Algorithm for Automatic Layout of BPMN Processes" (Kitzmann et al., 2009)
 */

class PNMLImporter {
    constructor(app) {
      this.app = app;
      this.currentParsedNet = null;
      this.previewRenderer = null;
      this.layoutAlgorithm = new LayoutAlgorithm();
      this.initializeUI();
    }
  
    initializeUI() {
      this.addImportButton();
    }
  
    addImportButton() {
      const fileOperationsSection = document.querySelector('#file-operations-section .section-content');
      if (!fileOperationsSection) return;
  
      const buttonGroup = fileOperationsSection.querySelector('.button-group');
      if (buttonGroup) {
        const importButton = document.createElement('button');
        importButton.id = 'btn-import-pnml';
        importButton.textContent = 'Load (PNML)';
        importButton.className = 'blue';
        importButton.addEventListener('click', () => this.showImportDialog());
        
        const loadButton = buttonGroup.querySelector('#btn-load');
        if (loadButton) {
          loadButton.insertAdjacentElement('afterend', importButton);
        } else {
          buttonGroup.appendChild(importButton);
        }
      }
    }
  
    showImportDialog() {
      const dialog = this.createImportDialog();
      document.body.appendChild(dialog);
      
      setTimeout(() => {
        const fileInput = dialog.querySelector('#pnml-file-input');
        if (fileInput) fileInput.focus();
      }, 100);
    }
  
    createImportDialog() {
      const dialog = document.createElement('div');
      dialog.className = 'modal-overlay';
      dialog.id = 'pnml-import-dialog';
      
      dialog.innerHTML = `
        <div class="modal-container pnml-import-container">
          <div class="modal-header">
            <h2>🔄 Import PNML File</h2>
            <button class="close-btn">&times;</button>
          </div>
          <div class="modal-body">
            <div class="pnml-import-content">
              <!-- Progress Bar -->
              <div class="progress-container" id="progress-container" style="display: none;">
                <div class="progress-info">
                  <span id="progress-text">Processing...</span>
                  <span id="progress-percentage">0%</span>
                </div>
                <div class="progress-bar">
                  <div class="progress-fill" id="progress-fill"></div>
                </div>
              </div>
  
              <!-- File Upload Section -->
              <div class="upload-section">
                <div class="upload-area" id="pnml-upload-area">
                  <div class="upload-icon">📁</div>
                  <p>Drag & drop your PNML file here or <strong>click to browse</strong></p>
                  <input type="file" id="pnml-file-input" accept=".pnml,.xml" style="display: none;">
                  <div class="upload-info">
                    Supports PNML and XML files
                  </div>
                </div>
              </div>
  
              <!-- Import Settings -->
              <div class="import-settings" id="import-settings" style="display: none;">
                <h3>📐 Layout Settings</h3>
                <div class="settings-grid">
                  <div class="setting-item">
                    <label for="apply-algorithm">
                      <input type="checkbox" id="apply-algorithm" checked>
                      Apply layout algorithm
                    </label>
                    <small>Apply BPMN layout even if positions exist in file</small>
                  </div>
                  <div class="setting-item">
                    <label for="element-spacing">Element Spacing:</label>
                    <input type="range" id="element-spacing" min="80" max="200" value="100" step="10">
                    <span class="range-value">100px</span>
                  </div>
                  <div class="setting-item">
                    <label for="element-size">Element Size:</label>
                    <input type="range" id="element-size" min="30" max="80" value="50" step="5">
                    <span class="range-value">50px</span>
                  </div>
                  <div class="setting-item">
                    <label for="center-layout">
                      <input type="checkbox" id="center-layout" checked>
                      Center in canvas
                    </label>
                  </div>
                  <div class="setting-item">
                    <label for="compact-layout">
                      <input type="checkbox" id="compact-layout" checked>
                      Apply compaction
                    </label>
                  </div>
                  <div class="setting-item">
                    <label for="prevent-overlap">
                      <input type="checkbox" id="prevent-overlap" checked>
                      Prevent overlapping
                    </label>
                    <small>Force minimum distance between elements</small>
                  </div>
                </div>
              </div>
  
              <!-- Preview Section -->
              <div class="preview-section" id="preview-section" style="display: none;">
                <h3>👁️ Preview</h3>
                <div class="preview-info" id="preview-info"></div>
                <div class="preview-container">
                  <canvas id="pnml-preview-canvas" width="400" height="300"></canvas>
                  <div class="preview-controls">
                    <button id="btn-refresh-preview" type="button">🔄 Refresh Preview</button>
                    <button id="btn-fit-preview" type="button">📐 Fit to View</button>
                  </div>
                </div>
              </div>
            </div>
          </div>
          <div class="modal-footer">
            <button id="btn-cancel-import" type="button">Cancel</button>
            <button id="btn-apply-import" type="button" disabled>Import to Editor</button>
          </div>
        </div>
      `;
  
      this.setupDialogEventListeners(dialog);
      return dialog;
    }
  
    setupDialogEventListeners(dialog) {
      // Close button
      const closeBtn = dialog.querySelector('.close-btn');
      const cancelBtn = dialog.querySelector('#btn-cancel-import');
      
      [closeBtn, cancelBtn].forEach(btn => {
        btn.addEventListener('click', () => {
          document.body.removeChild(dialog);
        });
      });
  
      // File upload area
      const uploadArea = dialog.querySelector('#pnml-upload-area');
      const fileInput = dialog.querySelector('#pnml-file-input');
      
      uploadArea.addEventListener('click', () => fileInput.click());
      
      // Drag and drop
      uploadArea.addEventListener('dragover', (e) => {
        e.preventDefault();
        uploadArea.classList.add('drag-over');
      });
      
      uploadArea.addEventListener('dragleave', () => {
        uploadArea.classList.remove('drag-over');
      });
      
      uploadArea.addEventListener('drop', (e) => {
        e.preventDefault();
        uploadArea.classList.remove('drag-over');
        const files = e.dataTransfer.files;
        if (files.length > 0) {
          this.handleFileUpload(files[0], dialog);
        }
      });
  
      fileInput.addEventListener('change', (e) => {
        if (e.target.files.length > 0) {
          this.handleFileUpload(e.target.files[0], dialog);
        }
      });
  
      // Settings controls
      const elementSpacing = dialog.querySelector('#element-spacing');
      const elementSize = dialog.querySelector('#element-size');
      const applyAlgorithm = dialog.querySelector('#apply-algorithm');
      const centerLayout = dialog.querySelector('#center-layout');
      const compactLayout = dialog.querySelector('#compact-layout');
      const preventOverlap = dialog.querySelector('#prevent-overlap');
      
      [elementSpacing, elementSize, applyAlgorithm, centerLayout, compactLayout, preventOverlap].forEach(control => {
        control.addEventListener('change', () => {
          this.updateRangeValues(dialog);
          // Update preview info when apply algorithm changes
          if (control === applyAlgorithm && this.currentParsedNet) {
            this.updatePreviewInfo(dialog, this.currentParsedNet);
          }
          this.updatePreview(dialog);
        });
      });
  
      elementSpacing.addEventListener('input', () => {
        this.updateRangeValues(dialog);
        // Update preview in real-time as user drags
        this.debouncePreviewUpdate(dialog);
      });
  
      elementSize.addEventListener('input', () => {
        this.updateRangeValues(dialog);
        // Update preview in real-time as user drags
        this.debouncePreviewUpdate(dialog);
      });
  
      // Preview controls
      const refreshBtn = dialog.querySelector('#btn-refresh-preview');
      const fitBtn = dialog.querySelector('#btn-fit-preview');
      
      refreshBtn.addEventListener('click', () => this.updatePreview(dialog));
      fitBtn.addEventListener('click', () => this.fitPreviewToView(dialog));
  
      // Import button
      const importBtn = dialog.querySelector('#btn-apply-import');
      importBtn.addEventListener('click', () => {
    
        this.importToEditor(dialog);
      });
    }
  
    // Debounce preview updates for real-time feedback
    debouncePreviewUpdate(dialog) {
      if (this.previewUpdateTimer) {
        clearTimeout(this.previewUpdateTimer);
      }
      this.previewUpdateTimer = setTimeout(() => {
        this.updatePreview(dialog);
      }, 300); // 300ms delay
    }
  
    updateRangeValues(dialog) {
      const elementSpacing = dialog.querySelector('#element-spacing');
      const elementSize = dialog.querySelector('#element-size');
      
      const spacingValue = dialog.querySelector('#element-spacing + .range-value');
      const sizeValue = dialog.querySelector('#element-size + .range-value');
      
      if (spacingValue) spacingValue.textContent = `${elementSpacing.value}px`;
      if (sizeValue) sizeValue.textContent = `${elementSize.value}px`;
    }
  
    async handleFileUpload(file, dialog) {
        try {
          await this.showProgress(dialog, 'Reading file...', 10);
          
          const content = await this.readFileContent(file);
          
          await this.showProgress(dialog, 'Parsing PNML...', 30);
          
          const parsedNet = this.parsePNML(content);
          
          if (!parsedNet) {
            throw new Error('Failed to parse PNML file. Please check the file format.');
          }
      
          this.currentParsedNet = parsedNet;
          
          // Check if we have data variables and ensure integration is ready
          if (parsedNet.dataVariables && parsedNet.dataVariables.length > 0) {
            await this.showProgress(dialog, 'Preparing data integration...', 40);
            await this.ensureDataPetriNetIntegration();
          }
          
          await this.showProgress(dialog, 'Preparing layout...', 60);
          
          // Show settings and preview sections
          dialog.querySelector('#import-settings').style.display = 'block';
          dialog.querySelector('#preview-section').style.display = 'block';
          
          // Update preview info
          this.updatePreviewInfo(dialog, parsedNet);
          
          // Set apply algorithm checkbox based on whether positions exist
          const hasPositions = parsedNet.places.some(p => p.position) || parsedNet.transitions.some(t => t.position);
          const applyAlgorithmCheckbox = dialog.querySelector('#apply-algorithm');
          if (hasPositions) {
            // If positions exist, default to preserving them (unchecked)
            applyAlgorithmCheckbox.checked = false;
          } else {
            // If no positions, must apply algorithm (checked and disabled)
            applyAlgorithmCheckbox.checked = true;
          }
          
          await this.showProgress(dialog, 'Generating preview...', 80);
          
          // Enable import button
          dialog.querySelector('#btn-apply-import').disabled = false;
          
          // Generate initial layout and preview
          await this.updatePreview(dialog);
          
          await this.showProgress(dialog, 'Ready!', 100);
          
          // Hide progress bar after a delay
          setTimeout(() => {
            this.hideProgress(dialog);
          }, 1000);
          
        } catch (error) {
          this.hideProgress(dialog);
          alert('Error loading PNML file: ' + error.message);
          console.error('PNML import error:', error);
        }
      }
      
      // Ensure DataPetriNet integration is ready before importing
      async ensureDataPetriNetIntegration() {
        return new Promise((resolve) => {
          // If already integrated, resolve immediately
          if (this.app.dataPetriNetUI || (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataPetriNetUI)) {
            resolve();
            return;
          }
          
          // Wait for integration to be ready
          let attempts = 0;
          const maxAttempts = 50; // 5 seconds max wait
          
          const checkIntegration = () => {
            attempts++;
            
            if (this.app.dataPetriNetUI || (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataPetriNetUI)) {
              console.log("DataPetriNet integration ready");
              resolve();
            } else if (attempts >= maxAttempts) {
              console.warn("DataPetriNet integration not ready after timeout, proceeding anyway");
              resolve();
            } else {
              setTimeout(checkIntegration, 100);
            }
          };
          
          checkIntegration();
        });
      }
      
      // Complete importToEditor method
      async importToEditor(dialog) {
        if (!this.currentParsedNet) return;
        
        this.app.resetPetriNet();
      
        try {
          await this.showProgress(dialog, 'Importing to editor...', 0);
      
          // Stop any auto-run simulation
          if (this.app.autoRunInterval) {
            this.app.stopAutoRun();
          }
      
          await this.showProgress(dialog, 'Creating API instance...', 20);
      
          // Create new API instance based on data content
          let newAPI;
          if (this.currentParsedNet.dataVariables.length > 0 || 
              this.currentParsedNet.transitions.some(t => t.isDataAware)) {
            newAPI = new DataPetriNetAPI(
              this.currentParsedNet.id,
              this.currentParsedNet.name,
              this.currentParsedNet.description
            );
          } else {
            newAPI = new PetriNetAPI(
              this.currentParsedNet.id,
              this.currentParsedNet.name,
              this.currentParsedNet.description
            );
          }
      
          await this.showProgress(dialog, 'Applying layout...', 40);
      
          // Get final layout settings and apply layout
          const settings = this.getLayoutSettings(dialog);
          const netWithLayout = await this.applyLayout(this.currentParsedNet, settings);
      
          await this.showProgress(dialog, 'Creating places...', 60);
      
          // Import places with proper positioning
          netWithLayout.places.forEach(placeData => {
            const place = new Place(
              placeData.id,
              placeData.position || { x: 100, y: 100 },
              placeData.label,
              placeData.tokens,
              placeData.capacity
            );
            newAPI.petriNet.places.set(placeData.id, place);
          });
      
          await this.showProgress(dialog, 'Creating transitions...', 70);
      
          // Import transitions with proper positioning and data-awareness detection
          netWithLayout.transitions.forEach(transitionData => {
            let transition;
            
            // Check if this should be a data-aware transition
            const shouldBeDataAware = transitionData.isDataAware || 
                                     transitionData.precondition || 
                                     transitionData.postcondition ||
                                     (newAPI instanceof DataPetriNetAPI);
            
            if (shouldBeDataAware && typeof DataAwareTransition !== 'undefined') {
              transition = new DataAwareTransition(
                transitionData.id,
                transitionData.position || { x: 100, y: 100 },
                transitionData.label,
                transitionData.priority,
                transitionData.delay,
                transitionData.precondition,
                transitionData.postcondition
              );
            } else {
              transition = new Transition(
                transitionData.id,
                transitionData.position || { x: 100, y: 100 },
                transitionData.label,
                transitionData.priority,
                transitionData.delay
              );
            }
            newAPI.petriNet.transitions.set(transitionData.id, transition);
          });
      
          await this.showProgress(dialog, 'Creating arcs...', 80);
      
          // Import arcs
          netWithLayout.arcs.forEach(arcData => {
            const arc = new Arc(
              arcData.id,
              arcData.source,
              arcData.target,
              arcData.weight,
              arcData.type,
              arcData.points,
              arcData.label || arcData.weight.toString()
            );
            newAPI.petriNet.arcs.set(arcData.id, arc);
          });
      
          await this.showProgress(dialog, 'Importing data variables...', 90);
      
          // Import data variables if present
          if (newAPI instanceof DataPetriNetAPI && netWithLayout.dataVariables.length > 0) {
            console.log("Importing data variables:", netWithLayout.dataVariables);
            netWithLayout.dataVariables.forEach(varData => {
              const variable = new DataVariable(
                varData.id,
                varData.name,
                varData.type,
                varData.currentValue,
                varData.description
              );
              newAPI.petriNet.dataVariables.set(varData.id, variable);
              console.log(`Imported data variable: ${varData.name} = ${varData.currentValue}`);
            });
          }
      
          await this.showProgress(dialog, 'Finalizing...', 95);
      
          // Replace the app's API
          this.app.api = newAPI;
          this.app.editor = newAPI.attachEditor(this.app.canvas);
      
          // Set up renderer based on API type
          if (newAPI instanceof DataPetriNetAPI) {
            this.app.editor.renderer = new DataPetriNetRenderer(this.app.canvas, newAPI.petriNet);
          }
      
          // Restore app functionality
          this.app.editor.app = this.app;
          this.app.editor.setOnSelectCallback(this.app.handleElementSelected.bind(this.app));
          this.app.editor.setOnChangeCallback(this.app.handleNetworkChanged.bind(this.app));
          this.app.editor.setSnapToGrid(this.app.gridEnabled);
          this.app.editor.setMode('select');
          this.app.updateActiveButton('btn-select');
      
          // Render and update displays
          this.app.editor.render();
          this.app.updateTokensDisplay();
          this.app.updateZoomDisplay();
          this.app.propertiesPanel.innerHTML = '<p>No element selected.</p>';
        

          // Update data displays - use multiple approaches to ensure it works
          if (newAPI instanceof DataPetriNetAPI && netWithLayout.dataVariables.length > 0) {
            console.log("Attempting to update data variables UI...");
            
            // Approach 1: Try through app.dataPetriNetUI
            if (this.app.dataPetriNetUI) {
              console.log("Updating data variables UI through app.dataPetriNetUI");
              this.app.dataPetriNetUI.updateDataVariablesDisplay();
              this.app.dataPetriNetUI.updateDataValuesDisplay();
            } else {
              console.log("app.dataPetriNetUI not available");
            }
            
            // Approach 2: Try through global integration object
            if (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataPetriNetUI) {
              console.log("Updating data variables UI through global integration");
              window.dataPetriNetIntegration.dataPetriNetUI.updateDataVariablesDisplay();
              window.dataPetriNetIntegration.dataPetriNetUI.updateDataValuesDisplay();
            } else {
              console.log("Global dataPetriNetIntegration not available");
            }
            
            // Approach 3: Force update after a short delay to ensure everything is initialized
            setTimeout(() => {
              console.log("Attempting delayed update of data variables UI");
              if (this.app.dataPetriNetUI) {
                console.log("Delayed update of data variables UI through app");
                this.app.dataPetriNetUI.updateDataVariablesDisplay();
                this.app.dataPetriNetUI.updateDataValuesDisplay();
              } else if (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataPetriNetUI) {
                console.log("Delayed update through global integration");
                window.dataPetriNetIntegration.dataPetriNetUI.updateDataVariablesDisplay();
                window.dataPetriNetIntegration.dataPetriNetUI.updateDataValuesDisplay();
              } else {
                console.warn("No data UI integration available for update");
              }
              
              // Additional debug info
              console.log("Final data variables count:", newAPI.petriNet.dataVariables.size);
              console.log("Final data variables:", Array.from(newAPI.petriNet.dataVariables.values()));
            }, 100);
            
            // Approach 4: Even longer delay as a last resort
            setTimeout(() => {
              console.log("Final attempt at updating data variables UI");
              if (this.app.dataPetriNetUI) {
                this.app.dataPetriNetUI.updateDataVariablesDisplay();
                this.app.dataPetriNetUI.updateDataValuesDisplay();
                console.log("Final update successful through app");
              } else if (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataPetriNetUI) {
                window.dataPetriNetIntegration.dataPetriNetUI.updateDataVariablesDisplay();
                window.dataPetriNetIntegration.dataPetriNetUI.updateDataValuesDisplay();
                console.log("Final update successful through global");
              }
            }, 500);
          }
      
          await this.showProgress(dialog, 'Complete!', 100);
      
          // Clean up
          this.currentParsedNet = null;
      
          // Close dialog and show success
          setTimeout(() => {
            document.body.removeChild(dialog);
            
            // Show detailed success message with data variable info
            let successMessage = 'PNML file imported successfully!';
            if (newAPI instanceof DataPetriNetAPI && netWithLayout.dataVariables.length > 0) {
              successMessage += `\n\nImported ${netWithLayout.dataVariables.length} data variables.`;
            }
            alert(successMessage);
          }, 500);
      
        } catch (error) {
          this.hideProgress(dialog);
          console.error('Error importing PNML:', error);
          alert('Error importing PNML file: ' + error.message);
        }
      }
  
    async showProgress(dialog, text, percentage) {
      const progressContainer = dialog.querySelector('#progress-container');
      const progressText = dialog.querySelector('#progress-text');
      const progressPercentage = dialog.querySelector('#progress-percentage');
      const progressFill = dialog.querySelector('#progress-fill');
      
      progressContainer.style.display = 'block';
      progressText.textContent = text;
      progressPercentage.textContent = `${percentage}%`;
      progressFill.style.width = `${percentage}%`;
      
      // Allow UI to update
      await new Promise(resolve => setTimeout(resolve, 100));
    }
  
    hideProgress(dialog) {
      const progressContainer = dialog.querySelector('#progress-container');
      progressContainer.style.display = 'none';
    }
  
    readFileContent(file) {
      return new Promise((resolve, reject) => {
        const reader = new FileReader();
        reader.onload = (e) => resolve(e.target.result);
        reader.onerror = () => reject(new Error('Failed to read file'));
        reader.readAsText(file);
      });
    }
  
    parsePNML(xmlContent) {
      try {
        const parser = new DOMParser();
        const xmlDoc = parser.parseFromString(xmlContent, 'text/xml');
        
        const parseError = xmlDoc.querySelector('parsererror');
        if (parseError) {
          throw new Error('Invalid XML format');
        }
  
        const net = xmlDoc.querySelector('net');
        if (!net) {
          throw new Error('No net element found in PNML file');
        }
  
        const parsedNet = {
          id: net.getAttribute('id') || this.generateUUID(),
          name: this.getTextContent(net.querySelector('name text')) || 'Imported Net',
          description: this.getTextContent(net.querySelector('description text')) || '',
          places: [],
          transitions: [],
          arcs: [],
          dataVariables: []
        };
  
        // Parse places
        const places = net.querySelectorAll('place');
        places.forEach(place => {
          const placeData = {
            id: place.getAttribute('id'),
            label: this.getTextContent(place.querySelector('name text')) || place.getAttribute('id'),
            tokens: parseInt(this.getTextContent(place.querySelector('initialMarking text')) || '0'),
            position: this.getPosition(place),
            capacity: null
          };
          parsedNet.places.push(placeData);
        });
  
        // Parse transitions
        const transitions = net.querySelectorAll('transition');
        transitions.forEach(transition => {
          // Check for data-aware attributes
          let precondition = this.getTextContent(transition.querySelector('dataGuard text')) || 
                             transition.getAttribute('guard') || '';

          let postcondition = this.getTextContent(transition.querySelector('dataUpdate text')) || 
                              this.getTextContent(transition.querySelector('dataAction text')) || '';
          
          let isDataAware = !!(precondition || postcondition || 
                               transition.querySelector('guard') ||
                               transition.querySelector('dataGuard') ||
                               transition.querySelector('dataUpdate') ||
                               transition.querySelector('dataAction'));

          const { pre, post } = this.splitPrePostConditions(precondition)

          precondition = pre || '';
          postcondition = post || '';
          const transitionData = {
            id: transition.getAttribute('id'),
            label: this.getTextContent(transition.querySelector('name text')) || transition.getAttribute('id'),
            position: this.getPosition(transition),
            priority: 1,
            delay: 0,
            precondition: precondition.replace(/'/g, ""),
            postcondition: postcondition,
            isDataAware: isDataAware
          };
          parsedNet.transitions.push(transitionData);
        });
  
        // Parse arcs
        const arcs = net.querySelectorAll('arc');
        arcs.forEach(arc => {
          const arcData = {
            id: arc.getAttribute('id') || this.generateUUID(),
            source: arc.getAttribute('source'),
            target: arc.getAttribute('target'),
            weight: parseInt(this.getTextContent(arc.querySelector('inscription text')) || '1'),
            type: this.getTextContent(arc.querySelector('arctype text')) || 'regular',
            points: [],
            label: ''
          };
          parsedNet.arcs.push(arcData);
        });
  
        // Parse data variables
        const variablesSection = net.querySelector('dataVariables') || net.querySelector('variables');
  
        if (variablesSection) {
          const variables = variablesSection.querySelectorAll('variable');
          variables.forEach(variable => {
            const varData = {
              id: variable.getAttribute('id') || this.generateUUID(),
              name: variable.querySelector("name").textContent || "Unnamed Variable",
              type: variable.getAttribute("type") || 'string',
              currentValue: this.getTextContent(variable.querySelector('initialValue text')),
              description: this.getTextContent(variable.querySelector('description text')) || ''
            };
            let minValue = variable.getAttribute('minValue')|| "";
            let maxValue = variable.getAttribute('maxValue')|| "";
            let initialValue =  variable.querySelector("initialValue") ? variable.querySelector("initialValue").textContent : "";
            // Convert value to appropriate type
            if (varData.type === 'number' || varData.type === 'java.lang.Double' || varData.type === 'java.lang.Integer') {
              varData.type = 'number';
              varData.currentValue = parseFloat(initialValue) || 0;
            } else if (varData.type === 'boolean' || varData.type === 'java.lang.Boolean') {
              varData.type = 'boolean';
              varData.currentValue = varData.currentValue === 'true';
            } else {
              varData.type = 'string';
              varData.currentValue = String(varData.currentValue || '');
            }
            
            parsedNet.dataVariables.push(varData);
          });
        }
  
        return parsedNet;
      } catch (error) {
        console.error('Error parsing PNML:', error);
        return null;
      }
    }

    splitPrePostConditions(inputString) {
      // Default return object in case of invalid input format
      const result = { pre: 'Invalid input format', post: 'Invalid input format' };

      // Find the boundary between the pre and post conditions.
      // We use ' | post: ' as the unique delimiter.
      const postMarker = ' | post: ';
      const postIndex = inputString.indexOf(postMarker);

      if (postIndex !== -1) {

          let prePart = inputString.substring(0, postIndex);

          let postPart = inputString.substring(postIndex + postMarker.length);

          // Clean up the 'pre' condition by removing the "pre: " prefix.
          if (prePart.startsWith('pre: ')) {
              result.pre = prePart.substring(5).trim();
          } else {
              result.pre = "";
          }

          // Clean up the 'post' condition by replacing all instances of ' | ' with ' ; '.
          // A global regex is used to ensure all occurrences are replaced.
          result.post = postPart.replace(/ \| /g, ' ; ').trim();
      }
      console.log("Split pre/post conditions:", result);

      return result;
    }
  
    getTextContent(element) {
      return element ? element.textContent.trim() : null;
    }
  
    getPosition(element) {
      const graphics = element.querySelector('graphics');
      if (graphics) {
        const position = graphics.querySelector('position');
        if (position) {
          return {
            x: parseFloat(position.getAttribute('x')) || 0,
            y: parseFloat(position.getAttribute('y')) || 0
          };
        }
      }
      return null;
    }
  
    updatePreviewInfo(dialog, parsedNet) {
      const infoElement = dialog.querySelector('#preview-info');
      const hasPositions = parsedNet.places.some(p => p.position) || parsedNet.transitions.some(t => t.position);
      const applyAlgorithm = dialog.querySelector('#apply-algorithm')?.checked ?? true;
      const dataTransitions = parsedNet.transitions.filter(t => t.isDataAware).length;
      
      // Determine what will happen with positions
      let positionStatus, positionClass;
      if (!hasPositions) {
        positionStatus = '🔄 Will be generated';
        positionClass = 'warning';
      } else if (applyAlgorithm) {
        positionStatus = '🔄 Will be recalculated';
        positionClass = 'warning';
      } else {
        positionStatus = '✅ Will be preserved';
        positionClass = 'success';
      }
      
      infoElement.innerHTML = `
        <div class="info-grid">
          <div class="info-item">
            <span class="info-label">Places:</span>
            <span class="info-value">${parsedNet.places.length}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Transitions:</span>
            <span class="info-value">${parsedNet.transitions.length}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Arcs:</span>
            <span class="info-value">${parsedNet.arcs.length}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Data Variables:</span>
            <span class="info-value">${parsedNet.dataVariables.length}</span>
          </div>
          <div class="info-item">
            <span class="info-label">Data Transitions:</span>
            <span class="info-value ${dataTransitions > 0 ? 'success' : ''}">${dataTransitions}</span>
          </div>
          <div class="info-item full-width">
            <span class="info-label">Layout:</span>
            <span class="info-value ${positionClass}">
              ${positionStatus}
            </span>
          </div>
        </div>
      `;
    }
  
    async updatePreview(dialog) {
      if (!this.currentParsedNet) return;
  
      // Get settings
      const settings = this.getLayoutSettings(dialog);
      
      // Apply layout if needed
      const netWithLayout = await this.applyLayout(this.currentParsedNet, settings);
      
      // Render preview
      this.renderPreview(dialog, netWithLayout);
    }
  
    getLayoutSettings(dialog) {
      return {
        applyAlgorithm: dialog.querySelector('#apply-algorithm').checked,
        elementSpacing: parseInt(dialog.querySelector('#element-spacing').value),
        elementSize: parseInt(dialog.querySelector('#element-size').value),
        centerLayout: dialog.querySelector('#center-layout').checked,
        compactLayout: dialog.querySelector('#compact-layout').checked,
        preventOverlap: dialog.querySelector('#prevent-overlap').checked
      };
    }
  
    async applyLayout(parsedNet, settings) {
      const netCopy = JSON.parse(JSON.stringify(parsedNet));
      
      // Check if we need to generate positions
      const hasPositions = netCopy.places.some(p => p.position) || netCopy.transitions.some(t => t.position);
      
      if (!hasPositions || settings.applyAlgorithm) {
        // Apply the BPMN layout algorithm
        await this.layoutAlgorithm.applyLayout(netCopy, settings);
      } else {
        // Scale existing positions to match our spacing requirements
        this.scaleExistingPositions(netCopy, settings);
      }
      
      // Apply overlap prevention if requested
      if (settings.preventOverlap) {
        this.preventElementOverlap(netCopy, settings);
      }
      
      return netCopy;
    }
  
    preventElementOverlap(net, settings) {
      const elements = [...net.places, ...net.transitions].filter(e => e.position);
      const minDistance = settings.elementSpacing * 0.8; // Minimum 80% of desired spacing
      
      // Sort elements by position for consistent processing
      elements.sort((a, b) => a.position.x - b.position.x || a.position.y - b.position.y);
      
      for (let i = 0; i < elements.length; i++) {
        for (let j = i + 1; j < elements.length; j++) {
          const elem1 = elements[i];
          const elem2 = elements[j];
          
          const dx = elem2.position.x - elem1.position.x;
          const dy = elem2.position.y - elem1.position.y;
          const distance = Math.sqrt(dx * dx + dy * dy);
          
          if (distance < minDistance && distance > 0) {
            // Calculate required separation
            const pushDistance = (minDistance - distance) / 2;
            const angle = Math.atan2(dy, dx);
            
            // Push elements apart
            const pushX = Math.cos(angle) * pushDistance;
            const pushY = Math.sin(angle) * pushDistance;
            
            elem1.position.x -= pushX;
            elem1.position.y -= pushY;
            elem2.position.x += pushX;
            elem2.position.y += pushY;
          }
        }
      }
    }
  
    scaleExistingPositions(net, settings) {
      // Find existing bounds
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      
      [...net.places, ...net.transitions].forEach(element => {
        if (element.position) {
          minX = Math.min(minX, element.position.x);
          minY = Math.min(minY, element.position.y);
          maxX = Math.max(maxX, element.position.x);
          maxY = Math.max(maxY, element.position.y);
        }
      });
      
      const currentWidth = maxX - minX;
      const currentHeight = maxY - minY;
      
      // Calculate desired spacing
      const desiredSpacing = settings.elementSpacing;
      
      // Scale positions to achieve desired spacing
      const scaleX = currentWidth > 0 ? (net.places.length + net.transitions.length - 1) * desiredSpacing / currentWidth : 1;
      const scaleY = currentHeight > 0 ? desiredSpacing / Math.max(currentHeight / (net.places.length + net.transitions.length), 1) : 1;
      
      [...net.places, ...net.transitions].forEach(element => {
        if (element.position) {
          element.position.x = (element.position.x - minX) * scaleX;
          element.position.y = (element.position.y - minY) * scaleY;
        }
      });
    }
  
    renderPreview(dialog, netWithLayout) {
      const canvas = dialog.querySelector('#pnml-preview-canvas');
      const ctx = canvas.getContext('2d');
      
      // Clear canvas
      ctx.clearRect(0, 0, canvas.width, canvas.height);
      ctx.fillStyle = '#2E3440';
      ctx.fillRect(0, 0, canvas.width, canvas.height);
      
      // Calculate bounds and scale
      const bounds = this.calculateBounds(netWithLayout);
      if (bounds.width === 0 || bounds.height === 0) return;
      
      const scale = this.calculateScale(bounds, canvas);
      const offset = this.calculateOffset(bounds, canvas, scale);
      
      // Apply transformations
      ctx.save();
      ctx.translate(offset.x, offset.y);
      ctx.scale(scale, scale);
      
      // Render elements
      this.renderPreviewArcs(ctx, netWithLayout);
      this.renderPreviewPlaces(ctx, netWithLayout);
      this.renderPreviewTransitions(ctx, netWithLayout);
      
      ctx.restore();
    }
  
    calculateBounds(net) {
      let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;
      
      [...net.places, ...net.transitions].forEach(element => {
        if (element.position) {
          minX = Math.min(minX, element.position.x);
          minY = Math.min(minY, element.position.y);
          maxX = Math.max(maxX, element.position.x);
          maxY = Math.max(maxY, element.position.y);
        }
      });
      
      // Add padding
      const padding = 50;
      return { 
        minX: minX - padding, 
        minY: minY - padding, 
        maxX: maxX + padding, 
        maxY: maxY + padding, 
        width: maxX - minX + 2 * padding, 
        height: maxY - minY + 2 * padding 
      };
    }
  
    calculateScale(bounds, canvas) {
      const padding = 20;
      const availableWidth = canvas.width - 2 * padding;
      const availableHeight = canvas.height - 2 * padding;
      
      const scaleX = availableWidth / bounds.width;
      const scaleY = availableHeight / bounds.height;
      
      return Math.min(scaleX, scaleY, 1);
    }
  
    calculateOffset(bounds, canvas, scale) {
      const scaledWidth = bounds.width * scale;
      const scaledHeight = bounds.height * scale;
      
      return {
        x: (canvas.width - scaledWidth) / 2 - bounds.minX * scale,
        y: (canvas.height - scaledHeight) / 2 - bounds.minY * scale
      };
    }
  
    renderPreviewArcs(ctx, net) {
      net.arcs.forEach(arc => {
        const source = [...net.places, ...net.transitions].find(e => e.id === arc.source);
        const target = [...net.places, ...net.transitions].find(e => e.id === arc.target);
        
        if (source && target && source.position && target.position) {
          ctx.strokeStyle = '#88C0D0';
          ctx.lineWidth = 2;
          ctx.beginPath();
          ctx.moveTo(source.position.x, source.position.y);
          ctx.lineTo(target.position.x, target.position.y);
          ctx.stroke();
          
          // Simple arrowhead
          const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);
          const arrowLength = 8;
          ctx.beginPath();
          ctx.moveTo(target.position.x, target.position.y);
          ctx.lineTo(
            target.position.x - arrowLength * Math.cos(angle - 0.5),
            target.position.y - arrowLength * Math.sin(angle - 0.5)
          );
          ctx.lineTo(
            target.position.x - arrowLength * Math.cos(angle + 0.5),
            target.position.y - arrowLength * Math.sin(angle + 0.5)
          );
          ctx.closePath();
          ctx.fillStyle = '#88C0D0';
          ctx.fill();
        }
      });
    }
  
    renderPreviewPlaces(ctx, net) {
      net.places.forEach(place => {
        if (place.position) {
          const radius = 15;
          
          // Place circle
          ctx.beginPath();
          ctx.arc(place.position.x, place.position.y, radius, 0, Math.PI * 2);
          ctx.fillStyle = '#ECEFF4';
          ctx.fill();
          ctx.strokeStyle = '#4C566A';
          ctx.lineWidth = 2;
          ctx.stroke();
          
          // Tokens
          if (place.tokens > 0) {
            ctx.fillStyle = '#2E3440';
            ctx.font = '10px Arial';
            ctx.textAlign = 'center';
            ctx.textBaseline = 'middle';
            ctx.fillText(place.tokens.toString(), place.position.x, place.position.y);
          }
        }
      });
    }
  
    renderPreviewTransitions(ctx, net) {
      net.transitions.forEach(transition => {
        if (transition.position) {
          const width = 15;
          const height = 30;
          
          ctx.fillStyle = '#D8DEE9';
          ctx.fillRect(
            transition.position.x - width/2,
            transition.position.y - height/2,
            width,
            height
          );
          ctx.strokeStyle = '#4C566A';
          ctx.lineWidth = 2;
          ctx.strokeRect(
            transition.position.x - width/2,
            transition.position.y - height/2,
            width,
            height
          );
        }
      });
    }
  
    fitPreviewToView(dialog) {
      this.updatePreview(dialog);
    }
  
    async importToEditor(dialog) {
      if (!this.currentParsedNet) return;
  
      try {
        await this.showProgress(dialog, 'Importing to editor...', 0);
  
        // Stop any auto-run simulation
        if (this.app.autoRunInterval) {
          this.app.stopAutoRun();
        }
  
        await this.showProgress(dialog, 'Creating API instance...', 20);
  
        // Create new API instance based on data content
        let newAPI;
        if (this.currentParsedNet.dataVariables.length > 0 || 
            this.currentParsedNet.transitions.some(t => t.isDataAware)) {
          newAPI = new DataPetriNetAPI(
            this.currentParsedNet.id,
            this.currentParsedNet.name,
            this.currentParsedNet.description
          );
        } else {
          newAPI = new PetriNetAPI(
            this.currentParsedNet.id,
            this.currentParsedNet.name,
            this.currentParsedNet.description
          );
        }
  
        await this.showProgress(dialog, 'Applying layout...', 40);
  
        // Get final layout settings and apply layout
        const settings = this.getLayoutSettings(dialog);
        const netWithLayout = await this.applyLayout(this.currentParsedNet, settings);
  
        await this.showProgress(dialog, 'Creating places...', 60);
  
        // Import places with proper positioning
        netWithLayout.places.forEach(placeData => {
          const place = new Place(
            placeData.id,
            placeData.position || { x: 100, y: 100 },
            placeData.label,
            placeData.tokens,
            placeData.capacity
          );
          newAPI.petriNet.places.set(placeData.id, place);
        });
  
        await this.showProgress(dialog, 'Creating transitions...', 70);
  
        // Import transitions with proper positioning and data-awareness detection
        netWithLayout.transitions.forEach(transitionData => {
          let transition;
          
          // Check if this should be a data-aware transition
          const shouldBeDataAware = transitionData.isDataAware || 
                                   transitionData.precondition || 
                                   transitionData.postcondition ||
                                   (newAPI instanceof DataPetriNetAPI);
          
          if (shouldBeDataAware && typeof DataAwareTransition !== 'undefined') {
            transition = new DataAwareTransition(
              transitionData.id,
              transitionData.position || { x: 100, y: 100 },
              transitionData.label,
              transitionData.priority,
              transitionData.delay,
              transitionData.precondition,
              transitionData.postcondition
            );
          } else {
            transition = new Transition(
              transitionData.id,
              transitionData.position || { x: 100, y: 100 },
              transitionData.label,
              transitionData.priority,
              transitionData.delay
            );
          }
          newAPI.petriNet.transitions.set(transitionData.id, transition);
        });
  
        await this.showProgress(dialog, 'Creating arcs...', 80);
  
        // Import arcs
        netWithLayout.arcs.forEach(arcData => {
          const arc = new Arc(
            arcData.id,
            arcData.source,
            arcData.target,
            arcData.weight,
            arcData.type,
            arcData.points,
            arcData.label || arcData.weight.toString()
          );
          newAPI.petriNet.arcs.set(arcData.id, arc);
        });
  
        await this.showProgress(dialog, 'Importing data variables...', 90);
  
        // Import data variables if present
        if (newAPI instanceof DataPetriNetAPI && netWithLayout.dataVariables.length > 0) {
          netWithLayout.dataVariables.forEach(varData => {
            const variable = new DataVariable(
              varData.id,
              varData.name,
              varData.type,
              varData.currentValue,
              varData.description
            );
            newAPI.petriNet.dataVariables.set(varData.id, variable);
          });
        }
  
        await this.showProgress(dialog, 'Finalizing...', 95);
  
        // Replace the app's API
        this.app.api = newAPI;
        this.app.editor = newAPI.attachEditor(this.app.canvas);
  
        // Set up renderer based on API type
        if (newAPI instanceof DataPetriNetAPI) {
          this.app.editor.renderer = new DataPetriNetRenderer(this.app.canvas, newAPI.petriNet);
        }
  
        // Restore app functionality
        this.app.editor.app = this.app;
        this.app.editor.setOnSelectCallback(this.app.handleElementSelected.bind(this.app));
        this.app.editor.setOnChangeCallback(this.app.handleNetworkChanged.bind(this.app));
        this.app.editor.setSnapToGrid(this.app.gridEnabled);
        this.app.editor.setMode('select');
        this.app.updateActiveButton('btn-select');
  
        // Render and update displays
        this.app.editor.render();
        this.app.updateTokensDisplay();
        this.app.updateZoomDisplay();
        this.app.propertiesPanel.innerHTML = '<p>No element selected.</p>';
  
        // Update data displays if DataPetriNet
        if (this.app.dataPetriNetUI) {
          this.app.dataPetriNetUI.updateDataVariablesDisplay();
          this.app.dataPetriNetUI.updateDataValuesDisplay();
        }
  
        await this.showProgress(dialog, 'Complete!', 100);
  
        // Clean up
        this.currentParsedNet = null;
  
        // Close dialog and show success
        setTimeout(() => {
          document.body.removeChild(dialog);
          alert('PNML file imported successfully!');
        }, 500);
  
      } catch (error) {
        this.hideProgress(dialog);
        console.error('Error importing PNML:', error);
        alert('Error importing PNML file: ' + error.message);
      }
    }
  
    generateUUID() {
      return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
        const r = Math.random() * 16 | 0;
        const v = c === 'x' ? r : (r & 0x3 | 0x8);
        return v.toString(16);
      });
    }
  }
  
  /**
   * BPMN Layout Algorithm Implementation
   * Based on "A Simple Algorithm for Automatic Layout of BPMN Processes" (Kitzmann et al., 2009)
   */
  class LayoutAlgorithm {
    constructor() {
      this.grid = null;
      this.sortedElements = [];
      this.elementTypes = new Map();
    }
  
    async applyLayout(net, settings) {
      // Step 1: Classify elements
      this.classifyElements(net);
      
      // Step 2: Modified topological sort
      this.sortedElements = this.modifiedTopologicalSort(net);
      
      // Step 3: Initialize grid
      this.grid = new Layouter();
      this.settings = settings; // Store settings for grid operations
      
      // Step 4: Position elements
      await this.positionElements(net, settings);
      
      // Step 5: Apply heuristics
      if (settings.compactLayout) {
        this.applyInterleaving();
      }
      
      // Step 6: Calculate final coordinates
      this.calculateFinalCoordinates(net, settings);
      
      // Step 7: Center if requested
      if (settings.centerLayout) {
        this.centerLayout(net);
      }
    }
  
    classifyElements(net) {
      this.elementTypes.clear();
      
      // Classify places and transitions
      [...net.places, ...net.transitions].forEach(element => {
        const types = new Set(['element']);
        
        // Count incoming and outgoing arcs
        const incomingArcs = net.arcs.filter(arc => arc.target === element.id);
        const outgoingArcs = net.arcs.filter(arc => arc.source === element.id);
        
        // Classify based on arc counts
        if (incomingArcs.length === 0) {
          types.add('start');
        }
        if (outgoingArcs.length === 0) {
          types.add('end');
        }
        if (incomingArcs.length > 1) {
          types.add('join');
        }
        if (outgoingArcs.length > 1) {
          types.add('split');
        }
        
        this.elementTypes.set(element.id, types);
      });
    }
  
    modifiedTopologicalSort(net) {
      const elements = [...net.places, ...net.transitions];
      const arcs = net.arcs;
      const incomingCount = new Map();
      const result = [];
      const backwardEdges = new Set();
      
      // Initialize incoming link counters
      elements.forEach(element => {
        const incomingArcs = arcs.filter(arc => arc.target === element.id);
        incomingCount.set(element.id, incomingArcs.length);
      });
      
      const originalIncomingCount = new Map(incomingCount);
      
      while (elements.some(e => !result.includes(e))) {
        // Find nodes with no incoming edges
        const freeNodes = elements.filter(element => 
          !result.includes(element) && incomingCount.get(element.id) === 0
        );
        
        if (freeNodes.length > 0) {
          // Standard topological sort step
          const node = freeNodes[0]; // Take first available
          result.push(node);
          
          // Update incoming counts for successors
          const outgoingArcs = arcs.filter(arc => arc.source === node.id);
          outgoingArcs.forEach(arc => {
            const targetId = arc.target;
            incomingCount.set(targetId, incomingCount.get(targetId) - 1);
          });
        } else {
          // Handle cycle - find loop entry
          const remainingElements = elements.filter(e => !result.includes(e));
          
          // Find a join that has some processed incoming edges
          let loopEntry = remainingElements.find(element => {
            const types = this.elementTypes.get(element.id);
            return types.has('join') && 
                   incomingCount.get(element.id) < originalIncomingCount.get(element.id);
          });
          
          if (!loopEntry) {
            // If no join found, take any remaining element
            loopEntry = remainingElements[0];
          }
          
          // Virtually reverse remaining incoming edges
          const remainingIncoming = arcs.filter(arc => 
            arc.target === loopEntry.id && 
            !result.find(e => e.id === arc.source)
          );
          
          remainingIncoming.forEach(arc => {
            backwardEdges.add(arc.id);
            incomingCount.set(loopEntry.id, incomingCount.get(loopEntry.id) - 1);
          });
        }
      }
      
      return result;
    }
  
    async positionElements(net, settings) {
      for (let i = 0; i < this.sortedElements.length; i++) {
        const element = this.sortedElements[i];
        const elementTypes = this.elementTypes.get(element.id);
        
        if (elementTypes.has('start')) {
          // Place start elements in the first column
          if (this.settings && this.settings.preventOverlap) {
            this.grid.placeElementWithSpacing(element.id, 0, this.grid.getNextAvailableRow(0), 1);
          } else {
            this.grid.placeElement(element.id, 0, this.grid.getNextAvailableRow(0));
          }
        } else {
          this.positionElementRelativeTopredecessors(element, net);
        }
        
        // Allow UI updates during layout
        if (i % 10 === 0) {
          await new Promise(resolve => setTimeout(resolve, 1));
        }
      }
    }
  
    positionElementRelativeTopredecessors(element, net) {
      const elementTypes = this.elementTypes.get(element.id);
      const incomingArcs = net.arcs.filter(arc => arc.target === element.id);
      
      if (incomingArcs.length === 0) {
        // No predecessors, place at origin
        if (this.settings && this.settings.preventOverlap) {
          this.grid.placeElementWithSpacing(element.id, 0, 0, 1);
        } else {
          this.grid.placeElement(element.id, 0, 0);
        }
        return;
      }
      
      const predecessorPositions = incomingArcs.map(arc => {
        return this.grid.getElementPosition(arc.source);
      }).filter(pos => pos !== null);
      
      if (predecessorPositions.length === 0) {
        // Predecessors not positioned yet, place at origin
        if (this.settings && this.settings.preventOverlap) {
          this.grid.placeElementWithSpacing(element.id, 0, 0, 1);
        } else {
          this.grid.placeElement(element.id, 0, 0);
        }
        return;
      }
      
      const useSpacing = this.settings && this.settings.preventOverlap;
      
      if (elementTypes.has('join')) {
        // Position join to the right of rightmost predecessor
        const rightmostCol = Math.max(...predecessorPositions.map(pos => pos.col));
        const targetCol = rightmostCol + 1;
        
        // Try to align with corresponding split if possible
        const avgRow = Math.round(
          predecessorPositions.reduce((sum, pos) => sum + pos.row, 0) / predecessorPositions.length
        );
        
        if (useSpacing) {
          this.grid.placeElementWithSpacing(element.id, targetCol, avgRow, 1);
        } else {
          this.grid.placeElement(element.id, targetCol, avgRow);
        }
      } else if (predecessorPositions.length === 1) {
        // Single predecessor - place to the right
        const predPos = predecessorPositions[0];
        const targetCol = predPos.col + 1;
        
        // Check if predecessor is a split
        const predElement = [...net.places, ...net.transitions].find(e => e.id === incomingArcs[0].source);
        const predTypes = this.elementTypes.get(predElement.id);
        
        if (predTypes.has('split')) {
          // Distribute elements after split
          const splitSuccessors = net.arcs.filter(arc => arc.source === predElement.id);
          const thisArcIndex = splitSuccessors.findIndex(arc => arc.target === element.id);
          const targetRow = predPos.row + thisArcIndex - Math.floor(splitSuccessors.length / 2);
          
          if (useSpacing) {
            this.grid.placeElementWithSpacing(element.id, targetCol, targetRow, 1);
          } else {
            this.grid.placeElement(element.id, targetCol, targetRow);
          }
        } else {
          // Regular sequence - place in same row
          if (useSpacing) {
            this.grid.placeElementWithSpacing(element.id, targetCol, predPos.row, 1);
          } else {
            this.grid.placeElement(element.id, targetCol, predPos.row);
          }
        }
      } else {
        // Multiple predecessors - place to the right of rightmost
        const rightmostCol = Math.max(...predecessorPositions.map(pos => pos.col));
        const avgRow = Math.round(
          predecessorPositions.reduce((sum, pos) => sum + pos.row, 0) / predecessorPositions.length
        );
        
        if (useSpacing) {
          this.grid.placeElementWithSpacing(element.id, rightmostCol + 1, avgRow, 1);
        } else {
          this.grid.placeElement(element.id, rightmostCol + 1, avgRow);
        }
      }
    }
  
    applyInterleaving() {
      // Compact the grid by interleaving rows where possible
      let changed = true;
      while (changed) {
        changed = false;
        
        for (let row = 0; row < this.grid.getMaxRow(); row++) {
          const nextRow = row + 1;
          if (this.grid.canInterleaveRows(row, nextRow)) {
            this.grid.interleaveRows(row, nextRow);
            changed = true;
            break; // Start over to maintain consistency
          }
        }
      }
    }
  
    calculateFinalCoordinates(net, settings) {
      const spacing = settings.elementSpacing;
      
      // Calculate grid cell sizes
      const colWidths = this.grid.getColumnWidths();
      const rowHeights = this.grid.getRowHeights();
      
      // Convert grid positions to actual coordinates
      [...net.places, ...net.transitions].forEach(element => {
        const gridPos = this.grid.getElementPosition(element.id);
        if (gridPos) {
          // Calculate cumulative position
          let x = 0;
          for (let col = 0; col < gridPos.col; col++) {
            x += spacing;
          }
          
          let y = 0;
          for (let row = 0; row < gridPos.row; row++) {
            y += spacing;
          }
          
          element.position = { x, y };
        }
      });
    }
  
    centerLayout(net) {
      const elements = [...net.places, ...net.transitions].filter(e => e.position);
      if (elements.length === 0) return;
      
      // Calculate bounds
      let minX = Math.min(...elements.map(e => e.position.x));
      let minY = Math.min(...elements.map(e => e.position.y));
      let maxX = Math.max(...elements.map(e => e.position.x));
      let maxY = Math.max(...elements.map(e => e.position.y));
      
      // Calculate center offset
      const centerX = (minX + maxX) / 2;
      const centerY = (minY + maxY) / 2;
      
      // Apply offset to center at origin
      elements.forEach(element => {
        element.position.x -= centerX;
        element.position.y -= centerY;
      });
    }
  }
  
  /**
   * Grid data structure for layout positioning
   */
  class Layouter {
    constructor() {
      this.cells = new Map(); // Map<'col,row', elementId>
      this.elementPositions = new Map(); // Map<elementId, {col, row}>
      this.maxCol = 0;
      this.maxRow = 0;
    }
  
    placeElement(elementId, col, row) {
      // Ensure row is available
      while (this.cells.has(`${col},${row}`)) {
        row++;
      }
      
      const key = `${col},${row}`;
      this.cells.set(key, elementId);
      this.elementPositions.set(elementId, { col, row });
      
      this.maxCol = Math.max(this.maxCol, col);
      this.maxRow = Math.max(this.maxRow, row);
    }
  
    placeElementWithSpacing(elementId, col, row, minSpacing = 1) {
      // Find available position with minimum spacing
      let bestRow = row;
      let foundValidPosition = false;
      
      // Try original position first
      if (this.isPositionAvailableWithSpacing(col, row, minSpacing)) {
        bestRow = row;
        foundValidPosition = true;
      } else {
        // Search nearby positions
        for (let offset = 1; offset <= 10; offset++) {
          // Try above
          if (row - offset >= 0 && this.isPositionAvailableWithSpacing(col, row - offset, minSpacing)) {
            bestRow = row - offset;
            foundValidPosition = true;
            break;
          }
          // Try below
          if (this.isPositionAvailableWithSpacing(col, row + offset, minSpacing)) {
            bestRow = row + offset;
            foundValidPosition = true;
            break;
          }
        }
      }
      
      // If no position with spacing found, place normally
      if (!foundValidPosition) {
        this.placeElement(elementId, col, row);
      } else {
        const key = `${col},${bestRow}`;
        this.cells.set(key, elementId);
        this.elementPositions.set(elementId, { col, row: bestRow });
        
        this.maxCol = Math.max(this.maxCol, col);
        this.maxRow = Math.max(this.maxRow, bestRow);
      }
    }
  
    isPositionAvailableWithSpacing(col, row, minSpacing) {
      // Check if position and surrounding cells are free
      for (let checkRow = row - minSpacing; checkRow <= row + minSpacing; checkRow++) {
        for (let checkCol = col - minSpacing; checkCol <= col + minSpacing; checkCol++) {
          if (checkRow >= 0 && checkCol >= 0) {
            const checkKey = `${checkCol},${checkRow}`;
            if (this.cells.has(checkKey)) {
              return false;
            }
          }
        }
      }
      return true;
    }
  
    getElementPosition(elementId) {
      return this.elementPositions.get(elementId) || null;
    }
  
    getNextAvailableRow(col) {
      let row = 0;
      while (this.cells.has(`${col},${row}`)) {
        row++;
      }
      return row;
    }
  
    getMaxRow() {
      return this.maxRow;
    }
  
    canInterleaveRows(row1, row2) {
      // Check if two rows can be merged
      for (let col = 0; col <= this.maxCol; col++) {
        const key1 = `${col},${row1}`;
        const key2 = `${col},${row2}`;
        
        if (this.cells.has(key1) && this.cells.has(key2)) {
          return false; // Both rows have elements in the same column
        }
      }
      return true;
    }
  
    interleaveRows(row1, row2) {
      // Merge row2 into row1
      for (let col = 0; col <= this.maxCol; col++) {
        const key2 = `${col},${row2}`;
        if (this.cells.has(key2)) {
          const elementId = this.cells.get(key2);
          this.cells.delete(key2);
          
          const key1 = `${col},${row1}`;
          this.cells.set(key1, elementId);
          this.elementPositions.set(elementId, { col, row: row1 });
        }
      }
      
      // Shift all rows above row2 down by one
      for (let row = row2 + 1; row <= this.maxRow; row++) {
        for (let col = 0; col <= this.maxCol; col++) {
          const oldKey = `${col},${row}`;
          if (this.cells.has(oldKey)) {
            const elementId = this.cells.get(oldKey);
            this.cells.delete(oldKey);
            
            const newKey = `${col},${row - 1}`;
            this.cells.set(newKey, elementId);
            this.elementPositions.set(elementId, { col, row: row - 1 });
          }
        }
      }
      
      this.maxRow--;
    }
  
    getColumnWidths() {
      // For now, return uniform widths
      return Array(this.maxCol + 1).fill(100);
    }
  
    getRowHeights() {
      // For now, return uniform heights
      return Array(this.maxRow + 1).fill(100);
    }
  }
  
  // Initialize when DOM is ready
  document.addEventListener('DOMContentLoaded', () => {
    const initTimer = setInterval(() => {
      if (window.petriApp) {
        window.pnmlImporter = new PNMLImporter(window.petriApp);
        clearInterval(initTimer);
      }
    }, 100);
  });