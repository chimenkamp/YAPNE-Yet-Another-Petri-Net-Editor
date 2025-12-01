/**
 * PNG Exporter for Petri Net Editor
 * Provides sophisticated PNG export functionality with extensive customization options
 */

class PNGExporter {
  constructor(app) {
    this.app = app;
    this.dialog = null;
    this.previewCanvas = null;
    this.localStorageKey = 'pngExporterSettings';
    this.exportSettings = this.loadSettings();
    this.initializeUI();
  }

  /**
   * Get default export settings
   */
  getDefaultSettings() {
    return {
      // Image properties
      width: 1920,
      height: 1080,
      format: 'png',
      quality: 1.0,
      backgroundColor: '#ffffff',
      
      // Canvas and viewport
      fitToContent: true,
      contentPadding: 50,
      maintainAspectRatio: true,
      
      // Element appearance
      showPlaces: true,
      showTransitions: true,
      showArcs: true,
      showLabels: true,
      showTokens: true,
      
      // Colors and styling
      placeColor: '#ffffff',
      placeStroke: '#000000',
      transitionColor: '#d3d3d3',
      transitionStroke: '#000000',
      enabledTransitionColor: '#90ee90',
      arcColor: '#000000',
      textColor: '#000000',
      tokenColor: '#000000',
      
      // Data Petri Net specific
      showConditions: true,
      showDataGuards: true,
      showDataUpdates: true,
      dataTransitionColor: '#8FBCBB',
      dataTransitionStroke: '#5E81AC',
      enabledDataTransitionColor: '#A3BE8C',
      disabledDataTransitionColor: '#D08770',
      
      // Visual enhancements
      highlightFirableTransitions: false,
      highlightSelectedElements: false,
      lineThickness: 2,
      fontSize: 12,
      fontFamily: 'Arial',
      
      // Advanced options
      antialiasing: true,
      transparency: false,
      dpiScale: 1.0,
      includeMetadata: false,
      
      // Condition display
      conditionPosition: 'top', // 'top', 'bottom', 'left', 'right', 'auto'
      conditionFontSize: 10,
      conditionColor: '#666666',
      conditionBackground: true,
      conditionBackgroundColor: '#f0f0f0',
      prettyPrintConditions: true,
      prettyPrintVariablesItalic: true,
      
      // Grid and guidelines
      showGrid: false,
      gridColor: '#767676ff',
      gridSize: 20
    };
  }

  /**
   * Load settings from local storage or return defaults
   */
  loadSettings() {
    try {
      const savedSettings = localStorage.getItem(this.localStorageKey);
      if (savedSettings) {
        const parsed = JSON.parse(savedSettings);
        // Merge with defaults to ensure new settings are included
        const defaults = this.getDefaultSettings();
        return { ...defaults, ...parsed };
      }
    } catch (error) {
      console.warn('Failed to load PNG exporter settings from local storage:', error);
    }
    return this.getDefaultSettings();
  }

  /**
   * Save current settings to local storage
   */
  saveSettings() {
    try {
      localStorage.setItem(this.localStorageKey, JSON.stringify(this.exportSettings));
    } catch (error) {
      console.error('Failed to save PNG exporter settings to local storage:', error);
    }
  }

  /**
   * Initialize the PNG exporter UI
   */
  initializeUI() {
    this.addExportButton();
  }

  /**
   * Add the PNG export button to the File Operations section
   */
  addExportButton() {
    const fileOperationsSection = document.querySelector('#file-operations-section .section-content');
    if (!fileOperationsSection) return;

    // Find or create the button group for PNG export
    let pngButtonGroup = fileOperationsSection.querySelector('#png-button-group');
    if (!pngButtonGroup) {
      pngButtonGroup = document.createElement('div');
      pngButtonGroup.className = 'button-group';
      pngButtonGroup.id = 'png-button-group';
      fileOperationsSection.appendChild(pngButtonGroup);
    }

    // Create the PNG export button
    const exportButton = document.createElement('button');
    exportButton.id = 'btn-export-png';
    exportButton.textContent = 'Save (PNG)';
    exportButton.style.backgroundColor = 'rgb(101, 127, 152)';

    exportButton.addEventListener('click', () => this.showExportDialog());
    
    pngButtonGroup.appendChild(exportButton);
  }

  /**
   * Show the PNG export dialog
   */
  showExportDialog() {
    if (this.dialog) {
      document.body.removeChild(this.dialog);
    }
    
    this.dialog = this.createExportDialog();
    document.body.appendChild(this.dialog);
    
    // Initialize preview
    this.updatePreview();
    
    setTimeout(() => {
      const firstInput = this.dialog.querySelector('input');
      if (firstInput) firstInput.focus();
    }, 100);
  }

  /**
   * Create the sophisticated PNG export dialog
   */
  createExportDialog() {
    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay';
    dialog.id = 'png-export-dialog';
    
    dialog.innerHTML = `
      <div class="modal-container png-export-container">
        <div class="modal-header">
          <h2>🖼️ Export as PNG</h2>
          <button class="close-btn">&times;</button>
        </div>
        <div class="modal-body">
          <div class="png-export-content">
            
            <!-- Tab Navigation -->
            <div class="form-tab-container">
              <div class="form-tabs">
                <button class="form-tab active" data-tab="image">Image</button>
                <button class="form-tab" data-tab="appearance">Appearance</button>
                <button class="form-tab" data-tab="elements">Elements</button>
                <button class="form-tab" data-tab="conditions">Conditions</button>
                <button class="form-tab" data-tab="advanced">Advanced</button>
                <button class="form-tab" data-tab="preview">Preview</button>
              </div>

              <!-- Image Settings Tab -->
              <div class="form-tab-content active" data-tab="image">
                <h3>🖼️ Image Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Dimensions</h4>
                    <div class="setting-item">
                      <label for="export-width">Width (px):</label>
                      <input type="number" id="export-width" min="100" max="8192" value="${this.exportSettings.width}">
                    </div>
                    <div class="setting-item">
                      <label for="export-height">Height (px):</label>
                      <input type="number" id="export-height" min="100" max="8192" value="${this.exportSettings.height}">
                    </div>
                    <div class="setting-item">
                      <label for="maintain-aspect-ratio">
                        <input type="checkbox" id="maintain-aspect-ratio" ${this.exportSettings.maintainAspectRatio ? 'checked' : ''}>
                        Maintain aspect ratio
                      </label>
                    </div>
                  </div>
                  
                  <div class="setting-group">
                    <h4>Content Fitting</h4>
                    <div class="setting-item">
                      <label for="fit-to-content">
                        <input type="checkbox" id="fit-to-content" ${this.exportSettings.fitToContent ? 'checked' : ''}>
                        Fit to content
                      </label>
                      <small>Automatically adjust view to show all elements</small>
                    </div>
                    <div class="setting-item">
                      <label for="content-padding">Content padding (px):</label>
                      <input type="range" id="content-padding" min="0" max="200" value="${this.exportSettings.contentPadding}">
                      <span class="range-value">${this.exportSettings.contentPadding}px</span>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Background</h4>
                    <div class="setting-item">
                      <label for="transparency">
                        <input type="checkbox" id="transparency" ${this.exportSettings.transparency ? 'checked' : ''}>
                        Transparent background
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="background-color">Background color:</label>
                      <input type="color" id="background-color" value="${this.exportSettings.backgroundColor}">
                    </div>
                  </div>
                </div>
              </div>

              <!-- Appearance Settings Tab -->
              <div class="form-tab-content" data-tab="appearance">
                <h3>🎨 Appearance Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Places</h4>
                    <div class="setting-item">
                      <label for="place-color">Fill color:</label>
                      <input type="color" id="place-color" value="${this.exportSettings.placeColor}">
                    </div>
                    <div class="setting-item">
                      <label for="place-stroke">Stroke color:</label>
                      <input type="color" id="place-stroke" value="${this.exportSettings.placeStroke}">
                    </div>
                    <div class="setting-item">
                      <label for="token-color">Token color:</label>
                      <input type="color" id="token-color" value="${this.exportSettings.tokenColor}">
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Transitions</h4>
                    <div class="setting-item">
                      <label for="transition-color">Fill color:</label>
                      <input type="color" id="transition-color" value="${this.exportSettings.transitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="transition-stroke">Stroke color:</label>
                      <input type="color" id="transition-stroke" value="${this.exportSettings.transitionStroke}">
                    </div>
                    <div class="setting-item">
                      <label for="enabled-transition-color">Enabled transition color:</label>
                      <input type="color" id="enabled-transition-color" value="${this.exportSettings.enabledTransitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="highlight-firable">
                        <input type="checkbox" id="highlight-firable" ${this.exportSettings.highlightFirableTransitions ? 'checked' : ''}>
                        Highlight firable transitions
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Data Transitions</h4>
                    <div class="setting-item">
                      <label for="data-transition-color">Data transition color:</label>
                      <input type="color" id="data-transition-color" value="${this.exportSettings.dataTransitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="data-transition-stroke">Data transition stroke:</label>
                      <input type="color" id="data-transition-stroke" value="${this.exportSettings.dataTransitionStroke}">
                    </div>
                    <div class="setting-item">
                      <label for="enabled-data-transition-color">Enabled data transition:</label>
                      <input type="color" id="enabled-data-transition-color" value="${this.exportSettings.enabledDataTransitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="disabled-data-transition-color">Disabled data transition:</label>
                      <input type="color" id="disabled-data-transition-color" value="${this.exportSettings.disabledDataTransitionColor}">
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Other Elements</h4>
                    <div class="setting-item">
                      <label for="arc-color">Arc color:</label>
                      <input type="color" id="arc-color" value="${this.exportSettings.arcColor}">
                    </div>
                    <div class="setting-item">
                      <label for="text-color">Text color:</label>
                      <input type="color" id="text-color" value="${this.exportSettings.textColor}">
                    </div>
                    <div class="setting-item">
                      <label for="line-thickness">Line thickness:</label>
                      <input type="range" id="line-thickness" min="1" max="10" value="${this.exportSettings.lineThickness}">
                      <span class="range-value">${this.exportSettings.lineThickness}px</span>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Elements Tab -->
              <div class="form-tab-content" data-tab="elements">
                <h3>🔧 Element Visibility</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Basic Elements</h4>
                    <div class="setting-item">
                      <label for="show-places">
                        <input type="checkbox" id="show-places" ${this.exportSettings.showPlaces ? 'checked' : ''}>
                        Show places
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="show-transitions">
                        <input type="checkbox" id="show-transitions" ${this.exportSettings.showTransitions ? 'checked' : ''}>
                        Show transitions
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="show-arcs">
                        <input type="checkbox" id="show-arcs" ${this.exportSettings.showArcs ? 'checked' : ''}>
                        Show arcs
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="show-labels">
                        <input type="checkbox" id="show-labels" ${this.exportSettings.showLabels ? 'checked' : ''}>
                        Show labels
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="show-tokens">
                        <input type="checkbox" id="show-tokens" ${this.exportSettings.showTokens ? 'checked' : ''}>
                        Show tokens
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Text and Fonts</h4>
                    <div class="setting-item">
                      <label for="font-size">Font size:</label>
                      <input type="range" id="font-size" min="8" max="32" value="${this.exportSettings.fontSize}">
                      <span class="range-value">${this.exportSettings.fontSize}px</span>
                    </div>
                    <div class="setting-item">
                      <label for="font-family">Font family:</label>
                      <select id="font-family">
                        <option value="Arial" ${this.exportSettings.fontFamily === 'Arial' ? 'selected' : ''}>Arial</option>
                        <option value="Helvetica" ${this.exportSettings.fontFamily === 'Helvetica' ? 'selected' : ''}>Helvetica</option>
                        <option value="Times New Roman" ${this.exportSettings.fontFamily === 'Times New Roman' ? 'selected' : ''}>Times New Roman</option>
                        <option value="Courier New" ${this.exportSettings.fontFamily === 'Courier New' ? 'selected' : ''}>Courier New</option>
                        <option value="Georgia" ${this.exportSettings.fontFamily === 'Georgia' ? 'selected' : ''}>Georgia</option>
                      </select>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Visual Enhancements</h4>
                    <div class="setting-item">
                      <label for="show-grid">
                        <input type="checkbox" id="show-grid" ${this.exportSettings.showGrid ? 'checked' : ''}>
                        Show grid
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="grid-color">Grid color:</label>
                      <input type="color" id="grid-color" value="${this.exportSettings.gridColor}">
                    </div>
                    <div class="setting-item">
                      <label for="grid-size">Grid size:</label>
                      <input type="range" id="grid-size" min="10" max="50" value="${this.exportSettings.gridSize}">
                      <span class="range-value">${this.exportSettings.gridSize}px</span>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Conditions Tab -->
              <div class="form-tab-content" data-tab="conditions">
                <h3>📋 Condition Display</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Data Petri Net Features</h4>
                    <div class="setting-item">
                      <label for="show-conditions">
                        <input type="checkbox" id="show-conditions" ${this.exportSettings.showConditions ? 'checked' : ''}>
                        Show pre/post conditions
                      </label>
                      <small>Display guard and update expressions for data transitions</small>
                    </div>
                    <div class="setting-item">
                      <label for="show-data-guards">
                        <input type="checkbox" id="show-data-guards" ${this.exportSettings.showDataGuards ? 'checked' : ''}>
                        Show data guards
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="show-data-updates">
                        <input type="checkbox" id="show-data-updates" ${this.exportSettings.showDataUpdates ? 'checked' : ''}>
                        Show data updates
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Condition Appearance</h4>
                    <div class="setting-item">
                      <label for="pretty-print-conditions">
                        <input type="checkbox" id="pretty-print-conditions" ${this.exportSettings.prettyPrintConditions ? 'checked' : ''}>
                        Pretty print operators
                      </label>
                      <small>Use Unicode symbols (≥, ≤, ≠, ∧, ∨, ¬, ×) for mathematical operators</small>
                    </div>
                    <div class="setting-item">
                      <label for="pretty-print-variables-italic">
                        <input type="checkbox" id="pretty-print-variables-italic" ${this.exportSettings.prettyPrintVariablesItalic ? 'checked' : ''}>
                        Italic variables
                      </label>
                      <small>Render variable names in italic font</small>
                    </div>
                    <div class="setting-item">
                      <label for="condition-position">Position:</label>
                      <select id="condition-position">
                        <option value="auto" ${this.exportSettings.conditionPosition === 'auto' ? 'selected' : ''}>Auto</option>
                        <option value="top" ${this.exportSettings.conditionPosition === 'top' ? 'selected' : ''}>Top</option>
                        <option value="bottom" ${this.exportSettings.conditionPosition === 'bottom' ? 'selected' : ''}>Bottom</option>
                        <option value="left" ${this.exportSettings.conditionPosition === 'left' ? 'selected' : ''}>Left</option>
                        <option value="right" ${this.exportSettings.conditionPosition === 'right' ? 'selected' : ''}>Right</option>
                      </select>
                    </div>
                    <div class="setting-item">
                      <label for="condition-font-size">Condition font size:</label>
                      <input type="range" id="condition-font-size" min="8" max="20" value="${this.exportSettings.conditionFontSize}">
                      <span class="range-value">${this.exportSettings.conditionFontSize}px</span>
                    </div>
                    <div class="setting-item">
                      <label for="condition-color">Condition text color:</label>
                      <input type="color" id="condition-color" value="${this.exportSettings.conditionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="condition-background">
                        <input type="checkbox" id="condition-background" ${this.exportSettings.conditionBackground ? 'checked' : ''}>
                        Show condition background
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="condition-background-color">Background color:</label>
                      <input type="color" id="condition-background-color" value="${this.exportSettings.conditionBackgroundColor}">
                    </div>
                  </div>
                </div>
              </div>

              <!-- Advanced Tab -->
              <div class="form-tab-content" data-tab="advanced">
                <h3>⚙️ Advanced Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Image Quality</h4>
                    <div class="setting-item">
                      <label for="dpi-scale">DPI Scale:</label>
                      <input type="range" id="dpi-scale" min="0.5" max="4" step="0.5" value="${this.exportSettings.dpiScale}">
                      <span class="range-value">${this.exportSettings.dpiScale}x</span>
                      <small>Higher values produce sharper images but larger file sizes</small>
                    </div>
                    <div class="setting-item">
                      <label for="antialiasing">
                        <input type="checkbox" id="antialiasing" ${this.exportSettings.antialiasing ? 'checked' : ''}>
                        Anti-aliasing
                      </label>
                      <small>Smooth edges and text</small>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Export Options</h4>
                    <div class="setting-item">
                      <label for="include-metadata">
                        <input type="checkbox" id="include-metadata" ${this.exportSettings.includeMetadata ? 'checked' : ''}>
                        Include metadata
                      </label>
                      <small>Add export settings and timestamp to image metadata</small>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Presets</h4>
                    <div class="setting-item preset-buttons">
                      <button type="button" id="preset-print">📄 Print Quality</button>
                      <button type="button" id="preset-web">🌐 Web Optimized</button>
                      <button type="button" id="preset-presentation">📊 Presentation</button>
                      <button type="button" id="preset-publication">📚 Publication</button>
                    </div>
                    <div class="setting-item">
                      <button type="button" id="reset-settings">🔄 Reset to Defaults</button>
                    </div>
                  </div>
                </div>
              </div>

              <!-- Preview Tab -->
              <div class="form-tab-content" data-tab="preview">
                <h3>👁️ Preview</h3>
                <div class="preview-container">
                  <div class="preview-info" id="preview-info">
                    <span class="preview-dimensions"></span>
                    <span class="preview-filesize"></span>
                  </div>
                  <div class="preview-canvas-container">
                    <canvas id="png-preview-canvas" width="400" height="300"></canvas>
                  </div>
                  <div class="preview-controls">
                    <button type="button" id="refresh-preview">🔄 Refresh Preview</button>
                    <button type="button" id="fit-preview">📐 Fit to View</button>
                  </div>
                </div>
              </div>
            </div>
          </div>
        </div>
        <div class="modal-footer">
          <button type="button" id="export-png-btn">Export PNG</button>
          <button type="button" id="cancel-png-btn">Cancel</button>
        </div>
      </div>
    `;

    this.setupDialogEventListeners(dialog);
    return dialog;
  }

  /**
   * Set up event listeners for the dialog
   */
  setupDialogEventListeners(dialog) {
    // Close button and cancel
    const closeBtn = dialog.querySelector('.close-btn');
    const cancelBtn = dialog.querySelector('#cancel-png-btn');
    
    [closeBtn, cancelBtn].forEach(btn => {
      btn.addEventListener('click', () => {
        document.body.removeChild(dialog);
      });
    });

    // Tab switching
    const tabs = dialog.querySelectorAll('.form-tab');
    tabs.forEach(tab => {
      tab.addEventListener('click', () => {
        this.switchTab(tab.getAttribute('data-tab'));
      });
    });

    // Range inputs with value display
    this.setupRangeInputs(dialog);

    // Setting change listeners
    this.setupSettingListeners(dialog);

    // Preset buttons
    this.setupPresetButtons(dialog);

    // Export button
    const exportBtn = dialog.querySelector('#export-png-btn');
    exportBtn.addEventListener('click', () => {
      this.exportPNG();
    });

    // Preview controls
    const refreshBtn = dialog.querySelector('#refresh-preview');
    const fitBtn = dialog.querySelector('#fit-preview');
    
    refreshBtn.addEventListener('click', () => this.updatePreview());
    fitBtn.addEventListener('click', () => this.fitPreviewToView());
  }

  /**
   * Set up range input value displays
   */
  setupRangeInputs(dialog) {
    const ranges = dialog.querySelectorAll('input[type="range"]');
    ranges.forEach(range => {
      const valueSpan = range.nextElementSibling;
      if (valueSpan && valueSpan.classList.contains('range-value')) {
        range.addEventListener('input', () => {
          let value = range.value;
          if (range.id === 'dpi-scale') {
            valueSpan.textContent = `${value}x`;
          } else {
            valueSpan.textContent = `${value}px`;
          }
        });
      }
    });
  }

  /**
   * Set up listeners for setting changes
   */
  setupSettingListeners(dialog) {
    const inputs = dialog.querySelectorAll('input, select');
    inputs.forEach(input => {
      input.addEventListener('change', () => {
        this.updateSettingsFromDialog(dialog);
        this.updatePreview();
      });
    });

    // Special handling for aspect ratio
    const widthInput = dialog.querySelector('#export-width');
    const heightInput = dialog.querySelector('#export-height');
    const aspectRatioCheckbox = dialog.querySelector('#maintain-aspect-ratio');
    
    let aspectRatio = this.exportSettings.width / this.exportSettings.height;
    
    const updateAspectRatio = () => {
      if (aspectRatioCheckbox.checked) {
        aspectRatio = widthInput.value / heightInput.value;
      }
    };
    
    widthInput.addEventListener('input', () => {
      if (aspectRatioCheckbox.checked) {
        heightInput.value = Math.round(widthInput.value / aspectRatio);
      }
    });
    
    heightInput.addEventListener('input', () => {
      if (aspectRatioCheckbox.checked) {
        widthInput.value = Math.round(heightInput.value * aspectRatio);
      }
    });
    
    aspectRatioCheckbox.addEventListener('change', updateAspectRatio);
  }

  /**
   * Set up preset button functionality
   */
  setupPresetButtons(dialog) {
    const presets = {
      'preset-print': {
        width: 3508,
        height: 2480,
        dpiScale: 2.0,
        backgroundColor: '#ffffff',
        fontSize: 14,
        lineThickness: 2
      },
      'preset-web': {
        width: 1200,
        height: 800,
        dpiScale: 1.0,
        backgroundColor: '#ffffff',
        fontSize: 12,
        lineThickness: 2
      },
      'preset-presentation': {
        width: 1920,
        height: 1080,
        dpiScale: 1.5,
        backgroundColor: '#ffffff',
        fontSize: 16,
        lineThickness: 3
      },
      'preset-publication': {
        width: 2400,
        height: 1600,
        dpiScale: 2.0,
        backgroundColor: '#ffffff',
        fontSize: 12,
        lineThickness: 2
      }
    };

    Object.keys(presets).forEach(presetId => {
      const button = dialog.querySelector(`#${presetId}`);
      button.addEventListener('click', () => {
        const preset = presets[presetId];
        Object.assign(this.exportSettings, preset);
        this.saveSettings();
        this.updateDialogFromSettings(dialog);
        this.updatePreview();
      });
    });

    // Reset button
    const resetBtn = dialog.querySelector('#reset-settings');
    resetBtn.addEventListener('click', () => {
      this.exportSettings = this.getDefaultSettings();
      this.saveSettings();
      this.updateDialogFromSettings(dialog);
      this.updatePreview();
    });
  }

  /**
   * Switch between dialog tabs
   */
  switchTab(tabId) {
    // Update tab buttons
    const tabButtons = this.dialog.querySelectorAll('.form-tab');
    tabButtons.forEach(button => {
      button.classList.toggle('active', button.getAttribute('data-tab') === tabId);
    });

    // Update tab content
    const tabContents = this.dialog.querySelectorAll('.form-tab-content');
    tabContents.forEach(content => {
      content.classList.toggle('active', content.getAttribute('data-tab') === tabId);
    });
  }

  /**
   * Update settings from dialog inputs
   */
  updateSettingsFromDialog(dialog) {
    // Image settings
    this.exportSettings.width = parseInt(dialog.querySelector('#export-width').value);
    this.exportSettings.height = parseInt(dialog.querySelector('#export-height').value);
    this.exportSettings.maintainAspectRatio = dialog.querySelector('#maintain-aspect-ratio').checked;
    this.exportSettings.fitToContent = dialog.querySelector('#fit-to-content').checked;
    this.exportSettings.contentPadding = parseInt(dialog.querySelector('#content-padding').value);
    this.exportSettings.transparency = dialog.querySelector('#transparency').checked;
    this.exportSettings.backgroundColor = dialog.querySelector('#background-color').value;

    // Appearance settings
    this.exportSettings.placeColor = dialog.querySelector('#place-color').value;
    this.exportSettings.placeStroke = dialog.querySelector('#place-stroke').value;
    this.exportSettings.tokenColor = dialog.querySelector('#token-color').value;
    this.exportSettings.transitionColor = dialog.querySelector('#transition-color').value;
    this.exportSettings.transitionStroke = dialog.querySelector('#transition-stroke').value;
    this.exportSettings.enabledTransitionColor = dialog.querySelector('#enabled-transition-color').value;
    this.exportSettings.highlightFirableTransitions = dialog.querySelector('#highlight-firable').checked;
    this.exportSettings.dataTransitionColor = dialog.querySelector('#data-transition-color').value;
    this.exportSettings.dataTransitionStroke = dialog.querySelector('#data-transition-stroke').value;
    this.exportSettings.enabledDataTransitionColor = dialog.querySelector('#enabled-data-transition-color').value;
    this.exportSettings.disabledDataTransitionColor = dialog.querySelector('#disabled-data-transition-color').value;
    this.exportSettings.arcColor = dialog.querySelector('#arc-color').value;
    this.exportSettings.textColor = dialog.querySelector('#text-color').value;
    this.exportSettings.lineThickness = parseInt(dialog.querySelector('#line-thickness').value);

    // Element visibility
    this.exportSettings.showPlaces = dialog.querySelector('#show-places').checked;
    this.exportSettings.showTransitions = dialog.querySelector('#show-transitions').checked;
    this.exportSettings.showArcs = dialog.querySelector('#show-arcs').checked;
    this.exportSettings.showLabels = dialog.querySelector('#show-labels').checked;
    this.exportSettings.showTokens = dialog.querySelector('#show-tokens').checked;
    this.exportSettings.fontSize = parseInt(dialog.querySelector('#font-size').value);
    this.exportSettings.fontFamily = dialog.querySelector('#font-family').value;
    this.exportSettings.showGrid = dialog.querySelector('#show-grid').checked;
    this.exportSettings.gridColor = dialog.querySelector('#grid-color').value;
    this.exportSettings.gridSize = parseInt(dialog.querySelector('#grid-size').value);

    // Conditions
    this.exportSettings.showConditions = dialog.querySelector('#show-conditions').checked;
    this.exportSettings.showDataGuards = dialog.querySelector('#show-data-guards').checked;
    this.exportSettings.showDataUpdates = dialog.querySelector('#show-data-updates').checked;
    this.exportSettings.conditionPosition = dialog.querySelector('#condition-position').value;
    this.exportSettings.conditionFontSize = parseInt(dialog.querySelector('#condition-font-size').value);
    this.exportSettings.conditionColor = dialog.querySelector('#condition-color').value;
    this.exportSettings.conditionBackground = dialog.querySelector('#condition-background').checked;
    this.exportSettings.conditionBackgroundColor = dialog.querySelector('#condition-background-color').value;
    this.exportSettings.prettyPrintConditions = dialog.querySelector('#pretty-print-conditions').checked;
    this.exportSettings.prettyPrintVariablesItalic = dialog.querySelector('#pretty-print-variables-italic').checked;

    // Advanced
    this.exportSettings.dpiScale = parseFloat(dialog.querySelector('#dpi-scale').value);
    this.exportSettings.antialiasing = dialog.querySelector('#antialiasing').checked;
    this.exportSettings.includeMetadata = dialog.querySelector('#include-metadata').checked;
    
    // Save settings to local storage
    this.saveSettings();
  }

  /**
   * Update dialog inputs from current settings
   */
  updateDialogFromSettings(dialog) {
    // Image settings
    dialog.querySelector('#export-width').value = this.exportSettings.width;
    dialog.querySelector('#export-height').value = this.exportSettings.height;
    dialog.querySelector('#maintain-aspect-ratio').checked = this.exportSettings.maintainAspectRatio;
    dialog.querySelector('#fit-to-content').checked = this.exportSettings.fitToContent;
    dialog.querySelector('#content-padding').value = this.exportSettings.contentPadding;
    dialog.querySelector('#transparency').checked = this.exportSettings.transparency;
    dialog.querySelector('#background-color').value = this.exportSettings.backgroundColor;

    // Update range value displays
    const ranges = dialog.querySelectorAll('input[type="range"]');
    ranges.forEach(range => {
      const event = new Event('input');
      range.dispatchEvent(event);
    });
  }

  /**
   * Update the preview canvas
   */
  updatePreview() {
    if (!this.dialog) return;

    const previewCanvas = this.dialog.querySelector('#png-preview-canvas');
    if (!previewCanvas) return;

    this.previewCanvas = previewCanvas;
    
    // Render the Petri net to the preview canvas with current settings
    this.renderToCanvas(previewCanvas, true);
    
    // Update preview info
    this.updatePreviewInfo();
  }

  /**
   * Update preview information display
   */
  updatePreviewInfo() {
    const previewInfo = this.dialog.querySelector('#preview-info');
    if (!previewInfo) return;

    const dimensionsSpan = previewInfo.querySelector('.preview-dimensions');
    const filesizeSpan = previewInfo.querySelector('.preview-filesize');

    if (dimensionsSpan) {
      dimensionsSpan.textContent = `${this.exportSettings.width} × ${this.exportSettings.height} px`;
    }

    // Estimate file size (very rough approximation)
    const pixels = this.exportSettings.width * this.exportSettings.height;
    const estimatedSize = this.exportSettings.transparency ? 
      Math.round(pixels * 4 / 1024) : // RGBA
      Math.round(pixels * 3 / 1024); // RGB
    
    if (filesizeSpan) {
      if (estimatedSize > 1024) {
        filesizeSpan.textContent = `~${(estimatedSize / 1024).toFixed(1)} MB`;
      } else {
        filesizeSpan.textContent = `~${estimatedSize} KB`;
      }
    }
  }

  /**
   * Fit preview to view
   */
  fitPreviewToView() {
    // Implementation would adjust preview canvas zoom/pan to show all content
    console.log('Fit preview to view');
  }

  /**
   * Render the Petri net to a canvas with current settings
   */
  renderToCanvas(canvas, isPreview = false) {
    const ctx = canvas.getContext('2d');
    const scale = isPreview ? 0.5 : this.exportSettings.dpiScale;
    
    // Clear canvas
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    
    // Set background
    if (!this.exportSettings.transparency) {
      ctx.fillStyle = this.exportSettings.backgroundColor;
      ctx.fillRect(0, 0, canvas.width, canvas.height);
    }

    // Enable/disable antialiasing
    ctx.imageSmoothingEnabled = this.exportSettings.antialiasing;

    // Save the current context state
    ctx.save();

    // Apply scaling for high DPI
    if (!isPreview) {
      ctx.scale(this.exportSettings.dpiScale, this.exportSettings.dpiScale);
    }

    // Create a temporary renderer for export
    const exportRenderer = this.createExportRenderer(canvas, isPreview);
    
    // Apply export settings to renderer theme
    this.applySettingsToRenderer(exportRenderer);
    
    // Adjust view to fit content if requested
    if (this.exportSettings.fitToContent) {
      this.adjustViewToFitContent(exportRenderer, isPreview);
    }
    
    // Render the Petri net
    try {
      this.renderPetriNetElements(exportRenderer, ctx, isPreview);
    } catch (error) {
      console.error('Error rendering Petri net:', error);
    }

    // Restore context state
    ctx.restore();
  }

  /**
   * Create a custom renderer for export
   */
  createExportRenderer(canvas, isPreview = false) {
    // Get the current petri net from the app
    const petriNet = this.app.api.petriNet;
    
    // Create a minimal renderer object with necessary properties
    const exportRenderer = {
      canvas: canvas,
      ctx: canvas.getContext('2d'),
      petriNet: petriNet,
      theme: { ...this.app.editor.renderer.theme },
      panOffset: { x: 0, y: 0 },
      zoomFactor: isPreview ? 0.3 : 1.0
    };
    
    return exportRenderer;
  }

  /**
   * Adjust view to fit all content
   */
  adjustViewToFitContent(renderer, isPreview) {
    const petriNet = renderer.petriNet;
    if (petriNet.places.size === 0 && petriNet.transitions.size === 0) {
      return;
    }

    // Calculate bounding box of all elements
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;

    // Include places
    for (const [id, place] of petriNet.places) {
      const radius = place.radius || 25;
      minX = Math.min(minX, place.position.x - radius);
      minY = Math.min(minY, place.position.y - radius);
      maxX = Math.max(maxX, place.position.x + radius);
      maxY = Math.max(maxY, place.position.y + radius);
    }

    // Include transitions
    for (const [id, transition] of petriNet.transitions) {
      const width = transition.width || 50;
      const height = transition.height || 30;
      minX = Math.min(minX, transition.position.x - width / 2);
      minY = Math.min(minY, transition.position.y - height / 2);
      maxX = Math.max(maxX, transition.position.x + width / 2);
      maxY = Math.max(maxY, transition.position.y + height / 2);
    }

    if (minX === Infinity) return;

    // Add padding
    const padding = this.exportSettings.contentPadding;
    minX -= padding;
    minY -= padding;
    maxX += padding;
    maxY += padding;

    // Calculate content dimensions
    const contentWidth = maxX - minX;
    const contentHeight = maxY - minY;

    // Calculate scale to fit content
    const canvasWidth = isPreview ? renderer.canvas.width : 
                       this.exportSettings.width;
    const canvasHeight = isPreview ? renderer.canvas.height : 
                        this.exportSettings.height;

    const scaleX = canvasWidth / contentWidth;
    const scaleY = canvasHeight / contentHeight;
    const scale = Math.min(scaleX, scaleY);

    // Apply scale and offset
    renderer.zoomFactor = scale;
    renderer.panOffset = {
      x: (canvasWidth - contentWidth * scale) / 2 - minX * scale,
      y: (canvasHeight - contentHeight * scale) / 2 - minY * scale
    };
  }

  /**
   * Render all Petri net elements
   */
  renderPetriNetElements(renderer, ctx, isPreview) {
    // Debug logging
    console.log('Rendering Petri net with:', renderer.petriNet.places.size, 'places,', 
                renderer.petriNet.transitions.size, 'transitions,', 
                renderer.petriNet.arcs.size, 'arcs');

    // Apply transformation
    ctx.save();
    ctx.translate(renderer.panOffset.x, renderer.panOffset.y);
    ctx.scale(renderer.zoomFactor, renderer.zoomFactor);

    // Draw grid if enabled
    if (this.exportSettings.showGrid) {
      this.drawGrid(ctx, renderer);
    }

    // Draw elements in order: arcs, places, transitions
    try {
      if (this.exportSettings.showArcs) {
        this.drawArcs(ctx, renderer);
      }
    } catch (error) {
      console.error('Error drawing arcs, skipping arc rendering:', error);
    }
    
    if (this.exportSettings.showPlaces) {
      this.drawPlaces(ctx, renderer);
    }
    
    if (this.exportSettings.showTransitions) {
      this.drawTransitions(ctx, renderer);
    }

    ctx.restore();
  }

  /**
   * Draw grid
   */
  drawGrid(ctx, renderer) {
    const gridSize = this.exportSettings.gridSize;
    
    // Calculate the visible area in world coordinates
    const canvasWidth = renderer.canvas.width;
    const canvasHeight = renderer.canvas.height;
    const zoom = renderer.zoomFactor;
    const panX = renderer.panOffset.x;
    const panY = renderer.panOffset.y;
    
    // Calculate world coordinates for the visible area
    const worldLeft = -panX / zoom;
    const worldTop = -panY / zoom;
    const worldRight = (canvasWidth - panX) / zoom;
    const worldBottom = (canvasHeight - panY) / zoom;
    
    // Extend the grid area slightly beyond visible bounds
    const margin = gridSize * 2;
    const gridLeft = Math.floor((worldLeft - margin) / gridSize) * gridSize;
    const gridTop = Math.floor((worldTop - margin) / gridSize) * gridSize;
    const gridRight = Math.ceil((worldRight + margin) / gridSize) * gridSize;
    const gridBottom = Math.ceil((worldBottom + margin) / gridSize) * gridSize;
    
    ctx.strokeStyle = this.exportSettings.gridColor;
    ctx.lineWidth = 1 / zoom; // Keep line width consistent regardless of zoom
    ctx.globalAlpha = 0.3;

    // Draw vertical lines
    for (let x = gridLeft; x <= gridRight; x += gridSize) {
      ctx.beginPath();
      ctx.moveTo(x, gridTop);
      ctx.lineTo(x, gridBottom);
      ctx.stroke();
    }

    // Draw horizontal lines
    for (let y = gridTop; y <= gridBottom; y += gridSize) {
      ctx.beginPath();
      ctx.moveTo(gridLeft, y);
      ctx.lineTo(gridRight, y);
      ctx.stroke();
    }

    ctx.globalAlpha = 1.0;
  }

  /**
   * Draw arcs
   */
  drawArcs(ctx, renderer) {
    const petriNet = renderer.petriNet;
    ctx.strokeStyle = this.exportSettings.arcColor;
    ctx.lineWidth = this.exportSettings.lineThickness;

    // Check if arcs exist
    if (!petriNet.arcs || petriNet.arcs.size === 0) {
      console.log('No arcs to draw');
      return;
    }

    for (const [id, arc] of petriNet.arcs) {
      try {
        // Resolve source and target from IDs
        let source = null;
        let target = null;

        // Check different possible properties for source/target IDs
        const sourceId = arc.sourceId || arc.source || arc.from;
        const targetId = arc.targetId || arc.target || arc.to;

        // Try to find source in places or transitions
        if (sourceId && petriNet.places.has(sourceId)) {
          source = petriNet.places.get(sourceId);
        } else if (sourceId && petriNet.transitions.has(sourceId)) {
          source = petriNet.transitions.get(sourceId);
        }

        // Try to find target in places or transitions
        if (targetId && petriNet.places.has(targetId)) {
          target = petriNet.places.get(targetId);
        } else if (targetId && petriNet.transitions.has(targetId)) {
          target = petriNet.transitions.get(targetId);
        }

        // If we still don't have source/target, try direct object references
        if (!source && arc.source && typeof arc.source === 'object' && arc.source.position) {
          source = arc.source;
        }
        if (!target && arc.target && typeof arc.target === 'object' && arc.target.position) {
          target = arc.target;
        }

        if (!source || !target || !source.position || !target.position) {
          console.warn('Skipping arc with invalid source/target:', id);
          continue;
        }

        // Calculate connection points (edge of shapes rather than centers)
        const connectionPoints = this.calculateConnectionPoints(source, target);

        ctx.beginPath();
        ctx.moveTo(connectionPoints.start.x, connectionPoints.start.y);
        ctx.lineTo(connectionPoints.end.x, connectionPoints.end.y);
        ctx.stroke();

        // Draw arrowhead
        this.drawArrowhead(ctx, connectionPoints.start, connectionPoints.end);

        // Draw weight if > 1
        if (arc.weight > 1 && this.exportSettings.showLabels) {
          this.drawArcWeight(ctx, arc, connectionPoints);
        }
      } catch (error) {
        console.error('Error drawing individual arc:', id, error);
      }
    }
  }

  /**
   * Calculate connection points on the edge of shapes rather than centers
   */
  calculateConnectionPoints(source, target) {
    const dx = target.position.x - source.position.x;
    const dy = target.position.y - source.position.y;
    const distance = Math.sqrt(dx * dx + dy * dy);
    
    if (distance === 0) {
      return {
        start: { x: source.position.x, y: source.position.y },
        end: { x: target.position.x, y: target.position.y }
      };
    }

    const unitX = dx / distance;
    const unitY = dy / distance;

    // Calculate offset based on shape type and size
    let sourceOffset = 0;
    let targetOffset = 0;

    // Source offset
    if (source.radius !== undefined) {
      // It's a place (circle)
      sourceOffset = source.radius;
    } else if (source.width !== undefined) {
      // It's a transition (rectangle) - approximate as circle for simplicity
      sourceOffset = Math.min(source.width, source.height) / 2;
    }

    // Target offset  
    if (target.radius !== undefined) {
      // It's a place (circle)
      targetOffset = target.radius;
    } else if (target.width !== undefined) {
      // It's a transition (rectangle) - approximate as circle for simplicity
      targetOffset = Math.min(target.width, target.height) / 2;
    }

    return {
      start: {
        x: source.position.x + unitX * sourceOffset,
        y: source.position.y + unitY * sourceOffset
      },
      end: {
        x: target.position.x - unitX * targetOffset,
        y: target.position.y - unitY * targetOffset
      }
    };
  }

  /**
   * Draw arrowhead
   */
  drawArrowhead(ctx, from, to) {
    const headSize = 10;
    const angle = Math.atan2(to.y - from.y, to.x - from.x);
    
    ctx.save();
    ctx.translate(to.x, to.y);
    ctx.rotate(angle);
    
    ctx.beginPath();
    ctx.moveTo(0, 0);
    ctx.lineTo(-headSize, -headSize / 2);
    ctx.lineTo(-headSize, headSize / 2);
    ctx.closePath();
    ctx.fillStyle = this.exportSettings.arcColor;
    ctx.fill();
    
    ctx.restore();
  }

  /**
   * Draw arc weight
   */
  drawArcWeight(ctx, arc, connectionPoints) {
    const midX = (connectionPoints.start.x + connectionPoints.end.x) / 2;
    const midY = (connectionPoints.start.y + connectionPoints.end.y) / 2;
    
    ctx.fillStyle = this.exportSettings.textColor;
    ctx.font = `${this.exportSettings.fontSize}px ${this.exportSettings.fontFamily}`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(arc.weight.toString(), midX, midY);
  }

  /**
   * Draw places
   */
  drawPlaces(ctx, renderer) {
    const petriNet = renderer.petriNet;

    for (const [id, place] of petriNet.places) {
      const radius = place.radius || 25;
      
      // Draw place circle
      ctx.beginPath();
      ctx.arc(place.position.x, place.position.y, radius, 0, Math.PI * 2);
      ctx.fillStyle = this.exportSettings.placeColor;
      ctx.fill();
      ctx.strokeStyle = this.exportSettings.placeStroke;
      ctx.lineWidth = this.exportSettings.lineThickness;
      ctx.stroke();

      // Draw tokens if enabled
      if (this.exportSettings.showTokens) {
        this.drawTokens(ctx, place);
      }

      // Draw label if enabled
      if (this.exportSettings.showLabels && place.label) {
        this.drawPlaceLabel(ctx, place);
      }
    }
  }

  /**
   * Draw tokens in a place
   */
  drawTokens(ctx, place) {
    const tokens = place.tokens || 0;
    if (tokens === 0) return;

    ctx.fillStyle = this.exportSettings.tokenColor;
    const tokenRadius = 3;
    const radius = place.radius || 25;

    if (tokens === 1) {
      // Single token in center
      ctx.beginPath();
      ctx.arc(place.position.x, place.position.y, tokenRadius, 0, Math.PI * 2);
      ctx.fill();
    } else if (tokens <= 4) {
      // Multiple tokens arranged in pattern
      const positions = this.getTokenPositions(tokens, radius * 0.6);
      positions.forEach(pos => {
        ctx.beginPath();
        ctx.arc(place.position.x + pos.x, place.position.y + pos.y, tokenRadius, 0, Math.PI * 2);
        ctx.fill();
      });
    } else {
      // Show number for many tokens
      ctx.fillStyle = this.exportSettings.textColor;
      ctx.font = `${this.exportSettings.fontSize}px ${this.exportSettings.fontFamily}`;
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(tokens.toString(), place.position.x, place.position.y);
    }
  }

  /**
   * Get token positions for multiple tokens
   */
  getTokenPositions(count, radius) {
    const positions = [];
    for (let i = 0; i < count; i++) {
      const angle = (i * 2 * Math.PI) / count;
      positions.push({
        x: Math.cos(angle) * radius,
        y: Math.sin(angle) * radius
      });
    }
    return positions;
  }

  /**
   * Draw place label
   */
  drawPlaceLabel(ctx, place) {
    ctx.fillStyle = this.exportSettings.textColor;
    ctx.font = `${this.exportSettings.fontSize}px ${this.exportSettings.fontFamily}`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    
    const y = place.position.y + (place.radius || 25) + 5;
    ctx.fillText(place.label, place.position.x, y);
  }

  /**
   * Draw transitions
   */
  drawTransitions(ctx, renderer) {
    const petriNet = renderer.petriNet;

    for (const [id, transition] of petriNet.transitions) {
      const width = transition.width || 50;
      const height = transition.height || 30;
      const x = transition.position.x - width / 2;
      const y = transition.position.y - height / 2;

      // Determine if this is a data transition
      const isDataTransition = typeof transition.evaluatePrecondition === 'function';
      
      // Choose colors based on transition type and state
      let fillColor, strokeColor;
      
      // Silent transitions are always grey
      if (transition.silent) {
        fillColor = '#808080';
        strokeColor = this.exportSettings.transitionStroke;
      } else if (isDataTransition) {
        if (transition.isEnabled) {
          fillColor = this.exportSettings.enabledDataTransitionColor;
        } else {
          fillColor = this.exportSettings.disabledDataTransitionColor;
        }
        strokeColor = this.exportSettings.dataTransitionStroke;
      } else {
        if (transition.isEnabled && this.exportSettings.highlightFirableTransitions) {
          fillColor = this.exportSettings.enabledTransitionColor;
        } else {
          fillColor = this.exportSettings.transitionColor;
        }
        strokeColor = this.exportSettings.transitionStroke;
      }

      // Draw transition rectangle
      ctx.beginPath();
      ctx.rect(x, y, width, height);
      ctx.fillStyle = fillColor;
      ctx.fill();
      ctx.strokeStyle = strokeColor;
      ctx.lineWidth = this.exportSettings.lineThickness;
      ctx.stroke();

      // Draw label if enabled and not a silent transition
      if (this.exportSettings.showLabels && transition.label && !transition.silent) {
        this.drawTransitionLabel(ctx, transition);
      }

      // Draw conditions if enabled, this is a data transition, and not silent
      if (isDataTransition && this.exportSettings.showConditions && !transition.silent) {
        this.drawTransitionConditions(ctx, transition);
      }
    }
  }

  /**
   * Draw transition label
   */
  drawTransitionLabel(ctx, transition) {
    ctx.fillStyle = this.exportSettings.textColor;
    ctx.font = `${this.exportSettings.fontSize}px ${this.exportSettings.fontFamily}`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    
    const y = transition.position.y + (transition.height || 30) / 2 + 5;
    ctx.fillText(transition.label, transition.position.x, y);
  }

  /**
   * Prettify mathematical expressions by replacing operators with Unicode symbols
   * and identifying variables for italic formatting.
   * Based on supported operators from z3-expression-evaluation.js
   * @param {string} expression - The mathematical expression to prettify
   * @returns {Array<{text: string, isVariable: boolean}>} Array of text segments with formatting info
   */
  prettifyExpression(expression) {
    if (!this.exportSettings.prettyPrintConditions) {
      return [{ text: expression, isVariable: false }];
    }

    // Operator mapping to Unicode symbols (based on z3-expression-evaluation.js operators)
    const operatorMap = {
      '>=': '≥',
      '<=': '≤',
      '==': '=',
      '!=': '≠',
      '&&': '∧',
      '||': '∨',
      '!': '¬',
      '*': '×',
      // Keep these as-is for now
      // '+': '+',
      // '-': '-',
      // '/': '÷',  // Could use ÷ but / is often clearer
    };

    let prettified = expression;
    
    // Replace operators (order matters - longer operators first)
    for (const [plain, pretty] of Object.entries(operatorMap)) {
      prettified = prettified.replace(new RegExp(plain.replace(/[.*+?^${}()|[\]\\]/g, '\\$&'), 'g'), pretty);
    }

    // Parse into segments: variables vs non-variables
    // Variables are identified as: letter/underscore followed by letters/digits/underscores
    // Also handle primed variables (e.g., x')
    const segments = [];
    const regex = /([A-Za-z_]\w*'?)|([^A-Za-z_]+)/g;
    let match;
    
    while ((match = regex.exec(prettified)) !== null) {
      if (match[1]) {
        // This is a variable
        segments.push({ text: match[1], isVariable: true });
      } else if (match[2]) {
        // This is not a variable (operators, numbers, spaces, etc.)
        segments.push({ text: match[2], isVariable: false });
      }
    }

    return segments.length > 0 ? segments : [{ text: prettified, isVariable: false }];
  }

  /**
   * Draw text with mixed regular and italic segments
   * @param {CanvasRenderingContext2D} ctx - Canvas context
   * @param {Array<{text: string, isVariable: boolean}>} segments - Text segments with formatting
   * @param {number} x - X position (center)
   * @param {number} y - Y position (middle)
   * @param {string} baseFont - Base font size and family (e.g., "10px Arial")
   */
  drawMixedText(ctx, segments, x, y, baseFont) {
    // Calculate total width for centering
    let totalWidth = 0;
    const fontParts = baseFont.split(' ');
    const fontSize = fontParts[0];
    const fontFamily = fontParts.slice(1).join(' ');

    segments.forEach(seg => {
      if (seg.isVariable && this.exportSettings.prettyPrintVariablesItalic) {
        ctx.font = `italic ${fontSize} ${fontFamily}`;
      } else {
        ctx.font = baseFont;
      }
      totalWidth += ctx.measureText(seg.text).width;
    });

    // Start drawing from left edge (centered)
    let currentX = x - totalWidth / 2;
    
    segments.forEach(seg => {
      if (seg.isVariable && this.exportSettings.prettyPrintVariablesItalic) {
        ctx.font = `italic ${fontSize} ${fontFamily}`;
      } else {
        ctx.font = baseFont;
      }
      
      ctx.fillText(seg.text, currentX, y);
      currentX += ctx.measureText(seg.text).width;
    });
  }

  /**
   * Draw transition conditions (guards and updates)
   */
  drawTransitionConditions(ctx, transition) {
    if (!this.exportSettings.showConditions) return;

    const conditions = [];
    
    // Add precondition (guard)
    if (this.exportSettings.showDataGuards && transition.precondition) {
      conditions.push({ expr: transition.precondition, prefix: '[', suffix: ']' });
    }
    
    // Add postcondition (update)
    if (this.exportSettings.showDataUpdates && transition.postcondition) {
      conditions.push({ expr: transition.postcondition, prefix: '{', suffix: '}' });
    }

    if (conditions.length === 0) return;

    // Set font and style for conditions
    const baseFont = `${this.exportSettings.conditionFontSize}px ${this.exportSettings.fontFamily}`;
    ctx.font = baseFont;
    ctx.fillStyle = this.exportSettings.conditionColor;
    ctx.textAlign = 'left'; // Changed to left since drawMixedText handles centering
    ctx.textBaseline = 'middle';

    // Calculate position based on setting
    const position = this.getConditionPosition(transition);
    
    conditions.forEach((condition, index) => {
      const x = position.x;
      const y = position.y + (index * (this.exportSettings.conditionFontSize + 4));
      
      // Prettify the expression
      const segments = this.prettifyExpression(condition.expr);
      
      // Add prefix and suffix as non-variable segments
      const fullSegments = [
        { text: condition.prefix, isVariable: false },
        ...segments,
        { text: condition.suffix, isVariable: false }
      ];
      
      // Draw background if enabled
      if (this.exportSettings.conditionBackground) {
        // Calculate total width for background
        let totalWidth = 0;
        const fontParts = baseFont.split(' ');
        const fontSize = fontParts[0];
        const fontFamily = fontParts.slice(1).join(' ');
        
        fullSegments.forEach(seg => {
          if (seg.isVariable && this.exportSettings.prettyPrintVariablesItalic) {
            ctx.font = `italic ${fontSize} ${fontFamily}`;
          } else {
            ctx.font = baseFont;
          }
          totalWidth += ctx.measureText(seg.text).width;
        });
        
        const textHeight = this.exportSettings.conditionFontSize;
        
        ctx.fillStyle = this.exportSettings.conditionBackgroundColor;
        ctx.fillRect(x - totalWidth / 2 - 2, y - textHeight / 2 - 1, 
                    totalWidth + 4, textHeight + 2);
        ctx.fillStyle = this.exportSettings.conditionColor;
      }
      
      // Draw the mixed text (with potential italic variables)
      this.drawMixedText(ctx, fullSegments, x, y, baseFont);
    });
    
    // Reset font to base
    ctx.font = baseFont;
  }

  /**
   * Get position for condition text
   */
  getConditionPosition(transition) {
    const width = transition.width || 50;
    const height = transition.height || 30;
    const x = transition.position.x;
    const y = transition.position.y;

    switch (this.exportSettings.conditionPosition) {
      case 'top':
        return { x: x, y: y - height / 2 - 15 };
      case 'bottom':
        return { x: x, y: y + height / 2 + 15 };
      case 'left':
        return { x: x - width / 2 - 30, y: y };
      case 'right':
        return { x: x + width / 2 + 30, y: y };
      case 'auto':
      default:
        // Place below transition by default
        return { x: x, y: y + height / 2 + 15 };
    }
  }

  /**
   * Apply export settings to renderer theme
   */
  applySettingsToRenderer(renderer) {
    const theme = renderer.theme;
    
    // Apply color settings
    theme.placeColor = this.exportSettings.placeColor;
    theme.placeStroke = this.exportSettings.placeStroke;
    theme.tokenColor = this.exportSettings.tokenColor;
    theme.transitionColor = this.exportSettings.transitionColor;
    theme.transitionStroke = this.exportSettings.transitionStroke;
    theme.enabledTransitionColor = this.exportSettings.enabledTransitionColor;
    theme.arcColor = this.exportSettings.arcColor;
    theme.textColor = this.exportSettings.textColor;
    theme.backgroundColor = this.exportSettings.backgroundColor;
    
    // Apply data transition colors if using DPN renderer
    if (this.exportSettings.dataTransitionColor) {
      theme.dataTransitionColor = this.exportSettings.dataTransitionColor;
      theme.dataTransitionStroke = this.exportSettings.dataTransitionStroke;
      theme.enabledDataTransitionColor = this.exportSettings.enabledDataTransitionColor;
      theme.disabledDataTransitionColor = this.exportSettings.disabledDataTransitionColor;
    }
  }

  /**
   * Export the Petri net as PNG
   */
  exportPNG() {
    try {
      // Create export canvas with actual export dimensions
      const exportCanvas = document.createElement('canvas');
      exportCanvas.width = this.exportSettings.width * this.exportSettings.dpiScale;
      exportCanvas.height = this.exportSettings.height * this.exportSettings.dpiScale;
      
      // Render to export canvas
      this.renderToCanvas(exportCanvas, false);
      
      // Convert to blob and download
      exportCanvas.toBlob((blob) => {
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        a.download = `petri-net-${new Date().toISOString().slice(0, 19).replace(/:/g, '-')}.png`;
        a.click();
        URL.revokeObjectURL(url);
        
        // Close dialog
        document.body.removeChild(this.dialog);
        this.dialog = null;
      }, 'image/png');
      
    } catch (error) {
      console.error('Error exporting PNG:', error);
      alert('Error exporting PNG. Please try again.');
    }
  }
}

// Initialize when DOM is ready
document.addEventListener('DOMContentLoaded', () => {
  const initTimer = setInterval(() => {
    if (window.petriApp) {
      window.pngExporter = new PNGExporter(window.petriApp);
      clearInterval(initTimer);
      console.log("PNG Exporter extension loaded");
    }
  }, 100);
});

export { PNGExporter };