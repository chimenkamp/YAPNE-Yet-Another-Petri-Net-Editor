/**
 * TikZ Exporter for Petri Net Editor
 * Generates LaTeX/TikZ for normal Petri nets and Data Petri Nets.
 */

class TikZExporter {
  constructor(app, options = {}) {
    this.app = app;
    this.dialog = null;
    this.localStorageKey = 'tikzExporterSettings';
    this.exportSettings = this.loadSettings();

    if (options.initializeUI !== false) {
      this.initializeUI();
    }
  }

  getDefaultSettings() {
    return {
      outputMode: 'standalone',
      figureCaption: 'Petri net',
      coordinateMode: 'normalized',
      coordinateScale: 0.025,
      coordinatePrecision: 2,
      contentPadding: 50,

      includeComments: true,
      includeColorDefinitions: true,
      includeBackground: false,
      backgroundColor: '#ffffff',

      showPlaces: true,
      showTransitions: true,
      showArcs: true,
      showLabels: true,
      showTokens: true,
      showArcWeights: true,
      showArcTypes: true,
      highlightFirableTransitions: false,

      showDataAnnotations: true,
      showDataGuards: true,
      showDataUpdates: true,
      showDataVariables: true,
      conditionsAsMath: true,
      conditionPosition: 'auto',

      placeColor: '#ffffff',
      placeStroke: '#000000',
      transitionColor: '#d3d3d3',
      transitionStroke: '#000000',
      enabledTransitionColor: '#90ee90',
      silentTransitionColor: '#808080',
      arcColor: '#000000',
      textColor: '#000000',
      tokenColor: '#000000',
      dataTransitionColor: '#8FBCBB',
      dataTransitionStroke: '#5E81AC',
      enabledDataTransitionColor: '#A3BE8C',
      disabledDataTransitionColor: '#D08770',
      conditionColor: '#444444',
      conditionBackground: true,
      conditionBackgroundColor: '#f0f0f0',

      lineWidth: 0.45,
      fontSize: 10,
      conditionFontSize: 8,
      tokenRadius: 0.075,
      labelOffset: 0.12,
      conditionOffset: 0.22
    };
  }

  loadSettings() {
    const defaults = this.getDefaultSettings();

    if (typeof localStorage === 'undefined') {
      return defaults;
    }

    try {
      const savedSettings = localStorage.getItem(this.localStorageKey);
      if (!savedSettings) return defaults;
      return { ...defaults, ...JSON.parse(savedSettings) };
    } catch (error) {
      console.warn('Failed to load TikZ exporter settings from local storage:', error);
      return defaults;
    }
  }

  saveSettings() {
    if (typeof localStorage === 'undefined') return;

    try {
      localStorage.setItem(this.localStorageKey, JSON.stringify(this.exportSettings));
    } catch (error) {
      console.error('Failed to save TikZ exporter settings to local storage:', error);
    }
  }

  initializeUI() {
    this.addExportButton();
  }

  addExportButton() {
    const fileOperationsSection = document.querySelector('#file-operations-section .section-content');
    if (!fileOperationsSection || fileOperationsSection.querySelector('#btn-export-tikz')) return;

    const tikzButtonGroup = document.createElement('div');
    tikzButtonGroup.className = 'button-group';
    tikzButtonGroup.id = 'tikz-button-group';

    const exportButton = document.createElement('button');
    exportButton.id = 'btn-export-tikz';
    exportButton.textContent = 'Save (TikZ)';
    exportButton.style.backgroundColor = 'rgb(101, 127, 152)';
    exportButton.addEventListener('click', () => this.showExportDialog());

    tikzButtonGroup.appendChild(exportButton);
    fileOperationsSection.appendChild(tikzButtonGroup);
  }

  showExportDialog() {
    this.closeDialog();
    this.dialog = this.createExportDialog();
    document.body.appendChild(this.dialog);
    this.updatePreview();

    setTimeout(() => {
      const firstInput = this.dialog.querySelector('select, input, textarea, button');
      if (firstInput) firstInput.focus();
    }, 100);
  }

  createExportDialog() {
    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay';
    dialog.id = 'tikz-export-dialog';

    dialog.innerHTML = `
      <div class="modal-container tikz-export-container">
        <div class="modal-header">
          <h2 id="tikz-dialog-title">Export as TikZ</h2>
          <button class="close-btn" aria-label="Close TikZ export dialog">&times;</button>
        </div>
        <div class="modal-body">
          <div class="tikz-export-content">
            <div class="form-tab-container">
              <div class="form-tabs">
                <button class="form-tab active" data-tab="document">Document</button>
                <button class="form-tab" data-tab="layout">Layout</button>
                <button class="form-tab" data-tab="elements">Elements</button>
                <button class="form-tab" data-tab="data">Data</button>
                <button class="form-tab" data-tab="appearance">Appearance</button>
                <button class="form-tab" data-tab="preview">Preview</button>
              </div>

              <div class="form-tab-content active" data-tab="document">
                <h3>Document Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Output</h4>
                    <div class="setting-item">
                      <label for="tikz-output-mode">Output mode:</label>
                      <select id="tikz-output-mode">
                        <option value="standalone" ${this.exportSettings.outputMode === 'standalone' ? 'selected' : ''}>Standalone LaTeX document</option>
                        <option value="figure" ${this.exportSettings.outputMode === 'figure' ? 'selected' : ''}>Figure environment</option>
                        <option value="tikzpicture" ${this.exportSettings.outputMode === 'tikzpicture' ? 'selected' : ''}>TikZ picture only</option>
                      </select>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-caption">Figure caption:</label>
                      <input type="text" id="tikz-caption" value="${this.escapeHTML(this.exportSettings.figureCaption)}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-include-comments">
                        <input type="checkbox" id="tikz-include-comments" ${this.exportSettings.includeComments ? 'checked' : ''}>
                        Include generator comments
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Definitions</h4>
                    <div class="setting-item">
                      <label for="tikz-include-colors">
                        <input type="checkbox" id="tikz-include-colors" ${this.exportSettings.includeColorDefinitions ? 'checked' : ''}>
                        Include color definitions
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-include-background">
                        <input type="checkbox" id="tikz-include-background" ${this.exportSettings.includeBackground ? 'checked' : ''}>
                        Draw background rectangle
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-background-color">Background color:</label>
                      <input type="color" id="tikz-background-color" value="${this.exportSettings.backgroundColor}">
                    </div>
                  </div>
                </div>
              </div>

              <div class="form-tab-content" data-tab="layout">
                <h3>Layout Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Coordinates</h4>
                    <div class="setting-item">
                      <label for="tikz-coordinate-mode">Coordinate mode:</label>
                      <select id="tikz-coordinate-mode">
                        <option value="normalized" ${this.exportSettings.coordinateMode === 'normalized' ? 'selected' : ''}>Normalize to content</option>
                        <option value="canvas" ${this.exportSettings.coordinateMode === 'canvas' ? 'selected' : ''}>Preserve canvas coordinates</option>
                      </select>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-coordinate-scale">Coordinate scale:</label>
                      <input type="number" id="tikz-coordinate-scale" min="0.005" max="0.2" step="0.005" value="${this.exportSettings.coordinateScale}">
                      <small>Canvas pixels converted to TikZ centimeters.</small>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-coordinate-precision">Coordinate precision:</label>
                      <input type="range" id="tikz-coordinate-precision" min="0" max="4" step="1" value="${this.exportSettings.coordinatePrecision}">
                      <span class="range-value">${this.exportSettings.coordinatePrecision} decimals</span>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-content-padding">Content padding (px):</label>
                      <input type="range" id="tikz-content-padding" min="0" max="200" value="${this.exportSettings.contentPadding}">
                      <span class="range-value">${this.exportSettings.contentPadding}px</span>
                    </div>
                  </div>
                </div>
              </div>

              <div class="form-tab-content" data-tab="elements">
                <h3>Element Visibility</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Petri Net Elements</h4>
                    <div class="setting-item">
                      <label for="tikz-show-places">
                        <input type="checkbox" id="tikz-show-places" ${this.exportSettings.showPlaces ? 'checked' : ''}>
                        Show places
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-transitions">
                        <input type="checkbox" id="tikz-show-transitions" ${this.exportSettings.showTransitions ? 'checked' : ''}>
                        Show transitions
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-arcs">
                        <input type="checkbox" id="tikz-show-arcs" ${this.exportSettings.showArcs ? 'checked' : ''}>
                        Show arcs
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-labels">
                        <input type="checkbox" id="tikz-show-labels" ${this.exportSettings.showLabels ? 'checked' : ''}>
                        Show labels
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Markings and Arcs</h4>
                    <div class="setting-item">
                      <label for="tikz-show-tokens">
                        <input type="checkbox" id="tikz-show-tokens" ${this.exportSettings.showTokens ? 'checked' : ''}>
                        Show tokens
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-arc-weights">
                        <input type="checkbox" id="tikz-show-arc-weights" ${this.exportSettings.showArcWeights ? 'checked' : ''}>
                        Show arc weights
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-arc-types">
                        <input type="checkbox" id="tikz-show-arc-types" ${this.exportSettings.showArcTypes ? 'checked' : ''}>
                        Use special arc styles
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-highlight-firable">
                        <input type="checkbox" id="tikz-highlight-firable" ${this.exportSettings.highlightFirableTransitions ? 'checked' : ''}>
                        Highlight firable transitions
                      </label>
                    </div>
                  </div>
                </div>
              </div>

              <div class="form-tab-content" data-tab="data">
                <h3>Data Petri Net Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Annotations</h4>
                    <div class="setting-item">
                      <label for="tikz-show-data-annotations">
                        <input type="checkbox" id="tikz-show-data-annotations" ${this.exportSettings.showDataAnnotations ? 'checked' : ''}>
                        Show data annotations
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-data-guards">
                        <input type="checkbox" id="tikz-show-data-guards" ${this.exportSettings.showDataGuards ? 'checked' : ''}>
                        Show guards
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-data-updates">
                        <input type="checkbox" id="tikz-show-data-updates" ${this.exportSettings.showDataUpdates ? 'checked' : ''}>
                        Show updates
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-show-data-variables">
                        <input type="checkbox" id="tikz-show-data-variables" ${this.exportSettings.showDataVariables ? 'checked' : ''}>
                        Show data variables
                      </label>
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Formatting</h4>
                    <div class="setting-item">
                      <label for="tikz-conditions-as-math">
                        <input type="checkbox" id="tikz-conditions-as-math" ${this.exportSettings.conditionsAsMath ? 'checked' : ''}>
                        Render guards and updates as math
                      </label>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-condition-position">Condition position:</label>
                      <select id="tikz-condition-position">
                        <option value="auto" ${this.exportSettings.conditionPosition === 'auto' ? 'selected' : ''}>Auto</option>
                        <option value="top" ${this.exportSettings.conditionPosition === 'top' ? 'selected' : ''}>Top</option>
                        <option value="bottom" ${this.exportSettings.conditionPosition === 'bottom' ? 'selected' : ''}>Bottom</option>
                        <option value="left" ${this.exportSettings.conditionPosition === 'left' ? 'selected' : ''}>Left</option>
                        <option value="right" ${this.exportSettings.conditionPosition === 'right' ? 'selected' : ''}>Right</option>
                      </select>
                    </div>
                    <div class="setting-item">
                      <label for="tikz-condition-font-size">Condition font size:</label>
                      <input type="range" id="tikz-condition-font-size" min="6" max="14" step="1" value="${this.exportSettings.conditionFontSize}">
                      <span class="range-value">${this.exportSettings.conditionFontSize}pt</span>
                    </div>
                  </div>
                </div>
              </div>

              <div class="form-tab-content" data-tab="appearance">
                <h3>Appearance Settings</h3>
                <div class="settings-grid">
                  <div class="setting-group">
                    <h4>Basic Colors</h4>
                    <div class="setting-item">
                      <label for="tikz-place-color">Place fill:</label>
                      <input type="color" id="tikz-place-color" value="${this.exportSettings.placeColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-place-stroke">Place stroke:</label>
                      <input type="color" id="tikz-place-stroke" value="${this.exportSettings.placeStroke}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-transition-color">Transition fill:</label>
                      <input type="color" id="tikz-transition-color" value="${this.exportSettings.transitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-transition-stroke">Transition stroke:</label>
                      <input type="color" id="tikz-transition-stroke" value="${this.exportSettings.transitionStroke}">
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Data Colors</h4>
                    <div class="setting-item">
                      <label for="tikz-data-transition-color">Data transition:</label>
                      <input type="color" id="tikz-data-transition-color" value="${this.exportSettings.dataTransitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-data-transition-stroke">Data transition stroke:</label>
                      <input type="color" id="tikz-data-transition-stroke" value="${this.exportSettings.dataTransitionStroke}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-enabled-data-transition-color">Enabled data transition:</label>
                      <input type="color" id="tikz-enabled-data-transition-color" value="${this.exportSettings.enabledDataTransitionColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-disabled-data-transition-color">Disabled data transition:</label>
                      <input type="color" id="tikz-disabled-data-transition-color" value="${this.exportSettings.disabledDataTransitionColor}">
                    </div>
                  </div>

                  <div class="setting-group">
                    <h4>Text and Lines</h4>
                    <div class="setting-item">
                      <label for="tikz-arc-color">Arc color:</label>
                      <input type="color" id="tikz-arc-color" value="${this.exportSettings.arcColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-text-color">Text color:</label>
                      <input type="color" id="tikz-text-color" value="${this.exportSettings.textColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-token-color">Token color:</label>
                      <input type="color" id="tikz-token-color" value="${this.exportSettings.tokenColor}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-line-width">Line width:</label>
                      <input type="number" id="tikz-line-width" min="0.1" max="3" step="0.05" value="${this.exportSettings.lineWidth}">
                    </div>
                    <div class="setting-item">
                      <label for="tikz-font-size">Font size:</label>
                      <input type="range" id="tikz-font-size" min="6" max="18" step="1" value="${this.exportSettings.fontSize}">
                      <span class="range-value">${this.exportSettings.fontSize}pt</span>
                    </div>
                  </div>
                </div>
              </div>

              <div class="form-tab-content" data-tab="preview">
                <h3>TikZ Preview</h3>
                <div class="tikz-preview-summary" id="tikz-preview-summary"></div>
                <textarea id="tikz-preview-source" readonly spellcheck="false"></textarea>
                <div class="tikz-preview-actions">
                  <button type="button" id="refresh-tikz-preview">Refresh Preview</button>
                  <button type="button" id="copy-tikz-btn">Copy TikZ</button>
                </div>
              </div>
            </div>
          </div>
        </div>
        <div class="modal-footer">
          <button type="button" id="export-tikz-btn">Export TikZ</button>
          <button type="button" id="reset-tikz-settings">Reset</button>
          <button type="button" id="cancel-tikz-btn">Cancel</button>
        </div>
      </div>
    `;

    this.setupDialogEventListeners(dialog);
    return dialog;
  }

  setupDialogEventListeners(dialog) {
    const close = () => this.closeDialog();
    dialog.querySelector('.close-btn')?.addEventListener('click', close);
    dialog.querySelector('#cancel-tikz-btn')?.addEventListener('click', close);
    dialog.addEventListener('click', event => {
      if (event.target === dialog) close();
    });

    dialog.querySelectorAll('.form-tab').forEach(tab => {
      tab.addEventListener('click', () => this.switchTab(tab.dataset.tab));
    });

    this.setupRangeInputs(dialog);
    this.setupSettingListeners(dialog);

    dialog.querySelector('#refresh-tikz-preview')?.addEventListener('click', () => this.updatePreview());
    dialog.querySelector('#copy-tikz-btn')?.addEventListener('click', () => this.copyTikZ());
    dialog.querySelector('#export-tikz-btn')?.addEventListener('click', () => this.exportTikZ());
    dialog.querySelector('#reset-tikz-settings')?.addEventListener('click', () => {
      this.exportSettings = this.getDefaultSettings();
      this.saveSettings();
      this.updateDialogFromSettings(dialog);
      this.updatePreview();
    });
  }

  setupRangeInputs(dialog) {
    dialog.querySelectorAll('input[type="range"]').forEach(range => {
      const valueSpan = range.nextElementSibling;
      if (!valueSpan || !valueSpan.classList.contains('range-value')) return;

      range.addEventListener('input', () => {
        if (range.id === 'tikz-coordinate-precision') {
          valueSpan.textContent = `${range.value} decimals`;
        } else if (range.id === 'tikz-content-padding') {
          valueSpan.textContent = `${range.value}px`;
        } else {
          valueSpan.textContent = `${range.value}pt`;
        }
      });
    });
  }

  setupSettingListeners(dialog) {
    dialog.querySelectorAll('input, select').forEach(input => {
      const eventName = input.type === 'range' ? 'input' : 'change';
      input.addEventListener(eventName, () => {
        this.updateSettingsFromDialog(dialog);
        this.updatePreview();
      });
    });
  }

  switchTab(tabId) {
    if (!this.dialog) return;

    this.dialog.querySelectorAll('.form-tab').forEach(button => {
      button.classList.toggle('active', button.dataset.tab === tabId);
    });

    this.dialog.querySelectorAll('.form-tab-content').forEach(content => {
      content.classList.toggle('active', content.dataset.tab === tabId);
    });

    if (tabId === 'preview') {
      this.updatePreview();
    }
  }

  updateSettingsFromDialog(dialog) {
    const value = selector => dialog.querySelector(selector)?.value;
    const checked = selector => Boolean(dialog.querySelector(selector)?.checked);

    this.exportSettings.outputMode = value('#tikz-output-mode') || 'standalone';
    this.exportSettings.figureCaption = value('#tikz-caption') || '';
    this.exportSettings.includeComments = checked('#tikz-include-comments');
    this.exportSettings.includeColorDefinitions = checked('#tikz-include-colors');
    this.exportSettings.includeBackground = checked('#tikz-include-background');
    this.exportSettings.backgroundColor = value('#tikz-background-color') || '#ffffff';

    this.exportSettings.coordinateMode = value('#tikz-coordinate-mode') || 'normalized';
    this.exportSettings.coordinateScale = this.parseNumber(value('#tikz-coordinate-scale'), 0.025);
    this.exportSettings.coordinatePrecision = this.parseInteger(value('#tikz-coordinate-precision'), 2);
    this.exportSettings.contentPadding = this.parseInteger(value('#tikz-content-padding'), 50);

    this.exportSettings.showPlaces = checked('#tikz-show-places');
    this.exportSettings.showTransitions = checked('#tikz-show-transitions');
    this.exportSettings.showArcs = checked('#tikz-show-arcs');
    this.exportSettings.showLabels = checked('#tikz-show-labels');
    this.exportSettings.showTokens = checked('#tikz-show-tokens');
    this.exportSettings.showArcWeights = checked('#tikz-show-arc-weights');
    this.exportSettings.showArcTypes = checked('#tikz-show-arc-types');
    this.exportSettings.highlightFirableTransitions = checked('#tikz-highlight-firable');

    this.exportSettings.showDataAnnotations = checked('#tikz-show-data-annotations');
    this.exportSettings.showDataGuards = checked('#tikz-show-data-guards');
    this.exportSettings.showDataUpdates = checked('#tikz-show-data-updates');
    this.exportSettings.showDataVariables = checked('#tikz-show-data-variables');
    this.exportSettings.conditionsAsMath = checked('#tikz-conditions-as-math');
    this.exportSettings.conditionPosition = value('#tikz-condition-position') || 'auto';
    this.exportSettings.conditionFontSize = this.parseInteger(value('#tikz-condition-font-size'), 8);

    this.exportSettings.placeColor = value('#tikz-place-color') || '#ffffff';
    this.exportSettings.placeStroke = value('#tikz-place-stroke') || '#000000';
    this.exportSettings.transitionColor = value('#tikz-transition-color') || '#d3d3d3';
    this.exportSettings.transitionStroke = value('#tikz-transition-stroke') || '#000000';
    this.exportSettings.dataTransitionColor = value('#tikz-data-transition-color') || '#8FBCBB';
    this.exportSettings.dataTransitionStroke = value('#tikz-data-transition-stroke') || '#5E81AC';
    this.exportSettings.enabledDataTransitionColor = value('#tikz-enabled-data-transition-color') || '#A3BE8C';
    this.exportSettings.disabledDataTransitionColor = value('#tikz-disabled-data-transition-color') || '#D08770';
    this.exportSettings.arcColor = value('#tikz-arc-color') || '#000000';
    this.exportSettings.textColor = value('#tikz-text-color') || '#000000';
    this.exportSettings.tokenColor = value('#tikz-token-color') || '#000000';
    this.exportSettings.lineWidth = this.parseNumber(value('#tikz-line-width'), 0.45);
    this.exportSettings.fontSize = this.parseInteger(value('#tikz-font-size'), 10);

    this.saveSettings();
  }

  updateDialogFromSettings(dialog) {
    const setValue = (selector, nextValue) => {
      const input = dialog.querySelector(selector);
      if (input) input.value = nextValue;
    };
    const setChecked = (selector, nextValue) => {
      const input = dialog.querySelector(selector);
      if (input) input.checked = Boolean(nextValue);
    };

    setValue('#tikz-output-mode', this.exportSettings.outputMode);
    setValue('#tikz-caption', this.exportSettings.figureCaption);
    setChecked('#tikz-include-comments', this.exportSettings.includeComments);
    setChecked('#tikz-include-colors', this.exportSettings.includeColorDefinitions);
    setChecked('#tikz-include-background', this.exportSettings.includeBackground);
    setValue('#tikz-background-color', this.exportSettings.backgroundColor);

    setValue('#tikz-coordinate-mode', this.exportSettings.coordinateMode);
    setValue('#tikz-coordinate-scale', this.exportSettings.coordinateScale);
    setValue('#tikz-coordinate-precision', this.exportSettings.coordinatePrecision);
    setValue('#tikz-content-padding', this.exportSettings.contentPadding);

    setChecked('#tikz-show-places', this.exportSettings.showPlaces);
    setChecked('#tikz-show-transitions', this.exportSettings.showTransitions);
    setChecked('#tikz-show-arcs', this.exportSettings.showArcs);
    setChecked('#tikz-show-labels', this.exportSettings.showLabels);
    setChecked('#tikz-show-tokens', this.exportSettings.showTokens);
    setChecked('#tikz-show-arc-weights', this.exportSettings.showArcWeights);
    setChecked('#tikz-show-arc-types', this.exportSettings.showArcTypes);
    setChecked('#tikz-highlight-firable', this.exportSettings.highlightFirableTransitions);

    setChecked('#tikz-show-data-annotations', this.exportSettings.showDataAnnotations);
    setChecked('#tikz-show-data-guards', this.exportSettings.showDataGuards);
    setChecked('#tikz-show-data-updates', this.exportSettings.showDataUpdates);
    setChecked('#tikz-show-data-variables', this.exportSettings.showDataVariables);
    setChecked('#tikz-conditions-as-math', this.exportSettings.conditionsAsMath);
    setValue('#tikz-condition-position', this.exportSettings.conditionPosition);
    setValue('#tikz-condition-font-size', this.exportSettings.conditionFontSize);

    setValue('#tikz-place-color', this.exportSettings.placeColor);
    setValue('#tikz-place-stroke', this.exportSettings.placeStroke);
    setValue('#tikz-transition-color', this.exportSettings.transitionColor);
    setValue('#tikz-transition-stroke', this.exportSettings.transitionStroke);
    setValue('#tikz-data-transition-color', this.exportSettings.dataTransitionColor);
    setValue('#tikz-data-transition-stroke', this.exportSettings.dataTransitionStroke);
    setValue('#tikz-enabled-data-transition-color', this.exportSettings.enabledDataTransitionColor);
    setValue('#tikz-disabled-data-transition-color', this.exportSettings.disabledDataTransitionColor);
    setValue('#tikz-arc-color', this.exportSettings.arcColor);
    setValue('#tikz-text-color', this.exportSettings.textColor);
    setValue('#tikz-token-color', this.exportSettings.tokenColor);
    setValue('#tikz-line-width', this.exportSettings.lineWidth);
    setValue('#tikz-font-size', this.exportSettings.fontSize);

    dialog.querySelectorAll('input[type="range"]').forEach(range => {
      range.dispatchEvent(new Event('input'));
    });
  }

  updatePreview() {
    if (!this.dialog) return;

    const source = this.generateTikZ();
    const sourceTextarea = this.dialog.querySelector('#tikz-preview-source');
    const summary = this.dialog.querySelector('#tikz-preview-summary');

    if (sourceTextarea) {
      sourceTextarea.value = source;
    }

    if (summary) {
      const petriNet = this.app?.api?.petriNet;
      const placeCount = petriNet?.places?.size || 0;
      const transitionCount = petriNet?.transitions?.size || 0;
      const arcCount = petriNet?.arcs?.size || 0;
      summary.textContent = `${placeCount} places, ${transitionCount} transitions, ${arcCount} arcs, ${source.split('\n').length} lines`;
    }
  }

  generateTikZ(overrides = {}) {
    const settings = { ...this.getDefaultSettings(), ...this.exportSettings, ...overrides };
    const petriNet = this.app?.api?.petriNet;

    if (!petriNet) {
      return '% No Petri net is available for export.';
    }

    const previousActiveSettings = this.activeSettings;
    this.activeSettings = settings;

    try {
      const model = this.createExportModel(petriNet, settings);
      const picture = this.generateTikZPicture(model, settings);
      const comments = settings.includeComments ? this.generateComments(model) : [];
      const colorDefinitions = settings.includeColorDefinitions ? this.generateColorDefinitions(settings) : [];
      const snippetHeader = settings.includeComments
        ? [
            ...comments,
            '% Requires \\usepackage{tikz}, \\usepackage{xcolor}, and \\usetikzlibrary{arrows.meta,positioning}.'
          ]
        : [];

      if (settings.outputMode === 'standalone') {
        return [
          '\\documentclass[tikz,border=5pt]{standalone}',
          '\\usepackage{xcolor}',
          '\\usetikzlibrary{arrows.meta,positioning}',
          ...comments,
          ...colorDefinitions,
          '\\begin{document}',
          picture,
          '\\end{document}'
        ].join('\n');
      }

      if (settings.outputMode === 'figure') {
        return [
          ...snippetHeader,
          ...colorDefinitions,
          '\\begin{figure}[htbp]',
          '\\centering',
          picture,
          `\\caption{${this.escapeLatex(settings.figureCaption || 'Petri net')}}`,
          '\\end{figure}'
        ].join('\n');
      }

      return [
        ...snippetHeader,
        ...colorDefinitions,
        picture
      ].join('\n');
    } finally {
      this.activeSettings = previousActiveSettings;
    }
  }

  createExportModel(petriNet, settings) {
    const bounds = this.calculateBounds(petriNet, settings);
    const transformedBounds = this.getTransformedBounds(bounds, settings);
    const transformPoint = point => this.transformPoint(point, bounds, settings);

    return {
      petriNet,
      bounds,
      transformedBounds,
      transformPoint
    };
  }

  generateTikZPicture(model, settings) {
    const parts = [
      '\\begin{tikzpicture}[',
      ...this.generateTikZStyles(settings).map((line, index, lines) => `  ${line}${index < lines.length - 1 ? ',' : ''}`),
      ']'
    ];

    if (settings.includeBackground) {
      parts.push(this.generateBackground(model, settings));
    }

    if (settings.showDataVariables) {
      const variablesBlock = this.generateDataVariablesBlock(model, settings);
      if (variablesBlock) parts.push(variablesBlock);
    }

    if (settings.showPlaces) {
      parts.push(...this.generatePlaceLines(model, settings));
    }

    if (settings.showTransitions) {
      parts.push(...this.generateTransitionLines(model, settings));
    }

    if (settings.showArcs) {
      parts.push(...this.generateArcLines(model, settings));
    }

    parts.push('\\end{tikzpicture}');
    return parts.filter(Boolean).join('\n');
  }

  generateTikZStyles(settings) {
    const fontSize = this.clamp(settings.fontSize, 6, 72);
    const conditionFontSize = this.clamp(settings.conditionFontSize, 5, 72);
    const baselineSkip = Math.round(fontSize * 1.2);
    const conditionBaselineSkip = Math.round(conditionFontSize * 1.2);

    return [
      '>=Latex',
      `place/.style={circle, draw=yapnePlaceStroke, fill=yapnePlaceFill, line width=${this.formatRawNumber(settings.lineWidth)}pt, minimum size=1cm, inner sep=0pt}`,
      `transition/.style={rectangle, draw=yapneTransitionStroke, fill=yapneTransitionFill, line width=${this.formatRawNumber(settings.lineWidth)}pt, minimum width=0.5cm, minimum height=1.25cm, inner sep=0pt}`,
      'enabled transition/.style={transition, fill=yapneEnabledTransitionFill}',
      'silent transition/.style={transition, fill=yapneSilentTransitionFill}',
      'data transition/.style={transition, draw=yapneDataTransitionStroke, fill=yapneDataTransitionFill}',
      'data enabled transition/.style={data transition, fill=yapneEnabledDataTransitionFill}',
      'data disabled transition/.style={data transition, fill=yapneDisabledDataTransitionFill}',
      `arc/.style={-{Latex[length=2.4mm]}, draw=yapneArc, line width=${this.formatRawNumber(settings.lineWidth)}pt}`,
      `inhibitor arc/.style={-{Circle[open,length=2.4mm]}, draw=yapneArc, line width=${this.formatRawNumber(settings.lineWidth)}pt}`,
      `read arc/.style={arc, double, double distance=${this.formatRawNumber(settings.lineWidth + 0.45)}pt}`,
      'reset arc/.style={arc, dashed}',
      `element label/.style={font=\\fontsize{${fontSize}pt}{${baselineSkip}pt}\\selectfont, text=yapneText, align=center}`,
      `arc label/.style={font=\\fontsize{${fontSize}pt}{${baselineSkip}pt}\\selectfont, text=yapneText, fill=white, inner sep=1pt}`,
      `condition label/.style={font=\\fontsize{${conditionFontSize}pt}{${conditionBaselineSkip}pt}\\selectfont, text=yapneConditionText, align=center, inner sep=1.5pt}`,
      'condition box/.style={fill=yapneConditionBackground, rounded corners=1pt}',
      'data variables/.style={font=\\scriptsize, text=yapneText, align=left, fill=white, draw=yapneTransitionStroke, rounded corners=2pt, inner sep=4pt}'
    ];
  }

  generateComments(model) {
    const { petriNet } = model;

    return [
      '% Generated by YAPNE - Yet Another Petri Net Editor',
      `% Net: ${this.escapeComment(petriNet.name || petriNet.id || 'Petri net')}`,
      `% Places: ${petriNet.places.size}, transitions: ${petriNet.transitions.size}, arcs: ${petriNet.arcs.size}`
    ];
  }

  generateColorDefinitions(settings) {
    const colors = {
      yapnePlaceFill: settings.placeColor,
      yapnePlaceStroke: settings.placeStroke,
      yapneTransitionFill: settings.transitionColor,
      yapneTransitionStroke: settings.transitionStroke,
      yapneEnabledTransitionFill: settings.enabledTransitionColor,
      yapneSilentTransitionFill: settings.silentTransitionColor,
      yapneDataTransitionFill: settings.dataTransitionColor,
      yapneDataTransitionStroke: settings.dataTransitionStroke,
      yapneEnabledDataTransitionFill: settings.enabledDataTransitionColor,
      yapneDisabledDataTransitionFill: settings.disabledDataTransitionColor,
      yapneArc: settings.arcColor,
      yapneText: settings.textColor,
      yapneToken: settings.tokenColor,
      yapneConditionText: settings.conditionColor,
      yapneConditionBackground: settings.conditionBackgroundColor,
      yapneBackground: settings.backgroundColor
    };

    return Object.entries(colors).map(([name, color]) => {
      return `\\definecolor{${name}}{HTML}{${this.hexForTikZ(color)}}`;
    });
  }

  generateBackground(model) {
    const { minX, minY, maxX, maxY } = model.transformedBounds;
    return `\\fill[yapneBackground] ${this.coordinate({ x: minX, y: minY })} rectangle ${this.coordinate({ x: maxX, y: maxY })};`;
  }

  generateDataVariablesBlock(model) {
    const variables = Array.from(model.petriNet.dataVariables?.values?.() || []);
    if (variables.length === 0) return '';

    const rows = [
      '\\textbf{Name} & \\textbf{Type} & \\textbf{Value} \\\\'
    ];

    variables.forEach(variable => {
      rows.push([
        this.escapeLatex(variable.name || variable.id || ''),
        this.escapeLatex(variable.type || ''),
        this.escapeLatex(this.formatValue(variable.currentValue))
      ].join(' & ') + ' \\\\');
    });

    const point = {
      x: model.transformedBounds.minX,
      y: model.transformedBounds.maxY + 0.45
    };

    return `\\node[data variables, anchor=south west] at ${this.coordinate(point)} {\\begin{tabular}{lll}\n${rows.join('\n')}\n\\end{tabular}};`;
  }

  generatePlaceLines(model, settings) {
    const lines = [];

    for (const [id, place] of model.petriNet.places) {
      const nodeName = this.nodeName(id, 'p');
      const point = model.transformPoint(place.position);
      const radius = this.pixelToTikZ(place.radius || 20, settings);
      const size = this.formatDimension((place.radius || 20) * 2, settings);

      lines.push(`\\node[place, minimum size=${size}] (${nodeName}) at ${this.coordinate(point)} {};`);

      if (settings.showTokens) {
        lines.push(...this.generateTokenLines(place, model, settings));
      }

      if (settings.showLabels && place.label) {
        const labelPoint = { x: point.x, y: point.y - radius - settings.labelOffset };
        lines.push(`\\node[element label, anchor=north] at ${this.coordinate(labelPoint)} {${this.escapeLatex(place.label)}};`);
      }
    }

    return lines;
  }

  generateTokenLines(place, model, settings) {
    const tokens = Number(place.tokens) || 0;
    if (tokens <= 0) return [];

    if (tokens === 1) {
      return [`\\fill[yapneToken] ${this.coordinate(model.transformPoint(place.position))} circle[radius=${this.formatRawNumber(settings.tokenRadius)}cm];`];
    }

    if (tokens <= 4) {
      const positions = this.getTokenPositions(tokens, (place.radius || 20) * 0.6);
      return positions.map(offset => {
        const point = model.transformPoint({
          x: place.position.x + offset.x,
          y: place.position.y + offset.y
        });
        return `\\fill[yapneToken] ${this.coordinate(point)} circle[radius=${this.formatRawNumber(settings.tokenRadius)}cm];`;
      });
    }

    return [`\\node[element label] at ${this.coordinate(model.transformPoint(place.position))} {${this.escapeLatex(tokens)}};`];
  }

  generateTransitionLines(model, settings) {
    const lines = [];

    for (const [id, transition] of model.petriNet.transitions) {
      const nodeName = this.nodeName(id, 't');
      const point = model.transformPoint(transition.position);
      const width = transition.width || 20;
      const height = transition.height || 50;
      const tikzHeight = this.pixelToTikZ(height, settings);
      const style = this.getTransitionStyle(transition, settings);

      lines.push(`\\node[${style}, minimum width=${this.formatDimension(width, settings)}, minimum height=${this.formatDimension(height, settings)}] (${nodeName}) at ${this.coordinate(point)} {};`);

      if (settings.showLabels && transition.label && !transition.silent) {
        const labelPoint = { x: point.x, y: point.y - tikzHeight / 2 - settings.labelOffset };
        lines.push(`\\node[element label, anchor=north] at ${this.coordinate(labelPoint)} {${this.escapeLatex(transition.label)}};`);
      }

      if (settings.showDataAnnotations && this.isDataTransition(transition) && !transition.silent) {
        lines.push(...this.generateConditionLines(transition, point, width, height, settings));
      }
    }

    return lines;
  }

  generateConditionLines(transition, point, width, height, settings) {
    const conditions = [];

    if (settings.showDataGuards && transition.precondition) {
      conditions.push({ expression: transition.precondition, type: 'guard' });
    }

    if (settings.showDataUpdates && transition.postcondition) {
      conditions.push({ expression: transition.postcondition, type: 'update' });
    }

    if (conditions.length === 0) return [];

    const lines = [];
    const basePoint = this.getConditionPoint(point, width, height, settings);
    const verticalStep = settings.conditionFontSize * 0.035 + 0.12;

    conditions.forEach((condition, index) => {
      const conditionPoint = {
        x: basePoint.x,
        y: basePoint.y - (basePoint.stackDown ? index * verticalStep : -index * verticalStep)
      };
      const label = this.formatConditionLabel(condition, settings);
      const style = settings.conditionBackground ? 'condition label, condition box' : 'condition label';
      lines.push(`\\node[${style}] at ${this.coordinate(conditionPoint)} {${label}};`);
    });

    return lines;
  }

  generateArcLines(model, settings) {
    const lines = [];

    for (const [, arc] of model.petriNet.arcs) {
      const sourceId = arc.sourceId || arc.source || arc.from;
      const targetId = arc.targetId || arc.target || arc.to;
      const source = this.resolveElement(model.petriNet, sourceId);
      const target = this.resolveElement(model.petriNet, targetId);

      if (!source || !target) continue;

      const sourcePrefix = model.petriNet.places.has(sourceId) ? 'p' : 't';
      const targetPrefix = model.petriNet.places.has(targetId) ? 'p' : 't';
      const pathParts = [
        `(${this.nodeName(sourceId, sourcePrefix)})`,
        ...(arc.points || []).map(point => this.coordinate(model.transformPoint(point))),
        `(${this.nodeName(targetId, targetPrefix)})`
      ];
      const style = settings.showArcTypes ? this.getArcStyle(arc) : 'arc';
      lines.push(`\\draw[${style}] ${pathParts.join(' -- ')};`);

      const arcLabel = this.getArcLabel(arc, settings);
      if (arcLabel) {
        const labelPoint = this.getArcLabelPoint(arc, source, target, model);
        lines.push(`\\node[arc label] at ${this.coordinate(labelPoint)} {${this.escapeLatex(arcLabel)}};`);
      }
    }

    return lines;
  }

  getTransitionStyle(transition, settings) {
    if (transition.silent) return 'silent transition';

    if (this.isDataTransition(transition)) {
      return transition.isEnabled ? 'data enabled transition' : 'data disabled transition';
    }

    if (transition.isEnabled && settings.highlightFirableTransitions) {
      return 'enabled transition';
    }

    return 'transition';
  }

  getArcStyle(arc) {
    if (arc.type === 'inhibitor') return 'inhibitor arc';
    if (arc.type === 'read') return 'read arc';
    if (arc.type === 'reset') return 'reset arc';
    return 'arc';
  }

  getArcLabel(arc, settings) {
    if (!settings.showArcWeights) return '';

    const weight = Number(arc.weight);
    if (Number.isFinite(weight) && weight > 1) return String(arc.weight);

    if (arc.label && arc.label !== '1') return arc.label;
    return '';
  }

  getArcLabelPoint(arc, source, target, model) {
    const points = [
      source.position,
      ...(arc.points || []),
      target.position
    ];
    const middleIndex = Math.floor((points.length - 1) / 2);
    const start = points[middleIndex];
    const end = points[middleIndex + 1] || points[middleIndex];

    return model.transformPoint({
      x: (start.x + end.x) / 2,
      y: (start.y + end.y) / 2
    });
  }

  getConditionPoint(point, width, height, settings) {
    const tikzWidth = this.pixelToTikZ(width, settings);
    const tikzHeight = this.pixelToTikZ(height, settings);
    const offset = settings.conditionOffset;
    const position = settings.conditionPosition === 'auto' ? 'top' : settings.conditionPosition;

    if (position === 'bottom') {
      return { x: point.x, y: point.y - tikzHeight / 2 - offset, stackDown: true };
    }
    if (position === 'left') {
      return { x: point.x - tikzWidth / 2 - offset, y: point.y, stackDown: true };
    }
    if (position === 'right') {
      return { x: point.x + tikzWidth / 2 + offset, y: point.y, stackDown: true };
    }

    return { x: point.x, y: point.y + tikzHeight / 2 + offset, stackDown: false };
  }

  formatConditionLabel(condition, settings) {
    if (!settings.conditionsAsMath) {
      const prefix = condition.type === 'guard' ? '[' : '{';
      const suffix = condition.type === 'guard' ? ']' : '}';
      return `\\texttt{${this.escapeLatex(prefix + condition.expression + suffix)}}`;
    }

    const expression = this.expressionToLatex(condition.expression);
    if (condition.type === 'guard') {
      return `$[${expression}]$`;
    }
    return `$\\{${expression}\\}$`;
  }

  expressionToLatex(expression) {
    const source = String(expression || '');
    const tokenRegex = /([A-Za-z_]\w*'?|\d+(?:\.\d+)?|>=|<=|!=|==|&&|\|\||=>|[(){}[\],;+*/<>=!-]|\s+|.)/g;
    const operatorMap = {
      '>=': '\\ge',
      '<=': '\\le',
      '!=': '\\ne',
      '==': '=',
      '&&': '\\land',
      '||': '\\lor',
      '=>': '\\Rightarrow',
      '*': '\\cdot',
      '!': '\\lnot'
    };
    const wordMap = {
      and: '\\land',
      or: '\\lor',
      not: '\\lnot',
      distinct: '\\ne',
      true: '\\mathrm{true}',
      false: '\\mathrm{false}'
    };

    return Array.from(source.matchAll(tokenRegex)).map(match => {
      const token = match[0];
      if (/^\s+$/.test(token)) return ' ';
      if (operatorMap[token]) return operatorMap[token];
      if (/^[A-Za-z_]\w*'?$/.test(token)) {
        const primed = token.endsWith("'");
        const bareToken = primed ? token.slice(0, -1) : token;
        const lowerToken = bareToken.toLowerCase();
        if (wordMap[lowerToken]) return wordMap[lowerToken];
        const identifier = `\\mathit{${this.escapeLatexMathIdentifier(bareToken)}}`;
        return primed ? `${identifier}^{\\prime}` : identifier;
      }
      if (/^\d/.test(token)) return token;
      if (token === '{') return '\\{';
      if (token === '}') return '\\}';
      return this.escapeLatexMathToken(token);
    }).join('').replace(/\s+/g, ' ').trim();
  }

  calculateBounds(petriNet, settings) {
    let minX = Infinity;
    let minY = Infinity;
    let maxX = -Infinity;
    let maxY = -Infinity;

    const include = (x1, y1, x2, y2) => {
      minX = Math.min(minX, x1);
      minY = Math.min(minY, y1);
      maxX = Math.max(maxX, x2);
      maxY = Math.max(maxY, y2);
    };

    for (const place of petriNet.places.values()) {
      const radius = place.radius || 20;
      include(place.position.x - radius, place.position.y - radius, place.position.x + radius, place.position.y + radius);
    }

    for (const transition of petriNet.transitions.values()) {
      const width = transition.width || 20;
      const height = transition.height || 50;
      include(transition.position.x - width / 2, transition.position.y - height / 2, transition.position.x + width / 2, transition.position.y + height / 2);
    }

    for (const arc of petriNet.arcs.values()) {
      for (const point of arc.points || []) {
        include(point.x, point.y, point.x, point.y);
      }
    }

    if (minX === Infinity) {
      minX = 0;
      minY = 0;
      maxX = 200;
      maxY = 120;
    }

    const padding = Number(settings.contentPadding) || 0;
    return {
      minX: minX - padding,
      minY: minY - padding,
      maxX: maxX + padding,
      maxY: maxY + padding
    };
  }

  getTransformedBounds(bounds, settings) {
    const points = [
      this.transformPoint({ x: bounds.minX, y: bounds.minY }, bounds, settings),
      this.transformPoint({ x: bounds.maxX, y: bounds.minY }, bounds, settings),
      this.transformPoint({ x: bounds.maxX, y: bounds.maxY }, bounds, settings),
      this.transformPoint({ x: bounds.minX, y: bounds.maxY }, bounds, settings)
    ];

    return {
      minX: Math.min(...points.map(point => point.x)),
      minY: Math.min(...points.map(point => point.y)),
      maxX: Math.max(...points.map(point => point.x)),
      maxY: Math.max(...points.map(point => point.y))
    };
  }

  transformPoint(point, bounds, settings) {
    const scale = this.getScale(settings);

    if (settings.coordinateMode === 'canvas') {
      return {
        x: point.x * scale,
        y: -point.y * scale
      };
    }

    return {
      x: (point.x - bounds.minX) * scale,
      y: (bounds.maxY - point.y) * scale
    };
  }

  resolveElement(petriNet, id) {
    if (!id) return null;
    return petriNet.places.get(id) || petriNet.transitions.get(id) || null;
  }

  isDataTransition(transition) {
    return typeof transition.evaluatePrecondition === 'function' || 'precondition' in transition || 'postcondition' in transition;
  }

  getTokenPositions(count, radius) {
    const positions = [];
    for (let index = 0; index < count; index++) {
      const angle = (index * 2 * Math.PI) / count;
      positions.push({
        x: Math.cos(angle) * radius,
        y: Math.sin(angle) * radius
      });
    }
    return positions;
  }

  async copyTikZ() {
    const source = this.generateTikZ();

    try {
      await navigator.clipboard.writeText(source);
      this.flashCopyState('Copied');
    } catch (error) {
      const textarea = this.dialog?.querySelector('#tikz-preview-source');
      if (textarea) {
        textarea.focus();
        textarea.select();
      }
      this.flashCopyState('Select and copy');
    }
  }

  flashCopyState(text) {
    const button = this.dialog?.querySelector('#copy-tikz-btn');
    if (!button) return;

    const originalText = button.textContent;
    button.textContent = text;
    setTimeout(() => {
      button.textContent = originalText;
    }, 1400);
  }

  exportTikZ() {
    try {
      const source = this.generateTikZ();
      const blob = new Blob([source], { type: 'text/x-tex;charset=utf-8' });
      this.downloadBlob(blob, 'tex');
      this.closeDialog();
    } catch (error) {
      console.error('Error exporting TikZ:', error);
      alert('Error exporting TikZ. Please try again.');
    }
  }

  downloadBlob(blob, extension) {
    const url = URL.createObjectURL(blob);
    const anchor = document.createElement('a');
    anchor.href = url;
    anchor.download = `petri-net-${new Date().toISOString().slice(0, 19).replace(/:/g, '-')}.${extension}`;
    anchor.click();
    URL.revokeObjectURL(url);
  }

  closeDialog() {
    if (this.dialog?.parentNode) {
      this.dialog.parentNode.removeChild(this.dialog);
    }
    this.dialog = null;
  }

  coordinate(point) {
    return `(${this.formatNumber(point.x)},${this.formatNumber(point.y)})`;
  }

  formatDimension(pixels, settings) {
    return `${this.formatRawNumber(this.pixelToTikZ(pixels, settings))}cm`;
  }

  pixelToTikZ(pixels, settings) {
    return Number(pixels || 0) * this.getScale(settings);
  }

  getScale(settings) {
    const scale = Number(settings.coordinateScale);
    return Number.isFinite(scale) && scale > 0 ? scale : 0.025;
  }

  formatNumber(value) {
    const precision = this.clamp(this.activeSettings?.coordinatePrecision ?? this.exportSettings.coordinatePrecision ?? 2, 0, 4);
    return this.formatRawNumber(value, precision);
  }

  formatRawNumber(value, precision = 3) {
    const number = Number(value);
    if (!Number.isFinite(number)) return '0';
    return Number(number.toFixed(precision)).toString();
  }

  nodeName(id, prefix) {
    const base = String(id || '')
      .replace(/[^A-Za-z0-9_]/g, '_')
      .replace(/^([^A-Za-z_])/, '_$1');
    return `${prefix}_${base || 'node'}`;
  }

  hexForTikZ(color) {
    const normalized = String(color || '').trim();
    const match = normalized.match(/^#?([0-9a-fA-F]{6})(?:[0-9a-fA-F]{2})?$/);
    return match ? match[1].toUpperCase() : '000000';
  }

  escapeHTML(value) {
    return String(value ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#039;');
  }

  escapeLatex(value) {
    return String(value ?? '')
      .replace(/\\/g, '\\textbackslash{}')
      .replace(/([#$%&_^{}])/g, '\\$1')
      .replace(/~/g, '\\textasciitilde{}');
  }

  escapeLatexMathIdentifier(value) {
    return String(value ?? '').replace(/([#$%&_^{}])/g, '\\$1');
  }

  escapeLatexMathToken(value) {
    return String(value ?? '')
      .replace(/\\/g, '\\backslash{}')
      .replace(/([#$%&_])/g, '\\$1')
      .replace(/\^/g, '\\hat{}')
      .replace(/~/g, '\\sim{}');
  }

  escapeComment(value) {
    return String(value ?? '').replace(/\n/g, ' ').replace(/%/g, '\\%');
  }

  formatValue(value) {
    if (value === null || value === undefined) return '';
    if (typeof value === 'boolean') return value ? 'true' : 'false';
    return String(value);
  }

  parseNumber(value, fallback) {
    const number = Number(value);
    return Number.isFinite(number) ? number : fallback;
  }

  parseInteger(value, fallback) {
    const number = parseInt(value, 10);
    return Number.isFinite(number) ? number : fallback;
  }

  clamp(value, min, max) {
    return Math.min(max, Math.max(min, Number(value)));
  }
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', () => {
    const initTimer = setInterval(() => {
      if (window.petriApp) {
        window.tikzExporter = new TikZExporter(window.petriApp);
        clearInterval(initTimer);
        console.log('TikZ Exporter extension loaded');
      }
    }, 100);
  });
}

export { TikZExporter };
