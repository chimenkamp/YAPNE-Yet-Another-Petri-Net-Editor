/**
 * Properties Panel Module
 * 
 * A toggleable side panel for viewing/editing Petri Net element properties.
 * Works alongside the SimulationDashboard panel – when both are open they stack.
 */

export class PropertiesPanel {
  constructor(app) {
    this.app = app;
    this.isOpen = true; // open by default
    this.panel = null;
    this.toggleBtn = null;
    this.contentEl = null;

    this._init();
  }

  _init() {
    this._createToggleButton();
    this._createPanel();

    // Listen for layout changes from simulation panel
    document.addEventListener('side-panel-changed', () => this._updateLayout());
  }

  _createToggleButton() {
    this.toggleBtn = document.createElement('button');
    this.toggleBtn.className = 'side-panel-toggle props-toggle active';
    this.toggleBtn.id = 'props-panel-toggle';
    this.toggleBtn.innerHTML = `
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06A1.65 1.65 0 0 0 4.68 15a1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06A1.65 1.65 0 0 0 9 4.68a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06A1.65 1.65 0 0 0 19.4 9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/>
      </svg>
      <span class="toggle-label">Properties</span>
    `;
    this.toggleBtn.title = 'Toggle Properties Panel';
    this.toggleBtn.addEventListener('click', () => this.toggle());

    const container = document.querySelector('.canvas-container');
    if (container) container.appendChild(this.toggleBtn);
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'props-panel side-panel open';
    this.panel.id = 'props-panel';
    this.panel.innerHTML = `
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <circle cx="12" cy="12" r="3"/><path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06A1.65 1.65 0 0 0 4.68 15a1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06A1.65 1.65 0 0 0 9 4.68a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06A1.65 1.65 0 0 0 19.4 9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/>
          </svg>
          <h3>Properties</h3>
        </div>
        <button class="panel-close" id="props-panel-close" title="Close">✕</button>
      </div>
      <div class="panel-body">
        <div id="props-content" class="props-content">
          <p class="sim-empty-state-text">No element selected.</p>
        </div>
        <!-- Data Variables Section -->
        <div class="dash-section" id="props-data-vars-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <polyline points="4 7 4 4 20 4 20 7"/><line x1="9" y1="20" x2="15" y2="20"/><line x1="12" y1="4" x2="12" y2="20"/>
              </svg>
            </span>
            <span>Data Variables</span>
          </div>
          <div class="dash-section-body" id="props-data-variables-content">
          </div>
        </div>
      </div>
    `;

    const editorContainer = document.querySelector('.editor-container');
    if (editorContainer) editorContainer.appendChild(this.panel);

    this.contentEl = this.panel.querySelector('#props-content');

    // Close
    const closeBtn = this.panel.querySelector('#props-panel-close');
    if (closeBtn) closeBtn.addEventListener('click', () => this.close());

    // Mirror data variables from hidden container
    this._setupDataVarsMirror();
  }

  toggle() {
    if (this.isOpen) {
      this.close();
    } else {
      this.open();
    }
  }

  open() {
    this.isOpen = true;
    this.panel.classList.add('open');
    this.toggleBtn.classList.add('active');
    this._updateLayout();
  }

  close() {
    this.isOpen = false;
    this.panel.classList.remove('open');
    this.toggleBtn.classList.remove('active');
    this._updateLayout();
  }

  /** Returns the content element for property HTML injection */
  getContentElement() {
    return this.contentEl;
  }

  /** Returns the data variables container */
  getDataVariablesContainer() {
    return this.panel.querySelector('#props-data-variables-content');
  }

  /**
   * Mirror content from the hidden data-variables-content-conatiner
   * into the new panel's data variables section
   */
  _setupDataVarsMirror() {
    const sourceContainer = document.getElementById('data-variables-content-conatiner');
    const targetContainer = this.panel.querySelector('#props-data-variables-content');
    if (!sourceContainer || !targetContainer) return;

    const rebindButtons = () => {
      // For every button in the mirror, forward clicks to the matching source button
      const mirrorButtons = targetContainer.querySelectorAll('button');
      mirrorButtons.forEach((mirrorBtn, index) => {
        const sourceButtons = sourceContainer.querySelectorAll('button');
        const sourceBtn = sourceButtons[index];
        if (sourceBtn) {
          mirrorBtn.addEventListener('click', (e) => {
            e.preventDefault();
            sourceBtn.click();
          });
        }
      });
    };

    // Observe changes in the hidden container and copy to the panel
    const observer = new MutationObserver(() => {
      targetContainer.innerHTML = sourceContainer.innerHTML;
      rebindButtons();
    });

    observer.observe(sourceContainer, { childList: true, subtree: true, characterData: true });
    
    // Initial copy
    if (sourceContainer.innerHTML.trim()) {
      targetContainer.innerHTML = sourceContainer.innerHTML;
      rebindButtons();
    }
  }

  _updateLayout() {
    document.dispatchEvent(new CustomEvent('side-panel-changed'));
  }

  destroy() {
    if (this.panel && this.panel.parentNode) {
      this.panel.parentNode.removeChild(this.panel);
    }
    if (this.toggleBtn && this.toggleBtn.parentNode) {
      this.toggleBtn.parentNode.removeChild(this.toggleBtn);
    }
  }
}

export default PropertiesPanel;
