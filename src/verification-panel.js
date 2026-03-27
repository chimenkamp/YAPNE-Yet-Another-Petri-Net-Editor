/**
 * Verification Panel Module
 *
 * A toggleable side panel for formal verification of Petri Net properties.
 * Hosts the Suvorov-Lomazova soundness verification UI that was previously
 * embedded in the File sidebar.
 */

export class VerificationPanel {
  constructor(app) {
    this.app = app;
    this.isOpen = false;
    this.panel = null;
    this.toggleBtn = null;
    this.contentEl = null;

    this._init();
  }

  _init() {
    this._createToggleButton();
    this._createPanel();
  }

  _createToggleButton() {
    this.toggleBtn = document.createElement('button');
    this.toggleBtn.className = 'side-panel-toggle verify-toggle';
    this.toggleBtn.id = 'verify-panel-toggle';
    this.toggleBtn.innerHTML = `
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <path d="M9 12l2 2 4-4"/>
        <path d="M12 3a9 9 0 1 0 0 18 9 9 0 0 0 0-18z"/>
      </svg>
      <span class="toggle-label">Verification</span>
    `;
    this.toggleBtn.title = 'Toggle Verification Panel';
    this.toggleBtn.addEventListener('click', () => this.toggle());

    const container = document.querySelector('.canvas-container');
    if (container) container.appendChild(this.toggleBtn);
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'verify-panel side-panel';
    this.panel.id = 'verify-panel';
    this.panel.innerHTML = `
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <path d="M9 12l2 2 4-4"/>
            <path d="M12 3a9 9 0 1 0 0 18 9 9 0 0 0 0-18z"/>
          </svg>
          <h3>Verification</h3>
        </div>
        <button class="panel-close" id="verify-panel-close" title="Close">✕</button>
      </div>
      <div class="panel-body">
        <div id="verify-content" class="verify-content">
          <!-- Soundness verification section will be injected here -->
          <div class="dash-section" id="verify-soundness-section">
            <div class="dash-section-header">
              <span class="dash-icon">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M9 12l2 2 4-4"/>
                  <path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/>
                </svg>
              </span>
              <span>Formal Soundness</span>
            </div>
            <div class="dash-section-body" id="verify-soundness-content">
              <p style="font-size: 13px; color: #D8DEE9; margin-bottom: 12px; line-height: 1.4;">
                Verify soundness properties (P1–P3) using Suvorov & Lomazova algorithms with Z3 SMT solver.
              </p>
              <button id="btn-sl-verify-panel" class="sim-btn sim-btn-primary" style="width: 100%; justify-content: center;">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M9 12l2 2 4-4"/>
                  <circle cx="12" cy="12" r="10"/>
                </svg>
                Run Formal Verification
              </button>
            </div>
          </div>
        </div>
      </div>
    `;

    const editorContainer = document.querySelector('.editor-container');
    if (editorContainer) editorContainer.appendChild(this.panel);

    this.contentEl = this.panel.querySelector('#verify-content');

    // Close button
    const closeBtn = this.panel.querySelector('#verify-panel-close');
    if (closeBtn) closeBtn.addEventListener('click', () => this.close());

    // Wire up the verification button to call the Suvorov-Lomazova UI
    const verifyBtn = this.panel.querySelector('#btn-sl-verify-panel');
    if (verifyBtn) {
      verifyBtn.addEventListener('click', () => {
        if (window.suvorovLomazovaUI) {
          window.suvorovLomazovaUI.startVerification();
        } else {
          alert('Verification engine not yet loaded. Please wait a moment and try again.');
        }
      });
    }
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

  /** Returns the content element for injection */
  getContentElement() {
    return this.contentEl;
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

export default VerificationPanel;
