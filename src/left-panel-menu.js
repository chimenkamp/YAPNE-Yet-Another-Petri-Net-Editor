/**
 * Left Panel Menu Module
 *
 * Creates a vertical icon bar on the left side of the canvas with toggle
 * buttons for Properties, Simulation and Verification.
 *
 * Stacking rules (right-side panels):
 * - 1 panel open  → full height
 * - 2 panels open → stacked vertically (top 45 vh / bottom 55 vh)
 * - 3 panels open → most-recently-opened panel gets full height and sits
 *                    in front (higher z-index); the other two stack behind
 * - closing one   → remaining panels re-stack accordingly
 */

export class LeftPanelMenu {
  /**
   * @param {object} opts
   * @param {import('./properties-panel').PropertiesPanel} opts.propsPanel
   * @param {import('./simulation-dashboard').SimulationDashboard} opts.simDashboard
   * @param {import('./verification-panel').VerificationPanel} opts.verifyPanel
   */
  constructor({ propsPanel, simDashboard, verifyPanel }) {
    this.propsPanel = propsPanel;
    this.simDashboard = simDashboard;
    this.verifyPanel = verifyPanel;

    /** Tracks the order panels were opened (most-recent last) */
    this._openOrder = [];

    this._createMenuBar();
    this._hookPanelEvents();
    this._applyLayout();
  }

  /* ── Menu Bar ── */

  _createMenuBar() {
    this.menuBar = document.createElement('div');
    this.menuBar.className = 'left-panel-menu';
    this.menuBar.innerHTML = `
      <button class="lpm-btn" data-panel="props" title="Properties">
        <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
          <circle cx="12" cy="12" r="3"/>
          <path d="M19.4 15a1.65 1.65 0 0 0 .33 1.82l.06.06a2 2 0 0 1-2.83 2.83l-.06-.06a1.65 1.65 0 0 0-1.82-.33 1.65 1.65 0 0 0-1 1.51V21a2 2 0 0 1-4 0v-.09A1.65 1.65 0 0 0 9 19.4a1.65 1.65 0 0 0-1.82.33l-.06.06a2 2 0 0 1-2.83-2.83l.06-.06A1.65 1.65 0 0 0 4.68 15a1.65 1.65 0 0 0-1.51-1H3a2 2 0 0 1 0-4h.09A1.65 1.65 0 0 0 4.6 9a1.65 1.65 0 0 0-.33-1.82l-.06-.06a2 2 0 0 1 2.83-2.83l.06.06A1.65 1.65 0 0 0 9 4.68a1.65 1.65 0 0 0 1-1.51V3a2 2 0 0 1 4 0v.09a1.65 1.65 0 0 0 1 1.51 1.65 1.65 0 0 0 1.82-.33l.06-.06a2 2 0 0 1 2.83 2.83l-.06.06A1.65 1.65 0 0 0 19.4 9a1.65 1.65 0 0 0 1.51 1H21a2 2 0 0 1 0 4h-.09a1.65 1.65 0 0 0-1.51 1z"/>
        </svg>
        <span class="lpm-label">Properties</span>
      </button>
      <button class="lpm-btn" data-panel="sim" title="Simulation">
        <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
          <polygon points="5 3 19 12 5 21 5 3"/>
        </svg>
        <span class="lpm-label">Simulation</span>
      </button>
      <button class="lpm-btn" data-panel="verify" title="Verification">
        <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
          <path d="M9 12l2 2 4-4"/>
          <path d="M12 3a9 9 0 1 0 0 18 9 9 0 0 0 0-18z"/>
        </svg>
        <span class="lpm-label">Verification</span>
      </button>
    `;

    // Insert into canvas container (left side)
    const canvasContainer = document.querySelector('.canvas-container');
    if (canvasContainer) canvasContainer.appendChild(this.menuBar);

    // Click handlers
    this.menuBar.querySelectorAll('.lpm-btn').forEach(btn => {
      btn.addEventListener('click', () => {
        const key = btn.dataset.panel;
        this._togglePanel(key);
      });
    });
  }

  /* ── Panel toggling ── */

  _panelFor(key) {
    switch (key) {
      case 'props': return this.propsPanel;
      case 'sim': return this.simDashboard;
      case 'verify': return this.verifyPanel;
    }
    return null;
  }

  _togglePanel(key) {
    const panel = this._panelFor(key);
    if (!panel) return;

    if (panel.isOpen) {
      panel.close();
      this._openOrder = this._openOrder.filter(k => k !== key);
    } else {
      panel.open();
      // Push to end (most-recently-opened)
      this._openOrder = this._openOrder.filter(k => k !== key);
      this._openOrder.push(key);
    }

    this._applyLayout();
    this._syncButtons();
  }

  /* ── Hook into panel open/close from their own toggle buttons ── */

  _hookPanelEvents() {
    document.addEventListener('side-panel-changed', () => {
      // Rebuild _openOrder from actual panel states
      const newOrder = [];
      for (const key of this._openOrder) {
        const p = this._panelFor(key);
        if (p && p.isOpen) newOrder.push(key);
      }
      // Add any newly-opened panels not yet tracked
      for (const key of ['props', 'sim', 'verify']) {
        const p = this._panelFor(key);
        if (p && p.isOpen && !newOrder.includes(key)) {
          newOrder.push(key);
        }
      }
      this._openOrder = newOrder;
      this._applyLayout();
      this._syncButtons();
    });
  }

  /* ── Layout engine ── */

  _applyLayout() {
    const openCount = this._openOrder.length;

    // Clear all layout classes
    document.body.classList.remove(
      'panels-open-0', 'panels-open-1', 'panels-open-2', 'panels-open-3',
      'both-panels-open', 'panel-open'
    );

    // Remove per-panel layout classes
    for (const key of ['props', 'sim', 'verify']) {
      const p = this._panelFor(key);
      if (p && p.panel) {
        p.panel.classList.remove('panel-front', 'panel-stack-top', 'panel-stack-bottom');
      }
    }

    document.body.classList.add(`panels-open-${openCount}`);

    if (openCount > 0) {
      document.body.classList.add('panel-open');
    }

    if (openCount === 2) {
      document.body.classList.add('both-panels-open');
      // First opened → top, second → bottom
      const [first, second] = this._openOrder;
      const firstPanel = this._panelFor(first);
      const secondPanel = this._panelFor(second);
      if (firstPanel?.panel) firstPanel.panel.classList.add('panel-stack-top');
      if (secondPanel?.panel) secondPanel.panel.classList.add('panel-stack-bottom');
    }

    if (openCount === 3) {
      // Most-recently-opened is in front with full height
      const frontKey = this._openOrder[2]; // last = most recent
      const stackKeys = [this._openOrder[0], this._openOrder[1]];

      const frontPanel = this._panelFor(frontKey);
      if (frontPanel?.panel) frontPanel.panel.classList.add('panel-front');

      const topPanel = this._panelFor(stackKeys[0]);
      const bottomPanel = this._panelFor(stackKeys[1]);
      if (topPanel?.panel) topPanel.panel.classList.add('panel-stack-top');
      if (bottomPanel?.panel) bottomPanel.panel.classList.add('panel-stack-bottom');
    }
  }

  /* ── Sync left-menu button active states ── */

  _syncButtons() {
    this.menuBar.querySelectorAll('.lpm-btn').forEach(btn => {
      const key = btn.dataset.panel;
      const p = this._panelFor(key);
      btn.classList.toggle('active', !!(p && p.isOpen));
    });
  }

  destroy() {
    if (this.menuBar && this.menuBar.parentNode) {
      this.menuBar.parentNode.removeChild(this.menuBar);
    }
  }
}

export default LeftPanelMenu;
