/**
 * Simulation Dashboard Module
 * 
 * A full simulation editor/dashboard for the Petri Net Editor.
 * Features:
 * - Active transitions list with manual firing
 * - Max simulation steps configuration
 * - Step counter and trace log
 * - Token state overview
 * - Variable popups on canvas next to transitions
 * - Auto-run with speed control
 */

export class SimulationDashboard {
  constructor(app) {
    this.app = app;
    this.isOpen = false;
    this.stepCount = 0;
    this.maxSteps = 0; // 0 = unlimited
    this.traceLog = [];
    this.autoRunSpeed = 500;
    this.isRunning = false;
    this.autoRunTimer = null;
    
    this.panel = null;
    this.toggleBtn = null;
    
    this._init();
  }

  _init() {
    this._createToggleButton();
    this._createPanel();
  }

  _createToggleButton() {
    this.toggleBtn = document.createElement('button');
    this.toggleBtn.className = 'side-panel-toggle sim-toggle';
    this.toggleBtn.id = 'sim-panel-toggle';
    this.toggleBtn.innerHTML = `
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <polygon points="5 3 19 12 5 21 5 3"/>
      </svg>
      <span class="toggle-label">Simulation</span>
    `;
    this.toggleBtn.title = 'Toggle Simulation Panel';
    this.toggleBtn.addEventListener('click', () => this.toggle());
    
    const container = document.querySelector('.canvas-container');
    if (container) container.appendChild(this.toggleBtn);
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'sim-dashboard-panel side-panel';
    this.panel.id = 'sim-dashboard';
    this.panel.innerHTML = this._getPanelHTML();
    
    const editorContainer = document.querySelector('.editor-container');
    if (editorContainer) editorContainer.appendChild(this.panel);
    
    this._bindPanelEvents();
  }

  _getPanelHTML() {
    return `
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <polygon points="5 3 19 12 5 21 5 3"/>
          </svg>
          <h3>Simulation</h3>
        </div>
        <button class="panel-close" id="sim-panel-close" title="Close">✕</button>
      </div>

      <div class="panel-body">
        <!-- Status Banner -->
        <div class="sim-status-banner" id="sim-status-banner">
          <div class="status-indicator stopped"></div>
          <span class="status-text">Ready</span>
        </div>

        <!-- Controls Section -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><polyline points="12 6 12 12 16 14"/></svg>
            </span>
            <span>Controls</span>
          </div>
          <div class="dash-section-body">
            <div class="sim-controls-row">
              <button id="sim-step-btn" class="sim-btn sim-btn-primary" title="Execute one step">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5"><polyline points="9 18 15 12 9 6"/></svg>
                Step
              </button>
              <button id="sim-run-btn" class="sim-btn sim-btn-success" title="Auto-run simulation">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polygon points="5 3 19 12 5 21 5 3"/></svg>
                Run
              </button>
              <button id="sim-reset-btn" class="sim-btn sim-btn-warning" title="Reset to initial state">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="1 4 1 10 7 10"/><path d="M3.51 15a9 9 0 1 0 2.13-9.36L1 10"/></svg>
                Reset
              </button>
            </div>

            <!-- Speed + Max Steps -->
            <div class="sim-config-grid">
              <div class="sim-config-item">
                <label>Speed</label>
                <div class="sim-speed-control">
                  <input type="range" id="sim-speed" min="50" max="2000" value="500" step="50">
                  <span id="sim-speed-label" class="sim-config-value">500ms</span>
                </div>
              </div>
              <div class="sim-config-item">
                <label>Max Steps</label>
                <input type="number" id="sim-max-steps" min="0" value="0" placeholder="0 = unlimited" class="sim-input-small">
              </div>
            </div>
          </div>
        </div>

        <!-- Step Counter -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polyline points="22 12 18 12 15 21 9 3 6 12 2 12"/></svg>
            </span>
            <span>Progress</span>
          </div>
          <div class="dash-section-body">
            <div class="sim-progress-bar-container">
              <div class="sim-progress-stats">
                <span>Step <strong id="sim-step-count">0</strong></span>
                <span id="sim-max-steps-display" class="sim-max-label">/ ∞</span>
              </div>
              <div class="sim-progress-bar">
                <div class="sim-progress-fill" id="sim-progress-fill" style="width: 0%"></div>
              </div>
            </div>
          </div>
        </div>

        <!-- Active Transitions -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M13 2L3 14h9l-1 8 10-12h-9l1-8z"/></svg>
            </span>
            <span>Active Transitions</span>
            <span class="dash-badge" id="sim-active-count">0</span>
          </div>
          <div class="dash-section-body">
            <div class="sim-transitions-list" id="sim-transitions-list">
              <div class="sim-empty-state">
                <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" opacity="0.4">
                  <rect x="3" y="3" width="18" height="18" rx="2" ry="2"/>
                  <line x1="9" y1="9" x2="15" y2="15"/><line x1="15" y1="9" x2="9" y2="15"/>
                </svg>
                <span>No active transitions</span>
              </div>
            </div>
          </div>
        </div>

        <!-- Token State -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><circle cx="12" cy="12" r="10"/><circle cx="12" cy="12" r="3"/></svg>
            </span>
            <span>Token State</span>
          </div>
          <div class="dash-section-body">
            <div class="sim-token-grid" id="sim-token-grid">
              <p class="sim-empty-state-text">No places defined.</p>
            </div>
          </div>
        </div>

        <!-- Final Markings -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M22 11.08V12a10 10 0 1 1-5.93-9.14"/><polyline points="22 4 12 14.01 9 11.01"/></svg>
            </span>
            <span>Final Markings</span>
          </div>
          <div class="dash-section-body">
            <div id="sim-final-markings">
              <p class="sim-empty-state-text">No final markings defined.</p>
            </div>
          </div>
        </div>

        <!-- Trace Log -->
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><line x1="8" y1="6" x2="21" y2="6"/><line x1="8" y1="12" x2="21" y2="12"/><line x1="8" y1="18" x2="21" y2="18"/><line x1="3" y1="6" x2="3.01" y2="6"/><line x1="3" y1="12" x2="3.01" y2="12"/><line x1="3" y1="18" x2="3.01" y2="18"/></svg>
            </span>
            <span>Trace Log</span>
            <button class="dash-clear-btn" id="sim-clear-trace" title="Clear trace log">Clear</button>
          </div>
          <div class="dash-section-body">
            <div class="sim-trace-container" id="sim-trace-container">
              <div class="sim-empty-state-text">No simulation steps recorded.</div>
            </div>
          </div>
        </div>
      </div>
    `;
  }

  _bindPanelEvents() {
    // Close button
    const closeBtn = this.panel.querySelector('#sim-panel-close');
    if (closeBtn) closeBtn.addEventListener('click', () => this.close());

    // Step
    const stepBtn = this.panel.querySelector('#sim-step-btn');
    if (stepBtn) stepBtn.addEventListener('click', () => this.step());

    // Run/Stop
    const runBtn = this.panel.querySelector('#sim-run-btn');
    if (runBtn) runBtn.addEventListener('click', () => this.toggleAutoRun());

    // Reset
    const resetBtn = this.panel.querySelector('#sim-reset-btn');
    if (resetBtn) resetBtn.addEventListener('click', () => this.reset());

    // Speed slider
    const speedSlider = this.panel.querySelector('#sim-speed');
    if (speedSlider) {
      speedSlider.addEventListener('input', (e) => {
        this.autoRunSpeed = parseInt(e.target.value);
        const label = this.panel.querySelector('#sim-speed-label');
        if (label) label.textContent = `${this.autoRunSpeed}ms`;
        // Update interval if running
        if (this.isRunning) {
          this._stopTimer();
          this._startTimer();
        }
      });
    }

    // Max steps
    const maxStepsInput = this.panel.querySelector('#sim-max-steps');
    if (maxStepsInput) {
      maxStepsInput.addEventListener('change', (e) => {
        this.maxSteps = parseInt(e.target.value) || 0;
        this._updateProgressDisplay();
      });
    }

    // Clear trace
    const clearBtn = this.panel.querySelector('#sim-clear-trace');
    if (clearBtn) {
      clearBtn.addEventListener('click', () => {
        this.traceLog = [];
        this._updateTraceDisplay();
      });
    }
  }

  // ── Public API ──

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
    this._setRendererOverlays(true);
    this.refresh();
    this._updatePanelLayout();
  }

  close() {
    this.isOpen = false;
    this.panel.classList.remove('open');
    this.toggleBtn.classList.remove('active');
    this._setRendererOverlays(false);
    this._updatePanelLayout();
  }

  _updatePanelLayout() {
    // Notify properties panel about layout change for stacking
    document.dispatchEvent(new CustomEvent('side-panel-changed'));
  }

  refresh() {
    if (!this.isOpen) return;
    // Keep renderer overlay flag in sync (renderer may be recreated on file load)
    this._setRendererOverlays(true);
    this._updateActiveTransitions();
    this._updateTokenState();
    this._updateFinalMarkings();
    this._updateProgressDisplay();
    // Variable overlays are drawn by the renderer on each render() call
    this._triggerRender();
  }

  async step() {
    if (!this.app || !this.app.api) return;

    // Check max steps
    if (this.maxSteps > 0 && this.stepCount >= this.maxSteps) {
      this._setStatus('completed', 'Max steps reached');
      this.stopAutoRun();
      return;
    }

    // Capture initial state on first step
    if (!this.app.simulationStarted) {
      this.app.captureInitialState();
    }

    const enabledTransitions = this.app.api.getEnabledTransitions();
    if (enabledTransitions.length === 0) {
      this._setStatus('deadlocked', 'No enabled transitions — deadlock');
      this.stopAutoRun();
      return;
    }

    // Get transition labels before firing
    const firedLabels = enabledTransitions.map(id => {
      const t = this.app.api.petriNet.transitions.get(id);
      return t ? (t.label || `T${id}`) : `T${id}`;
    });

    // Fire transitions (silent = true to suppress alert, dashboard handles its own refresh)
    await this.app.stepSimulation({ silent: true });

    this.stepCount++;

    // Invalidate overlay cache so postcondition previews recalculate
    this._invalidateOverlayCache();

    // Add trace entry
    this.traceLog.push({
      step: this.stepCount,
      transitions: firedLabels,
      timestamp: Date.now()
    });

    this.refresh();
    this._updateTraceDisplay();
    this._setStatus('running', `Step ${this.stepCount} completed`);
    
    // Update the original tokens display too
    this.app.updateTokensDisplay();
    this.app.updateSelectedElementProperties();
  }

  async fireSpecificTransition(transitionId) {
    if (!this.app || !this.app.api) return;

    if (!this.app.simulationStarted) {
      this.app.captureInitialState();
    }

    const t = this.app.api.petriNet.transitions.get(transitionId);
    const label = t ? (t.label || `T${transitionId}`) : `T${transitionId}`;

    if (await this.app.fireTransition(transitionId)) {
      this.stepCount++;
      this._invalidateOverlayCache();
      this.traceLog.push({
        step: this.stepCount,
        transitions: [label],
        timestamp: Date.now()
      });
      this.refresh();
      this._updateTraceDisplay();
      this._setStatus('running', `Fired: ${label}`);
      this.app.updateTokensDisplay();
      this.app.updateSelectedElementProperties();
    }
  }

  toggleAutoRun() {
    if (this.isRunning) {
      this.stopAutoRun();
    } else {
      this.startAutoRun();
    }
  }

  startAutoRun() {
    this.isRunning = true;
    const runBtn = this.panel.querySelector('#sim-run-btn');
    if (runBtn) {
      runBtn.innerHTML = `
        <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="6" y="4" width="4" height="16"/><rect x="14" y="4" width="4" height="16"/></svg>
        Stop
      `;
      runBtn.classList.remove('sim-btn-success');
      runBtn.classList.add('sim-btn-danger');
    }
    this._setStatus('running', 'Auto-running...');
    this._startTimer();
  }

  stopAutoRun() {
    this.isRunning = false;
    this._stopTimer();
    
    // Also stop the app's auto-run if it was started
    if (this.app.autoRunInterval) {
      this.app.stopAutoRun();
    }
    
    const runBtn = this.panel.querySelector('#sim-run-btn');
    if (runBtn) {
      runBtn.innerHTML = `
        <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><polygon points="5 3 19 12 5 21 5 3"/></svg>
        Run
      `;
      runBtn.classList.remove('sim-btn-danger');
      runBtn.classList.add('sim-btn-success');
    }
    this._setStatus('paused', `Paused at step ${this.stepCount}`);
  }

  reset() {
    this.stopAutoRun();
    this.stepCount = 0;
    this.traceLog = [];

    if (this.app.restoreInitialState()) {
      this._setStatus('stopped', 'Ready');
    } else {
      this._setStatus('stopped', 'Ready (no initial state)');
    }

    // Reset the app's simulation state
    this.app.simulationStarted = false;
    this.app.initialState = null;
    this._invalidateOverlayCache();

    this.refresh();
    this._updateTraceDisplay();
    this.app.updateTokensDisplay();
    this._triggerRender();
  }

  // ── Internal Methods ──

  _startTimer() {
    this._stopTimer();
    this.autoRunTimer = setInterval(async () => {
      if (this.maxSteps > 0 && this.stepCount >= this.maxSteps) {
        this._setStatus('completed', 'Max steps reached');
        this.stopAutoRun();
        return;
      }
      
      const enabled = this.app.api.getEnabledTransitions();
      if (enabled.length === 0) {
        this._setStatus('deadlocked', 'No enabled transitions');
        this.stopAutoRun();
        return;
      }
      await this.step();
    }, this.autoRunSpeed);
  }

  _stopTimer() {
    if (this.autoRunTimer) {
      clearInterval(this.autoRunTimer);
      this.autoRunTimer = null;
    }
  }

  _setStatus(type, text) {
    const banner = this.panel.querySelector('#sim-status-banner');
    if (!banner) return;
    
    const indicator = banner.querySelector('.status-indicator');
    const statusText = banner.querySelector('.status-text');
    
    if (indicator) {
      indicator.className = 'status-indicator ' + type;
    }
    if (statusText) {
      statusText.textContent = text;
    }
  }

  _updateActiveTransitions() {
    const list = this.panel.querySelector('#sim-transitions-list');
    const badge = this.panel.querySelector('#sim-active-count');
    if (!list || !this.app?.api) return;

    const net = this.app.api.petriNet;
    net.updateEnabledTransitions();

    const enabled = [];
    for (const [id, t] of net.transitions) {
      if (t.isEnabled) {
        enabled.push({ id, label: t.label || `T${id}`, silent: t.silent });
      }
    }

    if (badge) badge.textContent = enabled.length;

    if (enabled.length === 0) {
      list.innerHTML = `
        <div class="sim-empty-state">
          <svg width="24" height="24" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="1.5" opacity="0.4">
            <rect x="3" y="3" width="18" height="18" rx="2" ry="2"/>
            <line x1="9" y1="9" x2="15" y2="15"/><line x1="15" y1="9" x2="9" y2="15"/>
          </svg>
          <span>No active transitions</span>
        </div>
      `;
      return;
    }

    list.innerHTML = enabled.map(t => `
      <div class="sim-transition-item">
        <div class="sim-transition-info">
          <span class="sim-transition-dot enabled"></span>
          <span class="sim-transition-label">${t.silent ? 'τ' : t.label}</span>
          ${t.silent ? '<span class="sim-silent-badge">silent</span>' : ''}
        </div>
        <button class="sim-fire-btn" data-transition-id="${t.id}" title="Fire ${t.label}">
          <svg width="12" height="12" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.5"><polygon points="5 3 19 12 5 21 5 3"/></svg>
          Fire
        </button>
      </div>
    `).join('');

    // Bind fire buttons
    list.querySelectorAll('.sim-fire-btn').forEach(btn => {
      btn.addEventListener('click', (e) => {
        const tId = btn.getAttribute('data-transition-id');
        this.fireSpecificTransition(tId);
      });
    });
  }

  _updateTokenState() {
    const grid = this.panel.querySelector('#sim-token-grid');
    if (!grid || !this.app?.api) return;

    const net = this.app.api.petriNet;
    if (net.places.size === 0) {
      grid.innerHTML = '<p class="sim-empty-state-text">No places defined.</p>';
      return;
    }

    grid.innerHTML = Array.from(net.places.values()).map(p => `
      <div class="sim-token-item">
        <span class="sim-token-place">${p.label || p.id}</span>
        <span class="sim-token-count ${p.tokens > 0 ? 'has-tokens' : ''}">${p.tokens}</span>
      </div>
    `).join('');
  }

  _updateFinalMarkings() {
    const container = this.panel.querySelector('#sim-final-markings');
    if (!container || !this.app?.api) return;

    const net = this.app.api.petriNet;
    const results = this.app.api.checkFinalMarkings();

    if (results.placesWithFinalMarkings === 0) {
      container.innerHTML = '<p class="sim-empty-state-text">No final markings defined.</p>';
      return;
    }

    let html = `
      <div class="sim-final-summary">
        <div class="sim-final-progress">
          <span>${results.satisfiedFinalMarkings}/${results.placesWithFinalMarkings}</span>
          <span>${results.allSatisfied ? '✅ Complete' : '⏳ In progress'}</span>
        </div>
      </div>
    `;

    for (const [id, place] of net.places) {
      if (place.hasFinalMarking()) {
        const reached = place.hasReachedFinalMarking();
        html += `
          <div class="sim-final-item ${reached ? 'satisfied' : 'pending'}">
            <span>${place.label || id}</span>
            <span class="sim-final-status">${place.tokens}/${place.finalMarking} ${reached ? '✅' : '⏳'}</span>
          </div>
        `;
      }
    }

    if (results.allSatisfied) {
      html += '<div class="sim-final-complete">🎉 All final markings reached!</div>';
    }

    container.innerHTML = html;
  }

  _updateProgressDisplay() {
    const countEl = this.panel.querySelector('#sim-step-count');
    const maxEl = this.panel.querySelector('#sim-max-steps-display');
    const fillEl = this.panel.querySelector('#sim-progress-fill');

    if (countEl) countEl.textContent = this.stepCount;
    if (maxEl) maxEl.textContent = this.maxSteps > 0 ? `/ ${this.maxSteps}` : '/ ∞';
    
    if (fillEl) {
      if (this.maxSteps > 0) {
        const pct = Math.min((this.stepCount / this.maxSteps) * 100, 100);
        fillEl.style.width = `${pct}%`;
      } else {
        // Indeterminate-ish: show some progress 
        fillEl.style.width = this.stepCount > 0 ? `${Math.min(this.stepCount * 5, 100)}%` : '0%';
      }
    }
  }

  _updateTraceDisplay() {
    const container = this.panel.querySelector('#sim-trace-container');
    if (!container) return;

    if (this.traceLog.length === 0) {
      container.innerHTML = '<div class="sim-empty-state-text">No simulation steps recorded.</div>';
      return;
    }

    // Show last 50 entries (most recent first)
    const entries = this.traceLog.slice(-50).reverse();
    container.innerHTML = entries.map(entry => `
      <div class="sim-trace-entry">
        <span class="sim-trace-step">${entry.step}</span>
        <span class="sim-trace-arrow">→</span>
        <span class="sim-trace-transitions">${entry.transitions.join(', ')}</span>
      </div>
    `).join('');

    // Scroll to top (most recent)
    container.scrollTop = 0;
  }

  // ── Renderer Overlay Control ──

  /**
   * Invalidate the overlay cache so postcondition previews recalculate.
   * Call after any simulation state change (step, fire, reset).
   */
  _invalidateOverlayCache() {
    const renderer = this.app?.editor?.renderer;
    if (renderer && typeof renderer.invalidateOverlayCache === 'function') {
      renderer.invalidateOverlayCache();
    }
  }

  /**
   * Toggle the showDataOverlays flag on the DPN renderer
   */
  _setRendererOverlays(enabled) {
    const renderer = this.app?.editor?.renderer;
    if (renderer && 'showDataOverlays' in renderer) {
      renderer.showDataOverlays = enabled;
      this._triggerRender();
    }
  }

  /**
   * Force a canvas re-render so overlays are drawn/cleared
   */
  _triggerRender() {
    if (this.app?.editor) {
      this.app.editor.render();
    }
  }

  // Cleanup
  destroy() {
    this._stopTimer();
    this._setRendererOverlays(false);
    if (this.panel && this.panel.parentNode) {
      this.panel.parentNode.removeChild(this.panel);
    }
    if (this.toggleBtn && this.toggleBtn.parentNode) {
      this.toggleBtn.parentNode.removeChild(this.toggleBtn);
    }
  }
}

export default SimulationDashboard;
