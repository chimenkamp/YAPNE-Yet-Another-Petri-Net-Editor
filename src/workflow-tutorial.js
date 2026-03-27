/**
 * Workflow Tutorial Engine for YAPNE
 *
 * Provides interactive, step-by-step guided tutorials as a floating dialog
 * that does NOT overlap the Properties / Simulation side-panels on the right.
 *
 * Key design decisions:
 * - Dialog is positioned at bottom-left, leaving the right side free
 * - Each step has an `editorState` that is applied before highlighting:
 *   sets editor mode, loads an example model, opens/closes panels,
 *   selects elements, switches sidebar tabs, etc.
 * - Spotlight overlay + pulse highlight on the target element
 * - Floating tooltip anchored to the highlighted element
 */
import { WORKFLOW_DEFINITIONS } from './workflow-definitions.js';

const BASE_PATH = '/YAPNE-Yet-Another-Petri-Net-Editor/';

export class WorkflowTutorial {
  constructor() {
    this.workflows = WORKFLOW_DEFINITIONS;
    this.activeWorkflow = null;
    this.currentStepIndex = -1;
    this._highlightedEl = null;
    this._lastLoadedExample = null; // track to avoid reloading same example

    // DOM nodes (created once)
    this.dialog = null;
    this.overlay = null;
    this.tooltip = null;

    this._init();
  }

  /* ════════════════════════ Initialisation ════════════════════════ */

  _init() {
    this._createDialog();
    this._createOverlay();
    this._createTooltip();
    this._renderWorkflowList();

    document.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') {
        if (this.activeWorkflow) {
          this.exitWorkflow();
        } else if (this.dialog.classList.contains('open')) {
          this.closeDialog();
        }
      }
    });

    window.addEventListener('resize', () => {
      if (this.activeWorkflow && this.currentStepIndex >= 0) {
        this._positionTooltip();
      }
    });
  }

  /* ════════════════════ Floating Dialog (bottom-left) ═════════════ */

  _createDialog() {
    this.dialog = document.createElement('div');
    this.dialog.className = 'tutorial-dialog';
    this.dialog.id = 'tutorial-dialog';
    this.dialog.innerHTML = `
      <div class="tutorial-dialog-header" id="tutorial-dialog-header">
        <div class="tutorial-dialog-header-title">
          <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <path d="M2 3h6a4 4 0 0 1 4 4v14a3 3 0 0 0-3-3H2z"/>
            <path d="M22 3h-6a4 4 0 0 0-4 4v14a3 3 0 0 1 3-3h7z"/>
          </svg>
          <span>Workflow Tutorials</span>
        </div>
        <div class="tutorial-dialog-header-actions">
          <button class="tutorial-dialog-minimize" id="tutorial-minimize" title="Minimize">─</button>
          <button class="tutorial-dialog-close-btn" id="tutorial-close" title="Close">✕</button>
        </div>
      </div>
      <div class="tutorial-dialog-body" id="tutorial-dialog-body">
        <!-- content injected dynamically -->
      </div>
    `;

    document.body.appendChild(this.dialog);

    // Make dialog draggable by its header
    this._makeDraggable();

    // Close / minimize
    this.dialog.querySelector('#tutorial-close').addEventListener('click', () => this.closeDialog());
    this.dialog.querySelector('#tutorial-minimize').addEventListener('click', () => this._toggleMinimize());
  }

  _makeDraggable() {
    const header = this.dialog.querySelector('#tutorial-dialog-header');
    let isDragging = false, startX, startY, origLeft, origTop;

    header.addEventListener('mousedown', (e) => {
      if (e.target.closest('button')) return; // don't drag when clicking buttons
      isDragging = true;
      const rect = this.dialog.getBoundingClientRect();
      startX = e.clientX;
      startY = e.clientY;
      origLeft = rect.left;
      origTop = rect.top;
      header.style.cursor = 'grabbing';
      e.preventDefault();
    });

    document.addEventListener('mousemove', (e) => {
      if (!isDragging) return;
      const dx = e.clientX - startX;
      const dy = e.clientY - startY;
      this.dialog.style.left = `${origLeft + dx}px`;
      this.dialog.style.top = `${origTop + dy}px`;
      this.dialog.style.bottom = 'auto';
      this.dialog.style.right = 'auto';
    });

    document.addEventListener('mouseup', () => {
      if (isDragging) {
        isDragging = false;
        header.style.cursor = '';
      }
    });
  }

  _toggleMinimize() {
    this.dialog.classList.toggle('minimized');
  }

  /* ════════════════════ Overlay & Tooltip ═════════════════════════ */

  _createOverlay() {
    this.overlay = document.createElement('div');
    this.overlay.className = 'tutorial-spotlight-overlay';
    this.overlay.id = 'tutorial-overlay';
    this.overlay.addEventListener('click', () => {
      if (this.activeWorkflow) this.nextStep();
    });
    document.body.appendChild(this.overlay);
  }

  _createTooltip() {
    this.tooltip = document.createElement('div');
    this.tooltip.className = 'tutorial-tooltip';
    this.tooltip.id = 'tutorial-tooltip';
    this.tooltip.innerHTML = `
      <div class="tutorial-tooltip-content">
        <div class="tutorial-tooltip-title"></div>
        <div class="tutorial-tooltip-desc"></div>
        <div class="tutorial-tooltip-tip"></div>
        <div class="tutorial-tooltip-nav">
          <button class="tutorial-nav-btn" id="tt-prev">← Prev</button>
          <span class="tutorial-nav-counter" id="tt-counter"></span>
          <button class="tutorial-nav-btn tutorial-nav-next" id="tt-next">Next →</button>
        </div>
      </div>
    `;
    document.body.appendChild(this.tooltip);

    this.tooltip.querySelector('#tt-prev').addEventListener('click', (e) => { e.stopPropagation(); this.prevStep(); });
    this.tooltip.querySelector('#tt-next').addEventListener('click', (e) => { e.stopPropagation(); this.nextStep(); });
  }

  /* ════════════════════ Workflow List (dialog body) ═══════════════ */

  _renderWorkflowList() {
    const body = this.dialog.querySelector('#tutorial-dialog-body');
    body.innerHTML = `
      <div class="tutorial-intro">
        <p>Select a workflow to get a guided, step-by-step walkthrough. The editor will be set to the correct state for each step.</p>
      </div>
      <div class="tutorial-workflow-list">
        ${this.workflows.map((wf, i) => `
          <button class="tutorial-workflow-card" data-index="${i}" style="--wf-color: ${wf.color}">
            <div class="wf-card-icon">${wf.icon}</div>
            <div class="wf-card-body">
              <div class="wf-card-title">${wf.title}</div>
              <div class="wf-card-desc">${wf.description}</div>
              <div class="wf-card-meta">
                <span class="wf-card-steps">${wf.steps.length} steps</span>
                <span class="wf-card-features">${wf.features.join(', ')}</span>
              </div>
            </div>
            <div class="wf-card-arrow">▶</div>
          </button>
        `).join('')}
      </div>
    `;

    body.querySelectorAll('.tutorial-workflow-card').forEach(card => {
      card.addEventListener('click', () => {
        this.startWorkflow(parseInt(card.dataset.index, 10));
      });
    });
  }

  /* ════════════════════ Step View (in dialog) ═════════════════════ */

  _renderStepView() {
    const wf = this.activeWorkflow;
    const body = this.dialog.querySelector('#tutorial-dialog-body');

    body.innerHTML = `
      <button class="tutorial-back-btn" id="tutorial-back">← All Workflows</button>
      <div class="tutorial-wf-header" style="--wf-color: ${wf.color}">
        <span class="tutorial-wf-icon">${wf.icon}</span>
        <div>
          <h4 class="tutorial-wf-title">${wf.title}</h4>
          <span class="tutorial-wf-features">${wf.features.join(' · ')}</span>
        </div>
      </div>
      <div class="tutorial-progress">
        <div class="tutorial-progress-bar" id="tutorial-progress-bar" style="--wf-color: ${wf.color}"></div>
      </div>
      <div class="tutorial-step-list" id="tutorial-step-list">
        ${wf.steps.map((step, i) => `
          <button class="tutorial-step-item ${i === this.currentStepIndex ? 'active' : ''} ${i < this.currentStepIndex ? 'completed' : ''}" data-step="${i}">
            <div class="step-number">${i < this.currentStepIndex ? '✓' : i + 1}</div>
            <div class="step-label">${step.title}</div>
          </button>
        `).join('')}
      </div>
      <div class="tutorial-step-detail" id="tutorial-step-detail">
        ${this._getStepDetailHTML()}
      </div>
      <div class="tutorial-bottom-nav">
        <button class="tutorial-nav-btn" id="panel-prev" ${this.currentStepIndex <= 0 ? 'disabled' : ''}>← Previous</button>
        <button class="tutorial-nav-btn tutorial-nav-next" id="panel-next">
          ${this.currentStepIndex >= wf.steps.length - 1 ? 'Finish ✓' : 'Next →'}
        </button>
      </div>
    `;

    this._updateProgress();

    body.querySelector('#tutorial-back').addEventListener('click', () => this.exitWorkflow());
    body.querySelector('#panel-prev').addEventListener('click', () => this.prevStep());
    body.querySelector('#panel-next').addEventListener('click', () => this.nextStep());

    body.querySelectorAll('.tutorial-step-item').forEach(item => {
      item.addEventListener('click', () => {
        this.goToStep(parseInt(item.dataset.step, 10));
      });
    });
  }

  _getStepDetailHTML() {
    if (!this.activeWorkflow || this.currentStepIndex < 0) return '';
    const step = this.activeWorkflow.steps[this.currentStepIndex];
    return `
      <div class="step-detail-card">
        <h4>${step.title}</h4>
        <p>${step.description}</p>
        ${step.tip ? `<div class="step-tip">💡 ${step.tip}</div>` : ''}
      </div>
    `;
  }

  _updateProgress() {
    const bar = this.dialog.querySelector('#tutorial-progress-bar');
    if (!bar || !this.activeWorkflow) return;
    const pct = ((this.currentStepIndex + 1) / this.activeWorkflow.steps.length) * 100;
    bar.style.width = `${pct}%`;
  }

  /* ════════════════════ Workflow Lifecycle ═════════════════════════ */

  startWorkflow(index) {
    this.activeWorkflow = this.workflows[index];
    this.currentStepIndex = 0;
    this._lastLoadedExample = null;
    this._renderStepView();
    this._activateStep();
  }

  exitWorkflow() {
    this._clearHighlight();
    this.activeWorkflow = null;
    this.currentStepIndex = -1;
    this._lastLoadedExample = null;
    this._renderWorkflowList();
  }

  nextStep() {
    if (!this.activeWorkflow) return;
    if (this.currentStepIndex < this.activeWorkflow.steps.length - 1) {
      this.currentStepIndex++;
      this._renderStepView();
      this._activateStep();
    } else {
      this.exitWorkflow();
    }
  }

  prevStep() {
    if (!this.activeWorkflow || this.currentStepIndex <= 0) return;
    this.currentStepIndex--;
    this._renderStepView();
    this._activateStep();
  }

  goToStep(index) {
    if (!this.activeWorkflow) return;
    this.currentStepIndex = index;
    this._renderStepView();
    this._activateStep();
  }

  /* ════════════════════ Step Activation ═══════════════════════════ */

  _activateStep() {
    const step = this.activeWorkflow.steps[this.currentStepIndex];

    // 1. Apply editor state (may be async due to example loading)
    this._applyEditorState(step.editorState || {}, () => {
      // 2. Highlight the target element
      this._highlightElement(step.highlight, step.position);
      // 3. Show tooltip
      this._showTooltip(step);
    });
  }

  /* ═════════════════ Editor State Management ═════════════════════ */

  _applyEditorState(state, callback) {
    const app = window.petriApp;
    if (!app) { callback(); return; }

    // Load example if needed (async)
    if (state.loadExample && state.loadExample !== this._lastLoadedExample) {
      this._lastLoadedExample = state.loadExample;
      const fullPath = `${BASE_PATH}${state.loadExample}`;
      app.loadTemplate(fullPath);
      // Wait for template to load and render
      setTimeout(() => {
        this._applyEditorStateSync(state, app);
        callback();
      }, 600);
      return;
    }

    this._applyEditorStateSync(state, app);
    callback();
  }

  _applyEditorStateSync(state, app) {
    // Set editor mode
    if (state.mode && app.editor) {
      app.editor.setMode(state.mode);
      // Update toolbar button active states
      this._updateToolbarButtons(state.mode);
    }

    // Sidebar control
    this._controlSidebar(state.sidebar, state.sidebarTab);

    // Properties panel
    this._controlPanel('props', state.propsPanel);

    // Simulation panel
    this._controlPanel('sim', state.simPanel);

    // Verification panel
    this._controlPanel('verify', state.verifyPanel);

    // Select an element
    if (state.selectElement && app.editor) {
      setTimeout(() => this._selectElement(state.selectElement, app), 100);
    }
  }

  _updateToolbarButtons(mode) {
    const modeMap = {
      'select': 'btn-select',
      'addPlace': 'btn-add-place',
      'addTransition': 'btn-add-transition',
      'addArc': 'btn-add-arc'
    };
    // Remove active from all
    document.querySelectorAll('.vertical-toolbar button').forEach(b => b.classList.remove('active'));
    const btnId = modeMap[mode];
    if (btnId) {
      const btn = document.getElementById(btnId);
      if (btn) btn.classList.add('active');
    }
  }

  _controlSidebar(action, tab) {
    if (!action) return;
    const sidebar = document.getElementById('sidebar');
    const toggle = document.getElementById('sidebar-toggle');
    if (!sidebar || !toggle) return;

    const isVisible = sidebar.classList.contains('sidebar-visible');

    if (action === 'open' && !isVisible) {
      toggle.click();
    } else if (action === 'close' && isVisible) {
      toggle.click();
    }

    if (tab) {
      setTimeout(() => {
        const tabBtn = document.querySelector(`.sidebar-tab[data-tab="${tab}"]`);
        if (tabBtn) tabBtn.click();
      }, 50);
    }
  }

  _controlPanel(type, action) {
    if (!action) return;

    let toggleId, panelId;
    if (type === 'props') {
      toggleId = 'props-panel-toggle';
      panelId = 'props-panel';
    } else if (type === 'sim') {
      toggleId = 'sim-panel-toggle';
      panelId = 'sim-dashboard';
    } else if (type === 'verify') {
      toggleId = 'verify-panel-toggle';
      panelId = 'verify-panel';
    }

    const panel = document.getElementById(panelId);
    const toggle = document.getElementById(toggleId);
    if (!panel || !toggle) return;

    const isOpen = panel.classList.contains('open');

    if (action === 'open' && !isOpen) {
      toggle.click();
    } else if (action === 'close' && isOpen) {
      toggle.click();
    }
  }

  _selectElement(which, app) {
    const net = app.editor?.petriNet;
    if (!net) return;

    let id = null, type = null;

    if (which === 'firstPlace') {
      const first = net.places?.values().next().value;
      if (first) { id = first.id; type = 'place'; }
    } else if (which === 'firstTransition') {
      const first = net.transitions?.values().next().value;
      if (first) { id = first.id; type = 'transition'; }
    } else if (which === 'firstArc') {
      const first = net.arcs?.values().next().value;
      if (first) { id = first.id; type = 'arc'; }
    }

    if (id && type) {
      app.editor.selectElement(id, type);
      if (app.handleElementSelected) {
        app.handleElementSelected(id, type);
      }
    }
  }

  /* ═════════════════ Element Highlighting ═════════════════════════ */

  _highlightElement(selector, position) {
    this._clearHighlight();
    if (!selector) return;

    const el = document.querySelector(selector);
    if (!el) {
      this.overlay.classList.remove('visible');
      return;
    }

    this._highlightedEl = el;
    el.classList.add('tutorial-highlight');
    this._positionSpotlight(el);
    this.overlay.classList.add('visible');
  }

  _clearHighlight() {
    if (this._highlightedEl) {
      this._highlightedEl.classList.remove('tutorial-highlight');
      this._highlightedEl = null;
    }
    this.overlay.classList.remove('visible');
    this.tooltip.classList.remove('visible');
  }

  _positionSpotlight(el) {
    const rect = el.getBoundingClientRect();
    const pad = 8;
    const top = rect.top - pad;
    const left = rect.left - pad;
    const bottom = rect.bottom + pad;
    const right = rect.right + pad;

    this.overlay.style.clipPath = `polygon(
      0% 0%, 0% 100%, ${left}px 100%, ${left}px ${top}px,
      ${right}px ${top}px, ${right}px ${bottom}px, ${left}px ${bottom}px,
      ${left}px 100%, 100% 100%, 100% 0%
    )`;
  }

  /* ═════════════════ Tooltip ══════════════════════════════════════ */

  _showTooltip(step) {
    const titleEl = this.tooltip.querySelector('.tutorial-tooltip-title');
    const descEl = this.tooltip.querySelector('.tutorial-tooltip-desc');
    const tipEl = this.tooltip.querySelector('.tutorial-tooltip-tip');
    const counterEl = this.tooltip.querySelector('#tt-counter');

    titleEl.textContent = step.title;
    descEl.innerHTML = step.description;
    tipEl.innerHTML = step.tip ? `💡 ${step.tip}` : '';
    tipEl.style.display = step.tip ? 'block' : 'none';
    counterEl.textContent = `${this.currentStepIndex + 1} / ${this.activeWorkflow.steps.length}`;

    this.tooltip.querySelector('#tt-prev').disabled = this.currentStepIndex <= 0;
    const nextBtn = this.tooltip.querySelector('#tt-next');
    nextBtn.textContent = this.currentStepIndex >= this.activeWorkflow.steps.length - 1 ? 'Finish ✓' : 'Next →';

    this.tooltip.dataset.position = step.position || 'bottom';
    this.tooltip.classList.add('visible');

    requestAnimationFrame(() => this._positionTooltip());
  }

  _positionTooltip() {
    if (!this._highlightedEl) {
      this.tooltip.style.left = '50%';
      this.tooltip.style.top = '40%';
      this.tooltip.style.transform = 'translate(-50%, -50%)';
      return;
    }

    const elRect = this._highlightedEl.getBoundingClientRect();
    const ttRect = this.tooltip.getBoundingClientRect();
    const pos = this.tooltip.dataset.position || 'bottom';
    const gap = 16;
    let left, top;

    switch (pos) {
      case 'right':
        left = elRect.right + gap;
        top = elRect.top + (elRect.height / 2) - (ttRect.height / 2);
        break;
      case 'left':
        left = elRect.left - ttRect.width - gap;
        top = elRect.top + (elRect.height / 2) - (ttRect.height / 2);
        break;
      case 'top':
        left = elRect.left + (elRect.width / 2) - (ttRect.width / 2);
        top = elRect.top - ttRect.height - gap;
        break;
      default:
        left = elRect.left + (elRect.width / 2) - (ttRect.width / 2);
        top = elRect.bottom + gap;
        break;
    }

    // Keep within viewport, also avoid overlapping the dialog
    const vw = window.innerWidth;
    const vh = window.innerHeight;
    const dialogRect = this.dialog.getBoundingClientRect();
    if (left < 10) left = 10;
    if (left + ttRect.width > vw - 10) left = vw - ttRect.width - 10;
    if (top < 10) top = 10;
    if (top + ttRect.height > vh - 10) top = vh - ttRect.height - 10;

    // If tooltip overlaps the dialog, shift it up
    if (top + ttRect.height > dialogRect.top && left < dialogRect.right && left + ttRect.width > dialogRect.left) {
      top = dialogRect.top - ttRect.height - 10;
      if (top < 10) top = 10;
    }

    this.tooltip.style.left = `${left}px`;
    this.tooltip.style.top = `${top}px`;
    this.tooltip.style.transform = 'none';
  }

  /* ═════════════════ Dialog Open / Close ══════════════════════════ */

  openDialog() {
    this.dialog.classList.add('open');
    this.dialog.classList.remove('minimized');
  }

  closeDialog() {
    this._clearHighlight();
    if (this.activeWorkflow) {
      this.activeWorkflow = null;
      this.currentStepIndex = -1;
      this._renderWorkflowList();
    }
    this.dialog.classList.remove('open');
  }

  toggle() {
    if (this.dialog.classList.contains('open')) {
      this.closeDialog();
    } else {
      this.openDialog();
    }
  }
}

/* ═════════════════════ Auto-initialise ═════════════════════════════ */
let tutorialInstance = null;

export function initWorkflowTutorial() {
  if (!tutorialInstance) {
    tutorialInstance = new WorkflowTutorial();
  }
  return tutorialInstance;
}

export function getWorkflowTutorial() {
  return tutorialInstance;
}
