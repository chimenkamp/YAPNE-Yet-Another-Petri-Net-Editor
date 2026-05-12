import {
  analyzeCoverabilityTree,
  analyzeReachabilityGraph,
  analyzeStructuralProperties,
  formatAnalysisMarking,
  renderStateSpaceSvg,
  renderStructuralSvg
} from './petri-net-analysis.js';

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}

/**
 * Generation Panel Module
 *
 * A toggleable side panel for event-log and WebPPL generation actions.
 */

export class GenerationPanel {
  constructor(app) {
    this.app = app;
    this.isOpen = false;
    this.panel = null;
    this.toggleBtn = null;
    this.stateSpaceDialog = null;
    this.structuralDialog = null;
    this.selectedStructuralComponents = new Set();

    this._init();
  }

  _init() {
    this._createToggleButton();
    this._createPanel();
  }

  _createToggleButton() {
    this.toggleBtn = document.createElement('button');
    this.toggleBtn.className = 'side-panel-toggle generation-toggle';
    this.toggleBtn.id = 'generation-panel-toggle';
    this.toggleBtn.innerHTML = `
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <path d="M4 19V5"/>
        <path d="M4 5h12l-2 4 2 4H4"/>
        <path d="M18 19v-7"/>
        <path d="M15 16h6"/>
      </svg>
      <span class="toggle-label">Generation</span>
    `;
    this.toggleBtn.title = 'Toggle Generation Panel';
    this.toggleBtn.addEventListener('click', () => this.toggle());

    const container = document.querySelector('.canvas-container');
    if (container) container.appendChild(this.toggleBtn);
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'generation-panel side-panel';
    this.panel.id = 'generation-panel';
    this.panel.innerHTML = `
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <path d="M4 19V5"/>
            <path d="M4 5h12l-2 4 2 4H4"/>
            <path d="M18 19v-7"/>
            <path d="M15 16h6"/>
          </svg>
          <h3>Generation</h3>
        </div>
        <button class="panel-close" id="generation-panel-close" title="Close">✕</button>
      </div>
      <div class="panel-body">
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M3 3v18h18"/>
                <path d="M7 14l3-3 3 2 5-6"/>
              </svg>
            </span>
            <span>Event Log</span>
          </div>
          <div class="dash-section-body">
            <div class="generation-actions">
              <button id="btn-event-log" class="sim-btn sim-btn-primary" title="Generate an event log">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M14 2H6a2 2 0 0 0-2 2v16a2 2 0 0 0 2 2h12a2 2 0 0 0 2-2V8z"/>
                  <path d="M14 2v6h6"/>
                  <path d="M8 13h8"/>
                  <path d="M8 17h5"/>
                </svg>
                Generate Event Log
              </button>
              <button id="btn-view-webppl" class="sim-btn generation-secondary-btn" title="View generated WebPPL code">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M16 18l6-6-6-6"/>
                  <path d="M8 6l-6 6 6 6"/>
                </svg>
                View WebPPL Code
              </button>
            </div>
          </div>
        </div>
        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <circle cx="5" cy="12" r="3"/>
                <circle cx="19" cy="5" r="3"/>
                <circle cx="19" cy="19" r="3"/>
                <path d="M8 11l8-5"/>
                <path d="M8 13l8 5"/>
              </svg>
            </span>
            <span>Analysis</span>
          </div>
          <div class="dash-section-body">
            <div class="generation-actions">
              <button id="btn-state-space-analysis" class="sim-btn generation-analysis-btn" title="Open marking graph and coverability tree analysis">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M12 3v4"/>
                  <path d="M6 11l-3 3 3 3"/>
                  <path d="M18 11l3 3-3 3"/>
                  <circle cx="12" cy="7" r="3"/>
                  <circle cx="5" cy="14" r="3"/>
                  <circle cx="19" cy="14" r="3"/>
                  <path d="M10 9l-3 3"/>
                  <path d="M14 9l3 3"/>
                </svg>
                Marking Graphs & Trees
              </button>
              <button id="btn-structural-analysis" class="sim-btn generation-analysis-btn alt" title="Open S-components, S-coverability, and free-choice analysis">
                <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                  <path d="M4 7h6"/>
                  <path d="M14 7h6"/>
                  <path d="M10 7a2 2 0 0 0 4 0"/>
                  <path d="M7 7v10"/>
                  <path d="M17 7v10"/>
                  <circle cx="7" cy="17" r="3"/>
                  <circle cx="17" cy="17" r="3"/>
                </svg>
                S-Components & Free Choice
              </button>
            </div>
          </div>
        </div>
      </div>
    `;

    const editorContainer = document.querySelector('.editor-container');
    if (editorContainer) editorContainer.appendChild(this.panel);

    const closeBtn = this.panel.querySelector('#generation-panel-close');
    if (closeBtn) closeBtn.addEventListener('click', () => this.close());

    const stateSpaceBtn = this.panel.querySelector('#btn-state-space-analysis');
    if (stateSpaceBtn) stateSpaceBtn.addEventListener('click', () => this.openStateSpaceDialog());

    const structuralBtn = this.panel.querySelector('#btn-structural-analysis');
    if (structuralBtn) structuralBtn.addEventListener('click', () => this.openStructuralDialog());
  }

  getNet() {
    return this.app?.api?.petriNet;
  }

  openStateSpaceDialog() {
    if (this.stateSpaceDialog) {
      this.stateSpaceDialog.remove();
      this.stateSpaceDialog = null;
    }

    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay analysis-modal-overlay';
    dialog.id = 'state-space-analysis-dialog';
    dialog.innerHTML = `
      <div class="modal-container analysis-modal-container">
        <div class="modal-header analysis-modal-header">
          <div>
            <h2>Marking Graphs & Coverability Trees</h2>
            <p>Explore reachable markings, deadlocks, and unbounded growth from the current initial marking.</p>
          </div>
          <button class="close-btn" id="state-space-close">&times;</button>
        </div>
        <div class="modal-body analysis-modal-body">
          <div class="analysis-toolbar">
            <div class="analysis-segmented" role="tablist" aria-label="State space mode">
              <button class="active" data-mode="reachability">Marking Graph</button>
              <button data-mode="coverability">Coverability Tree</button>
            </div>
            <label>
              Max states
              <input id="analysis-max-nodes" type="number" min="10" max="600" value="140">
            </label>
            <label>
              Token cap
              <input id="analysis-token-limit" type="number" min="1" max="1000" value="50">
            </label>
            <button class="analysis-icon-btn" id="state-space-refresh" title="Recompute">
              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M21 12a9 9 0 0 1-15.5 6.3"/>
                <path d="M3 12A9 9 0 0 1 18.5 5.7"/>
                <path d="M3 19v-5h5"/>
                <path d="M21 5v5h-5"/>
              </svg>
            </button>
          </div>
          <div id="state-space-summary" class="analysis-summary-grid"></div>
          <div id="state-space-visual" class="analysis-visual"></div>
          <div id="state-space-details" class="analysis-details"></div>
        </div>
      </div>
    `;

    document.body.appendChild(dialog);
    this.stateSpaceDialog = dialog;

    const close = () => {
      dialog.remove();
      this.stateSpaceDialog = null;
    };

    dialog.querySelector('#state-space-close')?.addEventListener('click', close);
    dialog.addEventListener('click', event => {
      if (event.target === dialog) close();
    });

    dialog.querySelectorAll('.analysis-segmented button').forEach(button => {
      button.addEventListener('click', () => {
        dialog.querySelectorAll('.analysis-segmented button').forEach(item => item.classList.remove('active'));
        button.classList.add('active');
        this.renderStateSpaceDialog();
      });
    });

    dialog.querySelector('#state-space-refresh')?.addEventListener('click', () => this.renderStateSpaceDialog());
    dialog.querySelector('#analysis-max-nodes')?.addEventListener('change', () => this.renderStateSpaceDialog());
    dialog.querySelector('#analysis-token-limit')?.addEventListener('change', () => this.renderStateSpaceDialog());

    this.renderStateSpaceDialog();
  }

  renderStateSpaceDialog() {
    const dialog = this.stateSpaceDialog;
    const net = this.getNet();
    if (!dialog || !net) return;

    const mode = dialog.querySelector('.analysis-segmented button.active')?.dataset.mode || 'reachability';
    const maxNodes = Math.max(10, parseInt(dialog.querySelector('#analysis-max-nodes')?.value || '140', 10));
    const tokenLimit = Math.max(1, parseInt(dialog.querySelector('#analysis-token-limit')?.value || '50', 10));
    const analysis = mode === 'coverability'
      ? analyzeCoverabilityTree(net, { maxNodes })
      : analyzeReachabilityGraph(net, { maxNodes, tokenLimit });

    const summary = dialog.querySelector('#state-space-summary');
    const visual = dialog.querySelector('#state-space-visual');
    const details = dialog.querySelector('#state-space-details');

    const boundedCopy = mode === 'coverability'
      ? `${analysis.stats.unboundedPlaces} unbounded places`
      : `${analysis.stats.deadlocks} deadlock markings`;

    summary.innerHTML = `
      <div class="analysis-stat-card"><span>States</span><strong>${analysis.stats.states}</strong></div>
      <div class="analysis-stat-card"><span>Edges</span><strong>${analysis.stats.edges}</strong></div>
      <div class="analysis-stat-card ${analysis.truncated ? 'warn' : 'ok'}"><span>Status</span><strong>${analysis.truncated ? 'Truncated' : 'Complete'}</strong></div>
      <div class="analysis-stat-card"><span>${mode === 'coverability' ? 'Growth' : 'Deadlocks'}</span><strong>${boundedCopy}</strong></div>
    `;

    visual.innerHTML = renderStateSpaceSvg(analysis, {
      title: mode === 'coverability' ? 'Coverability Tree' : 'Marking Graph',
      tree: mode === 'coverability'
    });

    const notableNodes = mode === 'coverability'
      ? analysis.nodes.filter(node => node.marking.includes('w')).slice(0, 8)
      : analysis.nodes.filter(node => node.deadlock).slice(0, 8);

    details.innerHTML = `
      <div class="analysis-note ${analysis.truncated ? 'warn' : ''}">
        ${analysis.truncated
          ? 'The exploration hit the configured limit. Increase the state limit or use the coverability tree for unbounded nets.'
          : mode === 'coverability'
            ? 'ω marks places that can grow without a finite upper bound along the explored branch.'
            : 'The marking graph is finite within the selected limits.'}
      </div>
      <div class="analysis-marking-table">
        <h3>${mode === 'coverability' ? 'Unbounded Markings' : 'Deadlock Markings'}</h3>
        ${notableNodes.length
          ? notableNodes.map(node => `
            <div class="analysis-marking-row">
              <strong>${node.name}</strong>
              <span>${formatAnalysisMarking(node.marking, analysis.places)}</span>
            </div>
          `).join('')
          : '<div class="analysis-empty compact">No notable markings in this run.</div>'}
      </div>
    `;
  }

  openStructuralDialog() {
    if (this.structuralDialog) {
      this.structuralDialog.remove();
      this.structuralDialog = null;
    }

    const dialog = document.createElement('div');
    dialog.className = 'modal-overlay analysis-modal-overlay';
    dialog.id = 'structural-analysis-dialog';
    dialog.innerHTML = `
      <div class="modal-container analysis-modal-container">
        <div class="modal-header analysis-modal-header">
          <div>
            <h2>S-Components & Free Choice</h2>
            <p>Inspect structural state-machine components, S-coverability, and free-choice conflicts.</p>
          </div>
          <button class="close-btn" id="structural-close">&times;</button>
        </div>
        <div class="modal-body analysis-modal-body">
          <div class="analysis-toolbar">
            <button class="analysis-icon-btn wide" id="structural-refresh" title="Recompute structural analysis">
              <svg width="16" height="16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M21 12a9 9 0 0 1-15.5 6.3"/>
                <path d="M3 12A9 9 0 0 1 18.5 5.7"/>
                <path d="M3 19v-5h5"/>
                <path d="M21 5v5h-5"/>
              </svg>
              Recompute
            </button>
          </div>
          <div id="structural-summary" class="analysis-summary-grid"></div>
          <div id="structural-visual" class="analysis-visual"></div>
          <div id="structural-details" class="analysis-details structural-details"></div>
        </div>
      </div>
    `;

    document.body.appendChild(dialog);
    this.structuralDialog = dialog;

    const close = () => {
      dialog.remove();
      this.structuralDialog = null;
    };

    dialog.querySelector('#structural-close')?.addEventListener('click', close);
    dialog.addEventListener('click', event => {
      if (event.target === dialog) close();
    });
    dialog.querySelector('#structural-refresh')?.addEventListener('click', () => this.renderStructuralDialog());

    this.renderStructuralDialog();
  }

  getStructuralHighlightColors() {
    return ['#88C0D0', '#A3BE8C', '#B48EAD', '#EBCB8B', '#D08770', '#81A1C1', '#BF616A'];
  }

  labelIds(ids, elements) {
    return ids
      .map(id => elements.get(id)?.label || id)
      .join(', ');
  }

  applyStructuralHighlights(analysis) {
    const colors = this.getStructuralHighlightColors();
    const components = analysis.sComponents
      .map((component, index) => ({ ...component, color: colors[index % colors.length] }))
      .filter((_, index) => this.selectedStructuralComponents.has(index));

    this.app?.editor?.renderer?.setStructuralHighlights(components);
    this.app?.editor?.render({ updateEnabled: false });
  }

  clearStructuralHighlights() {
    this.selectedStructuralComponents.clear();
    this.app?.editor?.renderer?.clearStructuralHighlights();
    this.app?.editor?.render({ updateEnabled: false });
  }

  renderStructuralDialog() {
    const dialog = this.structuralDialog;
    const net = this.getNet();
    if (!dialog || !net) return;

    const analysis = analyzeStructuralProperties(net);
    const summary = dialog.querySelector('#structural-summary');
    const visual = dialog.querySelector('#structural-visual');
    const details = dialog.querySelector('#structural-details');

    summary.innerHTML = `
      <div class="analysis-stat-card"><span>S-components</span><strong>${analysis.sComponents.length}</strong></div>
      <div class="analysis-stat-card ${analysis.isWorkflowNet ? 'ok' : 'warn'}"><span>Workflow net</span><strong>${analysis.isWorkflowNet ? 'Yes' : 'No'}</strong></div>
      <div class="analysis-stat-card ${analysis.isSCoverable ? 'ok' : 'warn'}"><span>S-coverable</span><strong>${analysis.isSCoverable ? 'Yes' : 'No'}</strong></div>
      <div class="analysis-stat-card ${analysis.isFreeChoice ? 'ok' : 'warn'}"><span>Free-choice</span><strong>${analysis.isFreeChoice ? 'Yes' : 'No'}</strong></div>
      <div class="analysis-stat-card"><span>Uncovered places</span><strong>${analysis.uncoveredPlaces.length}</strong></div>
    `;

    visual.innerHTML = renderStructuralSvg(analysis);

    const placesById = new Map(analysis.places.map(place => [place.id, place]));
    const transitionsById = new Map(analysis.transitions.map(transition => [transition.id, transition]));
    const colors = this.getStructuralHighlightColors();
    this.selectedStructuralComponents = new Set(
      [...this.selectedStructuralComponents].filter(index => index < analysis.sComponents.length)
    );

    const componentList = analysis.sComponents.length
      ? analysis.sComponents.map((component, index) => `
        <div class="analysis-component-row selectable ${this.selectedStructuralComponents.has(index) ? 'selected' : ''}">
          <label class="analysis-component-select">
            <input type="checkbox" class="structural-component-checkbox" data-component-index="${index}" ${this.selectedStructuralComponents.has(index) ? 'checked' : ''}>
            <span class="analysis-component-color" style="--component-color:${colors[index % colors.length]}"></span>
            <strong>S${index + 1}</strong>
          </label>
          <span>Places: ${escapeHtml(this.labelIds(component.placeIds, placesById) || 'none')}</span>
          <span>Transitions: ${escapeHtml(this.labelIds(component.transitionIds, transitionsById) || 'none')}${component.usesShortCircuit ? ' + short-circuit' : ''}</span>
        </div>
      `).join('')
      : '<div class="analysis-empty compact">No S-components detected in this net.</div>';

    const violations = analysis.freeChoiceViolations.length
      ? analysis.freeChoiceViolations.map(item => `
        <div class="analysis-component-row warn">
          <strong>${escapeHtml(item.placeId)} → ${escapeHtml(item.transitionId)}</strong>
          <span>Transition preset: { ${escapeHtml(item.inputs.join(', ') || 'none')} }</span>
        </div>
      `).join('')
      : '<div class="analysis-empty compact">No free-choice violations detected.</div>';

    const workflowWarning = analysis.isWorkflowNet ? '' : `
      <div class="analysis-note warn">
        S-components are formally defined for workflow nets. ${analysis.workflowNetIssues.map(issue => escapeHtml(issue)).join(' ')}
      </div>
    `;

    details.innerHTML = `
      ${workflowWarning}
      <div class="analysis-two-column">
        <section>
          <h3>S-components</h3>
          <div class="analysis-component-actions">
            <button id="structural-show-selected" class="sim-btn sim-btn-primary" ${analysis.sComponents.length ? '' : 'disabled'}>Show in Model</button>
            <button id="structural-clear-selected" class="sim-btn generation-secondary-btn">Clear</button>
          </div>
          ${componentList}
        </section>
        <section>
          <h3>Free-choice checks</h3>
          ${violations}
          ${analysis.uncoveredPlaces.length ? `
            <div class="analysis-note warn">
              Uncovered places: ${escapeHtml(analysis.uncoveredPlaces.map(place => place.label || place.id).join(', '))}
            </div>
          ` : ''}
        </section>
      </div>
    `;

    details.querySelectorAll('.structural-component-checkbox').forEach(checkbox => {
      checkbox.addEventListener('change', event => {
        const index = Number(event.currentTarget.dataset.componentIndex);
        if (event.currentTarget.checked) {
          this.selectedStructuralComponents.add(index);
        } else {
          this.selectedStructuralComponents.delete(index);
        }
        event.currentTarget.closest('.analysis-component-row')?.classList.toggle('selected', event.currentTarget.checked);
      });
    });

    details.querySelector('#structural-show-selected')?.addEventListener('click', () => {
      this.applyStructuralHighlights(analysis);
    });

    details.querySelector('#structural-clear-selected')?.addEventListener('click', () => {
      details.querySelectorAll('.structural-component-checkbox').forEach(checkbox => {
        checkbox.checked = false;
        checkbox.closest('.analysis-component-row')?.classList.remove('selected');
      });
      this.clearStructuralHighlights();
    });
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

  _updateLayout() {
    document.dispatchEvent(new CustomEvent('side-panel-changed'));
  }

  destroy() {
    if (this.stateSpaceDialog) this.stateSpaceDialog.remove();
    if (this.structuralDialog) this.structuralDialog.remove();
    if (this.panel && this.panel.parentNode) {
      this.panel.parentNode.removeChild(this.panel);
    }
    if (this.toggleBtn && this.toggleBtn.parentNode) {
      this.toggleBtn.parentNode.removeChild(this.toggleBtn);
    }
  }
}

export default GenerationPanel;
