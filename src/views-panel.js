/**
 * Views Panel Module
 *
 * Manages named graphical views over one canonical Petri net.
 * Views keep independent layout/viewport data while referencing the same
 * places, transitions, arcs, markings, guards, and labels.
 */

export class ViewsPanel {
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
    this.toggleBtn.className = 'side-panel-toggle views-toggle';
    this.toggleBtn.id = 'views-panel-toggle';
    this.toggleBtn.innerHTML = `
      <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <rect x="3" y="3" width="7" height="7"/><rect x="14" y="3" width="7" height="7"/>
        <rect x="3" y="14" width="7" height="7"/><path d="M14 17h7"/><path d="M17.5 13.5v7"/>
      </svg>
      <span class="toggle-label">Views</span>
    `;
    this.toggleBtn.title = 'Toggle Views Panel';
    this.toggleBtn.addEventListener('click', () => this.toggle());

    const container = document.querySelector('.canvas-container');
    if (container) container.appendChild(this.toggleBtn);
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'views-panel side-panel';
    this.panel.id = 'views-panel';
    this.panel.innerHTML = `
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <rect x="3" y="3" width="7" height="7"/><rect x="14" y="3" width="7" height="7"/>
            <rect x="3" y="14" width="7" height="7"/><path d="M14 17h7"/><path d="M17.5 13.5v7"/>
          </svg>
          <h3>Views</h3>
        </div>
        <button class="panel-close" id="views-panel-close" title="Close">✕</button>
      </div>
      <div class="panel-body">
        <div id="views-content" class="views-content"></div>
      </div>
    `;

    const editorContainer = document.querySelector('.editor-container');
    if (editorContainer) editorContainer.appendChild(this.panel);

    this.contentEl = this.panel.querySelector('#views-content');
    this.panel.querySelector('#views-panel-close')?.addEventListener('click', () => this.close());
    this.contentEl.addEventListener('click', (event) => this._handleClick(event));
    this.refresh();
  }

  toggle() {
    if (this.isOpen) this.close();
    else this.open();
  }

  open() {
    this.isOpen = true;
    this.panel.classList.add('open');
    this.toggleBtn.classList.add('active');
    this.refresh();
    this._updateLayout();
  }

  close() {
    this.isOpen = false;
    this.panel.classList.remove('open');
    this.toggleBtn.classList.remove('active');
    this._updateLayout();
  }

  refresh() {
    if (!this.contentEl || !this.app?.api?.petriNet) return;

    const views = this.app.api.getViews ? this.app.api.getViews() : [];
    const activeView = this.app.api.getActiveView ? this.app.api.getActiveView() : null;
    const selectedCount = this.app.editor?.selectedElements?.size || 0;
    const selected = selectedCount > 0 ? selectedCount : (this.app.editor?.selectedElement ? 1 : 0);

    this.contentEl.innerHTML = `
      <div class="dash-section">
        <div class="dash-section-header">
          <span class="dash-icon">
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
              <path d="M12 5v14"/><path d="M5 12h14"/>
            </svg>
          </span>
          <span>Create</span>
        </div>
        <div class="dash-section-body views-actions">
          <button class="sim-btn sim-btn-primary" data-action="create-selection">Selection View</button>
          <button class="sim-btn sim-btn-secondary" data-action="create-transition">Transition View</button>
          <button class="sim-btn sim-btn-secondary" data-action="add-selection">Add Selection</button>
          <p class="views-hint">${selected} selected element${selected === 1 ? '' : 's'}</p>
        </div>
      </div>

      <div class="dash-section">
        <div class="dash-section-header">
          <span class="dash-icon">
            <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
              <path d="M3 6h18"/><path d="M3 12h18"/><path d="M3 18h18"/>
            </svg>
          </span>
          <span>Canvas Tree</span>
          <span class="dash-badge">${views.length}</span>
        </div>
        <div class="dash-section-body">
          <div class="views-list">
            ${views.map(view => this._renderViewRow(view, activeView?.id)).join('')}
          </div>
        </div>
      </div>
    `;
  }

  _renderViewRow(view, activeViewId) {
    const isActive = view.id === activeViewId;
    const nodeCount = view.includeAll ? this._allNodeCount() : (view.elementIds || []).length;
    const arcCount = view.includeAll ? this.app.api.petriNet.arcs.size : (view.arcIds || []).length;
    const readonly = view.id === 'main';

    return `
      <div class="views-row ${isActive ? 'active' : ''}" data-view-id="${this._escapeAttr(view.id)}">
        <button class="views-open" data-action="switch" data-view-id="${this._escapeAttr(view.id)}" title="Open view">
          <span class="views-name">${this._escapeHTML(view.name)}</span>
          <span class="views-meta">${nodeCount} nodes · ${arcCount} arcs</span>
        </button>
        <div class="views-row-actions">
          <button class="views-icon-btn" data-action="rename" data-view-id="${this._escapeAttr(view.id)}" title="Rename" ${readonly ? 'disabled' : ''}>
            <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 20h9"/><path d="M16.5 3.5a2.1 2.1 0 0 1 3 3L7 19l-4 1 1-4Z"/></svg>
          </button>
          <button class="views-icon-btn danger" data-action="delete" data-view-id="${this._escapeAttr(view.id)}" title="Delete" ${readonly ? 'disabled' : ''}>
            <svg width="13" height="13" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M3 6h18"/><path d="M8 6V4h8v2"/><path d="M19 6l-1 14H6L5 6"/></svg>
          </button>
        </div>
      </div>
    `;
  }

  _handleClick(event) {
    const button = event.target.closest('button[data-action]');
    if (!button) return;

    const action = button.dataset.action;
    const viewId = button.dataset.viewId;

    if (action === 'switch') {
      this._switchView(viewId);
    } else if (action === 'create-selection') {
      this._createSelectionView();
    } else if (action === 'create-transition') {
      this._createTransitionView();
    } else if (action === 'add-selection') {
      this._addSelection();
    } else if (action === 'rename') {
      this._renameView(viewId);
    } else if (action === 'delete') {
      this._deleteView(viewId);
    }
  }

  _switchView(viewId) {
    if (!this.app.api.switchView(viewId)) return;
    this.app.updateZoomDisplay?.();
    this.app.updateSelectedElementProperties?.();
    this.refresh();
  }

  _createSelectionView() {
    const name = window.prompt('Name for this view:', `View ${this.app.api.getViews().length}`);
    if (name === null) return;
    const view = this.app.api.createViewFromSelection(name.trim());
    if (!view) {
      window.alert('Select one or more places/transitions first.');
      return;
    }
    this.app._takeSnapshot?.(`Create view ${view.name}`);
    this.app.updateZoomDisplay?.();
    this.refresh();
  }

  _createTransitionView() {
    const name = window.prompt('Name for this transition view:', `Transition View ${this.app.api.getViews().length}`);
    if (name === null) return;
    const view = this.app.api.createViewFromSelectedTransitions(name.trim());
    if (!view) {
      window.alert('Select one or more transitions first.');
      return;
    }
    this.app._takeSnapshot?.(`Create view ${view.name}`);
    this.app.updateZoomDisplay?.();
    this.refresh();
  }

  _addSelection() {
    if (!this.app.api.addSelectionToActiveView()) {
      window.alert('Open a child view and select one or more places/transitions first.');
      return;
    }
    this.app._takeSnapshot?.('Add selection to view');
    this.refresh();
  }

  _renameView(viewId) {
    const view = this.app.api.petriNet.getView(viewId);
    if (!view || view.id === 'main') return;
    const nextName = window.prompt('Rename view:', view.name);
    if (nextName === null) return;
    if (this.app.api.renameView(viewId, nextName.trim())) {
      this.app._takeSnapshot?.(`Rename view ${nextName.trim()}`);
      this.refresh();
    }
  }

  _deleteView(viewId) {
    const view = this.app.api.petriNet.getView(viewId);
    if (!view || view.id === 'main') return;
    if (!window.confirm(`Delete view "${view.name}"? This only removes the graphical view.`)) return;
    if (this.app.api.deleteView(viewId)) {
      this.app._takeSnapshot?.(`Delete view ${view.name}`);
      this.app.updateZoomDisplay?.();
      this.refresh();
    }
  }

  _allNodeCount() {
    return this.app.api.petriNet.places.size + this.app.api.petriNet.transitions.size;
  }

  _escapeHTML(value) {
    return String(value ?? '')
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&#39;');
  }

  _escapeAttr(value) {
    return this._escapeHTML(value);
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

export default ViewsPanel;
