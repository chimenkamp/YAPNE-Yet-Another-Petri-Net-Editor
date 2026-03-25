/**
 * History Dialog – side-panel listing past undoable actions
 */
import { ActionHistory } from './action-history.js';

export class HistoryDialog {
  /**
   * @param {ActionHistory} actionHistory
   * @param {function} onHistoryNav – called after any undo/redo so the app can re-render
   */
  constructor(actionHistory, onHistoryNav) {
    this.history = actionHistory;
    this.onHistoryNav = onHistoryNav;
    this._panel = null;
    this._listEl = null;
    this._visible = false;
  }

  /** Create DOM (called once). Appends a fixed side-panel to the body. */
  init() {
    if (this._panel) return;

    // Inject styles
    const style = document.createElement('style');
    style.textContent = `
      .history-panel {
        position: fixed;
        top: 0;
        right: -340px;
        width: 320px;
        height: 100vh;
        background: #3B4252;
        border-left: 2px solid #4C566A;
        z-index: 9000;
        display: flex;
        flex-direction: column;
        transition: right 0.25s ease;
        box-shadow: -4px 0 16px rgba(0,0,0,0.4);
        font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif;
      }
      .history-panel.open { right: 0; }
      .history-panel-header {
        background: #434C5E;
        padding: 14px 16px;
        display: flex;
        justify-content: space-between;
        align-items: center;
        border-bottom: 1px solid #4C566A;
      }
      .history-panel-header h3 {
        margin: 0;
        color: #ECEFF4;
        font-size: 15px;
      }
      .history-panel-close {
        background: none;
        border: none;
        color: #D8DEE9;
        font-size: 20px;
        cursor: pointer;
        border-radius: 4px;
        width: 28px;
        height: 28px;
        display: flex;
        align-items: center;
        justify-content: center;
      }
      .history-panel-close:hover { background: #4C566A; }
      .history-panel-actions {
        display: flex;
        gap: 6px;
        padding: 10px 16px;
        border-bottom: 1px solid #4C566A;
      }
      .history-panel-actions button {
        flex: 1;
        padding: 6px 0;
        border: 1px solid #4C566A;
        background: #434C5E;
        color: #D8DEE9;
        border-radius: 4px;
        cursor: pointer;
        font-size: 13px;
      }
      .history-panel-actions button:disabled {
        opacity: 0.4;
        cursor: default;
      }
      .history-panel-actions button:not(:disabled):hover {
        background: #4C566A;
      }
      .history-list {
        flex: 1;
        overflow-y: auto;
        padding: 8px;
      }
      .history-list::-webkit-scrollbar { width: 6px; }
      .history-list::-webkit-scrollbar-thumb { background: #4C566A; border-radius: 3px; }
      .history-item {
        display: flex;
        align-items: center;
        gap: 10px;
        padding: 8px 10px;
        border-radius: 6px;
        cursor: pointer;
        margin-bottom: 2px;
        transition: background 0.15s;
      }
      .history-item:hover { background: rgba(136,192,208,0.12); }
      .history-item-icon { font-size: 16px; flex-shrink: 0; }
      .history-item-label {
        flex: 1;
        color: #D8DEE9;
        font-size: 13px;
        white-space: nowrap;
        overflow: hidden;
        text-overflow: ellipsis;
      }
      .history-item-time {
        color: #81A1C1;
        font-size: 11px;
        flex-shrink: 0;
      }
      .history-item.future-item { opacity: 0.45; }
      .history-empty {
        text-align: center;
        color: #81A1C1;
        padding: 40px 16px;
        font-size: 13px;
        font-style: italic;
      }
      .history-separator {
        text-align: center;
        color: #5E81AC;
        font-size: 11px;
        font-weight: 600;
        text-transform: uppercase;
        letter-spacing: 1px;
        padding: 6px 0;
        border-bottom: 1px solid #4C566A;
        margin: 4px 0;
      }
    `;
    document.head.appendChild(style);

    // Build DOM
    this._panel = document.createElement('div');
    this._panel.className = 'history-panel';
    this._panel.innerHTML = `
      <div class="history-panel-header">
        <h3>📜 Action History</h3>
        <button class="history-panel-close" title="Close">×</button>
      </div>
      <div class="history-panel-actions">
        <button id="hist-undo-btn">↩ Undo</button>
        <button id="hist-redo-btn">↪ Redo</button>
      </div>
      <div class="history-list"></div>
    `;
    document.body.appendChild(this._panel);

    this._listEl = this._panel.querySelector('.history-list');

    // Events
    this._panel.querySelector('.history-panel-close').addEventListener('click', () => this.toggle());
    this._panel.querySelector('#hist-undo-btn').addEventListener('click', () => {
      this.history.undo();
      this.onHistoryNav();
      this.refresh();
    });
    this._panel.querySelector('#hist-redo-btn').addEventListener('click', () => {
      this.history.redo();
      this.onHistoryNav();
      this.refresh();
    });

    // Refresh when history changes
    this.history.onChange(() => this.refresh());
  }

  toggle() {
    this._visible = !this._visible;
    this._panel.classList.toggle('open', this._visible);
    if (this._visible) this.refresh();
  }

  refresh() {
    if (!this._listEl) return;

    const undoBtn = this._panel.querySelector('#hist-undo-btn');
    const redoBtn = this._panel.querySelector('#hist-redo-btn');
    undoBtn.disabled = !this.history.canUndo;
    redoBtn.disabled = !this.history.canRedo;

    let html = '';

    if (this.history.past.length === 0 && this.history.future.length === 0) {
      html = '<div class="history-empty">No actions recorded yet.<br>Start editing to see history.</div>';
      this._listEl.innerHTML = html;
      return;
    }

    // Future items (redo stack, shown at the top, greyed out, oldest first)
    if (this.history.future.length > 0) {
      html += '<div class="history-separator">— Redo —</div>';
      // Future: bottom of stack is oldest = first to redo
      for (let i = 0; i < this.history.future.length; i++) {
        const action = this.history.future[i];
        html += this._renderItem(action, -1, true);
      }
    }

    // Current state marker
    html += '<div class="history-separator">— Now —</div>';

    // Past items (most recent first)
    for (let i = this.history.past.length - 1; i >= 0; i--) {
      const action = this.history.past[i];
      html += this._renderItem(action, i, false);
    }

    this._listEl.innerHTML = html;

    // Click handlers on past items
    this._listEl.querySelectorAll('.history-item[data-idx]').forEach(el => {
      el.addEventListener('click', () => {
        const idx = parseInt(el.dataset.idx, 10);
        if (idx >= 0) {
          this.history.undoTo(idx);
          this.onHistoryNav();
          this.refresh();
        }
      });
    });
  }

  _renderItem(action, index, isFuture) {
    const cls = isFuture ? 'history-item future-item' : 'history-item';
    const timeStr = this._formatTime(action.timestamp);
    const dataAttr = index >= 0 ? `data-idx="${index}"` : '';
    return `<div class="${cls}" ${dataAttr} title="${isFuture ? 'Future (redo)' : 'Click to undo to this point'}">
      <span class="history-item-icon">${action.icon || '•'}</span>
      <span class="history-item-label">${action.label}</span>
      <span class="history-item-time">${timeStr}</span>
    </div>`;
  }

  _formatTime(ts) {
    const d = new Date(ts);
    return d.toLocaleTimeString([], { hour: '2-digit', minute: '2-digit', second: '2-digit' });
  }
}

export default HistoryDialog;
