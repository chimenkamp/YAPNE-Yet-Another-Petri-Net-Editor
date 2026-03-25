/**
 * Action History – Undo / Redo system for YAPNE
 *
 * Provides an UndoableAction interface and a central ActionHistory service
 * that maintains bounded past/future stacks.
 */

/**
 * @typedef {Object} UndoableAction
 * @property {string} label  - Human-readable description (e.g. "Move place P1")
 * @property {string} icon   - Emoji icon for the action type
 * @property {number} timestamp - Date.now() when the action was pushed
 * @property {function} redo - Re-apply the action
 * @property {function} undo - Reverse the action
 */

export class ActionHistory {
  /**
   * @param {number} [maxSize=50] – Maximum entries kept in the past stack
   */
  constructor(maxSize = 50) {
    /** @type {UndoableAction[]} */
    this.past = [];
    /** @type {UndoableAction[]} */
    this.future = [];
    this.maxSize = maxSize;

    /**
     * Index into `past` that represents the last-saved state.
     * -1 means "saved before any action was pushed".
     * @type {number}
     */
    this._saveIndex = -1;

    /** @type {function|null} */
    this.onChangeCallback = null;
  }

  /* ─── public helpers ─── */

  /** Whether the model has unsaved changes */
  get isDirty() {
    return this.past.length - 1 !== this._saveIndex;
  }

  /** Mark the current state as "saved" */
  markSaved() {
    this._saveIndex = this.past.length - 1;
    this._notifyChange();
  }

  /** Reset everything (e.g. on file load) */
  clear() {
    this.past = [];
    this.future = [];
    this._saveIndex = -1;
    this._notifyChange();
  }

  /* ─── core API ─── */

  /**
   * Push a new undoable action. Clears the redo stack.
   * @param {UndoableAction} action
   */
  push(action) {
    this.past.push(action);
    this.future = [];
    // Trim if over limit
    if (this.past.length > this.maxSize) {
      this.past.shift();
      // Adjust save index
      this._saveIndex = Math.max(-1, this._saveIndex - 1);
    }
    this._notifyChange();
  }

  /** Undo the last action. Returns the action or null. */
  undo() {
    if (this.past.length === 0) return null;
    const action = this.past.pop();
    action.undo();
    this.future.push(action);
    this._notifyChange();
    return action;
  }

  /** Redo the next action. Returns the action or null. */
  redo() {
    if (this.future.length === 0) return null;
    const action = this.future.pop();
    action.redo();
    this.past.push(action);
    this._notifyChange();
    return action;
  }

  /**
   * Undo everything back to (and including) the entry at `targetIndex`.
   * All undone entries move to `future`.
   * @param {number} targetIndex – index in `past` (0-based)
   */
  undoTo(targetIndex) {
    while (this.past.length > targetIndex) {
      this.undo();
    }
  }

  get canUndo() {
    return this.past.length > 0;
  }

  get canRedo() {
    return this.future.length > 0;
  }

  /** Set a callback that fires whenever history state changes */
  onChange(cb) {
    this.onChangeCallback = cb;
  }

  _notifyChange() {
    if (this.onChangeCallback) {
      this.onChangeCallback();
    }
  }
}

/* ─── Action factory helpers ─── */

/**
 * Icons per action type for the history panel
 */
export const ACTION_ICONS = {
  add: '➕',
  delete: '🗑️',
  move: '↔️',
  edit: '✏️',
  layout: '🔄',
  style: '🎨',
  tokens: '⚫',
  arc: '→',
  compound: '📦',
};

/**
 * Create a generic undoable action.
 * @param {string} label
 * @param {string} icon
 * @param {function} redoFn
 * @param {function} undoFn
 * @returns {UndoableAction}
 */
export function createAction(label, icon, redoFn, undoFn) {
  return {
    label,
    icon,
    timestamp: Date.now(),
    redo: redoFn,
    undo: undoFn,
  };
}

/**
 * Wrap multiple actions into a single compound undoable action.
 * @param {string} label
 * @param {UndoableAction[]} actions
 * @returns {UndoableAction}
 */
export function compoundAction(label, actions) {
  return {
    label,
    icon: ACTION_ICONS.compound,
    timestamp: Date.now(),
    redo() {
      for (const a of actions) a.redo();
    },
    undo() {
      for (let i = actions.length - 1; i >= 0; i--) actions[i].undo();
    },
  };
}

export default ActionHistory;
