import { readDraft, saveDraft, clearDraft } from './browser-net-storage.js';

/** @type {number} */
const AUTOSAVE_INTERVAL_MS = 5_000;

/** @typedef {{dirty: boolean, error: string}} SaveStatus */

/** Track explicit saves separately from automatic recovery snapshots. */
export class AutoSaveManager {
  /**
   * @param {() => string|null} serialize Current JSON, or null during editor replacement.
   * @param {(json: string) => void} restore Validate and restore a complete model.
   * @param {(status: SaveStatus) => void} onStatus Publish user-visible save status.
   */
  constructor(serialize, restore, onStatus) {
    this._serialize = serialize;
    this._restore = restore;
    this._onStatus = onStatus;
    this._savedJSON = serialize();
    this._currentJSON = this._savedJSON;
    /** @type {string|null} */
    this._draftJSON = null;
    /** @type {ReturnType<typeof setInterval>|null} */
    this._intervalId = null;
    this._recoveryBlocked = false;
    this._error = '';
    this._beforeUnload = this._handleBeforeUnload.bind(this);
    this._visibilityChange = this._handleVisibilityChange.bind(this);
    this._pageHide = this.saveNow.bind(this);
    this._documentChange = () => queueMicrotask(() => this.saveNow());
  }

  /** Compare content rather than history length, which can repeat after branching.
   * @returns {boolean} Whether the current model differs from the explicit save.
   */
  get isDirty() {
    return this._currentJSON !== this._savedJSON;
  }

  /** Start periodic and page-lifecycle recovery saves.
   * @returns {void}
   */
  start() {
    this.stop();
    this._intervalId = setInterval(() => this.saveNow(), AUTOSAVE_INTERVAL_MS);
    document.addEventListener('visibilitychange', this._visibilityChange);
    document.addEventListener('change', this._documentChange);
    document.addEventListener('click', this._documentChange);
    window.addEventListener('pagehide', this._pageHide);
    this._publishStatus();
  }

  /** Remove timers and lifecycle listeners.
   * @returns {void}
   */
  stop() {
    if (this._intervalId !== null) clearInterval(this._intervalId);
    this._intervalId = null;
    document.removeEventListener('visibilitychange', this._visibilityChange);
    document.removeEventListener('change', this._documentChange);
    document.removeEventListener('click', this._documentChange);
    window.removeEventListener('pagehide', this._pageHide);
    window.removeEventListener('beforeunload', this._beforeUnload);
  }

  /** Update the draft without treating recovery storage as an explicit save.
   * @returns {void}
   */
  saveNow() {
    try {
      const json = this._serialize();
      if (json === null) return;
      this._currentJSON = json;
      if (this._recoveryBlocked) return;
      if (this.isDirty && json !== this._draftJSON) {
        saveDraft(json);
        this._draftJSON = json;
      } else if (!this.isDirty && this._draftJSON !== null) {
        clearDraft();
        this._draftJSON = null;
      }
      this._error = '';
    } catch (error) {
      this._error = `Browser draft could not be saved: ${error.message}. Save as JSON to keep a backup.`;
    } finally {
      this._publishStatus();
    }
  }

  /** Mark a successful JSON export, named save, or file load as the clean baseline.
   * @returns {void}
   */
  markSaved() {
    this._savedJSON = this._serialize();
    this.saveNow();
  }

  /** Keep a manually loaded recovery draft visibly unsaved.
   * @returns {void}
   */
  markUnsaved() {
    this._savedJSON = null;
    this.saveNow();
  }

  /** Restore a stored draft automatically; retain unreadable drafts for recovery.
   * @returns {boolean} Whether a draft was restored.
   */
  offerRestore() {
    try {
      const json = readDraft();
      if (json === null) return false;
      this._restore(json);
      this._savedJSON = null;
      this._currentJSON = this._serialize();
      this._draftJSON = json;
      return true;
    } catch (error) {
      this._recoveryBlocked = true;
      this._error = `Could not restore the browser draft: ${error.message}. The stored draft is preserved; save new work as JSON or under a browser name.`;
      return false;
    } finally {
      this._publishStatus();
    }
  }

  /** Flush immediately and request the browser's native warning only when dirty.
   * @param {BeforeUnloadEvent} event Page exit event.
   * @returns {void}
   */
  _handleBeforeUnload(event) {
    this.saveNow();
    if (!this.isDirty) return;
    event.preventDefault();
    event.returnValue = true;
  }

  /** Save when switching apps or tabs, without relying on a later unload event.
   * @returns {void}
   */
  _handleVisibilityChange() {
    if (document.visibilityState === 'hidden') this.saveNow();
  }

  /** Keep the visible status and leave-page listener in sync.
   * @returns {void}
   */
  _publishStatus() {
    window.removeEventListener('beforeunload', this._beforeUnload);
    if (this.isDirty) window.addEventListener('beforeunload', this._beforeUnload);
    this._onStatus({ dirty: this.isDirty, error: this._error });
  }
}

export default AutoSaveManager;
