/**
 * Auto-Save Manager – periodically saves model to localStorage / IndexedDB
 * and offers restore on next load.
 */

const STORAGE_KEY = 'yapne_autosave';
const STORAGE_TS_KEY = 'yapne_autosave_ts';
const AUTOSAVE_INTERVAL = 30_000; // 30 seconds

export class AutoSaveManager {
  /**
   * @param {function} serialize   – returns the current model JSON string
   * @param {function} restore     – restores from a JSON string
   * @param {import('./action-history.js').ActionHistory} actionHistory
   */
  constructor(serialize, restore, actionHistory) {
    this._serialize = serialize;
    this._restore = restore;
    this._history = actionHistory;
    this._intervalId = null;
  }

  /** Start periodic auto-save */
  start() {
    this.stop();
    this._intervalId = setInterval(() => this._save(), AUTOSAVE_INTERVAL);
  }

  stop() {
    if (this._intervalId) {
      clearInterval(this._intervalId);
      this._intervalId = null;
    }
  }

  _save() {
    try {
      if (!this._history.isDirty) return; // nothing new
      const json = this._serialize();
      localStorage.setItem(STORAGE_KEY, json);
      localStorage.setItem(STORAGE_TS_KEY, Date.now().toString());
    } catch (e) {
      console.warn('Auto-save failed:', e);
    }
  }

  /** Force an immediate save (e.g. before unload) */
  saveNow() {
    try {
      const json = this._serialize();
      localStorage.setItem(STORAGE_KEY, json);
      localStorage.setItem(STORAGE_TS_KEY, Date.now().toString());
    } catch (e) {
      console.warn('Auto-save failed:', e);
    }
  }

  /**
   * Check whether an auto-saved model exists and offer restore.
   * @returns {boolean} true if restored
   */
  offerRestore() {
    const json = localStorage.getItem(STORAGE_KEY);
    const ts = localStorage.getItem(STORAGE_TS_KEY);
    if (!json || !ts) return false;

    const date = new Date(parseInt(ts, 10));
    const timeStr = date.toLocaleString();

    const doRestore = confirm(
      `An auto-saved model was found from ${timeStr}.\n\nWould you like to restore it?`
    );

    if (doRestore) {
      try {
        this._restore(json);
        return true;
      } catch (e) {
        console.error('Auto-restore failed:', e);
        alert('Could not restore the auto-saved model.');
      }
    }

    // Clear stale auto-save
    this.clearSaved();
    return false;
  }

  /** Remove auto-save data */
  clearSaved() {
    localStorage.removeItem(STORAGE_KEY);
    localStorage.removeItem(STORAGE_TS_KEY);
  }
}

export default AutoSaveManager;
