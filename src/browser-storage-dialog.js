import { DRAFT_NAME, listBrowserModels, readBrowserModel, saveBrowserModel, validateModelName } from './browser-net-storage.js';

/** Bind the browser model dialog once; editor replacement does not remove it. */
export class BrowserStorageDialog {
  /** @param {import('./petri-net-app.js').default} app Editor application. */
  constructor(app) {
    this.app = app;
    this.dialog = document.getElementById('browser-storage-dialog');
    this.form = this.dialog.querySelector('form');
    this.nameInput = this.dialog.querySelector('#browser-model-name');
    this.modelSelect = this.dialog.querySelector('#browser-model-list');
    this.error = this.dialog.querySelector('[role="alert"]');
    this.submit = this.dialog.querySelector('[type="submit"]');
    /** @type {'save'|'load'} */
    this.mode = 'save';
    document.getElementById('btn-save-browser').addEventListener('click', () => this.open('save'));
    document.getElementById('btn-load-browser').addEventListener('click', () => this.open('load'));
    this.dialog.querySelector('[data-cancel]').addEventListener('click', () => this.dialog.close());
    this.dialog.addEventListener('keydown', event => event.stopPropagation());
    this.form.addEventListener('submit', event => {
      event.preventDefault();
      this.apply();
    });
  }

  /** Open the requested operation and refresh names from browser storage.
   * @param {'save'|'load'} mode File operation.
   * @returns {void}
   */
  open(mode) {
    this.app.commitFocusedPropertiesInput();
    this.app.autoSave.saveNow();
    this.mode = mode;
    this.error.textContent = '';
    this.dialog.querySelector('h2').textContent = mode === 'save' ? 'Save (Browser)' : 'Load (Browser)';
    this.nameInput.parentElement.hidden = mode !== 'save';
    this.modelSelect.parentElement.hidden = mode !== 'load';
    this.nameInput.required = mode === 'save';
    this.modelSelect.required = mode === 'load';
    this.nameInput.value = '';
    this.submit.textContent = mode === 'save' ? 'Save' : 'Load';
    this.submit.disabled = false;
    try {
      this.populateModels();
    } catch (error) {
      this.error.textContent = `Browser storage is unavailable: ${error.message}. Save as JSON instead.`;
      this.submit.disabled = true;
    }
    this.dialog.showModal();
    (mode === 'save' ? this.nameInput : this.modelSelect).focus();
  }

  /** Render names as text so user-provided names cannot introduce markup.
   * @returns {void}
   */
  populateModels() {
    const names = listBrowserModels();
    this.modelSelect.replaceChildren();
    for (const name of names) {
      const option = document.createElement('option');
      option.value = name;
      option.textContent = name;
      this.modelSelect.appendChild(option);
    }
    if (this.mode === 'load' && names.length === 0) {
      this.error.textContent = 'No models saved in this browser yet.';
      this.submit.disabled = true;
    }
  }

  /** Execute the selected operation and keep errors visible without closing.
   * @returns {void}
   */
  apply() {
    try {
      const completed = this.mode === 'save' ? this.save() : this.load();
      if (completed) this.dialog.close();
    } catch (error) {
      this.error.textContent = `${error.message} The current model has not been saved or replaced.`;
    }
  }

  /** Save under a name, confirming before replacing an existing named model.
   * @returns {boolean} Whether the model was saved.
   */
  save() {
    const name = validateModelName(this.nameInput.value);
    if (listBrowserModels().includes(name) && !confirm(`Replace the browser model "${name}"?`)) return false;
    saveBrowserModel(name, this.app.api.exportAsJSON());
    this.app.autoSave.markSaved();
    return true;
  }

  /** Validate and load the selection after confirming loss of unsaved edits.
   * @returns {boolean} Whether a model was loaded.
   */
  load() {
    const name = this.modelSelect.value;
    const json = readBrowserModel(name);
    this.app.autoSave.saveNow();
    if (this.app.autoSave.isDirty && !confirm('Replace the current model and its unsaved draft? Save it under a browser name or as JSON first to keep it.')) return false;
    this.app.loadModelJSON(json);
    if (name === DRAFT_NAME) this.app.autoSave.markUnsaved();
    else this.app.autoSave.markSaved();
    return true;
  }
}
