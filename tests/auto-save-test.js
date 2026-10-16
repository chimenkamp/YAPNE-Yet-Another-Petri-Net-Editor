import assert from 'node:assert/strict';
import test from 'node:test';
import { AutoSaveManager } from '../src/auto-save.js';

/** Provide isolated browser storage and event targets for each test.
 * @param {import('node:test').TestContext} context Test lifecycle.
 * @returns {Map<string, string>} Stored values.
 */
function browserEnvironment(context) {
  /** @type {Map<string, string>} */
  const values = new Map();
  context.mock.method(globalThis, 'setInterval', () => 1);
  context.mock.method(globalThis, 'clearInterval', () => {});
  globalThis.window = new EventTarget();
  globalThis.document = new EventTarget();
  globalThis.localStorage = {
    getItem: key => values.get(key) ?? null,
    setItem: (key, value) => values.set(key, value),
    removeItem: key => values.delete(key),
    key: index => [...values.keys()][index] ?? null,
    get length() { return values.size; },
  };
  context.after(() => {
    delete globalThis.window;
    delete globalThis.document;
    delete globalThis.localStorage;
  });
  return values;
}

test('unchanged initial models do not create an unsaved draft', context => {
  const values = browserEnvironment(context);
  const manager = new AutoSaveManager(() => '{"name":"initial"}', () => {}, () => {});
  manager.saveNow();
  assert.equal(values.has('yapne_autosave'), false);
});

test('edits persist immediately and autosave does not mark them explicitly saved', context => {
  const values = browserEnvironment(context);
  let json = '{"name":"initial"}';
  const manager = new AutoSaveManager(() => json, () => {}, () => {});
  json = '{"name":"edited"}';
  manager.saveNow();
  assert.equal(values.get('yapne_autosave'), json);
  assert.equal(manager.isDirty, true);
  manager.markSaved();
  assert.equal(manager.isDirty, false);
  assert.equal(values.has('yapne_autosave'), false);
});

test('draft restore is automatic, including older drafts without a timestamp', context => {
  const values = browserEnvironment(context);
  const draft = '{"name":"unsaved model"}';
  values.set('yapne_autosave', draft);
  let json = '{"name":"initial"}';
  const manager = new AutoSaveManager(() => json, restored => { json = restored; }, () => {});
  assert.equal(manager.offerRestore(), true);
  assert.equal(json, draft);
  assert.equal(manager.isDirty, true);
});

test('undo to the saved state clears dirty status but a new branch stays dirty', context => {
  browserEnvironment(context);
  let json = 'initial';
  const manager = new AutoSaveManager(() => json, () => {}, () => {});
  json = 'saved';
  manager.markSaved();
  json = 'initial';
  manager.saveNow();
  assert.equal(manager.isDirty, true);
  json = 'different branch';
  manager.saveNow();
  assert.equal(manager.isDirty, true);
  json = 'saved';
  manager.saveNow();
  assert.equal(manager.isDirty, false);
});

test('failed recovery preserves the draft and prevents automatic replacement', context => {
  const values = browserEnvironment(context);
  values.set('yapne_autosave', '{broken');
  let json = 'initial';
  let status;
  const manager = new AutoSaveManager(() => json, () => { throw new Error('Invalid model'); }, next => { status = next; });
  assert.equal(manager.offerRestore(), false);
  json = 'edit';
  manager.saveNow();
  assert.equal(values.get('yapne_autosave'), '{broken');
  assert.match(status.error, /restore|recover/i);
});

test('storage failures stay visible and never claim changes are saved', context => {
  const values = browserEnvironment(context);
  let json = 'initial';
  let status;
  const manager = new AutoSaveManager(() => json, () => {}, next => { status = next; });
  context.mock.method(localStorage, 'setItem', () => { throw new Error('Quota exceeded'); });
  json = 'edit';
  manager.saveNow();
  assert.equal(manager.isDirty, true);
  assert.equal(values.has('yapne_autosave'), false);
  assert.match(status.error, /Quota exceeded/);
});

test('leave-page protection is present only while dirty and flushes the draft', context => {
  const values = browserEnvironment(context);
  let json = 'initial';
  const manager = new AutoSaveManager(() => json, () => {}, () => {});
  manager.start();
  assert.equal(window.dispatchEvent(new Event('beforeunload', { cancelable: true })), true);
  json = 'edit';
  manager.saveNow();
  json = 'last edit';
  assert.equal(window.dispatchEvent(new Event('beforeunload', { cancelable: true })), false);
  assert.equal(values.get('yapne_autosave'), 'last edit');
  manager.markSaved();
  assert.equal(window.dispatchEvent(new Event('beforeunload', { cancelable: true })), true);
  manager.stop();
});

test('periodic and hidden-page saves catch changes outside the history callbacks', context => {
  const values = browserEnvironment(context);
  let json = 'initial';
  const manager = new AutoSaveManager(() => json, () => {}, () => {});
  manager.start();
  json = 'periodic edit';
  setInterval.mock.calls.at(-1).arguments[0]();
  assert.equal(values.get('yapne_autosave'), json);
  json = 'hidden edit';
  document.visibilityState = 'hidden';
  document.dispatchEvent(new Event('visibilitychange'));
  assert.equal(values.get('yapne_autosave'), json);
  manager.stop();
});

test('named saves coexist with the draft and reject empty or reserved names', async context => {
  browserEnvironment(context);
  const storage = await import('../src/browser-net-storage.js');
  storage.saveDraft('draft JSON');
  storage.saveBrowserModel(' First ', 'first JSON');
  storage.saveBrowserModel('Second', 'second JSON');
  assert.deepEqual(storage.listBrowserModels(), ['unsaved draft', 'First', 'Second']);
  assert.equal(storage.readBrowserModel('First'), 'first JSON');
  assert.equal(storage.readBrowserModel('unsaved draft'), 'draft JSON');
  assert.throws(() => storage.saveBrowserModel(' ', 'invalid'), /name/i);
  assert.throws(() => storage.saveBrowserModel('Unsaved Draft', 'invalid'), /reserved/i);
  assert.throws(() => storage.readBrowserModel('Missing'), /no longer|not found/i);
});

test('named save failures preserve the previous model and unrelated storage', async context => {
  const values = browserEnvironment(context);
  const storage = await import('../src/browser-net-storage.js');
  storage.saveBrowserModel('First', 'original');
  values.set('editor-settings', 'settings');
  context.mock.method(localStorage, 'setItem', () => { throw new Error('Storage full'); });
  assert.throws(() => storage.saveBrowserModel('First', 'replacement'), /Storage full/);
  assert.equal(storage.readBrowserModel('First'), 'original');
  assert.deepEqual(storage.listBrowserModels(), ['First']);
  assert.equal(values.get('editor-settings'), 'settings');
});

test('property changes and data-variable buttons flush after their UI handlers', async context => {
  const values = browserEnvironment(context);
  let json = 'initial';
  const manager = new AutoSaveManager(() => json, () => {}, () => {});
  manager.start();
  for (const eventName of ['change', 'click']) {
    json = eventName;
    document.dispatchEvent(new Event(eventName));
    await Promise.resolve();
    assert.equal(values.get('yapne_autosave'), json);
  }
  manager.stop();
});

test('denied storage access reports recovery failure instead of crashing', context => {
  browserEnvironment(context);
  let status;
  const manager = new AutoSaveManager(() => 'initial', () => {}, next => { status = next; });
  context.mock.method(localStorage, 'getItem', () => { throw new Error('Access denied'); });
  assert.equal(manager.offerRestore(), false);
  assert.match(status.error, /Access denied/);
  assert.doesNotThrow(() => manager.start());
  manager.stop();
});
