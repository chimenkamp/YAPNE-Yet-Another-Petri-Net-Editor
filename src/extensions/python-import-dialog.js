import { PythonToDPN } from './python-dpn-transpiler.js';

/**
 * Library of example Python programs users can load into the editor.
 */
const PYTHON_EXAMPLES = [
  {
    name: 'Simple Counter',
    description: 'Counts from 0 to 9',
    code: `x = 0
while x < 10:
    x = x + 1`
  },
  {
    name: 'If / Else Branching',
    description: 'Conditional with two branches',
    code: `x = 5
if x > 3:
    y = 1
else:
    y = 0`
  },
  {
    name: 'Nested Loops',
    description: 'Two nested for-range loops',
    code: `total = 0
for i in range(3):
    for j in range(4):
        total = total + 1`
  },
  {
    name: 'Fibonacci',
    description: 'Iterative Fibonacci sequence',
    code: `a = 0
b = 1
n = 10
i = 0
while i < n:
    temp = b
    b = a + b
    a = temp
    i = i + 1`
  },
  {
    name: 'Function Call',
    description: 'Function definition and inlined call',
    code: `def increment(v):
    v = v + 1
    return v

x = 0
increment(x)
increment(x)`
  },
  {
    name: 'GCD (Euclid)',
    description: 'Greatest common divisor via subtraction',
    code: `a = 48
b = 18
while a != b:
    if a > b:
        a = a - b
    else:
        b = b - a`
  },
  {
    name: 'Mutual Exclusion',
    description: 'Two-process flag-based mutex pattern',
    code: `flag1 = 0
flag2 = 0
turn = 1

# Process 1 enters
flag1 = 1
if flag2 == 0:
    turn = 1
    # critical section
    flag1 = 0
else:
    flag1 = 0

# Process 2 enters
flag2 = 1
if flag1 == 0:
    turn = 2
    # critical section
    flag2 = 0
else:
    flag2 = 0`
  },
  {
    name: 'Producer–Consumer',
    description: 'Bounded-buffer produce/consume cycle',
    code: `buffer = 0
capacity = 5
produced = 0
consumed = 0

while produced < 10:
    if buffer < capacity:
        buffer = buffer + 1
        produced = produced + 1
    if buffer > 0:
        buffer = buffer - 1
        consumed = consumed + 1`
  },
  {
    name: 'Factorial',
    description: 'Iterative factorial computation',
    code: `n = 6
result = 1
i = 1
while i <= n:
    result = result * i
    i = i + 1`
  },
  {
    name: 'Bubble Sort Pass',
    description: 'Single pass of bubble sort with swap flag',
    code: `swapped = 1
a = 5
b = 3
c = 8
d = 1

if a > b:
    temp = a
    a = b
    b = temp
    swapped = 1
if b > c:
    temp = b
    b = c
    c = temp
    swapped = 1
if c > d:
    temp = c
    c = d
    d = temp
    swapped = 1`
  },
  {
    name: 'Traffic Light',
    description: 'Cyclic state machine: red → green → yellow',
    code: `state = 0
cycles = 0
while cycles < 3:
    if state == 0:
        state = 1
    elif state == 1:
        state = 2
    elif state == 2:
        state = 0
        cycles = cycles + 1`
  },
  {
    name: 'Break & Continue',
    description: 'Loop with break and continue control flow',
    code: `total = 0
i = 0
while i < 20:
    i = i + 1
    if i == 5:
        continue
    if i == 15:
        break
    total = total + i`
  },
];

/**
 * Unsupported Python constructs that the transpiler cannot translate.
 * Each entry maps a human-readable label to a simple substring (or regex)
 * that is tested against the raw source code.
 */
const UNSUPPORTED_CHECKS = [
  { label: 'Class definitions (class)',              test: s => /^\s*class\s+/m.test(s) },
  { label: 'Try / except blocks',                    test: s => /^\s*try\s*:/m.test(s) },
  { label: 'With statements (context managers)',      test: s => /^\s*with\s+/m.test(s) },
  { label: 'Import statements',                      test: s => /^\s*(import |from\s+\S+\s+import)/m.test(s) },
  { label: 'Lambda expressions',                     test: s => /\blambda\b/.test(s) },
  { label: 'List comprehensions',                    test: s => /\[\s*\S+.*\bfor\b.*\bin\b/.test(s) },
  { label: 'Dict / set comprehensions',              test: s => /\{\s*\S+.*\bfor\b.*\bin\b/.test(s) },
  { label: 'Generator expressions',                  test: s => /\(\s*\S+.*\bfor\b.*\bin\b/.test(s) },
  { label: 'Async / await',                          test: s => /\basync\s+(def|for|with)\b/.test(s) },
  { label: 'Yield statements (generators)',           test: s => /\byield\b/.test(s) },
  { label: 'Global / nonlocal declarations',          test: s => /^\s*(global|nonlocal)\s+/m.test(s) },
  { label: 'Decorators (@)',                          test: s => /^\s*@\w/m.test(s) },
  { label: 'Starred expressions (*args, **kwargs)',   test: s => /\*\*\w|\*\w/.test(s) },
  { label: 'Assert statements',                      test: s => /^\s*assert\s+/m.test(s) },
  { label: 'Raise statements',                       test: s => /^\s*raise\s+/m.test(s) },
  { label: 'Delete statements',                      test: s => /^\s*del\s+/m.test(s) },
  { label: 'Modulo (%) / exponent (**) operators',    test: s => /%(?!=)|(?<!\*)\*\*(?!\*)/.test(s) },
  { label: 'Slice notation (a[1:3])',                 test: s => /\w\[.*:.*\]/.test(s) },
  { label: 'String operations (f-strings, .format)',  test: s => /f['"]|\.format\s*\(/.test(s) },
  { label: 'Dictionary literals ({key: val})',        test: s => /\{[^}]*:[^}]*\}/.test(s) },
];


/**
 * Modal dialog for importing Python source code as a Data Petri Net.
 */
export class PythonImportDialog {
  /**
   * @param {import('../petri-net-app.js').PetriNetApp} app
   */
  constructor(app) {
    this._app = app;
    this._overlay = null;
    this._code = '';
    this._mode = 'editor'; // 'editor' | 'file'
  }

  /** Open the dialog. */
  open() {
    if (this._overlay) return;
    this._build();
    document.body.appendChild(this._overlay);
    // focus textarea in next tick
    requestAnimationFrame(() => {
      const ta = this._overlay.querySelector('#python-code-input');
      if (ta) ta.focus();
    });
  }

  /** Close and remove the dialog. */
  close() {
    if (this._overlay) {
      this._overlay.remove();
      this._overlay = null;
    }
  }

  // ── private ──────────────────────────────────────────────────

  _build() {
    const overlay = document.createElement('div');
    overlay.className = 'modal-overlay';
    overlay.addEventListener('click', e => { if (e.target === overlay) this.close(); });

    overlay.innerHTML = `
      <div class="modal-container python-import-container">
        <div class="modal-header">
          <h2>🐍 Import Python as DPN (⚠️ BETA)</h2>
          <div class="modal-header-actions">
            <button class="python-help-btn" title="Help">❓</button>
            <button class="close-btn" title="Close">&times;</button>
          </div>
        </div>

        <div class="modal-body">
          <div class="python-import-content">

            <!-- Help panel (hidden by default) -->
            <div class="python-help-panel" id="python-help-panel" style="display:none">
              <div class="python-help-section">
                <h4>How to use</h4>
                <ol>
                  <li>Paste Python code in the editor or upload a <code>.py</code> file.</li>
                  <li>Choose an example from the dropdown to get started quickly.</li>
                  <li>Adjust <strong>Generalization</strong> (0 = exact model, higher = simpler) and <strong>Inlining Depth</strong> (levels of function inlining).</li>
                  <li>Review warnings for unsupported constructs, then click <strong>Import</strong>.</li>
                </ol>
              </div>
              <div class="python-help-section">
                <h4>Supported constructs</h4>
                <div class="python-help-columns">
                  <div class="python-help-col">
                    <h5>Statements</h5>
                    <ul>
                      <li><code>x = expr</code> — assignment</li>
                      <li><code>x += expr</code> — augmented assignment (<code>+=</code>, <code>-=</code>, <code>*=</code>, <code>/=</code>)</li>
                      <li><code>if / elif / else</code> — branching</li>
                      <li><code>while cond:</code> — while loops</li>
                      <li><code>for x in range(n):</code> — for-range loops</li>
                      <li><code>def f(args):</code> — function definitions</li>
                      <li><code>f(args)</code> — function calls (inlined)</li>
                      <li><code>return expr</code></li>
                      <li><code>break</code> / <code>continue</code></li>
                      <li><code>pass</code></li>
                    </ul>
                  </div>
                  <div class="python-help-col">
                    <h5>Expressions &amp; operators</h5>
                    <ul>
                      <li>Arithmetic: <code>+</code> <code>-</code> <code>*</code> <code>/</code></li>
                      <li>Comparison: <code>==</code> <code>!=</code> <code>&lt;</code> <code>&lt;=</code> <code>&gt;</code> <code>&gt;=</code></li>
                      <li>Logical: <code>and</code> <code>or</code> <code>not</code></li>
                      <li>Integer &amp; identifier literals</li>
                      <li>Parenthesized sub-expressions</li>
                      <li>Comments (<code>#</code>) are stripped</li>
                    </ul>
                    <h5>Translation model</h5>
                    <ul>
                      <li>Each statement becomes one or more transitions with guards (preconditions) and effects (postconditions).</li>
                      <li>Variables become DPN data variables.</li>
                      <li>Control flow (if/while/for) produces the corresponding Petri net routing pattern.</li>
                    </ul>
                  </div>
                </div>
              </div>
            </div>

            <!-- Tab switcher -->
            <div class="python-input-tabs">
              <button class="python-tab-btn active" data-tab="editor">✏️ Code Editor</button>
              <button class="python-tab-btn" data-tab="file">📂 Upload File</button>
            </div>

            <!-- Code editor pane -->
            <div class="python-pane" data-pane="editor">
              <div class="python-examples-bar">
                <label for="python-example-select">📚 Examples:</label>
                <select id="python-example-select">
                  <option value="">— Select an example —</option>
                  ${PYTHON_EXAMPLES.map((ex, i) =>
                    `<option value="${i}">${ex.name} — ${ex.description}</option>`
                  ).join('')}
                </select>
              </div>
              <div class="python-code-editor">
                <textarea id="python-code-input"
                  spellcheck="false"
                  placeholder="# Paste your Python code here…\nx = 0\nwhile x < 10:\n    x = x + 1"></textarea>
                <span class="python-line-count" id="python-line-count">0 lines</span>
              </div>
            </div>

            <!-- File upload pane (hidden initially) -->
            <div class="python-pane" data-pane="file" style="display:none">
              <div class="python-upload-area" id="python-upload-area">
                <span class="python-upload-icon">📄</span>
                <p>Drop a <strong>.py</strong> file here or <strong>click to browse</strong></p>
                <span class="python-upload-info">Accepts *.py files</span>
                <input type="file" accept=".py" style="display:none" id="python-file-input">
              </div>
              <div id="python-file-info" style="display:none"></div>
            </div>

            <!-- Warnings -->
            <div class="python-warnings" id="python-warnings" style="display:none">
              <div class="python-warnings-header">⚠️ Unsupported constructs detected</div>
              <ul class="python-warnings-list" id="python-warnings-list"></ul>
            </div>

            <!-- Settings -->
            <div class="python-settings">
              <h3>⚙️ Translation Settings</h3>
              <div class="python-settings-grid">
                <div class="python-setting-item">
                  <label>Generalization</label>
                  <span class="setting-description">0 = exact; higher drops guards &amp; effects</span>
                  <input type="range" id="python-gen" min="0" max="1" step="0.1" value="0">
                  <span class="python-range-value" id="python-gen-value">0</span>
                </div>
                <div class="python-setting-item">
                  <label>Inlining Depth</label>
                  <span class="setting-description">Levels of function-call inlining</span>
                  <input type="range" id="python-depth" min="0" max="5" step="1" value="1">
                  <span class="python-range-value" id="python-depth-value">1</span>
                </div>
              </div>
            </div>

            <!-- Quick summary -->
            <div class="python-summary" id="python-summary" style="display:none">
              <span class="stat-item">Places: <span class="stat-value" id="python-stat-places">0</span></span>
              <span class="stat-item">Transitions: <span class="stat-value" id="python-stat-transitions">0</span></span>
              <span class="stat-item">Variables: <span class="stat-value" id="python-stat-vars">0</span></span>
            </div>

          </div>
        </div>

        <div class="modal-footer">
          <button class="python-btn-cancel">Cancel</button>
          <button class="python-btn-import" id="python-btn-import" disabled>Import</button>
        </div>
      </div>
    `;

    this._overlay = overlay;
    this._wire(overlay);
  }

  _wire(root) {
    // Close
    root.querySelector('.close-btn').addEventListener('click', () => this.close());
    root.querySelector('.python-btn-cancel').addEventListener('click', () => this.close());

    // Help toggle
    const helpBtn = root.querySelector('.python-help-btn');
    const helpPanel = root.querySelector('#python-help-panel');
    helpBtn.addEventListener('click', () => {
      const open = helpPanel.style.display !== 'none';
      helpPanel.style.display = open ? 'none' : '';
      helpBtn.classList.toggle('active', !open);
    });
    document.addEventListener('keydown', this._escHandler = e => {
      if (e.key === 'Escape') this.close();
    });

    // Tabs
    const tabs = root.querySelectorAll('.python-tab-btn');
    const panes = root.querySelectorAll('.python-pane');
    tabs.forEach(btn => {
      btn.addEventListener('click', () => {
        tabs.forEach(t => t.classList.remove('active'));
        btn.classList.add('active');
        const target = btn.dataset.tab;
        panes.forEach(p => p.style.display = p.dataset.pane === target ? '' : 'none');
        this._mode = target;
      });
    });

    // Textarea
    const textarea = root.querySelector('#python-code-input');
    const lineCount = root.querySelector('#python-line-count');
    const onCodeChange = () => {
      this._code = textarea.value;
      const lines = (this._code.match(/\n/g) || []).length + (this._code.length ? 1 : 0);
      lineCount.textContent = `${lines} line${lines !== 1 ? 's' : ''}`;
      this._analyze();
    };
    textarea.addEventListener('input', onCodeChange);

    // Example selector
    const exampleSelect = root.querySelector('#python-example-select');
    exampleSelect.addEventListener('change', () => {
      const idx = exampleSelect.value;
      if (idx === '') return;
      const ex = PYTHON_EXAMPLES[parseInt(idx, 10)];
      if (ex) {
        textarea.value = ex.code;
        onCodeChange();
      }
    });
    // Allow Tab inside textarea
    textarea.addEventListener('keydown', e => {
      if (e.key === 'Tab') {
        e.preventDefault();
        const start = textarea.selectionStart;
        const end = textarea.selectionEnd;
        textarea.value = textarea.value.substring(0, start) + '    ' + textarea.value.substring(end);
        textarea.selectionStart = textarea.selectionEnd = start + 4;
        onCodeChange();
      }
    });

    // File upload
    const uploadArea = root.querySelector('#python-upload-area');
    const fileInput = root.querySelector('#python-file-input');
    const fileInfo = root.querySelector('#python-file-info');

    uploadArea.addEventListener('click', () => fileInput.click());
    uploadArea.addEventListener('dragover', e => { e.preventDefault(); uploadArea.classList.add('drag-over'); });
    uploadArea.addEventListener('dragleave', () => uploadArea.classList.remove('drag-over'));
    uploadArea.addEventListener('drop', e => {
      e.preventDefault();
      uploadArea.classList.remove('drag-over');
      const file = e.dataTransfer.files[0];
      if (file) this._loadFile(file, uploadArea, fileInfo);
    });
    fileInput.addEventListener('change', () => {
      const file = fileInput.files[0];
      if (file) this._loadFile(file, uploadArea, fileInfo);
    });

    // Settings sliders
    const genSlider = root.querySelector('#python-gen');
    const genValue = root.querySelector('#python-gen-value');
    genSlider.addEventListener('input', () => { genValue.textContent = genSlider.value; });

    const depthSlider = root.querySelector('#python-depth');
    const depthValue = root.querySelector('#python-depth-value');
    depthSlider.addEventListener('input', () => { depthValue.textContent = depthSlider.value; });

    // Import
    root.querySelector('#python-btn-import').addEventListener('click', () => this._doImport());
  }

  _loadFile(file, uploadArea, fileInfo) {
    if (!file.name.endsWith('.py')) {
      alert('Please select a .py file.');
      return;
    }
    const reader = new FileReader();
    reader.onload = (e) => {
      this._code = e.target.result;
      uploadArea.style.display = 'none';
      fileInfo.style.display = '';
      fileInfo.innerHTML = `
        <div class="python-file-loaded">
          <span>📄 ${this._escapeHtml(file.name)}</span>
          <span style="color:#D8DEE9">(${(file.size / 1024).toFixed(1)} KB)</span>
          <button class="file-remove" title="Remove file">&times;</button>
        </div>
      `;
      fileInfo.querySelector('.file-remove').addEventListener('click', () => {
        this._code = '';
        fileInfo.style.display = 'none';
        uploadArea.style.display = '';
        this._analyze();
      });
      this._analyze();
    };
    reader.readAsText(file);
  }

  /** Check for unsupported constructs and update warnings + summary. */
  _analyze() {
    const code = this._code;
    const importBtn = this._overlay.querySelector('#python-btn-import');
    const warningsBox = this._overlay.querySelector('#python-warnings');
    const warningsList = this._overlay.querySelector('#python-warnings-list');
    const summary = this._overlay.querySelector('#python-summary');

    if (!code.trim()) {
      importBtn.disabled = true;
      warningsBox.style.display = 'none';
      summary.style.display = 'none';
      return;
    }

    importBtn.disabled = false;

    // Warnings
    const hits = UNSUPPORTED_CHECKS.filter(c => c.test(code));
    if (hits.length > 0) {
      warningsBox.style.display = '';
      warningsList.innerHTML = hits.map(h =>
        `<li>${this._escapeHtml(h.label)}</li>`
      ).join('');
    } else {
      warningsBox.style.display = 'none';
    }

    // Quick dry-run to count elements
    try {
      const gen = parseFloat(this._overlay.querySelector('#python-gen').value);
      const depth = parseInt(this._overlay.querySelector('#python-depth').value, 10);
      const transpiler = new PythonToDPN({ generalization: gen, depth });
      const dpn = transpiler.convert(code);
      const json = JSON.parse(dpn.toJSON());

      summary.style.display = '';
      this._overlay.querySelector('#python-stat-places').textContent = json.places.length;
      this._overlay.querySelector('#python-stat-transitions').textContent = json.transitions.length;
      this._overlay.querySelector('#python-stat-vars').textContent = (json.dataVariables || []).length;
    } catch {
      summary.style.display = 'none';
    }
  }

  /** Run the transpiler and load the result into the editor. */
  _doImport() {
    const code = this._code;
    if (!code.trim()) return;

    const gen = parseFloat(this._overlay.querySelector('#python-gen').value);
    const depth = parseInt(this._overlay.querySelector('#python-depth').value, 10);

    try {
      const transpiler = new PythonToDPN({ generalization: gen, depth });
      const dpn = transpiler.convert(code);
      const jsonStr = dpn.toJSON();

      // Wrap as a File so the existing (possibly DPN-patched) loadFromFile handles it
      const blob = new Blob([jsonStr], { type: 'application/json' });
      const file = new File([blob], 'python-import.json', { type: 'application/json' });
      this._app.loadFromFile(file);

      this.close();
    } catch (err) {
      console.error('Python import failed:', err);
      alert('Import failed: ' + err.message);
    }
  }

  _escapeHtml(str) {
    const d = document.createElement('div');
    d.textContent = str;
    return d.innerHTML;
  }
}
