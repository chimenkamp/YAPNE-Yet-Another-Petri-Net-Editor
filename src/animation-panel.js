const EFFECTS = [
  { value: 'appear', label: 'Appear' },
  { value: 'disappear', label: 'Disappear' },
  { value: 'highlight', label: 'Highlight' },
  { value: 'pulse', label: 'Pulse' },
  { value: 'focus', label: 'Focus' },
  { value: 'tokenFlow', label: 'Token Flow' },
  { value: 'caption', label: 'Caption' },
  { value: 'variableCallout', label: 'Data Callout' }
];

const COLORS = {
  background: '#ECEFF4',
  ink: '#2E3440',
  muted: '#5B6474',
  placeFill: '#FFFFFF',
  transitionFill: '#D8DEE9',
  enabledFill: '#A3BE8C',
  arc: '#2E3440',
  blue: '#5E81AC',
  cyan: '#88C0D0',
  green: '#A3BE8C',
  yellow: '#EBCB8B',
  orange: '#D08770',
  red: '#BF616A',
  purple: '#B48EAD'
};

const EXPORT_RESOLUTIONS = [
  { value: '1280x720', label: 'HD 720p', width: 1280, height: 720 },
  { value: '1920x1080', label: 'Full HD 1080p', width: 1920, height: 1080 },
  { value: '2560x1440', label: 'QHD 1440p', width: 2560, height: 1440 },
  { value: '3840x2160', label: '4K UHD', width: 3840, height: 2160 },
  { value: 'custom', label: 'Custom', width: null, height: null }
];

function clamp(value, min, max) {
  return Math.max(min, Math.min(max, value));
}

function easeInOut(t) {
  const x = clamp(t, 0, 1);
  return x < 0.5 ? 2 * x * x : 1 - Math.pow(-2 * x + 2, 2) / 2;
}

function escapeHtml(value) {
  return String(value ?? '')
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}

function uid(prefix = 'clip') {
  return `${prefix}-${Date.now().toString(36)}-${Math.random().toString(36).slice(2, 7)}`;
}

function formatMs(ms) {
  return `${(Math.max(0, ms) / 1000).toFixed(2)}s`;
}

function normalizeMapLike(value) {
  if (!value) return [];
  if (value instanceof Map) return Array.from(value.entries());
  if (Array.isArray(value)) {
    return value.map(item => Array.isArray(item) ? item : [item.id, item]);
  }
  return Object.entries(value);
}

function downloadBlob(blob, filename) {
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = filename;
  document.body.appendChild(link);
  link.click();
  link.remove();
  setTimeout(() => URL.revokeObjectURL(url), 1000);
}

class SimpleGifEncoder {
  static encode(frames, width, height, delayCs) {
    const writer = new GifByteWriter();
    const palette = SimpleGifEncoder.webSafePalette();

    writer.writeString('GIF89a');
    writer.writeShort(width);
    writer.writeShort(height);
    writer.writeByte(0xF7);
    writer.writeByte(0);
    writer.writeByte(0);
    writer.writeBytes(palette);

    writer.writeByte(0x21);
    writer.writeByte(0xFF);
    writer.writeByte(0x0B);
    writer.writeString('NETSCAPE2.0');
    writer.writeByte(0x03);
    writer.writeByte(0x01);
    writer.writeShort(0);
    writer.writeByte(0);

    for (const frame of frames) {
      const indexes = SimpleGifEncoder.indexPixels(frame.data);
      const imageData = SimpleGifEncoder.lzwEncode(indexes, 8);

      writer.writeByte(0x21);
      writer.writeByte(0xF9);
      writer.writeByte(0x04);
      writer.writeByte(0x08);
      writer.writeShort(delayCs);
      writer.writeByte(0);
      writer.writeByte(0);

      writer.writeByte(0x2C);
      writer.writeShort(0);
      writer.writeShort(0);
      writer.writeShort(width);
      writer.writeShort(height);
      writer.writeByte(0);
      writer.writeByte(8);
      writer.writeSubBlocks(imageData);
    }

    writer.writeByte(0x3B);
    return new Blob([new Uint8Array(writer.bytes)], { type: 'image/gif' });
  }

  static webSafePalette() {
    const bytes = [];
    for (let r = 0; r < 6; r += 1) {
      for (let g = 0; g < 6; g += 1) {
        for (let b = 0; b < 6; b += 1) {
          bytes.push(r * 51, g * 51, b * 51);
        }
      }
    }

    while (bytes.length < 256 * 3) {
      const shade = Math.round(((bytes.length / 3) - 216) * (255 / 39));
      bytes.push(clamp(shade, 0, 255), clamp(shade, 0, 255), clamp(shade, 0, 255));
    }
    return bytes;
  }

  static indexPixels(data) {
    const indexes = new Uint8Array(data.length / 4);
    for (let source = 0, target = 0; source < data.length; source += 4, target += 1) {
      const r = Math.round(data[source] / 51);
      const g = Math.round(data[source + 1] / 51);
      const b = Math.round(data[source + 2] / 51);
      indexes[target] = clamp(r, 0, 5) * 36 + clamp(g, 0, 5) * 6 + clamp(b, 0, 5);
    }
    return indexes;
  }

  static lzwEncode(indexes, minCodeSize) {
    if (!indexes.length) return [];

    const clearCode = 1 << minCodeSize;
    const endCode = clearCode + 1;
    let nextCode = endCode + 1;
    let codeSize = minCodeSize + 1;
    let bitBuffer = 0;
    let bitCount = 0;
    const bytes = [];
    let dictionary = SimpleGifEncoder.initialDictionary(clearCode);

    const writeCode = code => {
      bitBuffer |= code << bitCount;
      bitCount += codeSize;
      while (bitCount >= 8) {
        bytes.push(bitBuffer & 0xFF);
        bitBuffer >>= 8;
        bitCount -= 8;
      }
    };

    const resetDictionary = () => {
      dictionary = SimpleGifEncoder.initialDictionary(clearCode);
      nextCode = endCode + 1;
      codeSize = minCodeSize + 1;
    };

    writeCode(clearCode);

    let phrase = String.fromCharCode(indexes[0]);
    for (let i = 1; i < indexes.length; i += 1) {
      const char = String.fromCharCode(indexes[i]);
      const nextPhrase = phrase + char;

      if (dictionary.has(nextPhrase)) {
        phrase = nextPhrase;
        continue;
      }

      writeCode(dictionary.get(phrase));

      if (nextCode < 4096) {
        dictionary.set(nextPhrase, nextCode);
        nextCode += 1;
        if (nextCode === (1 << codeSize) && codeSize < 12) {
          codeSize += 1;
        }
      } else {
        writeCode(clearCode);
        resetDictionary();
      }

      phrase = char;
    }

    writeCode(dictionary.get(phrase));
    writeCode(endCode);

    if (bitCount > 0) {
      bytes.push(bitBuffer & 0xFF);
    }
    return bytes;
  }

  static initialDictionary(clearCode) {
    const dictionary = new Map();
    for (let i = 0; i < clearCode; i += 1) {
      dictionary.set(String.fromCharCode(i), i);
    }
    return dictionary;
  }
}

class GifByteWriter {
  constructor() {
    this.bytes = [];
  }

  writeByte(value) {
    this.bytes.push(value & 0xFF);
  }

  writeShort(value) {
    this.writeByte(value & 0xFF);
    this.writeByte((value >> 8) & 0xFF);
  }

  writeString(value) {
    for (let i = 0; i < value.length; i += 1) {
      this.writeByte(value.charCodeAt(i));
    }
  }

  writeBytes(values) {
    for (const value of values) {
      this.writeByte(value);
    }
  }

  writeSubBlocks(values) {
    for (let i = 0; i < values.length; i += 255) {
      const block = values.slice(i, i + 255);
      this.writeByte(block.length);
      this.writeBytes(block);
    }
    this.writeByte(0);
  }
}

export class AnimationPanel {
  constructor(app) {
    this.app = app;
    this.isOpen = false;
    this.panel = null;
    this.toggleBtn = null;
    this.previewCanvas = null;
    this.clips = [];
    this.selectedClipId = null;
    this.timeMs = 0;
    this.isPlaying = false;
    this.playbackFrame = null;
    this.lastTick = 0;
    this.isExporting = false;
    this.settings = {
      duration: 8000,
      fps: 24,
      background: COLORS.background,
      aspect: '16:9',
      exportResolution: '1920x1080',
      exportWidth: 1920,
      exportHeight: 1080,
      defaultHidden: false,
      showLabels: true,
      showCaptions: true,
      showDataStrip: true,
      showDataCallouts: true,
      showProgress: true,
      showGrid: false
    };

    this._init();
  }

  _init() {
    this._createToolbarButton();
    this._createPanel();
    this.refreshFromNet({ buildIfEmpty: true });
  }

  _createToolbarButton() {
    this.toggleBtn = document.createElement('button');
    this.toggleBtn.id = 'btn-animation-suite';
    this.toggleBtn.className = 'blue';
    this.toggleBtn.title = 'Animation Studio';
    this.toggleBtn.innerHTML = `
      <svg width="22" height="22" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
        <rect x="3" y="5" width="18" height="14" rx="2"/>
        <path d="M7 5l2.2 4"/>
        <path d="M12 5l2.2 4"/>
        <path d="M17 5l2.2 4"/>
        <path d="M3 9h18"/>
        <path d="M10 13l4 2-4 2v-4z"/>
      </svg>
    `;
    this.toggleBtn.addEventListener('click', () => this.toggle());

    const toolbar = document.querySelector('.toolbar-group.vertical');
    if (toolbar) {
      const divider = document.createElement('hr');
      divider.className = 'animation-toolbar-divider';
      toolbar.appendChild(divider);
      toolbar.appendChild(this.toggleBtn);
    }
  }

  _createPanel() {
    this.panel = document.createElement('div');
    this.panel.className = 'animation-modal-overlay';
    this.panel.id = 'animation-panel';
    this.panel.innerHTML = this._getPanelHTML();

    document.body.appendChild(this.panel);

    this.previewCanvas = this.panel.querySelector('#animation-preview-canvas');
    this._bindPanelEvents();
  }

  _getPanelHTML() {
    return `
      <div class="animation-modal" role="dialog" aria-modal="true" aria-labelledby="animation-modal-title">
      <div class="panel-header">
        <div class="panel-header-title">
          <svg width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
            <rect x="3" y="5" width="18" height="14" rx="2"/>
            <path d="M7 5l2.2 4"/><path d="M12 5l2.2 4"/><path d="M17 5l2.2 4"/>
            <path d="M3 9h18"/><path d="M10 13l4 2-4 2v-4z"/>
          </svg>
          <h3 id="animation-modal-title">Animation Studio</h3>
        </div>
        <button class="panel-close" id="animation-panel-close" title="Close">x</button>
      </div>
      <div class="panel-body animation-panel-body">
        <div class="animation-status" id="animation-status">Loaded current Petri net.</div>

        <div class="animation-preview-wrap">
          <canvas id="animation-preview-canvas" width="640" height="360"></canvas>
          <div class="animation-preview-label" id="animation-preview-label">00.00s / 08.00s</div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <polygon points="5 3 19 12 5 21 5 3"/>
              </svg>
            </span>
            <span>Playback</span>
          </div>
          <div class="dash-section-body">
            <div class="animation-play-row">
              <button id="animation-play" class="sim-btn sim-btn-success" title="Play preview">Play</button>
              <button id="animation-stop" class="sim-btn sim-btn-warning" title="Stop preview">Stop</button>
              <button id="animation-refresh" class="sim-btn generation-secondary-btn" title="Reload current net">Reload Net</button>
            </div>
            <input id="animation-scrubber" class="animation-scrubber" type="range" min="0" max="8000" value="0" step="16">
          </div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M4 6h16"/><path d="M4 12h10"/><path d="M4 18h16"/><circle cx="17" cy="12" r="3"/>
              </svg>
            </span>
            <span>Presets</span>
          </div>
          <div class="dash-section-body animation-preset-grid">
            <button class="sim-btn sim-btn-primary" data-preset="reveal">Reveal Net</button>
            <button class="sim-btn generation-analysis-btn" data-preset="flow">Animate Flow</button>
            <button class="sim-btn generation-analysis-btn alt" data-preset="data">DPN Story</button>
            <button class="sim-btn sim-btn-danger" data-preset="clear">Clear</button>
          </div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M12 5v14"/><path d="M5 12h14"/>
              </svg>
            </span>
            <span>Add Clip</span>
          </div>
          <div class="dash-section-body animation-form-grid">
            <label>
              Element
              <select id="animation-target"></select>
            </label>
            <label>
              Effect
              <select id="animation-effect">
                ${EFFECTS.map(effect => `<option value="${effect.value}">${effect.label}</option>`).join('')}
              </select>
            </label>
            <label>
              Start
              <input id="animation-start" type="number" min="0" step="100" value="0">
            </label>
            <label>
              Duration
              <input id="animation-duration" type="number" min="100" step="100" value="700">
            </label>
            <label>
              Color
              <input id="animation-color" type="color" value="${COLORS.cyan}">
            </label>
            <label class="animation-form-wide">
              Text
              <input id="animation-text" type="text" value="Explain this step">
            </label>
            <button id="animation-add-clip" class="sim-btn sim-btn-primary animation-form-wide">Add to Timeline</button>
          </div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M3 12h18"/><path d="M7 7v10"/><path d="M17 7v10"/>
              </svg>
            </span>
            <span>Timeline</span>
            <span class="dash-badge" id="animation-clip-count">0</span>
          </div>
          <div class="dash-section-body">
            <div id="animation-timeline" class="animation-timeline"></div>
          </div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M12 20h9"/><path d="M16.5 3.5a2.1 2.1 0 0 1 3 3L7 19l-4 1 1-4Z"/>
              </svg>
            </span>
            <span>Clip Inspector</span>
          </div>
          <div class="dash-section-body" id="animation-inspector">
            <p class="sim-empty-state-text">Select a clip to edit its timing, color, and caption.</p>
          </div>
        </div>

        <div class="dash-section">
          <div class="dash-section-header">
            <span class="dash-icon">
              <svg width="14" height="14" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2">
                <path d="M15 10l4.6-2.3A1 1 0 0 1 21 8.6v6.8a1 1 0 0 1-1.4.9L15 14"/>
                <rect x="3" y="6" width="12" height="12" rx="2"/>
              </svg>
            </span>
            <span>Export</span>
          </div>
          <div class="dash-section-body animation-export-grid">
            <label>
              Length
              <input id="animation-total-duration" type="number" min="1000" max="120000" step="500" value="8000">
            </label>
            <label>
              FPS
              <input id="animation-fps" type="number" min="5" max="60" step="1" value="24">
            </label>
            <label>
              Video size
              <select id="animation-resolution">
                ${EXPORT_RESOLUTIONS.map(item => `
                  <option value="${item.value}" ${item.value === '1920x1080' ? 'selected' : ''}>${item.label}</option>
                `).join('')}
              </select>
            </label>
            <label>
              Width
              <input id="animation-export-width" type="number" min="320" max="4096" step="2" value="1920">
            </label>
            <label>
              Height
              <input id="animation-export-height" type="number" min="180" max="4096" step="2" value="1080">
            </label>
            <label>
              Background
              <input id="animation-bg" type="color" value="${COLORS.background}">
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-default-hidden" type="checkbox">
              Start hidden
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-labels" type="checkbox" checked>
              Labels
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-captions" type="checkbox" checked>
              Caption boxes
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-data" type="checkbox" checked>
              Data strip
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-callouts" type="checkbox" checked>
              Data table
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-progress" type="checkbox" checked>
              Progress bar
            </label>
            <label class="animation-checkbox-row">
              <input id="animation-show-grid" type="checkbox">
              Grid
            </label>
            <button id="animation-export-webm" class="sim-btn sim-btn-primary animation-form-wide">Export WebM</button>
            <button id="animation-export-gif" class="sim-btn generation-analysis-btn animation-form-wide">Export GIF</button>
            <button id="animation-export-png" class="sim-btn generation-secondary-btn animation-form-wide">Save Frame PNG</button>
          </div>
        </div>
      </div>
      </div>
    `;
  }

  _bindPanelEvents() {
    this.panel.querySelector('#animation-panel-close')?.addEventListener('click', () => this.close());
    this.panel.addEventListener('click', event => {
      if (event.target === this.panel) this.close();
    });
    document.addEventListener('keydown', event => {
      if (event.key === 'Escape' && this.isOpen) this.close();
    });
    this.panel.querySelector('#animation-play')?.addEventListener('click', () => this.play());
    this.panel.querySelector('#animation-stop')?.addEventListener('click', () => this.stop());
    this.panel.querySelector('#animation-refresh')?.addEventListener('click', () => this.refreshFromNet({ buildIfEmpty: false }));
    this.panel.querySelector('#animation-add-clip')?.addEventListener('click', () => this.addClipFromForm());
    this.panel.querySelector('#animation-export-webm')?.addEventListener('click', () => this.exportWebM());
    this.panel.querySelector('#animation-export-gif')?.addEventListener('click', () => this.exportGif());
    this.panel.querySelector('#animation-export-png')?.addEventListener('click', () => this.exportPng());

    this.panel.querySelector('#animation-scrubber')?.addEventListener('input', event => {
      this.timeMs = Number(event.target.value) || 0;
      this.stop();
      this.renderPreview();
    });

    this.panel.querySelectorAll('[data-preset]').forEach(button => {
      button.addEventListener('click', () => {
        const preset = button.dataset.preset;
        if (preset === 'reveal') this.buildRevealTimeline();
        if (preset === 'flow') this.buildFlowTimeline();
        if (preset === 'data') this.buildDataTimeline();
        if (preset === 'clear') this.clearTimeline();
      });
    });

    for (const id of [
      'animation-total-duration',
      'animation-fps',
      'animation-resolution',
      'animation-export-width',
      'animation-export-height',
      'animation-bg',
      'animation-default-hidden',
      'animation-show-labels',
      'animation-show-captions',
      'animation-show-data',
      'animation-show-callouts',
      'animation-show-progress',
      'animation-show-grid'
    ]) {
      const element = this.panel.querySelector(`#${id}`);
      element?.addEventListener('input', () => this.readSettings());
      element?.addEventListener('change', () => this.readSettings());
    }

    this.panel.querySelector('#animation-timeline')?.addEventListener('click', event => {
      const button = event.target.closest('button[data-action]');
      const row = event.target.closest('[data-clip-id]');
      if (!row) return;
      const clipId = row.dataset.clipId;

      if (!button) {
        this.selectClip(clipId);
        return;
      }

      const action = button.dataset.action;
      if (action === 'delete') this.deleteClip(clipId);
      if (action === 'duplicate') this.duplicateClip(clipId);
      if (action === 'select') this.selectClip(clipId);
    });

    this.panel.querySelector('#animation-inspector')?.addEventListener('input', event => {
      if (!event.target.matches('[data-inspector]')) return;
      this.updateSelectedClipFromInspector();
    });
  }

  toggle() {
    if (this.isOpen) this.close();
    else this.open();
  }

  open() {
    this.isOpen = true;
    this.panel.classList.add('open');
    this.toggleBtn.classList.add('active');
    this.refreshFromNet({ buildIfEmpty: this.clips.length === 0 });
  }

  close() {
    this.stop();
    this.isOpen = false;
    this.panel.classList.remove('open');
    this.toggleBtn.classList.remove('active');
  }

  getNet() {
    return this.app?.api?.petriNet || null;
  }

  readSettings() {
    this.settings.duration = clamp(Number(this.panel.querySelector('#animation-total-duration')?.value) || 8000, 1000, 120000);
    this.settings.fps = clamp(Number(this.panel.querySelector('#animation-fps')?.value) || 24, 5, 60);
    this.settings.exportResolution = this.panel.querySelector('#animation-resolution')?.value || '1920x1080';
    const resolution = EXPORT_RESOLUTIONS.find(item => item.value === this.settings.exportResolution);
    if (resolution && resolution.value !== 'custom') {
      this.settings.exportWidth = resolution.width;
      this.settings.exportHeight = resolution.height;
    } else {
      this.settings.exportWidth = clamp(Math.round(Number(this.panel.querySelector('#animation-export-width')?.value) || 1920), 320, 4096);
      this.settings.exportHeight = clamp(Math.round(Number(this.panel.querySelector('#animation-export-height')?.value) || 1080), 180, 4096);
    }
    this.syncResolutionInputs();
    this.settings.background = this.panel.querySelector('#animation-bg')?.value || COLORS.background;
    this.settings.defaultHidden = Boolean(this.panel.querySelector('#animation-default-hidden')?.checked);
    this.settings.showLabels = Boolean(this.panel.querySelector('#animation-show-labels')?.checked);
    this.settings.showCaptions = Boolean(this.panel.querySelector('#animation-show-captions')?.checked);
    this.settings.showDataStrip = Boolean(this.panel.querySelector('#animation-show-data')?.checked);
    this.settings.showDataCallouts = Boolean(this.panel.querySelector('#animation-show-callouts')?.checked);
    this.settings.showProgress = Boolean(this.panel.querySelector('#animation-show-progress')?.checked);
    this.settings.showGrid = Boolean(this.panel.querySelector('#animation-show-grid')?.checked);

    const scrubber = this.panel.querySelector('#animation-scrubber');
    if (scrubber) {
      scrubber.max = String(this.settings.duration);
      scrubber.value = String(clamp(this.timeMs, 0, this.settings.duration));
    }
    this.timeMs = clamp(this.timeMs, 0, this.settings.duration);
    this.renderPreview();
  }

  refreshFromNet({ buildIfEmpty = false } = {}) {
    this.readSettings();
    this.populateTargetSelect();
    this.updateStatus();

    if (buildIfEmpty && this.clips.length === 0) {
      this.buildRevealTimeline();
      return;
    }

    this.renderTimeline();
    this.renderInspector();
    this.renderPreview();
  }

  refresh() {
    if (!this.panel) return;
    this.populateTargetSelect();
    this.updateStatus();
    this.renderTimeline();
    this.renderPreview();
  }

  updateStatus(message = null) {
    const status = this.panel.querySelector('#animation-status');
    const net = this.getNet();
    if (!status || !net) return;

    const places = normalizeMapLike(net.getVisiblePlaces ? net.getVisiblePlaces() : net.places).length;
    const transitions = normalizeMapLike(net.getVisibleTransitions ? net.getVisibleTransitions() : net.transitions).length;
    const arcs = normalizeMapLike(net.getVisibleArcs ? net.getVisibleArcs() : net.arcs).length;
    const variables = this.getDataVariables().length;

    status.textContent = message || `Current net loaded: ${places} places, ${transitions} transitions, ${arcs} arcs${variables ? `, ${variables} data variables` : ''}.`;
  }

  getElements() {
    const net = this.getNet();
    if (!net) return [];

    const places = normalizeMapLike(net.getVisiblePlaces ? net.getVisiblePlaces() : net.places)
      .map(([id, element]) => ({ id, type: 'place', label: element.label || id, element }));
    const transitions = normalizeMapLike(net.getVisibleTransitions ? net.getVisibleTransitions() : net.transitions)
      .map(([id, element]) => ({ id, type: 'transition', label: element.label || id, element }));
    const arcs = normalizeMapLike(net.getVisibleArcs ? net.getVisibleArcs() : net.arcs)
      .map(([id, element]) => ({ id, type: 'arc', label: element.label || id, element }));

    return [...places, ...transitions, ...arcs].sort((a, b) => {
      const pa = this.getElementCenter(a);
      const pb = this.getElementCenter(b);
      return pa.x === pb.x ? pa.y - pb.y : pa.x - pb.x;
    });
  }

  getElementCenter(item) {
    if (item.type === 'arc') {
      const path = this.getArcPath(item.element);
      if (path.length < 2) return { x: 0, y: 0 };
      return this.pointAtPath(path, 0.5);
    }
    return item.element.position || { x: 0, y: 0 };
  }

  getDataVariables() {
    const net = this.getNet();
    if (!net?.dataVariables) return [];
    return normalizeMapLike(net.dataVariables).map(([, variable]) => variable);
  }

  getVisibleGraph() {
    const elements = this.getElements();
    const nodes = elements.filter(item => item.type !== 'arc');
    const nodeById = new Map(nodes.map(item => [item.id, item]));
    const arcs = elements.filter(item => (
      item.type === 'arc'
      && nodeById.has(item.element.source)
      && nodeById.has(item.element.target)
    ));
    const outgoing = new Map(nodes.map(item => [item.id, []]));
    const incoming = new Map(nodes.map(item => [item.id, []]));

    for (const arc of arcs) {
      outgoing.get(arc.element.source)?.push(arc);
      incoming.get(arc.element.target)?.push(arc);
    }

    const sortByFlowPosition = (a, b) => {
      const ca = this.getElementCenter(a);
      const cb = this.getElementCenter(b);
      return ca.x === cb.x ? ca.y - cb.y : ca.x - cb.x;
    };
    const sortArcsByTarget = (a, b) => {
      const ta = nodeById.get(a.element.target);
      const tb = nodeById.get(b.element.target);
      return sortByFlowPosition(ta || a, tb || b);
    };

    for (const list of outgoing.values()) list.sort(sortArcsByTarget);
    for (const list of incoming.values()) list.sort((a, b) => sortByFlowPosition(
      nodeById.get(a.element.source) || a,
      nodeById.get(b.element.source) || b
    ));

    return { nodes, arcs, nodeById, outgoing, incoming, sortByFlowPosition };
  }

  getFlowRevealStarts(graph, remainingNodeIds = null) {
    const inScope = item => !remainingNodeIds || remainingNodeIds.has(item.id);
    const candidates = graph.nodes.filter(inScope).sort(graph.sortByFlowPosition);
    const markedPlaces = candidates.filter(item => item.type === 'place' && Number(item.element.tokens) > 0);
    if (markedPlaces.length) return markedPlaces;

    const sourcePlaces = candidates.filter(item => {
      if (item.type !== 'place') return false;
      const incoming = graph.incoming.get(item.id) || [];
      return !incoming.some(arc => !remainingNodeIds || remainingNodeIds.has(arc.element.source));
    });
    if (sourcePlaces.length) return sourcePlaces;

    const sourceNodes = candidates.filter(item => {
      const incoming = graph.incoming.get(item.id) || [];
      return !incoming.some(arc => !remainingNodeIds || remainingNodeIds.has(arc.element.source));
    });
    return sourceNodes.length ? sourceNodes : candidates.slice(0, 1);
  }

  populateTargetSelect() {
    const select = this.panel.querySelector('#animation-target');
    if (!select) return;

    const previous = select.value;
    const elements = this.getElements();
    select.innerHTML = `
      <option value="__all__" data-type="all">All elements</option>
      <option value="__scene__" data-type="scene">Scene caption</option>
      ${elements.map(item => `
        <option value="${escapeHtml(item.id)}" data-type="${item.type}">
          ${escapeHtml(item.type)}: ${escapeHtml(item.label)}
        </option>
      `).join('')}
    `;
    if ([...select.options].some(option => option.value === previous)) {
      select.value = previous;
    }
  }

  buildRevealTimeline() {
    const graph = this.getVisibleGraph();
    let cursor = 360;
    this.settings.defaultHidden = true;
    const hiddenInput = this.panel.querySelector('#animation-default-hidden');
    if (hiddenInput) hiddenInput.checked = true;

    this.clips = [{
      id: uid(),
      effect: 'caption',
      targetId: '__scene__',
      targetType: 'scene',
      label: 'Opening title',
      start: 0,
      duration: 1800,
      color: COLORS.blue,
      text: this.getNet()?.name || 'Petri net presentation'
    }];

    if (!graph.nodes.length) {
      this.settings.duration = 5000;
      this.syncSettingsInputs();
      this.afterTimelineChange('Reveal timeline generated for an empty net.');
      return;
    }

    const revealedNodes = new Set();
    const revealedArcs = new Set();
    const queuedNodes = new Set();
    const queue = [];

    const pushClip = (effect, item, start, duration, color, label, text = item.label) => {
      this.clips.push({
        id: uid(),
        effect,
        targetId: item.id,
        targetType: item.type,
        label,
        start,
        duration,
        color,
        text
      });
    };

    const revealNode = (item, start, { pulse = false } = {}) => {
      if (!item || revealedNodes.has(item.id)) return false;
      revealedNodes.add(item.id);
      const color = item.type === 'transition' ? COLORS.green : COLORS.cyan;
      pushClip(
        'appear',
        item,
        start,
        item.type === 'transition' ? 640 : 580,
        color,
        `Reveal ${item.label}`
      );
      if (pulse) {
        pushClip('pulse', item, start + 140, 900, COLORS.green, `Start at ${item.label}`);
      }
      if (!queuedNodes.has(item.id)) {
        queue.push(item);
        queuedNodes.add(item.id);
      }
      return true;
    };

    const revealArc = (item, start) => {
      if (!item || revealedArcs.has(item.id)) return false;
      revealedArcs.add(item.id);
      const source = graph.nodeById.get(item.element.source);
      const target = graph.nodeById.get(item.element.target);
      const arcText = `${source?.label || item.element.source} -> ${target?.label || item.element.target}`;
      pushClip('appear', item, start, 440, COLORS.orange, `Reveal ${arcText}`, arcText);
      pushClip('tokenFlow', item, start + 80, 660, COLORS.orange, `Flow ${arcText}`, arcText);
      return true;
    };

    const revealStarts = starts => {
      let latest = cursor;
      starts.forEach((item, index) => {
        const start = cursor + index * 160;
        if (revealNode(item, start, { pulse: true })) {
          latest = Math.max(latest, start + 760);
        }
      });
      cursor = latest + 220;
    };

    revealStarts(this.getFlowRevealStarts(graph));

    while (queue.length || revealedNodes.size < graph.nodes.length) {
      if (!queue.length) {
        const remainingNodeIds = new Set(graph.nodes.filter(item => !revealedNodes.has(item.id)).map(item => item.id));
        revealStarts(this.getFlowRevealStarts(graph, remainingNodeIds));
        continue;
      }

      const source = queue.shift();
      const outgoing = graph.outgoing.get(source.id) || [];
      if (!outgoing.length) {
        cursor += 90;
        continue;
      }

      for (const arc of outgoing) {
        const target = graph.nodeById.get(arc.element.target);
        if (!target) continue;

        if (revealArc(arc, cursor)) cursor += 310;
        if (revealNode(target, cursor)) {
          cursor += target.type === 'transition' ? 430 : 380;
        }
      }
      cursor += 120;
    }

    for (const arc of graph.arcs) {
      if (revealArc(arc, cursor)) cursor += 260;
    }

    this.settings.duration = Math.max(5000, cursor + 1200);
    this.syncSettingsInputs();
    const markedCount = graph.nodes.filter(item => item.type === 'place' && Number(item.element.tokens) > 0).length;
    this.afterTimelineChange(`Flow-direction reveal generated${markedCount ? ` from ${markedCount} marked place${markedCount === 1 ? '' : 's'}` : ''}.`);
  }

  buildFlowTimeline() {
    const net = this.getNet();
    const transitions = this.getElements().filter(item => item.type === 'transition');
    let cursor = 500;
    this.settings.defaultHidden = false;
    const hiddenInput = this.panel.querySelector('#animation-default-hidden');
    if (hiddenInput) hiddenInput.checked = false;

    this.clips = [{
      id: uid(),
      effect: 'caption',
      targetId: '__scene__',
      targetType: 'scene',
      label: 'Flow title',
      start: 0,
      duration: 1600,
      color: COLORS.blue,
      text: 'Execution flow'
    }];

    for (const item of transitions) {
      const incoming = this.getArcsForTransition(item.id, 'incoming');
      const outgoing = this.getArcsForTransition(item.id, 'outgoing');
      this.clips.push({
        id: uid(),
        effect: 'focus',
        targetId: item.id,
        targetType: 'transition',
        label: `Focus ${item.label}`,
        start: cursor,
        duration: 900,
        color: COLORS.yellow,
        text: item.label
      });
      this.clips.push({
        id: uid(),
        effect: 'pulse',
        targetId: item.id,
        targetType: 'transition',
        label: `Fire ${item.label}`,
        start: cursor + 120,
        duration: 780,
        color: COLORS.green,
        text: item.label
      });

      for (const arc of [...incoming, ...outgoing]) {
        this.clips.push({
          id: uid(),
          effect: 'tokenFlow',
          targetId: arc.id,
          targetType: 'arc',
          label: `Token ${arc.id}`,
          start: cursor + 160,
          duration: 720,
          color: COLORS.orange,
          text: arc.label || arc.id
        });
      }

      if (net?.dataVariables?.size || Array.isArray(net?.dataVariables)) {
        this.clips.push({
          id: uid(),
          effect: 'variableCallout',
          targetId: item.id,
          targetType: 'transition',
          label: `Data ${item.label}`,
          start: cursor + 260,
          duration: 1100,
          color: COLORS.purple,
          text: item.label
        });
      }

      cursor += 1050;
    }

    this.settings.duration = Math.max(5000, cursor + 800);
    this.syncSettingsInputs();
    this.afterTimelineChange('Flow animation generated.');
  }

  buildDataTimeline() {
    const transitions = this.getElements().filter(item => item.type === 'transition');
    this.settings.defaultHidden = false;
    const hiddenInput = this.panel.querySelector('#animation-default-hidden');
    if (hiddenInput) hiddenInput.checked = false;

    this.clips = [{
      id: uid(),
      effect: 'caption',
      targetId: '__scene__',
      targetType: 'scene',
      label: 'Data title',
      start: 0,
      duration: 1700,
      color: COLORS.purple,
      text: 'Data Petri net variables and guards'
    }, {
      id: uid(),
      effect: 'variableCallout',
      targetId: '__scene__',
      targetType: 'scene',
      label: 'Initial data',
      start: 700,
      duration: 2200,
      color: COLORS.purple,
      text: 'Initial data valuation'
    }];

    let cursor = 2600;
    for (const item of transitions.filter(item => item.element.precondition || item.element.postcondition)) {
      this.clips.push({
        id: uid(),
        effect: 'focus',
        targetId: item.id,
        targetType: 'transition',
        label: `Guard ${item.label}`,
        start: cursor,
        duration: 1200,
        color: COLORS.yellow,
        text: item.label
      });
      this.clips.push({
        id: uid(),
        effect: 'caption',
        targetId: '__scene__',
        targetType: 'scene',
        label: `Caption ${item.label}`,
        start: cursor,
        duration: 1200,
        color: COLORS.blue,
        text: `${item.label}: ${item.element.precondition || item.element.postcondition || 'data update'}`
      });
      cursor += 1350;
    }

    this.settings.duration = Math.max(6000, cursor + 900);
    this.syncSettingsInputs();
    this.afterTimelineChange('DPN story timeline generated.');
  }

  clearTimeline() {
    this.clips = [];
    this.selectedClipId = null;
    this.settings.defaultHidden = false;
    const hiddenInput = this.panel.querySelector('#animation-default-hidden');
    if (hiddenInput) hiddenInput.checked = false;
    this.afterTimelineChange('Timeline cleared.');
  }

  getArcsForTransition(transitionId, direction) {
    const net = this.getNet();
    if (!net) return [];

    return normalizeMapLike(net.getVisibleArcs ? net.getVisibleArcs() : net.arcs)
      .filter(([, arc]) => direction === 'incoming' ? arc.target === transitionId : arc.source === transitionId)
      .map(([id, arc]) => ({ id, arc }));
  }

  addClipFromForm() {
    const targetSelect = this.panel.querySelector('#animation-target');
    const selected = targetSelect?.selectedOptions?.[0];
    const effect = this.panel.querySelector('#animation-effect')?.value || 'highlight';
    const targetId = targetSelect?.value || '__all__';
    const targetType = selected?.dataset.type || 'all';
    const start = Math.max(0, Number(this.panel.querySelector('#animation-start')?.value) || 0);
    const duration = Math.max(100, Number(this.panel.querySelector('#animation-duration')?.value) || 700);
    const color = this.panel.querySelector('#animation-color')?.value || COLORS.cyan;
    const text = this.panel.querySelector('#animation-text')?.value || selected?.textContent?.trim() || effect;

    const clip = {
      id: uid(),
      effect,
      targetId,
      targetType,
      label: `${EFFECTS.find(item => item.value === effect)?.label || effect}: ${text}`,
      start,
      duration,
      color,
      text
    };
    this.clips.push(clip);
    this.settings.duration = Math.max(this.settings.duration, start + duration + 500);
    this.syncSettingsInputs();
    this.selectClip(clip.id);
    this.afterTimelineChange('Clip added.');
  }

  afterTimelineChange(message) {
    this.clips.sort((a, b) => a.start === b.start ? a.duration - b.duration : a.start - b.start);
    this.updateStatus(message);
    this.renderTimeline();
    this.renderInspector();
    this.renderPreview();
  }

  syncResolutionInputs() {
    const resolutionInput = this.panel.querySelector('#animation-resolution');
    const widthInput = this.panel.querySelector('#animation-export-width');
    const heightInput = this.panel.querySelector('#animation-export-height');
    const isCustom = this.settings.exportResolution === 'custom';

    if (resolutionInput) resolutionInput.value = this.settings.exportResolution;
    if (widthInput) {
      widthInput.value = String(this.settings.exportWidth);
      widthInput.disabled = !isCustom;
    }
    if (heightInput) {
      heightInput.value = String(this.settings.exportHeight);
      heightInput.disabled = !isCustom;
    }
  }

  syncSettingsInputs() {
    const durationInput = this.panel.querySelector('#animation-total-duration');
    const fpsInput = this.panel.querySelector('#animation-fps');
    const bgInput = this.panel.querySelector('#animation-bg');
    if (durationInput) durationInput.value = String(this.settings.duration);
    if (fpsInput) fpsInput.value = String(this.settings.fps);
    if (bgInput) bgInput.value = this.settings.background;
    this.syncResolutionInputs();
    this.readSettings();
  }

  renderTimeline() {
    const container = this.panel.querySelector('#animation-timeline');
    const badge = this.panel.querySelector('#animation-clip-count');
    if (badge) badge.textContent = String(this.clips.length);
    if (!container) return;

    if (!this.clips.length) {
      container.innerHTML = '<p class="sim-empty-state-text">No animation clips yet. Use a preset or add a clip.</p>';
      return;
    }

    container.innerHTML = this.clips.map(clip => {
      const left = clamp((clip.start / this.settings.duration) * 100, 0, 100);
      const width = clamp((clip.duration / this.settings.duration) * 100, 2, 100 - left);
      return `
        <div class="animation-clip-row ${clip.id === this.selectedClipId ? 'selected' : ''}" data-clip-id="${escapeHtml(clip.id)}">
          <button class="animation-clip-main" data-action="select" title="Select clip">
            <span class="animation-clip-effect" style="background:${escapeHtml(clip.color)}"></span>
            <span>
              <strong>${escapeHtml(clip.label || clip.effect)}</strong>
              <small>${escapeHtml(clip.effect)} at ${formatMs(clip.start)} for ${formatMs(clip.duration)}</small>
            </span>
          </button>
          <div class="animation-clip-actions">
            <button data-action="duplicate" title="Duplicate">Copy</button>
            <button data-action="delete" title="Delete">Del</button>
          </div>
          <div class="animation-clip-bar">
            <span style="left:${left}%;width:${width}%;background:${escapeHtml(clip.color)}"></span>
          </div>
        </div>
      `;
    }).join('');
  }

  selectClip(clipId) {
    this.selectedClipId = clipId;
    const clip = this.clips.find(item => item.id === clipId);
    if (clip) {
      this.timeMs = clamp(clip.start, 0, this.settings.duration);
    }
    this.renderTimeline();
    this.renderInspector();
    this.renderPreview();
  }

  deleteClip(clipId) {
    this.clips = this.clips.filter(clip => clip.id !== clipId);
    if (this.selectedClipId === clipId) this.selectedClipId = null;
    this.afterTimelineChange('Clip deleted.');
  }

  duplicateClip(clipId) {
    const clip = this.clips.find(item => item.id === clipId);
    if (!clip) return;
    const copy = { ...clip, id: uid(), start: clip.start + 300, label: `${clip.label} copy` };
    this.clips.push(copy);
    this.selectClip(copy.id);
    this.afterTimelineChange('Clip duplicated.');
  }

  renderInspector() {
    const container = this.panel.querySelector('#animation-inspector');
    if (!container) return;
    const clip = this.clips.find(item => item.id === this.selectedClipId);

    if (!clip) {
      container.innerHTML = '<p class="sim-empty-state-text">Select a clip to edit its timing, color, and caption.</p>';
      return;
    }

    container.innerHTML = `
      <div class="animation-form-grid">
        <label>
          Effect
          <select data-inspector="effect">
            ${EFFECTS.map(effect => `<option value="${effect.value}" ${clip.effect === effect.value ? 'selected' : ''}>${effect.label}</option>`).join('')}
          </select>
        </label>
        <label>
          Start
          <input data-inspector="start" type="number" min="0" step="50" value="${clip.start}">
        </label>
        <label>
          Duration
          <input data-inspector="duration" type="number" min="100" step="50" value="${clip.duration}">
        </label>
        <label>
          Color
          <input data-inspector="color" type="color" value="${clip.color}">
        </label>
        <label class="animation-form-wide">
          Label
          <input data-inspector="label" type="text" value="${escapeHtml(clip.label || '')}">
        </label>
        <label class="animation-form-wide">
          Text
          <input data-inspector="text" type="text" value="${escapeHtml(clip.text || '')}">
        </label>
      </div>
    `;
  }

  updateSelectedClipFromInspector() {
    const clip = this.clips.find(item => item.id === this.selectedClipId);
    if (!clip) return;

    const inspector = this.panel.querySelector('#animation-inspector');
    clip.effect = inspector.querySelector('[data-inspector="effect"]')?.value || clip.effect;
    clip.start = Math.max(0, Number(inspector.querySelector('[data-inspector="start"]')?.value) || 0);
    clip.duration = Math.max(100, Number(inspector.querySelector('[data-inspector="duration"]')?.value) || 100);
    clip.color = inspector.querySelector('[data-inspector="color"]')?.value || clip.color;
    clip.label = inspector.querySelector('[data-inspector="label"]')?.value || clip.label;
    clip.text = inspector.querySelector('[data-inspector="text"]')?.value || clip.text;
    this.settings.duration = Math.max(this.settings.duration, clip.start + clip.duration + 500);
    this.syncSettingsInputs();
    this.afterTimelineChange('Clip updated.');
  }

  play() {
    if (this.isPlaying || this.isExporting) return;
    this.isPlaying = true;
    this.lastTick = performance.now();
    this.panel.querySelector('#animation-play').textContent = 'Playing';

    const tick = now => {
      if (!this.isPlaying) return;
      const delta = now - this.lastTick;
      this.lastTick = now;
      this.timeMs += delta;
      if (this.timeMs > this.settings.duration) {
        this.timeMs = 0;
      }
      this.renderPreview();
      this.playbackFrame = requestAnimationFrame(tick);
    };
    this.playbackFrame = requestAnimationFrame(tick);
  }

  stop() {
    if (this.playbackFrame) {
      cancelAnimationFrame(this.playbackFrame);
      this.playbackFrame = null;
    }
    this.isPlaying = false;
    const playBtn = this.panel?.querySelector('#animation-play');
    if (playBtn) playBtn.textContent = 'Play';
  }

  renderPreview() {
    if (!this.previewCanvas) return;
    this.drawFrame(this.previewCanvas, this.timeMs);
    const scrubber = this.panel.querySelector('#animation-scrubber');
    if (scrubber) scrubber.value = String(this.timeMs);
    const label = this.panel.querySelector('#animation-preview-label');
    if (label) label.textContent = `${formatMs(this.timeMs)} / ${formatMs(this.settings.duration)}`;
  }

  drawFrame(canvas, timeMs) {
    const ctx = canvas.getContext('2d');
    const net = this.getNet();
    const width = canvas.width;
    const height = canvas.height;

    ctx.save();
    ctx.fillStyle = this.settings.background;
    ctx.fillRect(0, 0, width, height);

    if (!net) {
      ctx.fillStyle = COLORS.ink;
      ctx.font = '18px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.fillText('No Petri net loaded', width / 2, height / 2);
      ctx.restore();
      return;
    }

    const camera = this.computeCamera(width, height);
    const states = this.computeElementStates(timeMs);
    const activeClips = this.getActiveClips(timeMs);

    ctx.save();
    ctx.translate(camera.x, camera.y);
    ctx.scale(camera.scale, camera.scale);
    if (this.settings.showGrid) this.drawPresentationGrid(ctx, camera, width, height);

    for (const [, arc] of normalizeMapLike(net.getVisibleArcs ? net.getVisibleArcs() : net.arcs)) {
      const state = states.get(arc.id) || { opacity: 1, glow: 0, scale: 1 };
      this.drawArc(ctx, arc, state, states);
    }

    for (const [, place] of normalizeMapLike(net.getVisiblePlaces ? net.getVisiblePlaces() : net.places)) {
      this.drawPlace(ctx, place, states.get(place.id) || { opacity: 1, glow: 0, scale: 1 });
    }

    for (const [, transition] of normalizeMapLike(net.getVisibleTransitions ? net.getVisibleTransitions() : net.transitions)) {
      this.drawTransition(ctx, transition, states.get(transition.id) || { opacity: 1, glow: 0, scale: 1 });
    }

    for (const clip of activeClips.filter(item => item.effect === 'tokenFlow')) {
      this.drawTokenFlow(ctx, clip, timeMs);
    }

    ctx.restore();

    this.drawSceneOverlays(ctx, activeClips, timeMs, width, height);
    ctx.restore();
  }

  computeElementStates(timeMs) {
    const elements = this.getElements();
    const states = new Map();
    const hasAppear = new Map();
    for (const clip of this.clips) {
      if (clip.effect !== 'appear') continue;
      for (const item of elements) {
        if (this.clipMatches(clip, item)) hasAppear.set(item.id, true);
      }
    }

    for (const item of elements) {
      states.set(item.id, {
        opacity: this.settings.defaultHidden || hasAppear.get(item.id) ? 0 : 1,
        glow: 0,
        scale: 1,
        color: COLORS.cyan
      });
    }

    for (const clip of this.clips) {
      for (const item of elements) {
        if (!this.clipMatches(clip, item)) continue;
        const state = states.get(item.id);
        const local = (timeMs - clip.start) / clip.duration;
        const progress = easeInOut(local);

        if (clip.effect === 'appear') {
          if (timeMs >= clip.start + clip.duration) state.opacity = Math.max(state.opacity, 1);
          else if (timeMs >= clip.start) state.opacity = Math.max(state.opacity, progress);
        } else if (clip.effect === 'disappear') {
          if (timeMs >= clip.start + clip.duration) state.opacity = 0;
          else if (timeMs >= clip.start) state.opacity = Math.min(state.opacity, 1 - progress);
        } else if (timeMs >= clip.start && timeMs <= clip.start + clip.duration) {
          if (clip.effect === 'highlight' || clip.effect === 'focus') {
            state.glow = Math.max(state.glow, Math.sin(clamp(local, 0, 1) * Math.PI));
            state.color = clip.color;
          }
          if (clip.effect === 'pulse') {
            state.scale = Math.max(state.scale, 1 + Math.sin(clamp(local, 0, 1) * Math.PI * 4) * 0.14);
            state.glow = Math.max(state.glow, 0.8);
            state.color = clip.color;
          }
        }
      }
    }

    return states;
  }

  clipMatches(clip, item) {
    if (clip.targetId === '__all__') return true;
    if (clip.targetType === 'scene') return false;
    return clip.targetId === item.id;
  }

  getActiveClips(timeMs) {
    return this.clips.filter(clip => timeMs >= clip.start && timeMs <= clip.start + clip.duration);
  }

  computeCamera(width, height) {
    const bounds = this.getNetBounds();
    const padding = 70;
    const worldWidth = Math.max(1, bounds.maxX - bounds.minX);
    const worldHeight = Math.max(1, bounds.maxY - bounds.minY);
    const scale = Math.min((width - padding * 2) / worldWidth, (height - padding * 2) / worldHeight);
    const safeScale = clamp(scale, 0.15, 3);
    return {
      scale: safeScale,
      x: width / 2 - ((bounds.minX + bounds.maxX) / 2) * safeScale,
      y: height / 2 - ((bounds.minY + bounds.maxY) / 2) * safeScale
    };
  }

  getNetBounds() {
    const net = this.getNet();
    const points = [];
    if (!net) return { minX: 0, minY: 0, maxX: 100, maxY: 100 };

    for (const [, place] of normalizeMapLike(net.getVisiblePlaces ? net.getVisiblePlaces() : net.places)) {
      const r = place.radius || 20;
      points.push({ x: place.position.x - r - 30, y: place.position.y - r - 40 });
      points.push({ x: place.position.x + r + 30, y: place.position.y + r + 42 });
    }
    for (const [, transition] of normalizeMapLike(net.getVisibleTransitions ? net.getVisibleTransitions() : net.transitions)) {
      const w = transition.width || 20;
      const h = transition.height || 50;
      points.push({ x: transition.position.x - w / 2 - 35, y: transition.position.y - h / 2 - 40 });
      points.push({ x: transition.position.x + w / 2 + 35, y: transition.position.y + h / 2 + 42 });
    }
    for (const [, arc] of normalizeMapLike(net.getVisibleArcs ? net.getVisibleArcs() : net.arcs)) {
      for (const point of arc.points || []) points.push(point);
    }

    if (!points.length) return { minX: 0, minY: 0, maxX: 100, maxY: 100 };
    return {
      minX: Math.min(...points.map(point => point.x)),
      minY: Math.min(...points.map(point => point.y)),
      maxX: Math.max(...points.map(point => point.x)),
      maxY: Math.max(...points.map(point => point.y))
    };
  }

  drawPresentationGrid(ctx, camera, width, height) {
    const step = 50;
    const worldLeft = -camera.x / camera.scale;
    const worldTop = -camera.y / camera.scale;
    const worldRight = (width - camera.x) / camera.scale;
    const worldBottom = (height - camera.y) / camera.scale;
    ctx.save();
    ctx.strokeStyle = 'rgba(76, 86, 106, 0.12)';
    ctx.lineWidth = 1 / camera.scale;
    ctx.beginPath();
    for (let x = Math.floor(worldLeft / step) * step; x <= worldRight; x += step) {
      ctx.moveTo(x, worldTop);
      ctx.lineTo(x, worldBottom);
    }
    for (let y = Math.floor(worldTop / step) * step; y <= worldBottom; y += step) {
      ctx.moveTo(worldLeft, y);
      ctx.lineTo(worldRight, y);
    }
    ctx.stroke();
    ctx.restore();
  }

  drawArc(ctx, arc, state, states) {
    const net = this.getNet();
    const source = net.places.get(arc.source) || net.transitions.get(arc.source);
    const target = net.places.get(arc.target) || net.transitions.get(arc.target);
    if (!source || !target) return;

    const sourceOpacity = states.get(source.id)?.opacity ?? 1;
    const targetOpacity = states.get(target.id)?.opacity ?? 1;
    const endpointOpacity = this.settings.defaultHidden
      ? Math.max(sourceOpacity, targetOpacity)
      : Math.min(sourceOpacity, targetOpacity);
    const opacity = clamp((state.opacity ?? 1) * endpointOpacity, 0, 1);
    if (opacity <= 0.01) return;

    const path = this.getArcPath(arc);
    if (path.length < 2) return;

    ctx.save();
    ctx.globalAlpha = opacity;
    ctx.lineWidth = state.glow ? 4 : 2;
    ctx.strokeStyle = state.glow ? state.color : COLORS.arc;
    ctx.fillStyle = ctx.strokeStyle;
    if (arc.type === 'modifier') ctx.setLineDash([7, 6]);

    ctx.beginPath();
    ctx.moveTo(path[0].x, path[0].y);
    for (const point of path.slice(1)) ctx.lineTo(point.x, point.y);
    ctx.stroke();

    const end = path[path.length - 1];
    const previous = path[path.length - 2];
    const angle = Math.atan2(end.y - previous.y, end.x - previous.x);
    if (arc.type === 'inhibitor') this.drawCircleEnding(ctx, end, angle);
    else this.drawArrowhead(ctx, end, angle);

    if ((arc.weight > 1 || arc.label) && this.settings.showLabels) {
      const mid = this.pointAtPath(path, 0.5);
      const label = arc.label || String(arc.weight);
      ctx.font = '12px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      const metrics = ctx.measureText(label);
      ctx.fillStyle = this.settings.background;
      ctx.fillRect(mid.x - metrics.width / 2 - 4, mid.y - 9, metrics.width + 8, 18);
      ctx.fillStyle = COLORS.ink;
      ctx.fillText(label, mid.x, mid.y);
    }

    ctx.restore();
  }

  drawPlace(ctx, place, state) {
    const opacity = clamp(state.opacity ?? 1, 0, 1);
    if (opacity <= 0.01) return;
    const radius = (place.radius || 20) * (state.scale || 1);

    ctx.save();
    ctx.globalAlpha = opacity;
    if (state.glow) {
      ctx.shadowColor = state.color;
      ctx.shadowBlur = 22 * state.glow;
    }

    ctx.beginPath();
    ctx.arc(place.position.x, place.position.y, radius, 0, Math.PI * 2);
    ctx.fillStyle = COLORS.placeFill;
    ctx.fill();
    ctx.lineWidth = 2.2;
    ctx.strokeStyle = state.glow ? state.color : COLORS.ink;
    ctx.stroke();

    if (place.finalMarking !== null && place.finalMarking !== undefined) {
      ctx.beginPath();
      ctx.arc(place.position.x, place.position.y, radius + 4, 0, Math.PI * 2);
      ctx.strokeStyle = place.tokens === place.finalMarking ? COLORS.green : COLORS.yellow;
      ctx.stroke();
    }

    this.drawTokens(ctx, place, radius);

    if (this.settings.showLabels) {
      ctx.shadowBlur = 0;
      ctx.fillStyle = COLORS.ink;
      ctx.font = '12px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'top';
      ctx.fillText(place.label || place.id, place.position.x, place.position.y + radius + 8);
    }
    ctx.restore();
  }

  drawTransition(ctx, transition, state) {
    const opacity = clamp(state.opacity ?? 1, 0, 1);
    if (opacity <= 0.01) return;
    const width = (transition.width || 20) * (state.scale || 1);
    const height = (transition.height || 50) * (state.scale || 1);
    const x = transition.position.x - width / 2;
    const y = transition.position.y - height / 2;

    ctx.save();
    ctx.globalAlpha = opacity;
    if (state.glow) {
      ctx.shadowColor = state.color;
      ctx.shadowBlur = 24 * state.glow;
    }

    ctx.fillStyle = transition.silent ? COLORS.muted : transition.isEnabled ? COLORS.enabledFill : COLORS.transitionFill;
    ctx.strokeStyle = state.glow ? state.color : COLORS.ink;
    ctx.lineWidth = 2.2;
    ctx.fillRect(x, y, width, height);
    ctx.strokeRect(x, y, width, height);

    if (this.settings.showLabels && !transition.silent) {
      ctx.shadowBlur = 0;
      ctx.fillStyle = COLORS.ink;
      ctx.font = '12px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'top';
      ctx.fillText(transition.label || transition.id, transition.position.x, y + height + 8);
    }
    ctx.restore();
  }

  drawTokens(ctx, place, radius) {
    const tokens = Number(place.tokens) || 0;
    if (tokens <= 0) return;
    ctx.fillStyle = COLORS.ink;

    if (tokens > 3) {
      ctx.font = 'bold 14px system-ui, sans-serif';
      ctx.textAlign = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(String(tokens), place.position.x, place.position.y);
      return;
    }

    const offsets = {
      1: [[0, 0]],
      2: [[-5, 0], [5, 0]],
      3: [[0, -5], [-5, 6], [5, 6]]
    }[tokens];
    for (const [dx, dy] of offsets) {
      ctx.beginPath();
      ctx.arc(place.position.x + dx * (radius / 20), place.position.y + dy * (radius / 20), 4, 0, Math.PI * 2);
      ctx.fill();
    }
  }

  drawTokenFlow(ctx, clip, timeMs) {
    const net = this.getNet();
    const arc = net?.arcs?.get(clip.targetId);
    if (!arc) return;
    const path = this.getArcPath(arc);
    if (path.length < 2) return;

    const local = clamp((timeMs - clip.start) / clip.duration, 0, 1);
    const point = this.pointAtPath(path, easeInOut(local));
    ctx.save();
    ctx.shadowColor = clip.color;
    ctx.shadowBlur = 16;
    ctx.fillStyle = clip.color;
    ctx.beginPath();
    ctx.arc(point.x, point.y, 7, 0, Math.PI * 2);
    ctx.fill();
    ctx.restore();
  }

  drawSceneOverlays(ctx, activeClips, timeMs, width, height) {
    const uiScale = this.getFrameUiScale(width, height);
    const logicalWidth = width / uiScale;
    const logicalHeight = height / uiScale;

    ctx.save();
    ctx.scale(uiScale, uiScale);

    if (this.settings.showDataStrip && this.getDataVariables().length) {
      this.drawDataStrip(ctx, logicalWidth);
    }

    const caption = activeClips.find(clip => clip.effect === 'caption');
    if (caption && this.settings.showCaptions) this.drawCaption(ctx, caption, timeMs, logicalWidth, logicalHeight);

    const callout = activeClips.find(clip => clip.effect === 'variableCallout');
    if (callout && this.settings.showDataCallouts) this.drawVariableCallout(ctx, callout, logicalWidth, logicalHeight);

    if (this.settings.showProgress) {
      ctx.fillStyle = 'rgba(46, 52, 64, 0.24)';
      ctx.fillRect(0, logicalHeight - 5, logicalWidth, 5);
      ctx.fillStyle = COLORS.blue;
      ctx.fillRect(0, logicalHeight - 5, logicalWidth * clamp(timeMs / this.settings.duration, 0, 1), 5);
    }

    ctx.restore();
  }

  getFrameUiScale(width, height) {
    return clamp(Math.min(width / 640, height / 360), 1, 6);
  }

  drawCaption(ctx, clip, timeMs, width, height) {
    const local = clamp((timeMs - clip.start) / clip.duration, 0, 1);
    const alpha = Math.min(easeInOut(local * 3), easeInOut((1 - local) * 3));
    const text = clip.text || clip.label || 'Presentation step';

    ctx.save();
    ctx.globalAlpha = alpha;
    ctx.fillStyle = 'rgba(46, 52, 64, 0.88)';
    this.roundRect(ctx, 34, height - 86, width - 68, 54, 8);
    ctx.fill();
    ctx.fillStyle = clip.color || COLORS.cyan;
    ctx.fillRect(34, height - 86, 5, 54);
    ctx.fillStyle = COLORS.background;
    ctx.font = 'bold 18px system-ui, sans-serif';
    ctx.textAlign = 'left';
    ctx.textBaseline = 'middle';
    this.wrapText(ctx, text, 56, height - 59, width - 110, 22);
    ctx.restore();
  }

  drawDataStrip(ctx, width) {
    const variables = this.getDataVariables();
    if (!variables.length) return;
    const text = variables
      .map(variable => `${variable.name}: ${variable.currentValue ?? variable.value ?? 'null'}`)
      .join('   ');

    ctx.save();
    ctx.fillStyle = 'rgba(46, 52, 64, 0.82)';
    this.roundRect(ctx, 18, 16, Math.min(width - 36, Math.max(220, text.length * 7.2)), 34, 7);
    ctx.fill();
    ctx.fillStyle = COLORS.background;
    ctx.font = '12px system-ui, sans-serif';
    ctx.textAlign = 'left';
    ctx.textBaseline = 'middle';
    ctx.fillText(text, 32, 33);
    ctx.restore();
  }

  drawVariableCallout(ctx, clip, width, height) {
    const variables = this.getDataVariables();
    if (!variables.length) return;

    const boxWidth = Math.min(330, width - 44);
    const rowHeight = 24;
    const boxHeight = 52 + variables.length * rowHeight;
    const x = width - boxWidth - 22;
    const y = 68;

    ctx.save();
    ctx.fillStyle = 'rgba(46, 52, 64, 0.9)';
    this.roundRect(ctx, x, y, boxWidth, boxHeight, 8);
    ctx.fill();
    ctx.strokeStyle = clip.color || COLORS.purple;
    ctx.lineWidth = 2;
    ctx.stroke();

    ctx.fillStyle = COLORS.background;
    ctx.font = 'bold 14px system-ui, sans-serif';
    ctx.textAlign = 'left';
    ctx.textBaseline = 'top';
    ctx.fillText(clip.text || 'Data variables', x + 16, y + 14);

    ctx.font = '12px system-ui, sans-serif';
    variables.forEach((variable, index) => {
      const rowY = y + 44 + index * rowHeight;
      ctx.fillStyle = index % 2 ? 'rgba(216, 222, 233, 0.06)' : 'rgba(216, 222, 233, 0.12)';
      ctx.fillRect(x + 12, rowY - 3, boxWidth - 24, rowHeight - 2);
      ctx.fillStyle = COLORS.cyan;
      ctx.fillText(variable.name, x + 22, rowY);
      ctx.fillStyle = COLORS.background;
      ctx.textAlign = 'right';
      ctx.fillText(String(variable.currentValue ?? variable.value ?? 'null'), x + boxWidth - 22, rowY);
      ctx.textAlign = 'left';
    });
    ctx.restore();
  }

  getArcPath(arc) {
    const net = this.getNet();
    if (!net) return [];
    const source = net.places.get(arc.source) || net.transitions.get(arc.source);
    const target = net.places.get(arc.target) || net.transitions.get(arc.target);
    if (!source || !target) return [];
    const { start, end } = this.calculateArcEndpoints(source, target);
    return [start, ...(arc.points || []), end];
  }

  calculateArcEndpoints(source, target) {
    const start = { x: source.position.x, y: source.position.y };
    const end = { x: target.position.x, y: target.position.y };
    const sourceIsPlace = this.getNet()?.places?.has(source.id);
    const targetIsPlace = this.getNet()?.places?.has(target.id);
    const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);

    if (sourceIsPlace) {
      const radius = source.radius || 20;
      start.x += Math.cos(angle) * radius;
      start.y += Math.sin(angle) * radius;
    } else {
      this.adjustRectEndpoint(start, source, target, 1);
    }

    if (targetIsPlace) {
      const radius = target.radius || 20;
      end.x -= Math.cos(angle) * radius;
      end.y -= Math.sin(angle) * radius;
    } else {
      this.adjustRectEndpoint(end, target, source, -1);
    }

    return { start, end };
  }

  adjustRectEndpoint(point, rectElement, otherElement, direction) {
    const dx = otherElement.position.x - rectElement.position.x;
    const dy = otherElement.position.y - rectElement.position.y;
    const width = rectElement.width || 20;
    const height = rectElement.height || 50;

    if (Math.abs(dx) * height > Math.abs(dy) * width) {
      const side = dx > 0 ? 1 : -1;
      point.x = rectElement.position.x + direction * side * width / 2;
      point.y = rectElement.position.y + direction * dy * (width / 2) / Math.max(1, Math.abs(dx));
    } else {
      const side = dy > 0 ? 1 : -1;
      point.y = rectElement.position.y + direction * side * height / 2;
      point.x = rectElement.position.x + direction * dx * (height / 2) / Math.max(1, Math.abs(dy));
    }
  }

  drawArrowhead(ctx, position, angle) {
    const size = 11;
    ctx.beginPath();
    ctx.moveTo(position.x, position.y);
    ctx.lineTo(position.x - size * Math.cos(angle - Math.PI / 6), position.y - size * Math.sin(angle - Math.PI / 6));
    ctx.lineTo(position.x - size * Math.cos(angle + Math.PI / 6), position.y - size * Math.sin(angle + Math.PI / 6));
    ctx.closePath();
    ctx.fill();
  }

  drawCircleEnding(ctx, position, angle) {
    const x = position.x - Math.cos(angle) * 9;
    const y = position.y - Math.sin(angle) * 9;
    ctx.beginPath();
    ctx.arc(x, y, 6, 0, Math.PI * 2);
    ctx.fillStyle = this.settings.background;
    ctx.fill();
    ctx.stroke();
  }

  pointAtPath(path, ratio) {
    const parts = [];
    let total = 0;
    for (let i = 1; i < path.length; i += 1) {
      const from = path[i - 1];
      const to = path[i];
      const length = Math.hypot(to.x - from.x, to.y - from.y);
      parts.push({ from, to, start: total, end: total + length, length });
      total += length;
    }
    if (!total) return path[0] || { x: 0, y: 0 };
    const distance = clamp(ratio, 0, 1) * total;
    const part = parts.find(item => distance <= item.end) || parts[parts.length - 1];
    const local = part.length ? (distance - part.start) / part.length : 0;
    return {
      x: part.from.x + (part.to.x - part.from.x) * local,
      y: part.from.y + (part.to.y - part.from.y) * local
    };
  }

  roundRect(ctx, x, y, width, height, radius) {
    const r = Math.min(radius, width / 2, height / 2);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + width - r, y);
    ctx.quadraticCurveTo(x + width, y, x + width, y + r);
    ctx.lineTo(x + width, y + height - r);
    ctx.quadraticCurveTo(x + width, y + height, x + width - r, y + height);
    ctx.lineTo(x + r, y + height);
    ctx.quadraticCurveTo(x, y + height, x, y + height - r);
    ctx.lineTo(x, y + r);
    ctx.quadraticCurveTo(x, y, x + r, y);
    ctx.closePath();
  }

  wrapText(ctx, text, x, y, maxWidth, lineHeight) {
    const words = String(text).split(/\s+/);
    let line = '';
    let currentY = y;
    for (const word of words) {
      const testLine = line ? `${line} ${word}` : word;
      if (ctx.measureText(testLine).width > maxWidth && line) {
        ctx.fillText(line, x, currentY);
        line = word;
        currentY += lineHeight;
      } else {
        line = testLine;
      }
    }
    if (line) ctx.fillText(line, x, currentY);
  }

  getExportDimensions({ forGif = false } = {}) {
    const width = clamp(Math.round(this.settings.exportWidth || 1920), 320, 4096);
    const height = clamp(Math.round(this.settings.exportHeight || 1080), 180, 4096);
    const scale = forGif ? Math.min(1, 960 / width, 540 / height) : 1;
    const makeEven = value => Math.max(2, Math.round((value * scale) / 2) * 2);
    return {
      width: makeEven(width),
      height: makeEven(height)
    };
  }

  createExportCanvas(options = {}) {
    const { width, height } = this.getExportDimensions(options);
    const canvas = document.createElement('canvas');
    canvas.width = width;
    canvas.height = height;
    return canvas;
  }

  getVideoBitrate(width, height, fps) {
    const pixelsPerSecond = width * height * fps;
    return clamp(Math.round(pixelsPerSecond * 0.14), 6_000_000, 60_000_000);
  }

  async exportWebM() {
    const exportCanvas = this.createExportCanvas();
    if (!exportCanvas.captureStream || typeof MediaRecorder === 'undefined') {
      window.alert('This browser does not support canvas video recording.');
      return;
    }

    this.stop();
    this.setExporting(true, `Recording WebM ${exportCanvas.width}x${exportCanvas.height}...`);
    const previousTime = this.timeMs;
    const stream = exportCanvas.captureStream(this.settings.fps);
    const mimeType = MediaRecorder.isTypeSupported('video/webm;codecs=vp9')
      ? 'video/webm;codecs=vp9'
      : 'video/webm';
    const recorder = new MediaRecorder(stream, {
      mimeType,
      videoBitsPerSecond: this.getVideoBitrate(exportCanvas.width, exportCanvas.height, this.settings.fps)
    });
    const chunks = [];
    recorder.ondataavailable = event => {
      if (event.data?.size) chunks.push(event.data);
    };

    const done = new Promise(resolve => {
      recorder.onstop = () => resolve();
    });

    recorder.start();
    await this.renderFramesRealtime(exportCanvas, this.settings.fps, progress => {
      this.setExporting(true, `Recording WebM ${exportCanvas.width}x${exportCanvas.height} ${Math.round(progress * 100)}%`);
    });
    recorder.stop();
    await done;
    stream.getTracks().forEach(track => track.stop());

    downloadBlob(new Blob(chunks, { type: 'video/webm' }), `yapne-animation-${exportCanvas.width}x${exportCanvas.height}-${Date.now()}.webm`);
    this.timeMs = previousTime;
    this.renderPreview();
    this.setExporting(false, 'WebM exported.');
  }

  async exportGif() {
    this.stop();
    this.setExporting(true, 'Rendering GIF frames...');
    const previousTime = this.timeMs;
    const fps = Math.min(12, this.settings.fps);
    const frameMs = 1000 / fps;
    const canvas = this.createExportCanvas({ forGif: true });
    const width = canvas.width;
    const height = canvas.height;
    const ctx = canvas.getContext('2d');
    const frameCount = Math.min(240, Math.ceil(this.settings.duration / frameMs));
    const frames = [];

    for (let i = 0; i < frameCount; i += 1) {
      const time = Math.min(this.settings.duration, i * frameMs);
      this.drawFrame(canvas, time);
      frames.push(ctx.getImageData(0, 0, width, height));
      if (i % 4 === 0) {
        this.setExporting(true, `Rendering GIF ${Math.round((i / frameCount) * 100)}%`);
        await new Promise(resolve => setTimeout(resolve, 0));
      }
    }

    this.setExporting(true, 'Encoding GIF...');
    const blob = SimpleGifEncoder.encode(frames, width, height, Math.max(2, Math.round(frameMs / 10)));
    downloadBlob(blob, `yapne-animation-${width}x${height}-${Date.now()}.gif`);
    this.timeMs = previousTime;
    this.renderPreview();
    this.setExporting(false, 'GIF exported.');
  }

  exportPng() {
    const previousTime = this.timeMs;
    const canvas = this.createExportCanvas();
    this.drawFrame(canvas, previousTime);
    canvas.toBlob(blob => {
      if (blob) downloadBlob(blob, `yapne-frame-${canvas.width}x${canvas.height}-${Date.now()}.png`);
    }, 'image/png');
  }

  async renderFramesRealtime(canvas, fps, onProgress) {
    const frameMs = 1000 / fps;
    const frameCount = Math.ceil(this.settings.duration / frameMs);
    for (let i = 0; i <= frameCount; i += 1) {
      const time = Math.min(this.settings.duration, i * frameMs);
      this.timeMs = time;
      this.drawFrame(canvas, time);
      onProgress?.(i / frameCount);
      await new Promise(resolve => setTimeout(resolve, frameMs));
    }
  }

  setExporting(isExporting, message = '') {
    this.isExporting = isExporting;
    this.panel.classList.toggle('animation-exporting', isExporting);
    for (const button of this.panel.querySelectorAll('button')) {
      if (!button.classList.contains('panel-close')) button.disabled = isExporting;
    }
    if (message) this.updateStatus(message);
  }
}

export default AnimationPanel;
