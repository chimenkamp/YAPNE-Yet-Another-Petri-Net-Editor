const STORAGE_KEY = 'yapne_editor_settings';

export const DEFAULT_EDITOR_SETTINGS = {
  zoomSensitivity: 0.05,
  panSensitivity: 1,
  snapToGrid: true,
  gridSize: 10,
  showGrid: false,
  autoConnectEnabled: true,
  autoConnectDistance: 300
};

function clamp(value, min, max, fallback) {
  const parsed = Number(value);
  if (!Number.isFinite(parsed)) return fallback;
  return Math.min(max, Math.max(min, parsed));
}

function normalizeBoolean(value, fallback) {
  if (typeof value === 'boolean') return value;
  if (value === 'true') return true;
  if (value === 'false') return false;
  return fallback;
}

export function loadEditorSettings() {
  if (!window.localStorage) {
    return { ...DEFAULT_EDITOR_SETTINGS };
  }

  try {
    const raw = localStorage.getItem(STORAGE_KEY);
    if (!raw) return { ...DEFAULT_EDITOR_SETTINGS };

    const parsed = JSON.parse(raw);
    return {
      zoomSensitivity: clamp(parsed.zoomSensitivity, 0.01, 0.5, DEFAULT_EDITOR_SETTINGS.zoomSensitivity),
      panSensitivity: clamp(parsed.panSensitivity, 0.25, 3, DEFAULT_EDITOR_SETTINGS.panSensitivity),
      snapToGrid: normalizeBoolean(parsed.snapToGrid, DEFAULT_EDITOR_SETTINGS.snapToGrid),
      gridSize: clamp(parsed.gridSize, 5, 100, DEFAULT_EDITOR_SETTINGS.gridSize),
      showGrid: normalizeBoolean(parsed.showGrid, DEFAULT_EDITOR_SETTINGS.showGrid),
      autoConnectEnabled: normalizeBoolean(parsed.autoConnectEnabled, DEFAULT_EDITOR_SETTINGS.autoConnectEnabled),
      autoConnectDistance: clamp(parsed.autoConnectDistance, 50, 800, DEFAULT_EDITOR_SETTINGS.autoConnectDistance)
    };
  } catch (error) {
    console.error('Failed to load editor settings', error);
    return { ...DEFAULT_EDITOR_SETTINGS };
  }
}

export function saveEditorSettings(nextSettings) {
  const normalized = {
    zoomSensitivity: clamp(nextSettings.zoomSensitivity, 0.01, 0.5, DEFAULT_EDITOR_SETTINGS.zoomSensitivity),
    panSensitivity: clamp(nextSettings.panSensitivity, 0.25, 3, DEFAULT_EDITOR_SETTINGS.panSensitivity),
    snapToGrid: Boolean(nextSettings.snapToGrid),
    gridSize: clamp(nextSettings.gridSize, 5, 100, DEFAULT_EDITOR_SETTINGS.gridSize),
    showGrid: Boolean(nextSettings.showGrid),
    autoConnectEnabled: Boolean(nextSettings.autoConnectEnabled),
    autoConnectDistance: clamp(nextSettings.autoConnectDistance, 50, 800, DEFAULT_EDITOR_SETTINGS.autoConnectDistance)
  };

  if (window.localStorage) {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(normalized));
  }

  return normalized;
}