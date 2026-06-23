import { DataPetriNetIntegration } from "./src/extensions/dpn-integration.js";
import { initializeProbabilisticExecution } from "./src/extensions/probabilistic-integration.js";
import { initWorkflowTutorial } from "./src/workflow-tutorial.js";
import { PythonImportDialog } from "./src/extensions/python-import-dialog.js";
import { DEFAULT_EDITOR_SETTINGS, loadEditorSettings } from "./src/editor-settings.js";

const BASE_PATH = '/YAPNE-Yet-Another-Petri-Net-Editor/';
const MOBILE_VIEWPORT_QUERY = '(max-width: 700px), (max-height: 520px), (pointer: coarse)';

function setupMobileViewportSizing() {
    const root = document.documentElement;
    const mobileQuery = window.matchMedia?.(MOBILE_VIEWPORT_QUERY);
    let resizeFrame = 0;
    let chromeNudgeTimer = 0;

    const isMobileViewport = () => mobileQuery?.matches ?? (window.innerWidth <= 700 || window.innerHeight <= 520);

    const nudgeBrowserChrome = () => {
        if (!isMobileViewport() || window.scrollY > 0) {
            return;
        }

        window.scrollTo({ top: 1, left: 0, behavior: 'auto' });
    };

    const scheduleBrowserChromeNudge = () => {
        window.clearTimeout(chromeNudgeTimer);
        chromeNudgeTimer = window.setTimeout(nudgeBrowserChrome, 120);
    };

    const updateViewportVars = () => {
        window.cancelAnimationFrame(resizeFrame);
        resizeFrame = window.requestAnimationFrame(() => {
            const visualViewport = window.visualViewport;
            const width = Math.round(visualViewport?.width || window.innerWidth);
            const height = Math.round(visualViewport?.height || window.innerHeight);
            const offsetTop = Math.max(0, Math.round(visualViewport?.offsetTop || 0));
            const offsetLeft = Math.max(0, Math.round(visualViewport?.offsetLeft || 0));

            root.style.setProperty('--mobile-viewport-width', `${width}px`);
            root.style.setProperty('--mobile-viewport-height', `${height}px`);
            root.style.setProperty('--mobile-viewport-top', `${offsetTop}px`);
            root.style.setProperty('--mobile-viewport-left', `${offsetLeft}px`);
            root.style.setProperty('--mobile-panel-height', `${Math.min(Math.round(height * 0.5), 560)}px`);

            document.body?.classList.toggle('mobile-viewport-active', isMobileViewport());
            window.petriApp?.resizeCanvas?.();

            if (isMobileViewport()) {
                scheduleBrowserChromeNudge();
            }
        });
    };

    window.addEventListener('resize', updateViewportVars, { passive: true });
    window.addEventListener('orientationchange', () => {
        updateViewportVars();
        scheduleBrowserChromeNudge();
    }, { passive: true });

    if (window.visualViewport) {
        window.visualViewport.addEventListener('resize', updateViewportVars, { passive: true });
        window.visualViewport.addEventListener('scroll', updateViewportVars, { passive: true });
    }

    if (mobileQuery?.addEventListener) {
        mobileQuery.addEventListener('change', updateViewportVars);
    } else {
        mobileQuery?.addListener?.(updateViewportVars);
    }
    updateViewportVars();
}

setupMobileViewportSizing();

document.addEventListener('DOMContentLoaded', () => {
    try {
        let editorSettings = loadEditorSettings();

        // Sidebar tab functionality
        const tabs = document.querySelectorAll('.sidebar-tab');
        tabs.forEach(tab => {
            tab.addEventListener('click', () => {
                // Deactivate all tabs
                tabs.forEach(t => t.classList.remove('active'));
                // Activate clicked tab
                tab.classList.add('active');
                
                // Hide all panes
                const panes = document.querySelectorAll('.sidebar-pane');
                panes.forEach(pane => pane.classList.remove('active'));
                
                // Show corresponding pane
                const targetPane = document.querySelector(`.sidebar-pane[data-tab="${tab.dataset.tab}"]`);
                if (targetPane) targetPane.classList.add('active');
                
                // Save active tab in localStorage
                if (window.localStorage) {
                    localStorage.setItem('activeTab', tab.dataset.tab);
                }
            });
        });

        // Sidebar toggle functionality
        const sidebar = document.getElementById('sidebar');
        const sidebarToggle = document.getElementById('sidebar-toggle');

        function toggleSidebar() {
            const isVisible = sidebar.classList.contains('sidebar-visible');
            if (isVisible) {
                sidebar.classList.remove('sidebar-visible');
                sidebar.classList.add('sidebar-hidden');
                sidebarToggle.classList.remove('sidebar-expanded');
                sidebarToggle.innerHTML = '▶';
                sidebarToggle.title = 'Show sidebar (Tab)';
                document.body.classList.remove('sidebar-open');
            } else {
                sidebar.classList.remove('sidebar-hidden');
                sidebar.classList.add('sidebar-visible');
                sidebarToggle.classList.add('sidebar-expanded');
                sidebarToggle.innerHTML = '◀';
                sidebarToggle.title = 'Hide sidebar (Tab)';
                document.body.classList.add('sidebar-open');
            }
            if (window.localStorage) {
                localStorage.setItem('sidebarHidden', isVisible ? 'true' : 'false');
            }
            // Trigger canvas resize after sidebar animation completes
            setTimeout(() => {
                if (window.petriApp && window.petriApp.resizeCanvas) {
                    window.petriApp.resizeCanvas();
                }
            }, 350);
        }

        if (sidebarToggle) {
            sidebarToggle.addEventListener('click', toggleSidebar);
        }

        // Restore sidebar state - default to hidden (File/Help on left)
        if (window.localStorage) {
            const sidebarHidden = localStorage.getItem('sidebarHidden');
            if (sidebarHidden !== 'false') {
                // Default hidden
                sidebar.classList.add('sidebar-hidden');
                sidebar.classList.remove('sidebar-visible');
                sidebarToggle.classList.remove('sidebar-expanded');
                sidebarToggle.innerHTML = '▶';
                sidebarToggle.title = 'Show sidebar (Tab)';
                document.body.classList.remove('sidebar-open');
            } else {
                sidebar.classList.add('sidebar-visible');
                sidebar.classList.remove('sidebar-hidden');
                sidebarToggle.classList.add('sidebar-expanded');
                sidebarToggle.innerHTML = '◀';
                sidebarToggle.title = 'Hide sidebar (Tab)';
                document.body.classList.add('sidebar-open');
            }
        } else {
            // Default hidden
            sidebar.classList.add('sidebar-hidden');
            sidebarToggle.innerHTML = '▶';
        }
        
        // Section collapse functionality
        const sectionHeaders = document.querySelectorAll('.section-header');
        sectionHeaders.forEach(header => {
            header.addEventListener('click', () => {
                const section = header.closest('.sidebar-section');
                section.classList.toggle('section-collapsed');
                
                // Save collapsed state
                if (window.localStorage) {
                    saveCollapsedSections();
                }
            });
        });
        
        // Function to save collapsed section states
        function saveCollapsedSections() {
            const collapsedSections = [];
            document.querySelectorAll('.sidebar-section.section-collapsed').forEach(section => {
                if (section.id) collapsedSections.push(section.id);
            });
            localStorage.setItem('sidebarSections', JSON.stringify(collapsedSections));
        }
        
        // Help Dialog functionality
        const helpDialogOverlay = document.getElementById('help-dialog-overlay');
        const helpDialogClose = document.getElementById('help-dialog-close');
        const openHelpButton = document.getElementById('btn-open-help');

        function openHelpDialog() {
            helpDialogOverlay.style.display = 'flex';
            document.body.style.overflow = 'hidden'; // Prevent background scrolling
        }

        function closeHelpDialog() {
            helpDialogOverlay.style.display = 'none';
            document.body.style.overflow = ''; // Restore scrolling
        }

        // Check if this is the first time the user is using the tool
        function checkFirstTimeUser() {
            if (window.localStorage) {
                const hasSeenHelp = localStorage.getItem('hasSeenHelpDialog');
                if (!hasSeenHelp) {
                    setTimeout(() => {
                        openHelpDialog();
                        localStorage.setItem('hasSeenHelpDialog', 'true');
                    }, 1000);
                }
            }
        }

        // Initialize first-time user check
        checkFirstTimeUser();

        // Open help dialog
        if (openHelpButton) {
            openHelpButton.addEventListener('click', openHelpDialog);
        }

        // Close help dialog
        if (helpDialogClose) {
            helpDialogClose.addEventListener('click', closeHelpDialog);
        }

        // Close help dialog when clicking overlay
        if (helpDialogOverlay) {
            helpDialogOverlay.addEventListener('click', (e) => {
                if (e.target === helpDialogOverlay) {
                    closeHelpDialog();
                }
            });
        }

        // Close help dialog with Escape key
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Escape' && helpDialogOverlay.style.display === 'flex') {
                closeHelpDialog();
            }
        });

        
        // Restore previous states
        if (window.localStorage) {
            // Restore active tab
            const savedTab = localStorage.getItem('activeTab');
            if (savedTab) {
                const tab = document.querySelector(`.sidebar-tab[data-tab="${savedTab}"]`);
                if (tab) tab.click();
            }
            
            // Restore collapsed sections
            const savedState = localStorage.getItem('sidebarSections');
            if (savedState) {
                try {
                    const collapsedSections = JSON.parse(savedState);
                    document.querySelectorAll('.sidebar-section').forEach(section => {
                        if (section.id && collapsedSections.includes(section.id)) {
                            section.classList.add('section-collapsed');
                        }
                    });
                } catch (e) {
                    console.error('Error restoring sidebar state', e);
                }
            }
        }

        const isMac = navigator.userAgent.includes('Mac');
        const modifierKey = isMac ? 'Command' : 'Alt';
        const isCompactTouch = window.matchMedia?.('(max-width: 700px), (pointer: coarse)').matches;
        const panText = isCompactTouch
            ? 'Pan/zoom: two-finger drag or pinch'
            : `Pan: Middle mouse button or ${modifierKey}+drag`;
        
        const panInstructions = document.getElementById('pan-instructions');
        panInstructions.innerHTML = `<span>${panText}</span>`;
        
        const navigationHelpList = document.getElementById('navigation-help-list');
        const panHelpItem = navigationHelpList.querySelector('li:first-child');
        panHelpItem.innerHTML = isCompactTouch
            ? '<strong>Pan/zoom:</strong> Two-finger drag or pinch'
            : `<strong>Pan:</strong> Middle mouse button or ${modifierKey}+drag`;
        
        const app = new window.PetriNetApp();

        window.petriApp = app;

        const zoomSensitivityInput = document.getElementById('setting-zoom-sensitivity');
        const zoomSensitivityValue = document.getElementById('setting-zoom-sensitivity-value');
        const panSensitivityInput = document.getElementById('setting-pan-sensitivity');
        const panSensitivityValue = document.getElementById('setting-pan-sensitivity-value');
        const snapToGridInput = document.getElementById('setting-snap-to-grid');
        const gridSizeInput = document.getElementById('setting-grid-size');
        const gridSizeValue = document.getElementById('setting-grid-size-value');
        const gridSizeWrapper = document.getElementById('setting-grid-size-wrapper');
        const showGridInput = document.getElementById('setting-show-grid');
        const showGridWrapper = document.getElementById('setting-show-grid-wrapper');
        const invertEditorColorsInput = document.getElementById('setting-invert-editor-colors');
        const autoConnectEnabledInput = document.getElementById('setting-auto-connect-enabled');
        const autoConnectDistanceInput = document.getElementById('setting-auto-connect-distance');
        const autoConnectDistanceValue = document.getElementById('setting-auto-connect-distance-value');
        const autoConnectDistanceWrapper = document.getElementById('setting-auto-connect-distance-wrapper');
        const resetSettingsButton = document.getElementById('btn-reset-editor-settings');

        const updateSettingsDisplay = (settings) => {
            zoomSensitivityInput.value = Number(settings.zoomSensitivity).toFixed(2);
            zoomSensitivityValue.textContent = Number(settings.zoomSensitivity).toFixed(2);
            panSensitivityInput.value = Number(settings.panSensitivity).toFixed(2);
            panSensitivityValue.textContent = `${Number(settings.panSensitivity).toFixed(2)}x`;
            snapToGridInput.checked = settings.snapToGrid;
            gridSizeInput.value = Number(settings.gridSize).toFixed(0);
            gridSizeValue.textContent = `${Number(settings.gridSize).toFixed(0)} px`;
            showGridInput.checked = settings.showGrid;
            invertEditorColorsInput.checked = settings.invertEditorColors;
            autoConnectEnabledInput.checked = settings.autoConnectEnabled;
            autoConnectDistanceInput.value = Number(settings.autoConnectDistance).toFixed(0);
            autoConnectDistanceValue.textContent = `${Number(settings.autoConnectDistance).toFixed(0)} px`;

            const gridControlsEnabled = settings.snapToGrid;
            gridSizeWrapper.classList.toggle('setting-item-disabled', !gridControlsEnabled);
            showGridWrapper.classList.toggle('setting-item-disabled', !gridControlsEnabled);
            gridSizeInput.disabled = !gridControlsEnabled;
            showGridInput.disabled = !gridControlsEnabled;

            autoConnectDistanceWrapper.classList.toggle('setting-item-disabled', !settings.autoConnectEnabled);
            autoConnectDistanceInput.disabled = !settings.autoConnectEnabled;
        };

        const applySettings = (nextPartialSettings, options = {}) => {
            editorSettings = {
                ...editorSettings,
                ...nextPartialSettings
            };
            app.applyEditorSettings(editorSettings, options);
        };

        const reapplyLoadedSettings = () => {
            applySettings(editorSettings, { persist: false });
            if (app.resizeCanvas) {
                app.resizeCanvas();
            }
        };

        document.addEventListener('editor-settings-changed', (event) => {
            editorSettings = event.detail;
            updateSettingsDisplay(editorSettings);
        });

        updateSettingsDisplay(editorSettings);
        reapplyLoadedSettings();
        requestAnimationFrame(() => {
            reapplyLoadedSettings();
        });

        zoomSensitivityInput.addEventListener('input', () => {
            applySettings({ zoomSensitivity: Number(zoomSensitivityInput.value) });
        });

        panSensitivityInput.addEventListener('input', () => {
            applySettings({ panSensitivity: Number(panSensitivityInput.value) });
        });

        snapToGridInput.addEventListener('change', () => {
            applySettings({ snapToGrid: snapToGridInput.checked });
        });

        gridSizeInput.addEventListener('input', () => {
            applySettings({ gridSize: Number(gridSizeInput.value) });
        });

        showGridInput.addEventListener('change', () => {
            applySettings({ showGrid: showGridInput.checked });
        });

        invertEditorColorsInput.addEventListener('change', () => {
            applySettings({ invertEditorColors: invertEditorColorsInput.checked });
        });

        autoConnectEnabledInput.addEventListener('change', () => {
            applySettings({ autoConnectEnabled: autoConnectEnabledInput.checked });
        });

        autoConnectDistanceInput.addEventListener('input', () => {
            applySettings({ autoConnectDistance: Number(autoConnectDistanceInput.value) });
        });

        resetSettingsButton.addEventListener('click', () => {
            applySettings(DEFAULT_EDITOR_SETTINGS);
        });

        // Ghost element feature enhancements
        const canvas = document.getElementById('petri-canvas');
        const ghostHint = document.getElementById('ghost-hint');
        
        // Monitor for shift key and selection state
        let isGhostModeActive = false;
        
        function updateGhostMode() {
            const isShiftPressed = app.editor && app.editor.isShiftPressed;
            const hasSelection = app.editor && app.editor.selectedElement && 
                                (app.editor.selectedElement.type === 'place' || app.editor.selectedElement.type === 'transition');
            
            const newGhostModeActive = isShiftPressed && hasSelection && app.editor.mode === 'select';
            
            if (newGhostModeActive !== isGhostModeActive) {
                isGhostModeActive = newGhostModeActive;
                
                if (isGhostModeActive) {
                    canvas.classList.add('ghost-mode');
                    ghostHint.classList.add('show');
                } else {
                    canvas.classList.remove('ghost-mode');
                    ghostHint.classList.remove('show');
                }
            }
        }
        
        // Check ghost mode periodically
        setInterval(updateGhostMode, 100);

        app.loadTemplateFile(`${BASE_PATH}examples/example-config.json`).then((data) => {
            const templateSelect = document.getElementById('template-select');
            data.forEach((example) => {
                const option = document.createElement('option');
                option.value = `${BASE_PATH}${example.path}`;
                option.textContent = example.name;
                templateSelect.appendChild(option);
            });
        });

        // const fullscreenButton = document.getElementById('btn-fullscreen');
        // fullscreenButton.addEventListener('click', toggleFullscreen);
        
        // function toggleFullscreen() {
        //     const body = document.body;
            
        //     body.classList.toggle('fullscreen-mode');
            
        //     if (body.classList.contains('fullscreen-mode')) {
        //         fullscreenButton.innerHTML = '⤣';
        //         fullscreenButton.title = 'Exit Full Screen';
        //     } else {
        //         fullscreenButton.innerHTML = '⛶';
        //         fullscreenButton.title = 'Toggle Full Screen';
        //     }
            
        //     if (window.petriApp && window.petriApp.resizeCanvas) {
        //         setTimeout(() => {
        //             window.petriApp.resizeCanvas();
        //         }, 50);
                
        //         setTimeout(() => {
        //             window.petriApp.resizeCanvas();
        //         }, 350);
        //     }
        // }
        
        // document.addEventListener('keydown', (e) => {
        //     if (e.key === 'Escape' && document.body.classList.contains('fullscreen-mode')) {
        //         toggleFullscreen();
        //     } else if (e.key === 'F' && (e.ctrlKey || e.metaKey)) {
        //         e.preventDefault(); // Prevent browser's find functionality
        //         toggleFullscreen();
        //     }
        // });

        // Keyboard shortcut to toggle sidebar (Tab key, only when no input is focused)
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Tab') {
                const activeEl = document.activeElement;
                const isInputFocused = activeEl && (activeEl.tagName === 'INPUT' || activeEl.tagName === 'TEXTAREA' || activeEl.tagName === 'SELECT');
                if (!isInputFocused) {
                    e.preventDefault();
                    toggleSidebar();
                }
            }
        });

        const initTimer = setInterval(() => {
            if (window.petriApp) {
                window.dataPetriNetIntegration = new DataPetriNetIntegration(window.petriApp);

                // Python Import Dialog
                const btnImportPython = document.getElementById('btn-import-python');
                if (btnImportPython) {
                    btnImportPython.addEventListener('click', () => {
                        const dialog = new PythonImportDialog(window.petriApp);
                        dialog.open();
                    });
                }
                
                // Initialize Probabilistic Execution Integration
                // Implements "Data Petri Nets Meet Probabilistic Programming" (Kuhn et al., BPM 2024)
                // This adds probabilistic step/playout capabilities using the paper's approach
                window.probabilisticIntegration = initializeProbabilisticExecution(window.petriApp);
                
                // Initialize Workflow Tutorial System
                window.workflowTutorial = initWorkflowTutorial();

                // Wire up "Workflow Tutorials" button
                const tutorialBtn = document.getElementById('btn-open-tutorials');
                if (tutorialBtn) {
                    tutorialBtn.addEventListener('click', () => {
                        window.workflowTutorial.toggle();
                    });
                }

                // Wire up "Workflow Tutorials" button in the welcome dialog
                const tutorialWelcomeBtn = document.getElementById('btn-open-tutorials-welcome');
                if (tutorialWelcomeBtn) {
                    tutorialWelcomeBtn.addEventListener('click', () => {
                        closeHelpDialog();
                        window.workflowTutorial.openDialog();
                    });
                }

                reapplyLoadedSettings();
                
                clearInterval(initTimer);
            }
        }, 100);
        
    } catch (error) {
        console.error('Error initializing application:', error);
        alert('Error initializing application: ' + error);
    }
});
