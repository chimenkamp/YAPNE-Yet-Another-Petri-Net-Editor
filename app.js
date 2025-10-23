import { DataPetriNetIntegration } from "./src/extensions/dpn-integration.js";

// Use Vite's BASE_URL which is '/' for dev and '/YAPNE-Yet-Another-Petri-Net-Editor/' for production
const BASE_PATH = import.meta.env.BASE_URL;

document.addEventListener('DOMContentLoaded', () => {
    try {

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
        
        const panInstructions = document.getElementById('pan-instructions');
        panInstructions.innerHTML = `<span>Pan: Middle mouse button or ${modifierKey}+drag</span>`;
        
        const navigationHelpList = document.getElementById('navigation-help-list');
        const panHelpItem = navigationHelpList.querySelector('li:first-child');
        panHelpItem.innerHTML = `<strong>Pan:</strong> Middle mouse button or ${modifierKey}+drag`;
        
        const app = new window.PetriNetApp();

        window.petriApp = app;

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

        const fullscreenButton = document.getElementById('btn-fullscreen');
        fullscreenButton.addEventListener('click', toggleFullscreen);
        
        function toggleFullscreen() {
            const body = document.body;
            const canvasElement = document.getElementById('petri-canvas');
            
            body.classList.toggle('fullscreen-mode');
            
            if (body.classList.contains('fullscreen-mode')) {
                fullscreenButton.innerHTML = '⤣';
                fullscreenButton.title = 'Exit Full Screen';
                
                setTimeout(() => {
                    canvasElement.width = window.innerWidth;
                    canvasElement.height = window.innerHeight;
                }, 10);
            } else {
                fullscreenButton.innerHTML = '⛶';
                fullscreenButton.title = 'Toggle Full Screen';
                
                setTimeout(() => {
                    canvasElement.width = "1090";
                    canvasElement.height = "800";
                }, 10);
            }
            
            if (window.petriApp && window.petriApp.resizeCanvas) {
                setTimeout(() => {
                    window.petriApp.resizeCanvas();
                }, 50);
                
                setTimeout(() => {
                    window.petriApp.resizeCanvas();
                }, 350); // slightly longer than the CSS transition duration
            }
        }
        
        document.addEventListener('keydown', (e) => {
            if (e.key === 'Escape' && document.body.classList.contains('fullscreen-mode')) {
                toggleFullscreen();
            } else if (e.key === 'F' && (e.ctrlKey || e.metaKey)) {
                e.preventDefault(); // Prevent browser's find functionality
                toggleFullscreen();
            }
        });

        const initTimer = setInterval(() => {
            if (window.petriApp) {
                window.dataPetriNetIntegration = new DataPetriNetIntegration(window.petriApp);
                clearInterval(initTimer);
            }
        }, 100);
        
    } catch (error) {
        console.error('Error initializing application:', error);
        alert('Error initializing application: ' + error);
    }
});