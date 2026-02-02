/**
 * Petri Net Editor Example Application
 *
 * This file contains the implementation of a web application that uses the Petri Net Editor library.
 * It demonstrates how to create, edit, simulate, and analyze Petri nets.
 */
import { PetriNetAPI } from './petri-net-simulator.js';

class PetriNetApp {
  /**
   * Constructor for the PetriNetApp
   */
  constructor() {

    this.api = null;
    this.editor = null;
    this.canvas = null;


    this.propertiesPanel = null;
    this.tokensDisplay = null;
    this.zoomDisplay = null;


    this.autoRunInterval = null;
    this.autoRunDelay = 1000;
    this.gridEnabled = true;

    this.initialState = null;
    this.simulationStarted = false;


    this.canvas = document.getElementById("petri-canvas");
    if (!this.canvas) {
      throw new Error("Canvas element not found");
    }


    this.propertiesPanel = document.getElementById("properties-content");
    if (!this.propertiesPanel) {
      throw new Error("Properties panel element not found");
    }


    this.tokensDisplay = document.getElementById("tokens-display");
    if (!this.tokensDisplay) {
      throw new Error("Tokens display element not found");
    }


    this.zoomDisplay = document.getElementById("zoom-display");


    this.api = new PetriNetAPI();
    this.editor = this.api.attachEditor(this.canvas);
    
    

    this.api.setZoomSensitivity(0.05);

    this.editor.app = this;


    this.editor.setOnSelectCallback(this.handleElementSelected.bind(this));
    this.editor.setOnChangeCallback(this.handleNetworkChanged.bind(this));

    this.setupResizeObserver();
    this.resizeCanvas();

    this.initEventHandlers();

    // Add initial place to the editor
    this.addInitialPlace();

    this.editor.render();
    this.updateTokensDisplay();
    this.updateZoomDisplay();

  }

  /**
   * Captures the current state as the initial state for simulation reset
   */
  captureInitialState() {
    this.initialState = {
      places: new Map(),
      dataVariables: null
    };

    // Capture place tokens
    for (const [id, place] of this.api.petriNet.places) {
      this.initialState.places.set(id, place.tokens);
    }

    // Capture data variables if DPN integration is available
    if (window.dataPetriNetIntegration && window.dataPetriNetIntegration.dataVariables) {
      this.initialState.dataVariables = new Map();
      for (const [name, variable] of window.dataPetriNetIntegration.dataVariables) {
        this.initialState.dataVariables.set(name, {
          value: variable.value,
          type: variable.type
        });
      }
    }

    this.simulationStarted = true;
    console.log("Initial state captured for simulation reset");
  }

  /**
   * Restores the simulation to its initial captured state
   */
  restoreInitialState() {
    if (!this.initialState) {
      console.warn("No initial state captured - cannot reset simulation");
      return false;
    }

    // Restore place tokens
    for (const [id, initialTokens] of this.initialState.places) {
      const place = this.api.petriNet.places.get(id);
      if (place) {
        place.tokens = initialTokens;
      }
    }

    // Restore data variables if they exist
    if (this.initialState.dataVariables && window.dataPetriNetIntegration) {
      for (const [name, initialVar] of this.initialState.dataVariables) {
        const variable = window.dataPetriNetIntegration.dataVariables.get(name);
        if (variable) {
          variable.value = initialVar.value;
        }
      }
      
      // Update data variables display if available
      if (window.dataPetriNetIntegration.updateDataValuesDisplay) {
        window.dataPetriNetIntegration.updateDataValuesDisplay();
      }
    }

    // Update displays
    this.updateTokensDisplay();
    this.updateSelectedElementProperties();
    this.editor.render();

    // Update transition status if an element is selected
    if (this.editor.selectedElement && this.editor.selectedElement.type === 'transition') {
      this.updateTransitionStatus(this.editor.selectedElement.id);
    }

    console.log("Simulation reset to initial state");
    return true;
  }

  /**
   * Adds an initial place to the editor when it starts
   */
  addInitialPlace() {
    // Calculate a good position for the initial place
    const canvasWidth = this.canvas.width;
    const canvasHeight = this.canvas.height;
    
    // Position the initial place at about 1/4 from left and 1/3 from top
    const initialX = canvasWidth * 0.25;
    const initialY = canvasHeight * 0.33;
    
    // Create the initial place with 1 token
    const placeId = this.api.createPlace(initialX, initialY, "Start", 1);
    
    // Optionally select the initial place
    // this.editor.selectElement(placeId, 'place');
  }

  /**
   * Initialize all UI event handlers
   */
initEventHandlers() {
  // Clear any existing app-level event listeners first
  this.cleanupAppEventListeners();

  const btnSelect = document.getElementById("btn-select");
  if (btnSelect) {
    const handler = () => {
      this.editor.setMode("select");
      this.updateActiveButton("btn-select");
    };
    btnSelect.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnSelect]);
  }

  const btnAddPlace = document.getElementById("btn-add-place");
  if (btnAddPlace) {
    const handler = () => {
      this.editor.setMode("addPlace");
      this.updateActiveButton("btn-add-place");
    };
    btnAddPlace.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnAddPlace]);
  }

  const btnAddTransition = document.getElementById("btn-add-transition");
  if (btnAddTransition) {
    const handler = () => {
      this.editor.setMode("addTransition");
      this.updateActiveButton("btn-add-transition");
    };
    btnAddTransition.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnAddTransition]);
  }

  const btnFitToCanvas = document.getElementById("btn-fit-to-canvas");
  if (btnFitToCanvas) {
    const handler = () => {
      this.fitNetworkToCanvas();
    };
    btnFitToCanvas.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnFitToCanvas]);
  }

  const btnAddArc = document.getElementById("btn-add-arc");
  if (btnAddArc) {
    const handler = () => {
      this.editor.setMode("addArc");
      this.updateActiveButton("btn-add-arc");
    };
    btnAddArc.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnAddArc]);
  }

  // Space key handlers for arc mode
  const keydownHandler = (e) => {
    if (e.key === ' ' && this.editor && this.editor.mode !== 'addArc') {
      e.preventDefault();
      e.stopPropagation();
      this.editor.setMode('addArc');
      this.updateActiveButton("btn-add-arc");
    }
  };

  const keyupHandler = (e) => {
    if (e.key === ' ' && this.editor) {
      e.preventDefault();
      e.stopPropagation();
      this.editor.setMode('select');
      this.updateActiveButton("btn-select");
    }
  };

  document.addEventListener('keydown', keydownHandler);
  document.addEventListener('keyup', keyupHandler);
  this.appEventListeners.push(['keydown', keydownHandler, document]);
  this.appEventListeners.push(['keyup', keyupHandler, document]);

  const btnDelete = document.getElementById("btn-delete");
  if (btnDelete) {
    const handler = () => {
      this.editor.deleteSelected();
    };
    btnDelete.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnDelete]);
  }

  const btnClear = document.getElementById("btn-clear");
  if (btnClear) {
    const handler = () => {
      if (confirm("Are you sure you want to clear the entire Petri net?")) {
        this.resetPetriNet();
      }
    };
    btnClear.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnClear]);
  }

  const btnGrid = document.getElementById("btn-grid");
  if (btnGrid) {
    const handler = () => {
      this.gridEnabled = !this.gridEnabled;
      this.editor.setSnapToGrid(this.gridEnabled);
      btnGrid.classList.toggle("active", this.gridEnabled);
    };
    btnGrid.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnGrid]);
  }

  const btnAuto = document.getElementById("btn-auto-layout");
  if (btnAuto) {
    const handler = async () => {
      const originalText = btnAuto.textContent;
      btnAuto.textContent = "Laying out...";
      btnAuto.disabled = true;
      
      try {
        await this.api.autoLayout({
          elementSpacing: 150,
          verticalSpacing: 100,
          centerLayout: true,
          compactLayout: true
        });
      } catch (error) {
        console.error("Layout error:", error);
      } finally {
        btnAuto.textContent = originalText;
        btnAuto.disabled = false;
      }
    };
    btnAuto.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnAuto]);
  }

  const btnZoomIn = document.getElementById("btn-zoom-in");
  if (btnZoomIn) {
    const handler = () => {
      const centerX = this.canvas.width / 2;
      const centerY = this.canvas.height / 2;
      this.editor.renderer.adjustZoom(1.2, centerX, centerY);
      this.editor.render();
      this.updateZoomDisplay();
    };
    btnZoomIn.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnZoomIn]);
  }

  const btnZoomOut = document.getElementById("btn-zoom-out");
  if (btnZoomOut) {
    const handler = () => {
      const centerX = this.canvas.width / 2;
      const centerY = this.canvas.height / 2;
      this.editor.renderer.adjustZoom(0.8, centerX, centerY);
      this.editor.render();
      this.updateZoomDisplay();
    };
    btnZoomOut.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnZoomOut]);
  }

  const btnResetView = document.getElementById("btn-reset-view");
  if (btnResetView) {
    const handler = () => {
      this.editor.resetView();
      this.updateZoomDisplay();
    };
    btnResetView.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnResetView]);
  }

  const templateSelect = document.getElementById("template-select");
  if (templateSelect) {
    const handler = (e) => {
      const template = e.target.value;
      if (template) {
        this.loadTemplate(template);
      }
    };
    templateSelect.addEventListener("change", handler);
    this.appEventListeners.push(['change', handler, templateSelect]);
  }

  const btnStep = document.getElementById("btn-step");
  if (btnStep) {
    const handler = () => {
      if (!this.simulationStarted) {
        this.captureInitialState();
      }
      this.stepSimulation();
    };
    btnStep.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnStep]);
  }

  const btnAutoRun = document.getElementById("btn-auto-run");
  if (btnAutoRun) {
    const handler = () => {
      if (this.autoRunInterval) {
        this.stopAutoRun();
        btnAutoRun.textContent = "Auto Run";
      } else {
        if (!this.simulationStarted) {
          this.captureInitialState();
        }
        this.startAutoRun();
        btnAutoRun.textContent = "Stop";
      }
    };
    btnAutoRun.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnAutoRun]);
  }

  const btnReset = document.getElementById("btn-reset");
  if (btnReset) {
    const handler = () => {
      if (this.autoRunInterval) {
        this.stopAutoRun();
        const btnAutoRun = document.getElementById("btn-auto-run");
        if (btnAutoRun) {
          btnAutoRun.textContent = "Auto Run";
        }
      }
      
      if (this.restoreInitialState()) {
        console.log("Simulation reset successfully");
      } else {
        console.warn("Could not reset simulation - no initial state captured");
      }
    };
    btnReset.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnReset]);
  }

  const btnSave = document.getElementById("btn-save");
  if (btnSave) {
    const handler = () => {
      this.saveToFile();
    };
    btnSave.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnSave]);
  }

  const btnLoad = document.getElementById("btn-load");
  if (btnLoad) {
    const handler = () => {
      document.getElementById("file-input")?.click();
    };
    btnLoad.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnLoad]);
  }

  const fileInput = document.getElementById("file-input");
  if (fileInput) {
    const handler = (event) => {
      const input = event.target;
      if (input.files && input.files.length > 0) {
        console.log(input.files[0]);
        this.loadFromFile(input.files[0]);
      }
    };
    fileInput.addEventListener("change", handler);
    this.appEventListeners.push(['change', handler, fileInput]);
  }

  const btnExportPnml = document.getElementById("btn-export-pnml");
  if (btnExportPnml) {
    const handler = () => {
      this.exportToPNML();
    };
    btnExportPnml.addEventListener("click", handler);
    this.appEventListeners.push(['click', handler, btnExportPnml]);
  }
}

  /**
   * Updates the active state of toolbar buttons
   */
  updateActiveButton(activeId) {
    const buttons = [
      "btn-select",
      "btn-add-place",
      "btn-add-transition",
      "btn-add-arc",
    ];

    buttons.forEach((id) => {
      const button = document.getElementById(id);
      if (button) {
        button.classList.toggle("active", id === activeId);
      }
    });
  }

  /**
   * Updates the zoom display
   */
  updateZoomDisplay() {
    if (this.zoomDisplay) {
      const zoomPercent = Math.round(this.editor.renderer.zoomFactor * 100);
      this.zoomDisplay.textContent = `${zoomPercent}%`;
    }
  }

  /**
   * Handles when an element is selected in the editor
   */
  handleElementSelected(id, type) {
    if (!id || !type) {
      this.propertiesPanel.innerHTML = "<p>No element selected.</p>";
      return;
    }


    if (type === "place") {
      this.showPlaceProperties(id);
    } else if (type === "transition") {
      this.showTransitionProperties(id);
    } else if (type === "arc") {
      this.showArcProperties(id);

    }
  }

  showPlaceProperties(id) {
    const place = this.api.petriNet.places.get(id);
    if (!place) return;

    this.propertiesPanel.innerHTML = `
      <div class="form-group">
        <label for="place-id">ID</label>
        <input type="text" id="place-id" value="${id}" disabled>
      </div>
      <div class="form-group">
        <label for="place-label">Label</label>
        <input type="text" id="place-label" value="${place.label}">
      </div>
      <div class="form-group">
        <label for="place-tokens">Tokens</label>
        <input type="number" id="place-tokens" value="${place.tokens}" min="0">
      </div>
      <div class="form-group">
        <label for="place-capacity">Capacity (0 for unlimited)</label>
        <input type="number" id="place-capacity" value="${
          place.capacity || 0
        }" min="0">
      </div>
      <div class="form-group">
        <label for="place-final-marking">
          Final Marking
          ${place.hasFinalMarking() ? 
            (place.hasReachedFinalMarking() ? '✅' : '⏳') : ''
          }
        </label>
        <input type="number" id="place-final-marking" value="${
          place.finalMarking !== null ? place.finalMarking : ''
        }" min="0" placeholder="Leave empty for no final marking">
      </div>
    `;

    // Keep existing event listeners and add new one for final marking
    const labelInput = document.getElementById("place-label");
    if (labelInput) {
      labelInput.addEventListener("change", (e) => {
        this.api.setLabel(id, e.target.value);
      });
    }

    const tokensInput = document.getElementById("place-tokens");
    if (tokensInput) {
      tokensInput.addEventListener("change", (e) => {
        const value = parseInt(e.target.value, 10);
        if (!isNaN(value) && value >= 0) {
          this.api.setPlaceTokens(id, value);
          this.updateTokensDisplay();
          this.updateFinalMarkingDisplay(); 
          this.editor.render();
        }
      });
    }

    const capacityInput = document.getElementById("place-capacity");
    if (capacityInput) {
      capacityInput.addEventListener("change", (e) => {
        const value = parseInt(e.target.value, 10);
        if (!isNaN(value)) {
          place.capacity = value === 0 ? null : value;
          this.editor.render();
        }
      });
    }

    const finalMarkingInput = document.getElementById("place-final-marking");
    if (finalMarkingInput) {
      finalMarkingInput.addEventListener("change", (e) => {
        const value = e.target.value.trim();
        if (value === '') {
          place.finalMarking = null;
        } else {
          const numValue = parseInt(value, 10);
          if (!isNaN(numValue) && numValue >= 0) {
            place.finalMarking = numValue;
          }
        }
        this.editor.render();
        this.updateFinalMarkingDisplay();
        this.showPlaceProperties(id);
      });
    }
  }
  
  /**
   * Fits the Petri net to the canvas viewport
   */
  fitNetworkToCanvas() {
    if (this.api && this.api.fitToCanvas) {
      this.api.fitToCanvas();
      this.updateZoomDisplay();
    }
  }

  /**
   * Updates the zoom display
   */
  updateZoomDisplay() {
    if (this.zoomDisplay && this.editor && this.editor.renderer) {
      const zoomPercent = Math.round(this.editor.renderer.zoomFactor * 100);
      this.zoomDisplay.textContent = `${zoomPercent}%`;
    }
  }

  /**
   * Displays properties for a selected transition
   */
  showTransitionProperties(id) {
    const transition = this.api.petriNet.transitions.get(id);
    if (!transition) return;

    const isSilent = transition.silent || false;

    this.propertiesPanel.innerHTML = `
   <div class="form-group">
   <label for="transition-id">ID</label>
   <input type="text" id="transition-id" value="${id}" disabled>
   </div>
   <div class="form-group">
   <label for="transition-silent" style="display: flex; align-items: center; gap: 8px; cursor: pointer;">
     <input type="checkbox" id="transition-silent" ${isSilent ? 'checked' : ''} style="width: auto; margin: 0;">
     Silent Transition (τ)
   </label>
   <small>Silent transitions are invisible in event logs</small>
   </div>
   <div class="form-group" id="transition-label-group" ${isSilent ? 'style="opacity: 0.5; pointer-events: none;"' : ''}>
   <label for="transition-label">Label</label>
   <input type="text" id="transition-label" value="${transition.label}" ${isSilent ? 'disabled' : ''}>
   </div>
   <div class="form-group" id="transition-priority-group" ${isSilent ? 'style="opacity: 0.5; pointer-events: none;"' : ''}>
   <label for="transition-priority">Priority</label>
   <input type="number" id="transition-priority" value="${transition.priority}" min="1" ${isSilent ? 'disabled' : ''}>
   </div>
   <div class="form-group" id="transition-delay-group" ${isSilent ? 'style="opacity: 0.5; pointer-events: none;"' : ''}>
   <label for="transition-delay">Delay (ms)</label>
   <input type="number" id="transition-delay" value="${transition.delay}" min="0" ${isSilent ? 'disabled' : ''}>
   </div>
   <div class="form-group">
   <label>Status</label>
   <div id="transition-status-container"></div>
   </div>
   <div class="form-group" id="fire-button-container"></div>
  `;


    this.updateTransitionStatus(id);

    // Silent checkbox handler
    const silentCheckbox = document.getElementById("transition-silent");
    if (silentCheckbox) {
      silentCheckbox.addEventListener("change", (e) => {
        transition.silent = e.target.checked;
        // Re-render the properties panel to update disabled state
        this.showTransitionProperties(id);
        this.editor.render();
      });
    }

    const labelInput = document.getElementById("transition-label");
    if (labelInput) {
      labelInput.addEventListener("change", (e) => {
        this.api.setLabel(id, e.target.value);
      });
    }

    const priorityInput = document.getElementById("transition-priority");
    if (priorityInput) {
      priorityInput.addEventListener("change", (e) => {
        const value = parseInt(e.target.value, 10);
        if (!isNaN(value) && value >= 1) {
          transition.priority = value;
          this.editor.render();
        }
      });
    }

    const delayInput = document.getElementById("transition-delay");
    if (delayInput) {
      delayInput.addEventListener("change", (e) => {
        const value = parseInt(e.target.value, 10);
        if (!isNaN(value) && value >= 0) {
          transition.delay = value;
          this.editor.render();
        }
      });
    }
  }

  updateSelectedElementProperties() {
    if (this.editor.selectedElement) {
      this.handleElementSelected(
        this.editor.selectedElement.id,
        this.editor.selectedElement.type
      );
    }
  }

  /**
   * Updates only the status portion of the transition properties panel
   */
  updateTransitionStatus(id) {
    const transition = this.api.petriNet.transitions.get(id);
    if (!transition) return;

    const isEnabled = this.api.petriNet.isTransitionEnabled(id);


    const statusContainer = document.getElementById(
      "transition-status-container"
    );
    if (statusContainer) {
      statusContainer.innerHTML = `
            <div style="padding: 8px; background-color: ${
              isEnabled ? "#d5f5e3" : "#f5e6e6"
            }; border-radius: 4px;">
                ${isEnabled ? "✅ Enabled" : "❌ Disabled"}
            </div>
        `;
    }


    const fireButtonContainer = document.getElementById(
      "fire-button-container"
    );
    if (fireButtonContainer) {
      fireButtonContainer.innerHTML = `
            <button id="btn-fire-transition" ${
              !isEnabled ? "disabled" : ""
            }>Fire Transition</button>
        `;


      const fireButton = document.getElementById("btn-fire-transition");
      if (fireButton) {
        fireButton.addEventListener("click", async () => {
          // Capture initial state on first transition fire
          if (!this.simulationStarted) {
            this.captureInitialState();
          }
          
          if (await this.fireTransition(id)) {
            this.updateTokensDisplay();
            this.updateTransitionStatus(id);
            this.updateSelectedElementProperties();
          }
        });
      }
    }
  }

  /**
   * Fire a specific transition (ASYNC)
   * @param {string} id - ID of the transition to fire
   * @returns {Promise<boolean>} Whether the transition fired successfully
   */
  async fireTransition(id) {
    return await this.api.fireTransition(id);
  }

  /**
   * Displays properties for a selected arc
   */
  showArcProperties(id) {
    const arc = this.api.petriNet.arcs.get(id);
    if (!arc) return;


    const sourcePlace = this.api.petriNet.places.get(arc.source);
    const sourceTransition = this.api.petriNet.transitions.get(arc.source);
    const targetPlace = this.api.petriNet.places.get(arc.target);
    const targetTransition = this.api.petriNet.transitions.get(arc.target);

    const sourceName = sourcePlace
      ? `Place: ${sourcePlace.label}`
      : `Transition: ${sourceTransition?.label}`;

    const targetName = targetPlace
      ? `Place: ${targetPlace.label}`
      : `Transition: ${targetTransition?.label}`;

    this.propertiesPanel.innerHTML = `
      <div class="form-group">
        <label for="arc-id">ID</label>
        <input type="text" id="arc-id" value="${id}" disabled>
      </div>
      <div class="form-group">
        <label for="arc-source">Source</label>
        <input type="text" id="arc-source" value="${sourceName}" disabled>
      </div>
      <div class="form-group">
        <label for="arc-target">Target</label>
        <input type="text" id="arc-target" value="${targetName}" disabled>
      </div>
      <div class="form-group">
        <label for="arc-weight">Weight</label>
        <input type="number" id="arc-weight" value="${arc.weight}" min="1">
      </div>
      <div class="form-group">
        <label for="arc-type">Type</label>
        <select id="arc-type">
          <option value="regular" ${arc.type === "regular" ? "selected" : ""}>Regular</option>
          <option value="inhibitor" ${arc.type === "inhibitor" ? "selected" : ""}>Inhibitor</option>
          <option value="reset" ${arc.type === "reset" ? "selected" : ""}>Reset</option>
          <option value="read" ${arc.type === "read" ? "selected" : ""}>Read</option>
          <!-- <option value="modifier" ${arc.type === "modifier" ? "selected" : ""}>Modifier</option> -->
        </select>
      </div>
      <div class="form-group">
        <label for="arc-label">Label (leave empty to use weight)</label>
        <input type="text" id="arc-label" value="${
          arc.label !== arc.weight.toString() ? arc.label : ""
        }">
      </div>
    `;


    const weightInput = document.getElementById("arc-weight");
    if (weightInput) {
      weightInput.addEventListener("change", (e) => {
        const value = parseInt(e.target.value, 10);
        if (!isNaN(value) && value >= 1) {
          this.api.setArcWeight(id, value);


          const labelInput = document.getElementById("arc-label");
          if (labelInput && !labelInput.value) {
            arc.label = value.toString();
          }
        }
      });
    }

    const typeSelect = document.getElementById("arc-type");
    if (typeSelect) {
      typeSelect.addEventListener("change", (e) => {
        this.api.setArcType(id, e.target.value);
      });
    }

    const labelInput = document.getElementById("arc-label");
    if (labelInput) {
      labelInput.addEventListener("change", (e) => {
        const label = e.target.value || arc.weight.toString();
        arc.label = label;
        this.editor.render();
      });
    }
  }

  updateFinalMarkingDisplay() {
    const finalMarkingContent = document.getElementById("final-marking-content");
    if (!finalMarkingContent) return;

    const results = this.api.checkFinalMarkings();
    
    if (results.placesWithFinalMarkings === 0) {
      finalMarkingContent.innerHTML = "<p>No final markings defined.</p>";
      return;
    }

    let html = `
      <div class="final-marking-summary">
        <div style="margin-bottom: 10px;">
          <strong>Progress:</strong> ${results.satisfiedFinalMarkings}/${results.placesWithFinalMarkings} 
          ${results.allSatisfied ? '✅' : '⏳'}
        </div>
      </div>
      <div class="final-marking-details">
    `;

    for (const [id, place] of this.api.petriNet.places) {
      if (place.hasFinalMarking()) {
        const status = place.hasReachedFinalMarking() ? '✅' : '⏳';
        const statusClass = place.hasReachedFinalMarking() ? 'satisfied' : 'pending';
        
        html += `
          <div class="final-marking-item ${statusClass}">
            <span class="place-label">${place.label}</span>
            <span class="marking-status">${place.tokens}/${place.finalMarking} ${status}</span>
          </div>
        `;
      }
    }

    html += '</div>';
    
    if (results.allSatisfied) {
      html += `
        <div class="final-marking-completed" style="
          background-color: rgba(163, 190, 140, 0.2); 
          border: 1px solid #A3BE8C; 
          border-radius: 4px; 
          padding: 8px; 
          margin-top: 10px;
          text-align: center;
        ">
          🎉 All final markings reached!
        </div>
      `;
    }

    finalMarkingContent.innerHTML = html;
  }

  handleNetworkChanged() {
    this.updateTokensDisplay();
    this.updateFinalMarkingDisplay();

    if (this.editor.selectedElement) {
      this.handleElementSelected(
        this.editor.selectedElement.id,
        this.editor.selectedElement.type
      );
    }
  }

  /**
   * Updates the tokens display in the sidebar
   */
  updateTokensDisplay() {

    this.tokensDisplay.innerHTML = "";


    if (this.api.petriNet.places.size === 0) {
      this.tokensDisplay.innerHTML = "<p>No places in the Petri net.</p>";
      return;
    }


    const header = document.createElement("div");
    header.innerHTML = "<strong>Place Tokens:</strong>";
    this.tokensDisplay.appendChild(header);


    for (const [id, place] of this.api.petriNet.places) {
      const placeDiv = document.createElement("div");
      placeDiv.textContent = `${place.label}: ${place.tokens}`;
      this.tokensDisplay.appendChild(placeDiv);
    }
  }
  /**
   * Initializes a ResizeObserver to automatically handle canvas resizing.
   * @returns {void}
   */
  setupResizeObserver() {
    const resizeObserver = new ResizeObserver(() => {
        // Use requestAnimationFrame to avoid ResizeObserver loop errors in Safari
        requestAnimationFrame(() => {
            this.resizeCanvas();
        });
    });
    // Observe the canvas's parent container for size changes
    if (this.canvas.parentElement) {
        resizeObserver.observe(this.canvas.parentElement);
    }
  }

   /**
   * Resizes the canvas to fit its container while maintaining sharp resolution.
   * This function should be called whenever the canvas's container size changes.
   * @returns {void}
   */
  resizeCanvas() {
    if (!this.canvas || !this.canvas.parentElement) {
        return;
    }

    const container = this.canvas.parentElement;
    const dpr = window.devicePixelRatio || 1;
    
    // Get the new size from the container, which has a stable size now
    const displayWidth = container.clientWidth;
    const displayHeight = container.clientHeight;

    // Set the canvas drawing buffer size.
    if (this.canvas.width !== displayWidth * dpr || this.canvas.height !== displayHeight * dpr) {
        this.canvas.width = displayWidth * dpr;
        this.canvas.height = displayHeight * dpr;

        if (this.editor) {
            this.editor.render();
        }
    }
  }

  /**
   * Steps the simulation by firing all enabled transitions simultaneously (ASYNC)
   * Uses synchronous step semantics with conflict resolution
   */
  async stepSimulation() {
    const enabledTransitions = this.api.getEnabledTransitions();

    if (enabledTransitions.length === 0) {
      alert("No enabled transitions.");
      return;
    }

    // Fire all enabled transitions simultaneously using synchronous step semantics
    // This includes automatic conflict resolution with randomization
    if (typeof this.api.petriNet.fireTransitionsSynchronously === 'function') {
      await this.api.petriNet.fireTransitionsSynchronously(enabledTransitions);
    } else {
      // Fallback for non-DPN petri nets - call synchronous method directly
      this.api.petriNet.fireTransitionsSynchronously(enabledTransitions);
    }
    
    // Update enabled transitions after firing
    this.api.petriNet.updateEnabledTransitions();
    
    // Force a render update
    if (this.api.editor) {
      this.api.editor.render();
    }
    
    this.updateTokensDisplay();
    this.updateSelectedElementProperties();
  }

  /**
   * Starts auto-running the simulation (ASYNC)
   */
  startAutoRun() {

    this.stopAutoRun();


    this.autoRunInterval = window.setInterval(async () => {
      const enabledTransitions = this.api.getEnabledTransitions();
      if (enabledTransitions.length === 0) {
        this.stopAutoRun();
        alert("Auto-run stopped: no more enabled transitions.");
        const autoRunButton = document.getElementById("btn-auto-run");
        if (autoRunButton) {
          autoRunButton.textContent = "Auto Run";
        }
        return;
      }

      await this.stepSimulation();
    }, this.autoRunDelay);
  }

  /**
   * Stops auto-running the simulation
   */
  stopAutoRun() {
    if (this.autoRunInterval !== null) {
      clearInterval(this.autoRunInterval);
      this.autoRunInterval = null;
    }
  }

  /**
   * Resets the simulation to initial state
   */
  resetSimulation() {
    // Stop auto-run
    this.stopAutoRun();

    const json = this.api.exportAsJSON();
    
    // IMPORTANT: Completely destroy the old editor and clean up all references
    this.destroyCurrentEditor();

    this.api = PetriNetAPI.importFromJSON(json);
    this.editor = this.api.attachEditor(this.canvas);

    // IMPORTANT: Re-establish the app reference after reset
    this.editor.app = this;

    // Reset simulation state tracking
    this.initialState = null;
    this.simulationStarted = false;

    // Re-initialize event handlers for the new editor
    this.initEventHandlers();

    this.editor.setOnSelectCallback(this.handleElementSelected.bind(this));
    this.editor.setOnChangeCallback(this.handleNetworkChanged.bind(this));
    this.editor.setSnapToGrid(this.gridEnabled);
    this.editor.setMode("select");
    this.updateActiveButton("btn-select");

    this.editor.render();
    this.updateTokensDisplay();
    this.updateZoomDisplay();
    this.propertiesPanel.innerHTML = "<p>No element selected.</p>";
  }
  /**
   * Clean up all app-level event listeners
   */
  cleanupAppEventListeners() {
    this.appEventListeners?.forEach(([eventType, handler, element]) => {
      element.removeEventListener(eventType, handler);
    });
    this.appEventListeners = [];
  }

  destroyCurrentEditor() {
  // Force stop all interactions immediately
  if (this.editor) {
    this.editor.isPanning = false;
    this.editor.lastPanPosition = null;
    this.editor.dragStart = null;
    this.editor.dragOffset = null;
    this.editor.arcDrawing = null;
    this.editor.selectedElement = null;
    this.editor.ghostElement = null;
    this.editor.ghostPosition = null;
    this.editor.isShiftPressed = false;
    
    // Clear any renderer state and force canvas clear
    if (this.editor.renderer) {
      this.editor.renderer.panOffset = { x: 0, y: 0 };
      this.editor.renderer.zoomFactor = 1.0;
      
      // Force renderer to clear its internal state
      if (this.canvas) {
        const ctx = this.canvas.getContext('2d');
        ctx.save();
        ctx.setTransform(1, 0, 0, 1, 0, 0);
        ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
        ctx.fillStyle = 'white';
        ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
        ctx.restore();
      }
    }
  }
  
  // Clean up all app-level event listeners
  this.cleanupAppEventListeners();
  
  // Destroy editor's internal event listeners
  if (this.editor && typeof this.editor.destroy === 'function') {
    this.editor.destroy();
  }
  
  // Force complete object dereferencing
  this.editor = null;
  this.api = null;
  
  // Reset canvas cursor and ensure it's completely clean
  if (this.canvas) {
    this.canvas.style.cursor = 'default';
    // Final canvas clear
    const ctx = this.canvas.getContext('2d');
    ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);
  }
}


  /**
   * New method to stop all ongoing interactions
   */
  stopAllInteractions() {
    if (this.editor) {
      // Reset all interaction states
      this.editor.isPanning = false;
      this.editor.lastPanPosition = null;
      this.editor.dragStart = null;
      this.editor.dragOffset = null;
      this.editor.arcDrawing = null;
      this.editor.selectedElement = null;
      this.editor.ghostElement = null;
      this.editor.ghostPosition = null;
      this.editor.isShiftPressed = false;
      
      // Reset canvas cursor
      if (this.canvas) {
        this.canvas.style.cursor = 'default';
      }
    }
  }
  /**
   * Resets the Petri net completely
   */
  resetPetriNet() {
    this.stopAutoRun();
    this.stopAllInteractions();

    if (this.fitCanvasTimeout) {
      clearTimeout(this.fitCanvasTimeout);
      this.fitCanvasTimeout = null;
    }

    this.destroyCurrentEditor();

    if (this._resetTimeout) {
      clearTimeout(this._resetTimeout);
      this._resetTimeout = null;
    }

    return new Promise((resolve, reject) => {
      this._resetTimeout = setTimeout(() => {
        try {
          this.api = new PetriNetAPI();
          this.editor = this.api.attachEditor(this.canvas);

          this.editor.app = this;

          this.initialState = null;
          this.simulationStarted = false;

          if (this.editor.renderer) {
            this.editor.renderer.panOffset = { x: 0, y: 0 };
            this.editor.renderer.zoomFactor = 1.0;
          }

          this.initEventHandlers();

          this.editor.setOnSelectCallback(this.handleElementSelected.bind(this));
          this.editor.setOnChangeCallback(this.handleNetworkChanged.bind(this));
          this.editor.setSnapToGrid(this.gridEnabled);
          this.editor.setMode("select");
          this.updateActiveButton("btn-select");

          this.editor.render();
          this.updateTokensDisplay();
          this.updateZoomDisplay();
          this.propertiesPanel.innerHTML = "<p>No element selected.</p>";

          this._resetTimeout = null;
          resolve();
        } catch (err) {
          this._resetTimeout = null;
          reject(err);
        }
      }, 50);
    });
  }


  /**
   * Creates a File object from JSON data
   */
  createFileFromJSON(jsonData, fileName = "data.json") {

    const jsonString =
      typeof jsonData === "object"
        ? JSON.stringify(jsonData, null, 2)
        : jsonData;

    const blob = new Blob([jsonString], { type: "application/json" });
    const file = new File([blob], fileName, { type: "application/json" });
    return file;
  }

  /**
   * Loads a template Petri net
   */
  loadTemplate(template_path) {
    this.stopAutoRun();
    fetch(template_path)
      .then((response) => {
        if (!response.ok) {
          throw new Error(`HTTP error! Status: ${response.status}`);
        }
        return response.json();
      })
      .then((jsonData) => {
        const file = this.createFileFromJSON(jsonData);
        return this.loadFromFile(file);
      }).then(() => {
        setTimeout(() => {
          this.fitNetworkToCanvas();
        }, 100);
      })
      .catch((error) => {
        console.error("Error loading template:", error);
      });
  }

  /**
   * Saves the current Petri net to a JSON file
   */
  saveToFile() {
    const json = this.api.exportAsJSON();
    const blob = new Blob([json], { type: "application/json" });
    const url = URL.createObjectURL(blob);

    const a = document.createElement("a");
    a.href = url;
    a.download = "petri-net.json";
    a.click();

    URL.revokeObjectURL(url);
  }

  /**
   * Loads a Petri net from a JSON file
   */
  loadFromFile(file) {
    const reader = new FileReader();
    reader.onload = (e) => {
      try {
        const json = e.target?.result;
        if (!json) return;

        // Stop all running processes
        this.stopAutoRun();
        this.stopAllInteractions();

        // Clear any pending timeouts
        if (this.fitCanvasTimeout) {
          clearTimeout(this.fitCanvasTimeout);
          this.fitCanvasTimeout = null;
        }

        // Completely destroy the old editor and clean up event listeners
        this.destroyCurrentEditor();

        // Clear the canvas completely and keep it clear
        const canvas = this.canvas;
        const ctx = canvas.getContext('2d');
        
        // Force complete canvas reset - this prevents any cached render data
        const width = canvas.width;
        const height = canvas.height;
        canvas.width = width;  // Resetting width clears the entire canvas buffer
        canvas.height = height;
        
        ctx.fillStyle = 'white';
        ctx.fillRect(0, 0, width, height);

        // Small delay to ensure cleanup is complete
        setTimeout(() => {
          // Create completely new API and editor instances
          this.api = PetriNetAPI.importFromJSON(json);
          this.editor = this.api.attachEditor(this.canvas);

          // CRITICAL FIX: Ensure all references point to the new petriNet
          // The editor and renderer must both reference the same new PetriNet instance
          if (this.editor.renderer) {
            this.editor.renderer.petriNet = this.api.petriNet;
          }
          if (this.editor) {
            this.editor.petriNet = this.api.petriNet;
          }

          // Re-establish app reference and callbacks
          this.editor.app = this;
          this.editor.setOnSelectCallback(this.handleElementSelected.bind(this));
          this.editor.setOnChangeCallback(this.handleNetworkChanged.bind(this));
          
          // Reinitialize all handlers
          this.initEventHandlers();

          // Reset all simulation and UI state
          this.initialState = null;
          this.simulationStarted = false;
          this.editor.setSnapToGrid(this.gridEnabled);
          this.editor.setMode("select");
          this.updateActiveButton("btn-select");
          this.propertiesPanel.innerHTML = "<p>No element selected.</p>";

          // Force immediate render
          this.editor.render();
          this.updateTokensDisplay();
          this.updateZoomDisplay();
          this.updateFinalMarkingDisplay();

          // Fit canvas to new network
          this.fitCanvasTimeout = setTimeout(() => {
            this.fitNetworkToCanvas();
          }, 100);

        }, 50);

      } catch (error) {
        console.error("Error loading file:", error);
        alert("Error loading file: " + error);
      }
    };
    reader.readAsText(file);
  }

  loadTemplateFile(file) {
    return fetch(file).then((response) => response.json());
  }

  /**
   * Fully destroys a canvas and replaces it with a pristine one that keeps the same
   * element ID and width/height properties. Any previous drawing state, pixel contents,
   * and event listeners bound to the old element are discarded.
   *
   * @param {HTMLCanvasElement} canvas - The canvas element to reset.
   * @returns {HTMLCanvasElement} - The newly created pristine canvas element.
   */
  recreatePristineCanvas(canvas) {
    if (!(canvas instanceof HTMLCanvasElement)) {
      throw new TypeError("Expected an HTMLCanvasElement.");
    }

    const parent = canvas.parentNode;
    const nextSibling = canvas.nextSibling;

    const preservedId = canvas.id || "";
    const preservedWidth = canvas.width;
    const preservedHeight = canvas.height;

    try {
      const webgl2 = canvas.getContext("webgl2");
      if (webgl2 && typeof webgl2.getExtension === "function") {
        const ext = webgl2.getExtension("WEBGL_lose_context");
        if (ext && typeof ext.loseContext === "function") ext.loseContext();
      }
    } catch (_) {}

    try {
      const webgl = canvas.getContext("webgl") || canvas.getContext("experimental-webgl");
      if (webgl && typeof webgl.getExtension === "function") {
        const ext = webgl.getExtension("WEBGL_lose_context");
        if (ext && typeof ext.loseContext === "function") ext.loseContext();
      }
    } catch (_) {}

    try {
      const ctx2d = canvas.getContext("2d");
      if (ctx2d) {
        canvas.width = canvas.width;
      }
    } catch (_) {}

    const fresh = document.createElement("canvas");
    if (preservedId) fresh.id = preservedId;
    fresh.width = preservedWidth;
    fresh.height = preservedHeight;

    if (parent) {
      parent.replaceChild(fresh, canvas);
    }

    return fresh;
  }


  /**
   * Exports the current Petri net to PNML format
   */
  exportToPNML() {
    const pnml = this.api.exportAsPNML();
    const blob = new Blob([pnml], { type: "application/xml" });
    const url = URL.createObjectURL(blob);

    const a = document.createElement("a");
    a.href = url;
    a.download = "petri-net.pnml";
    a.click();

    URL.revokeObjectURL(url);
  }
}

window.PetriNetApp = PetriNetApp;

export default PetriNetApp;