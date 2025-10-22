
import { PetriNetAPI, PetriNetEditor, Place, Arc } from '../petri-net-simulator.js';
import { DataPetriNetAPI } from './dpn-api.js';
import { DataAwareTransition } from './dpn-model.js';
import { DataPetriNetRenderer } from './dpn-renderer.js';
import { DataPetriNetUI } from './dpn-ui.js';


class DataPetriNetIntegration {
  /**
   * Initialize the Data Petri Net extensions
   * @param {PetriNetApp} app - Reference to the main application
   * @param {function} callback - Optional callback function after initialization
   */
  constructor(app, callback) {

    if (DataPetriNetIntegration.initialized) {
      if (typeof callback === 'function') {
        callback(window.dataPetriNetIntegration);
      }
      return;
    }
    

    DataPetriNetIntegration.initialized = true;
    this.app = app;
    

    this.injectStyles()
      .then(() => this.extendAPI())
      .then(() => this.extendRenderer())
      .then(() => this.initializeUI())
      .then(() => {
        if (typeof callback === 'function') {
          callback(this);
        }
      })
      .catch(error => {
        console.error("Error initializing Data Petri Net extensions:", error);
      });
  }

  /**
   * Inject CSS styles for Data Petri Net UI
   * @returns {Promise} Promise that resolves when styles are injected
   */
  async injectStyles() {
    return new Promise((resolve) => {

      if (document.getElementById('data-petri-net-styles')) {
        console.log("Data Petri Net styles already injected");
        resolve();
        return;
      }
      

      const style = document.createElement('style');
      style.id = 'data-petri-net-styles';
      

      style.textContent = `
/* Data Petri Net extension styles */
.data-variables-panel {
  margin-top: 15px;
  padding-top: 15px;
  border-top: 1px solid #434C5E;
}
/* ... rest of CSS ... */
      `;
      

      document.head.appendChild(style);
      resolve();
    });
  }

  /**
   * Extend the API to use Data Petri Net functionality
   * @returns {Promise} Promise that resolves when API is extended
   */
  async extendAPI() {
    return new Promise((resolve) => {

      if (this.app.api instanceof DataPetriNetAPI) {
        console.log("API already extended to DataPetriNetAPI");
        resolve();
        return;
      }
      

      const oldAPI = this.app.api;

      const newAPI = new DataPetriNetAPI(
        oldAPI.petriNet.id,
        oldAPI.petriNet.name,
        oldAPI.petriNet.description
      );
      

      for (const [id, place] of oldAPI.petriNet.places) {
        const newPlace = new Place(
          id,
          { x: place.position.x, y: place.position.y },
          place.label,
          place.tokens,
          place.capacity
        );
        newAPI.petriNet.places.set(id, newPlace);
      }
      
      for (const [id, transition] of oldAPI.petriNet.transitions) {

        const newTransition = new DataAwareTransition(
          id,
          { x: transition.position.x, y: transition.position.y },
          transition.label,
          transition.priority,
          transition.delay,
          "",  // empty precondition
          ""   // empty postcondition
        );
        newTransition.isEnabled = transition.isEnabled;
        newAPI.petriNet.transitions.set(id, newTransition);
      }
      
      for (const [id, arc] of oldAPI.petriNet.arcs) {
        const newArc = new Arc(
          id,
          arc.source,
          arc.target,
          arc.weight,
          arc.type,
          [...arc.points],
          arc.label
        );
        newAPI.petriNet.arcs.set(id, newArc);
      }
      

      if (oldAPI.editor && oldAPI.canvas) {
        newAPI.canvas = oldAPI.canvas;
      }
      

      this.app.api = newAPI;
      resolve();
    });
  }

  /**
   * Extend the renderer to use Data Petri Net rendering
   * @returns {Promise} Promise that resolves when renderer is extended
   */
  async extendRenderer() {
    return new Promise((resolve) => {
      const api = this.app.api;
    
      const canvas = api.canvas;
      
      if (!canvas) {
        console.error("Canvas not found, cannot extend renderer");
        resolve();
        return;
      }
      

      if (this.app.editor && this.app.editor.renderer instanceof DataPetriNetRenderer) {
        console.log("Renderer already extended to DataPetriNetRenderer");
        resolve();
        return;
      }
      

      const oldEditor = this.app.editor;
      const selectedElement = oldEditor ? oldEditor.selectedElement : null;
      const mode = oldEditor ? oldEditor.mode : 'select';
      const snapToGrid = oldEditor ? oldEditor.snapToGrid : true;
      const gridSize = oldEditor ? oldEditor.gridSize : 10;
      const callbacks = oldEditor ? oldEditor.callbacks : { onChange: null, onSelect: null };
      

      if (oldEditor) {
        oldEditor.destroy();
      }
      

      this.app.editor = new PetriNetEditor(canvas, api.petriNet);
      

      this.app.editor.renderer = new DataPetriNetRenderer(canvas, api.petriNet);
      

      this.app.editor.setMode(mode);
      this.app.editor.setSnapToGrid(snapToGrid, gridSize);
      this.app.editor.callbacks = callbacks;
      

      this.app.editor.app = this.app;
      

      api.editor = this.app.editor;
      

      if (selectedElement) {
        this.app.editor.selectElement(selectedElement.id, selectedElement.type);
      }
      

      this.app.editor.render();
      
      resolve();
    });
  }

/**
 * Initialize the UI components
 * @returns {Promise} Promise that resolves when UI is initialized
 */
async initializeUI() {
  return new Promise((resolve) => {
    // Check if already initialized
    if (this.dataPetriNetUI) {
      console.log("Data Petri Net UI already initialized");
      resolve();
      return;
    }
    
    // Clean up any existing UI elements
    this.cleanupExistingUIElements();
    
    // Create the UI
    this.dataPetriNetUI = new DataPetriNetUI(this.app);
    
    this.app.dataPetriNetUI = this.dataPetriNetUI;
    console.log("DataPetriNetUI attached to app:", this.app.dataPetriNetUI);
    
    // Extend event handlers and app functions
    this.extendEventHandlers();
    this.extendAppFunctions();
    
    resolve();
  });
}

  /**
   * Clean up any existing UI elements that may be duplicates
   */
  cleanupExistingUIElements() {

    const dataVariablesPanels = document.querySelectorAll('.data-variables-panel');
    if (dataVariablesPanels.length > 0) {
      console.log(`Found ${dataVariablesPanels.length} existing data variables panels, removing all`);
      dataVariablesPanels.forEach(panel => {
        panel.parentNode.removeChild(panel);
      });
    }
    

    const dataValuesDisplays = document.querySelectorAll('.data-values-display');
    if (dataValuesDisplays.length > 0) {
      console.log(`Found ${dataValuesDisplays.length} existing data values displays, removing all`);
      dataValuesDisplays.forEach(display => {
        display.parentNode.removeChild(display);
      });
    }
    

    const dataTransitionButtons = document.querySelectorAll('#btn-add-data-transition');
    if (dataTransitionButtons.length > 0) {
      console.log(`Found ${dataTransitionButtons.length} existing data transition buttons, removing all`);
      dataTransitionButtons.forEach(button => {
        button.parentNode.removeChild(button);
      });
    }
  }

  /**
   * Extend the app's event handlers
   */
  extendEventHandlers() {

    if (this.handlersExtended) return;
    this.handlersExtended = true;
    

    const originalHandleNetworkChanged = this.app.handleNetworkChanged;
    this.app.handleNetworkChanged = () => {

      originalHandleNetworkChanged.call(this.app);
      

      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataVariablesDisplay();
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
    };
    

    const originalResetSimulation = this.app.resetSimulation;
    this.app.resetSimulation = () => {

      originalResetSimulation.call(this.app);
      

      if (this.app.api && typeof this.app.api.resetDataVariables === 'function') {
        this.app.api.resetDataVariables();
      }
      

      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
    };
  }

  /**
   * Extend the app's functions
   */
  extendAppFunctions() {

    if (this.functionsExtended) return;
    this.functionsExtended = true;
    

    const originalResetPetriNet = this.app.resetPetriNet;
    this.app.resetPetriNet = () => {

      originalResetPetriNet.call(this.app);
      

      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataVariablesDisplay();
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
      

      if (!(this.app.api instanceof DataPetriNetAPI)) {
        console.warn("API is not DataPetriNetAPI after reset, reinitializing");
        this.extendAPI().then(() => this.extendRenderer());
      }
    };
    

    const originalLoadFromFile = this.app.loadFromFile;
    this.app.loadFromFile = (file) => {

      const reader = new FileReader();
      reader.onload = (e) => {
        try {
          const json = e.target?.result;
          

          this.app.api = DataPetriNetAPI.importFromJSON(json);
          this.app.editor = this.app.api.attachEditor(this.app.canvas);
          

          this.app.editor.renderer = new DataPetriNetRenderer(this.app.canvas, this.app.api.petriNet);
          

          this.app.editor.app = this.app;
          

          this.app.editor.setOnSelectCallback(this.app.handleElementSelected.bind(this.app));
          this.app.editor.setOnChangeCallback(this.app.handleNetworkChanged.bind(this.app));
          this.app.editor.setSnapToGrid(this.app.gridEnabled);
          this.app.editor.setMode('select');
          this.app.updateActiveButton('btn-select');
          

          this.app.editor.render();
          this.app.updateTokensDisplay();
          this.app.updateZoomDisplay();
          this.app.propertiesPanel.innerHTML = '<p>No element selected.</p>';
          

          if (this.dataPetriNetUI) {
            this.dataPetriNetUI.updateDataVariablesDisplay();
            this.dataPetriNetUI.updateDataValuesDisplay();
          }
        } catch (error) {
          console.error("Error loading file:", error);
          alert('Error loading file: ' + error);
        }
      };
      reader.readAsText(file);
    };
  }
}


DataPetriNetIntegration.initialized = false;


document.addEventListener('DOMContentLoaded', () => {

  const initTimer = setInterval(() => {
    if (window.petriApp) {

      if (!window.dataPetriNetIntegration) {
        console.log("Initializing Data Petri Net extension");
        window.dataPetriNetIntegration = new DataPetriNetIntegration(window.petriApp);
      }
      clearInterval(initTimer);
    }
  }, 100);
});

export { DataPetriNetIntegration };