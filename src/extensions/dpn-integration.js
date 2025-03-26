
class DataPetriNetIntegration {
  /**
   * Initialize the Data Petri Net extensions
   * @param {PetriNetApp} app - Reference to the main application
   * @param {function} callback - Optional callback function after initialization
   */
  constructor(app, callback) {
    // Check for existing initialization
    if (DataPetriNetIntegration.initialized) {
      console.log("Data Petri Net Integration already initialized");
      if (typeof callback === 'function') {
        callback(window.dataPetriNetIntegration);
      }
      return;
    }
    
    // Mark as initialized
    DataPetriNetIntegration.initialized = true;
    this.app = app;
    
    // Initialize in this sequence
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
      // Check if styles are already injected
      if (document.getElementById('data-petri-net-styles')) {
        console.log("Data Petri Net styles already injected");
        resolve();
        return;
      }
      
      // Create a style element
      const style = document.createElement('style');
      style.id = 'data-petri-net-styles';
      
      // Add the CSS content (condensed for brevity)
      style.textContent = `
/* Data Petri Net extension styles */
.data-variables-panel {
  margin-top: 15px;
  padding-top: 15px;
  border-top: 1px solid #434C5E;
}
/* ... rest of CSS ... */
      `;
      
      // Add to document head
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
      // Check if API is already extended
      if (this.app.api instanceof DataPetriNetAPI) {
        console.log("API already extended to DataPetriNetAPI");
        resolve();
        return;
      }
      
      // Upgrade the application's API to use DataPetriNetAPI
      const oldAPI = this.app.api;
      
      // Create a new DataPetriNetAPI with the same ID, name, and description
      const newAPI = new DataPetriNetAPI(
        oldAPI.petriNet.id,
        oldAPI.petriNet.name,
        oldAPI.petriNet.description
      );
      
      // Copy existing places, transitions, and arcs
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
        // Create as DataAwareTransition to ensure proper upgrade
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
      
      // Attach the editor
      if (oldAPI.editor && oldAPI.canvas) {
        newAPI.canvas = oldAPI.canvas;
      }
      
      // Replace the app's API
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
      
      // Check if renderer is already extended
      if (this.app.editor && this.app.editor.renderer instanceof DataPetriNetRenderer) {
        console.log("Renderer already extended to DataPetriNetRenderer");
        resolve();
        return;
      }
      
      // Keep a reference to the old editor and its state
      const oldEditor = this.app.editor;
      const selectedElement = oldEditor ? oldEditor.selectedElement : null;
      const mode = oldEditor ? oldEditor.mode : 'select';
      const snapToGrid = oldEditor ? oldEditor.snapToGrid : true;
      const gridSize = oldEditor ? oldEditor.gridSize : 10;
      const callbacks = oldEditor ? oldEditor.callbacks : { onChange: null, onSelect: null };
      
      // If old editor exists, clean it up
      if (oldEditor) {
        oldEditor.destroy();
      }
      
      // Create new editor with DataPetriNetRenderer
      this.app.editor = new PetriNetEditor(canvas, api.petriNet);
      
      // Replace the editor's renderer with DataPetriNetRenderer
      this.app.editor.renderer = new DataPetriNetRenderer(canvas, api.petriNet);
      
      // Restore editor state
      this.app.editor.setMode(mode);
      this.app.editor.setSnapToGrid(snapToGrid, gridSize);
      this.app.editor.callbacks = callbacks;
      
      // Reference app in editor for extensions
      this.app.editor.app = this.app;
      
      // Reattach editor to API
      api.editor = this.app.editor;
      
      // Restore selection if there was one
      if (selectedElement) {
        this.app.editor.selectElement(selectedElement.id, selectedElement.type);
      }
      
      // Initial render
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
      // Check if UI is already initialized
      if (this.dataPetriNetUI) {
        console.log("Data Petri Net UI already initialized");
        resolve();
        return;
      }
      
      // First, clean up any existing UI elements that may be duplicates
      this.cleanupExistingUIElements();
      
      // Initialize the Data Petri Net UI
      this.dataPetriNetUI = new DataPetriNetUI(this.app);
      
      // Update event handlers that might need adjustment
      this.extendEventHandlers();
      
      // Update the app's functions that need to be extended for data petri nets
      this.extendAppFunctions();
      
      resolve();
    });
  }

  /**
   * Clean up any existing UI elements that may be duplicates
   */
  cleanupExistingUIElements() {
    // Find and remove duplicate data variables panels
    const dataVariablesPanels = document.querySelectorAll('.data-variables-panel');
    if (dataVariablesPanels.length > 0) {
      console.log(`Found ${dataVariablesPanels.length} existing data variables panels, removing all`);
      dataVariablesPanels.forEach(panel => {
        panel.parentNode.removeChild(panel);
      });
    }
    
    // Find and remove duplicate data values displays
    const dataValuesDisplays = document.querySelectorAll('.data-values-display');
    if (dataValuesDisplays.length > 0) {
      console.log(`Found ${dataValuesDisplays.length} existing data values displays, removing all`);
      dataValuesDisplays.forEach(display => {
        display.parentNode.removeChild(display);
      });
    }
    
    // Find and remove duplicate data transition buttons
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
    // Avoid extending handlers multiple times
    if (this.handlersExtended) return;
    this.handlersExtended = true;
    
    // Extend handleNetworkChanged to update data displays
    const originalHandleNetworkChanged = this.app.handleNetworkChanged;
    this.app.handleNetworkChanged = () => {
      // Call original handler
      originalHandleNetworkChanged.call(this.app);
      
      // Update data displays
      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataVariablesDisplay();
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
    };
    
    // Extend simulation reset to handle data variables
    const originalResetSimulation = this.app.resetSimulation;
    this.app.resetSimulation = () => {
      // Call original handler
      originalResetSimulation.call(this.app);
      
      // Reset data variables
      if (this.app.api && typeof this.app.api.resetDataVariables === 'function') {
        this.app.api.resetDataVariables();
      }
      
      // Update data displays
      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
    };
  }

  /**
   * Extend the app's functions
   */
  extendAppFunctions() {
    // Avoid extending functions multiple times
    if (this.functionsExtended) return;
    this.functionsExtended = true;
    
    // Extend resetPetriNet to handle data variables
    const originalResetPetriNet = this.app.resetPetriNet;
    this.app.resetPetriNet = () => {
      // Call original method
      originalResetPetriNet.call(this.app);
      
      // Update our UI
      if (this.dataPetriNetUI) {
        this.dataPetriNetUI.updateDataVariablesDisplay();
        this.dataPetriNetUI.updateDataValuesDisplay();
      }
      
      // Ensure we're using DataPetriNetAPI
      if (!(this.app.api instanceof DataPetriNetAPI)) {
        console.warn("API is not DataPetriNetAPI after reset, reinitializing");
        this.extendAPI().then(() => this.extendRenderer());
      }
    };
    
    // Extend loadFromFile to handle data variables
    const originalLoadFromFile = this.app.loadFromFile;
    this.app.loadFromFile = (file) => {
      // We need to intercept this to ensure DataPetriNetAPI.importFromJSON is used
      const reader = new FileReader();
      reader.onload = (e) => {
        try {
          const json = e.target?.result;
          
          // Use DataPetriNetAPI.importFromJSON instead
          this.app.api = DataPetriNetAPI.importFromJSON(json);
          this.app.editor = this.app.api.attachEditor(this.app.canvas);
          
          // Replace the editor's renderer with DataPetriNetRenderer
          this.app.editor.renderer = new DataPetriNetRenderer(this.app.canvas, this.app.api.petriNet);
          
          // Reference app in editor for extensions
          this.app.editor.app = this.app;
          
          // Reset UI state
          this.app.editor.setOnSelectCallback(this.app.handleElementSelected.bind(this.app));
          this.app.editor.setOnChangeCallback(this.app.handleNetworkChanged.bind(this.app));
          this.app.editor.setSnapToGrid(this.app.gridEnabled);
          this.app.editor.setMode('select');
          this.app.updateActiveButton('btn-select');
          
          // Render the network
          this.app.editor.render();
          this.app.updateTokensDisplay();
          this.app.updateZoomDisplay();
          this.app.propertiesPanel.innerHTML = '<p>No element selected.</p>';
          
          // Update data displays
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

// Static initialization flag
DataPetriNetIntegration.initialized = false;

// Initialize the Data Petri Net extensions when the app is ready
document.addEventListener('DOMContentLoaded', () => {
  // Wait for the PetriNetApp to be initialized
  const initTimer = setInterval(() => {
    if (window.petriApp) {
      // Check if already initialized
      if (!window.dataPetriNetIntegration) {
        console.log("Initializing Data Petri Net extension");
        window.dataPetriNetIntegration = new DataPetriNetIntegration(window.petriApp);
      }
      clearInterval(initTimer);
    }
  }, 100);
});