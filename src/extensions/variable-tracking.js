/**
 * Data Petri Net Variable Tracking Extension
 * 
 * This script extends the simulation functionality to properly update
 * the data variables display during simulation.
 */


document.addEventListener('DOMContentLoaded', () => {

    const checkInterval = setInterval(() => {
      if (window.petriApp && window.dataPetriNetIntegration) {
        clearInterval(checkInterval);
        

        extendSimulationFunctionality();
      }
    }, 100);
  });
  
  /**
   * Extends the simulation functionality to update variable display
   */
  function extendSimulationFunctionality() {
    const app = window.petriApp;
    

    if (!app) return;
    

    const originalStepSimulation = app.stepSimulation;
    app.stepSimulation = function() {

      const result = originalStepSimulation.call(this);
      

      updateDataValuesDisplay();
      

      updateVariableHistory();
      
      return result;
    };
    

    const originalFireTransition = app.fireTransition;
    app.fireTransition = function(id) {

      const result = originalFireTransition.call(this, id);
      

      updateDataValuesDisplay();
      

      updateVariableHistory();
      
      return result;
    };
    

    if (app.api && app.api.fireTransition) {
      const originalAPIFireTransition = app.api.fireTransition;
      app.api.fireTransition = function(id) {

        const result = originalAPIFireTransition.call(this, id);
        

        updateDataValuesDisplay();
        

        updateVariableHistory(`Transition ${id}`);
        
        return result;
      };
    }
    

    const originalStartAutoRun = app.startAutoRun;
    app.startAutoRun = function() {

      const result = originalStartAutoRun.call(this);
      

      const originalInterval = this.autoRunInterval;
      if (originalInterval) {
        clearInterval(originalInterval);
        
        this.autoRunInterval = setInterval(() => {
          const enabledTransitions = this.api.getEnabledTransitions();
          if (enabledTransitions.length === 0) {
            this.stopAutoRun();
            alert('Auto-run stopped: no more enabled transitions.');
            const autoRunButton = document.getElementById('btn-auto-run');
            if (autoRunButton) {
              autoRunButton.textContent = 'Auto Run';
            }
            return;
          }
          
          this.stepSimulation();

        }, this.autoRunDelay);
      }
      
      return result;
    };
    

    createVariableHistoryPanel();
    
    console.log('Data Petri Net Variable Tracking Extension loaded.');
  }
  
  /**
   * Updates the data values display
   */
  function updateDataValuesDisplay() {
    const app = window.petriApp;
    if (!app || !window.dataPetriNetIntegration) return;
    

    if (window.dataPetriNetIntegration.dataPetriNetUI) {

      const previousValues = {};
      

      const valuesTable = document.querySelector('.data-values-table');
      if (valuesTable) {
        const rows = valuesTable.querySelectorAll('tr');
        for (let i = 1; i < rows.length; i++) { // Skip header row
          const cells = rows[i].querySelectorAll('td');
          if (cells.length >= 2) {
            const name = cells[0].textContent.trim();
            const value = cells[1].textContent.trim();
            previousValues[name] = value;
          }
        }
      }
      

      window.dataPetriNetIntegration.dataPetriNetUI.updateDataValuesDisplay();
      

      const newValuesTable = document.querySelector('.data-values-table');
      if (newValuesTable) {
        const rows = newValuesTable.querySelectorAll('tr');
        for (let i = 1; i < rows.length; i++) { // Skip header row
          const cells = rows[i].querySelectorAll('td');
          if (cells.length >= 2) {
            const name = cells[0].textContent.trim();
            const value = cells[1].textContent.trim();
            

            if (previousValues[name] !== undefined && previousValues[name] !== value) {

              cells[1].classList.add('data-variable-changed');
            }
          }
        }
      }
    }
  }
  
  /**
   * Create a panel to show variable history
   */
  function createVariableHistoryPanel() {

    if (!document.getElementById('variable-history-container')) {
      const simulationPanel = document.querySelector('.simulation-controls');
      if (!simulationPanel) return;
      
      const historyPanel = document.createElement('div');
      historyPanel.className = 'variable-history-panel';
      historyPanel.innerHTML = `
        <div class="variable-history-header">
          <h4>Variable History</h4>
          <div class="variable-history-controls">
            <button id="btn-toggle-history" title="Toggle history tracking">Start Tracking</button>
            <button id="btn-clear-history" title="Clear history">Clear</button>
          </div>
        </div>
        <div id="variable-history-content" class="variable-history-content">
          <p>History tracking is disabled. Click "Start Tracking" to begin.</p>
        </div>
      `;
      

      const dataValuesDisplay = simulationPanel.querySelector('.data-values-display');
      if (dataValuesDisplay) {
        simulationPanel.insertBefore(historyPanel, dataValuesDisplay.nextSibling);
      } else {
        simulationPanel.appendChild(historyPanel);
      }
      

      const toggleButton = document.getElementById('btn-toggle-history');
      if (toggleButton) {
        toggleButton.addEventListener('click', toggleVariableHistoryTracking);
      }
      
      const clearButton = document.getElementById('btn-clear-history');
      if (clearButton) {
        clearButton.addEventListener('click', clearVariableHistory);
      }
      

      addVariableHistoryStyles();
    }
  }
  

  let historyTracking = {
    enabled: false,
    entries: [],
    maxEntries: 100  // Maximum number of history entries to keep
  };
  
  /**
   * Toggle variable history tracking
   */
  function toggleVariableHistoryTracking() {
    historyTracking.enabled = !historyTracking.enabled;
    
    const toggleButton = document.getElementById('btn-toggle-history');
    if (toggleButton) {
      toggleButton.textContent = historyTracking.enabled ? 'Stop Tracking' : 'Start Tracking';
    }
    
    const historyContent = document.getElementById('variable-history-content');
    if (historyContent) {
      if (historyTracking.enabled) {
        historyContent.innerHTML = '<p>Tracking started. Variable changes will appear here.</p>';

        addVariableSnapshot('Initial State');
      } else {
        historyContent.innerHTML += '<p>Tracking stopped.</p>';
      }
    }
  }
  
  /**
   * Clear variable history
   */
  function clearVariableHistory() {
    historyTracking.entries = [];
    
    const historyContent = document.getElementById('variable-history-content');
    if (historyContent) {
      if (historyTracking.enabled) {
        historyContent.innerHTML = '<p>History cleared. Tracking continues.</p>';

        addVariableSnapshot('Initial State');
      } else {
        historyContent.innerHTML = '<p>History tracking is disabled. Click "Start Tracking" to begin.</p>';
      }
    }
  }
  
  /**
   * Add a snapshot of current variable values to history
   */
  function addVariableSnapshot(label) {
    const app = window.petriApp;
    if (!app || !app.api || !app.api.petriNet || !app.api.petriNet.dataVariables) return;
    

    const timestamp = new Date();
    const snapshot = {
      label: label || `Step ${historyTracking.entries.length + 1}`,
      timestamp: timestamp,
      values: {}
    };
    

    for (const [id, variable] of app.api.petriNet.dataVariables) {
      snapshot.values[variable.name] = variable.currentValue;
    }
    

    let valuesChanged = true;
    if (historyTracking.entries.length > 0) {
      const previousSnapshot = historyTracking.entries[historyTracking.entries.length - 1];
      valuesChanged = false;
      

      for (const [name, value] of Object.entries(snapshot.values)) {
        if (previousSnapshot.values[name] !== value) {
          valuesChanged = true;
          break;
        }
      }
    }
    

    if (valuesChanged || historyTracking.entries.length === 0) {

      historyTracking.entries.push(snapshot);
      

      if (historyTracking.entries.length > historyTracking.maxEntries) {
        historyTracking.entries.shift();
      }
      

      updateVariableHistoryDisplay();
    }
  }
  
  /**
   * Update variable history display
   */
  function updateVariableHistory() {
    if (!historyTracking.enabled) return;
    
    const app = window.petriApp;
    if (!app || !app.api || !app.api.petriNet || !app.api.petriNet.dataVariables) return;
    

    let transitionLabel = "Step";
    const enabledTransitions = app.api.getEnabledTransitions();
    if (enabledTransitions.length > 0) {
      const lastTransition = app.api.petriNet.transitions.get(enabledTransitions[0]);
      if (lastTransition) {
        transitionLabel = lastTransition.label || lastTransition.id;
      }
    }
    

    addVariableSnapshot(`After firing: ${transitionLabel}`);
    

    updateVariableHistoryDisplay();
  }
  
  /**
   * Update the variable history display
   */
  function updateVariableHistoryDisplay() {
    const historyContent = document.getElementById('variable-history-content');
    if (!historyContent) return;
    

    let html = '';
    
    if (historyTracking.entries.length === 0) {
      html = '<p>No history entries yet.</p>';
    } else {
      html = '<div class="history-entries">';
      

      for (let i = historyTracking.entries.length - 1; i >= 0; i--) {
        const entry = historyTracking.entries[i];
        const time = entry.timestamp.toLocaleTimeString();
        
        html += `
          <div class="history-entry">
            <div class="history-entry-header">
              <span class="history-entry-label">${entry.label}</span>
              <span class="history-entry-time">${time}</span>
            </div>
            <div class="history-entry-values">
        `;
        

        for (const [name, value] of Object.entries(entry.values)) {
          html += `
            <div class="history-entry-variable">
              <span class="history-variable-name">${name}:</span>
              <span class="history-variable-value">${value !== null ? value : '(null)'}</span>
            </div>
          `;
        }
        
        html += `
            </div>
          </div>
        `;
      }
      
      html += '</div>';
    }
    
    historyContent.innerHTML = html;
  }
  
  /**
   * Add styles for the variable history panel
   */
  function addVariableHistoryStyles() {

    let styleElement = document.getElementById('variable-history-styles');
    if (!styleElement) {
      styleElement = document.createElement('style');
      styleElement.id = 'variable-history-styles';
      document.head.appendChild(styleElement);
    }
    

    styleElement.textContent = `
      .variable-history-panel {
        margin-top: 15px;
        border-top: 1px solid #434C5E;
        padding-top: 10px;
      }
      
      .variable-history-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 10px;
      }
      
      .variable-history-header h4 {
        margin: 0;
        color: #E5E9F0;
      }
      
      .variable-history-controls {
        display: flex;
        gap: 5px;
      }
      
      .variable-history-content {
        max-height: 300px;
        overflow-y: auto;
        padding-right: 5px;
      }
      
      .history-entries {
        display: flex;
        flex-direction: column;
        gap: 10px;
      }
      
      .history-entry {
        background-color: #3B4252;
        border-radius: 4px;
        padding: 8px;
        border-left: 3px solid #81A1C1;
      }
      
      .history-entry-header {
        display: flex;
        justify-content: space-between;
        margin-bottom: 5px;
        font-size: 14px;
      }
      
      .history-entry-label {
        font-weight: bold;
        color: #ECEFF4;
      }
      
      .history-entry-time {
        color: #D8DEE9;
        font-size: 12px;
      }
      
      .history-entry-values {
        display: flex;
        flex-direction: column;
        gap: 3px;
      }
      
      .history-entry-variable {
        display: flex;
        gap: 5px;
        font-size: 13px;
      }
      
      .history-variable-name {
        color: #88C0D0;
        font-family: monospace;
      }
      
      .history-variable-value {
        color: #A3BE8C;
        font-family: monospace;
      }
    `;
  }