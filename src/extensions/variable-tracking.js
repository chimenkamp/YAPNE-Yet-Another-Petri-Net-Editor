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
      
      // Extend simulation functionality
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
  
  // Override stepSimulation to update variable display after each step
  const originalStepSimulation = app.stepSimulation;
  app.stepSimulation = function() {
    // Call original method
    const result = originalStepSimulation.call(this);
    
    // Update data values display
    updateDataValuesDisplay();
    
    // Add to variable history
    updateVariableHistory();
    
    return result;
  };
  
  // Override fireTransition to update variable display after firing
  const originalFireTransition = app.fireTransition;
  app.fireTransition = function(id) {
    // Call original method
    const result = originalFireTransition.call(this, id);
    
    // Update data values display
    updateDataValuesDisplay();
    
    // Add to variable history
    updateVariableHistory();
    
    return result;
  };
  
  // Override API-level fireTransition
  if (app.api && app.api.fireTransition) {
    const originalAPIFireTransition = app.api.fireTransition;
    app.api.fireTransition = function(id) {
      // Call original method
      const result = originalAPIFireTransition.call(this, id);
      
      // Update data values display
      updateDataValuesDisplay();
      
      // Add to variable history with label
      const transition = this.petriNet.transitions.get(id);
      const label = transition ? transition.label || `Transition ${id}` : `Transition ${id}`;
      updateVariableHistory(`After firing: ${label}`);
      
      return result;
    };
  }
  
  // Override startAutoRun to update variable display during autorun
  const originalStartAutoRun = app.startAutoRun;
  app.startAutoRun = function() {
    // Call original method
    const result = originalStartAutoRun.call(this);
    
    // Override the autorun interval to update variable display
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
        // Variable display updates are handled in stepSimulation
      }, this.autoRunDelay);
    }
    
    return result;
  };
  
  // Setup the history tracking buttons
  setupHistoryTracking();
  
  // Add styles for highlighting changes
  addVariableHistoryStyles();
  
  console.log('Data Petri Net Variable Tracking Extension loaded.');
}

/**
 * Updates the data values display
 */
function updateDataValuesDisplay() {
  const app = window.petriApp;
  if (!app || !window.dataPetriNetIntegration) return;
  
  if (window.dataPetriNetIntegration.dataPetriNetUI) {
    // Store previous values to highlight changes
    const previousValues = {};
    
    // Get current values from the table
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
    
    // Update the display (this will recreate the table)
    window.dataPetriNetIntegration.dataPetriNetUI.updateDataValuesDisplay();
    
    // Apply highlighting to changed values
    const newValuesTable = document.querySelector('.data-values-table');
    if (newValuesTable) {
      const rows = newValuesTable.querySelectorAll('tr');
      for (let i = 1; i < rows.length; i++) { // Skip header row
        const cells = rows[i].querySelectorAll('td');
        if (cells.length >= 2) {
          const name = cells[0].textContent.trim();
          const value = cells[1].textContent.trim();
          
          // Highlight changed values
          if (previousValues[name] !== undefined && previousValues[name] !== value) {
            cells[1].classList.add('data-variable-changed');
          }
        }
      }
    }
  }
}

// Variable history tracking state
let historyTracking = {
  enabled: false,
  entries: [],
  maxEntries: 100  // Maximum number of history entries to keep
};

/**
 * Setup the history tracking buttons
 */
function setupHistoryTracking() {
  // Get the existing buttons from HTML
  const toggleButton = document.getElementById('btn-toggle-history');
  const clearButton = document.getElementById('btn-clear-history');
  
  if (toggleButton) {
    toggleButton.addEventListener('click', toggleVariableHistoryTracking);
  }
  
  if (clearButton) {
    clearButton.addEventListener('click', clearVariableHistory);
  }
}

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
      // Add initial snapshot
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
      // Add new initial snapshot
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
  
  // Create timestamp and snapshot
  const timestamp = new Date();
  const snapshot = {
    label: label || `Step ${historyTracking.entries.length + 1}`,
    timestamp: timestamp,
    values: {}
  };
  
  // Collect current values
  for (const [id, variable] of app.api.petriNet.dataVariables) {
    snapshot.values[variable.name] = variable.currentValue;
  }
  
  // Check if values have changed from previous snapshot
  let valuesChanged = true;
  if (historyTracking.entries.length > 0) {
    const previousSnapshot = historyTracking.entries[historyTracking.entries.length - 1];
    valuesChanged = false;
    
    // Compare current values with previous values
    for (const [name, value] of Object.entries(snapshot.values)) {
      if (previousSnapshot.values[name] !== value) {
        valuesChanged = true;
        break;
      }
    }
  }
  
  // Only add the snapshot if values have changed or this is the first entry
  if (valuesChanged || historyTracking.entries.length === 0) {
    // Add the snapshot to history
    historyTracking.entries.push(snapshot);
    
    // Remove oldest entries if exceeding maximum
    if (historyTracking.entries.length > historyTracking.maxEntries) {
      historyTracking.entries.shift();
    }
    
    // Update the display
    updateVariableHistoryDisplay();
  }
}

/**
 * Update variable history when transitions are fired
 */
function updateVariableHistory(label) {
  if (!historyTracking.enabled) return;
  
  const app = window.petriApp;
  if (!app || !app.api || !app.api.petriNet || !app.api.petriNet.dataVariables) return;
  
  // Default label if none provided
  if (!label) {
    let transitionLabel = "Step";
    const enabledTransitions = app.api.getEnabledTransitions();
    if (enabledTransitions.length > 0) {
      const lastTransition = app.api.petriNet.transitions.get(enabledTransitions[0]);
      if (lastTransition) {
        transitionLabel = lastTransition.label || lastTransition.id;
      }
    }
    label = `After firing: ${transitionLabel}`;
  }
  
  // Add snapshot with the given label
  addVariableSnapshot(label);
}

/**
 * Update the variable history display
 */
function updateVariableHistoryDisplay() {
  const historyContent = document.getElementById('variable-history-content');
  if (!historyContent) return;
  
  // Start with empty HTML
  let html = '';
  
  if (historyTracking.entries.length === 0) {
    html = '<p>No history entries yet.</p>';
  } else {
    html = '<div class="history-entries">';
    
    // Display entries in reverse order (newest first)
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
      
      // Add each variable and its value
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
  // Check if styles are already added
  let styleElement = document.getElementById('variable-history-styles');
  if (!styleElement) {
    styleElement = document.createElement('style');
    styleElement.id = 'variable-history-styles';
    document.head.appendChild(styleElement);
  }
  
  // Add CSS styles
  styleElement.textContent = `
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