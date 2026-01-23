import { EventLogGenerator } from './event-log-generator.js';
import { PetriNet } from './petri-net-simulator.js';
import { DataPetriNet } from './extensions/dpn-model.js';

/**
 * Event Log Generator Integration
 * This module integrates the EventLogGenerator class with the Petri Net Editor
 * It adds UI elements for configuring and running simulations
 * Now supports Data Petri Nets with variable tracking
 */

class EventLogIntegration {
    constructor(app) {
      this.app = app;
      this.eventLog = [];
      this.dialog = null;
      this.table = null;
      this.eventLogGenerator = null;
      

      this.simulationOptions = {
        startTimestamp: new Date(),
        defaultTransitionDuration: 1000,
        timeUnit: 'minutes',
        timeScale: 1,
        caseArrivalRate: 10,
        arrivalDistribution: 'exponential',
        arrivalParams: {},
        transitionSelectionStrategy: 'priority',
        transitionWeights: {},
        caseName: 'Case',
        initialMarking: null,
        startPlaces: [],
        endPlaces: [],
        seed: null,
        numCases: 10,
        maxSteps: 100,
        eventLogFormat: 'lifecycle'
      };
      
      this.initialize();
    }
    
    initialize() {

      this.createUI();
      

      this.setupEventListeners();
    }
    
    createUI() {

      this.dialog = document.createElement('div');
      this.dialog.className = 'modal-overlay hidden';
      this.dialog.id = 'event-log-dialog';
      
      const dialogContent = `
        <div class="modal-container">
          <div class="modal-header">
            <h2>Event Log Generator</h2>
            <button class="close-btn" id="event-log-close">&times;</button>
          </div>
          <div class="modal-body">
            <div class="form-tab-container">
              <div class="form-tabs">
                <button class="form-tab active" data-tab="basic">Basic</button>
                <button class="form-tab" data-tab="timing">Timing</button>
                <button class="form-tab" data-tab="cases">Cases</button>
                <button class="form-tab" data-tab="advanced">Advanced</button>
              </div>
              
              <div class="form-tab-content active" data-tab="basic">
                <div class="form-group">
                  <label for="num-cases">Number of Cases</label>
                  <input type="number" id="num-cases" min="1" max="1000" value="10">
                </div>
                <div class="form-group">
                  <label for="max-steps">Max Steps per Case</label>
                  <input type="number" id="max-steps" min="1" max="1000" value="100">
                </div>
                <div class="form-group">
                  <label for="case-name">Case Name Prefix</label>
                  <input type="text" id="case-name" value="Case">
                </div>
                <div class="form-group">
                  <label for="transition-strategy">Transition Selection Strategy</label>
                  <select id="transition-strategy">
                    <option value="priority">Priority</option>
                    <option value="random">Random</option>
                    <option value="weighted">Weighted</option>
                  </select>
                </div>
                <div class="form-group">
                  <label for="event-log-format">Event Log Format</label>
                  <select id="event-log-format">
                    <option value="lifecycle">Lifecycle (Start/Complete events)</option>
                    <option value="classic">Classic (Single event with variable columns)</option>
                  </select>
                  <small class="form-hint">Lifecycle: XES format with start/complete events. Classic: One row per activity with variables as separate columns.</small>
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="timing">
                <div class="form-group">
                  <label for="time-unit">Time Unit</label>
                  <select id="time-unit">
                    <option value="seconds">Seconds</option>
                    <option value="minutes" selected>Minutes</option>
                    <option value="hours">Hours</option>
                    <option value="days">Days</option>
                  </select>
                </div>
                <div class="form-group">
                  <label for="time-scale">Time Scale Factor</label>
                  <input type="number" id="time-scale" min="0.1" step="0.1" value="1">
                </div>
                <div class="form-group">
                  <label for="transition-duration">Default Transition Duration (ms)</label>
                  <input type="number" id="transition-duration" min="1" value="1000">
                </div>
                <div class="form-group">
                  <label for="start-timestamp">Start Timestamp</label>
                  <input type="datetime-local" id="start-timestamp">
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="cases">
                <div class="form-group">
                  <label for="case-arrival-rate">Case Arrival Rate</label>
                  <input type="number" id="case-arrival-rate" min="0.1" step="0.1" value="10">
                </div>
                <div class="form-group">
                  <label for="arrival-distribution">Arrival Distribution</label>
                  <select id="arrival-distribution">
                    <option value="fixed">Fixed</option>
                    <option value="exponential" selected>Exponential</option>
                    <option value="normal">Normal</option>
                  </select>
                </div>
                <div class="form-group normal-params hidden">
                  <label for="stddev">Standard Deviation</label>
                  <input type="number" id="stddev" min="0.1" step="0.1" value="3">
                </div>
                <div class="form-group">
                  <label for="random-seed">Random Seed (leave empty for random)</label>
                  <input type="number" id="random-seed" min="1" step="1" placeholder="Random">
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="advanced">
                <div class="form-group">
                  <label for="start-places">Start Places (comma-separated IDs, leave empty for auto-detect)</label>
                  <input type="text" id="start-places" placeholder="Auto-detect">
                </div>
                <div class="form-group">
                  <label for="end-places">End Places (comma-separated IDs, leave empty for auto-detect)</label>
                  <input type="text" id="end-places" placeholder="Auto-detect">
                </div>
                <div class="form-group">
                  <label for="initial-marking">Initial Marking (JSON, leave empty for current marking)</label>
                  <textarea id="initial-marking" rows="4" placeholder='{"place1": 1, "place2": 0}'></textarea>
                </div>
              </div>
            </div>
          </div>
          <div class="modal-footer">
            <button class="btn" id="event-log-run">Run Simulation</button>
            <button class="btn" id="event-log-reset">Reset Options</button>
          </div>
        </div>
      `;
      
      this.dialog.innerHTML = dialogContent;
      document.body.appendChild(this.dialog);
      

      this.eventLogPanel = document.createElement('div');
      this.eventLogPanel.className = 'event-log-panel hidden';
      this.eventLogPanel.id = 'event-log-panel';
      
      const eventLogPanelContent = `
        <div class="event-log-header">
          <h3>Event Log</h3>
          <div class="event-log-controls">
            <button id="export-csv" title="Export as CSV">CSV</button>
            <button id="export-json" title="Export as JSON">JSON</button>
            <button id="export-xes" title="Export as XES">XES</button>
            <button id="close-event-log" title="Close">&times;</button>
          </div>
        </div>
        <div class="event-log-stats">
          <div id="event-log-stats-content"></div>
        </div>
        <div class="event-log-table-container">
          <table id="event-log-table">
            <thead>
              <tr>
                <th>Case</th>
                <th>Activity</th>
                <th>Timestamp</th>
                <th>Lifecycle</th>
                <th>Resource</th>
                <th>Data</th>
              </tr>
            </thead>
            <tbody id="event-log-table-body">
              <!-- Events will be added here -->
            </tbody>
          </table>
        </div>
      `;
      
      this.eventLogPanel.innerHTML = eventLogPanelContent;
      document.body.appendChild(this.eventLogPanel);
      

      const fileOperationsDiv = document.querySelector('.file-operations');
      if (fileOperationsDiv) {
        const eventLogButton = document.createElement('div');
        eventLogButton.className = 'toolbar-group';
        eventLogButton.innerHTML = `<button id="btn-event-log" class="blue">Generate Event Log</button>`;
        fileOperationsDiv.appendChild(eventLogButton);
      }
      

      const startTimestampInput = document.getElementById('start-timestamp');
      if (startTimestampInput) {
        const now = new Date();
        const year = now.getFullYear();
        const month = String(now.getMonth() + 1).padStart(2, '0');
        const day = String(now.getDate()).padStart(2, '0');
        const hours = String(now.getHours()).padStart(2, '0');
        const minutes = String(now.getMinutes()).padStart(2, '0');
        
        startTimestampInput.value = `${year}-${month}-${day}T${hours}:${minutes}`;
      }
    }
    
    setupEventListeners() {

      const openButton = document.getElementById('btn-event-log');
      if (openButton) {
        openButton.addEventListener('click', () => this.openDialog());
      }
      

      const closeButton = document.getElementById('event-log-close');
      if (closeButton) {
        closeButton.addEventListener('click', () => this.closeDialog());
      }
      

      const runButton = document.getElementById('event-log-run');
      if (runButton) {
        runButton.addEventListener('click', () => this.runSimulation());
      }
      

      const resetButton = document.getElementById('event-log-reset');
      if (resetButton) {
        resetButton.addEventListener('click', () => this.resetOptions());
      }
      

      const tabButtons = document.querySelectorAll('.form-tab');
      tabButtons.forEach(button => {
        button.addEventListener('click', (e) => {
          const tab = e.target.getAttribute('data-tab');
          this.switchTab(tab);
        });
      });
      

      const arrivalDistribution = document.getElementById('arrival-distribution');
      if (arrivalDistribution) {
        arrivalDistribution.addEventListener('change', (e) => {
          const normalParams = document.querySelector('.normal-params');
          if (normalParams) {
            normalParams.classList.toggle('hidden', e.target.value !== 'normal');
          }
        });
      }
      

      const exportCsvButton = document.getElementById('export-csv');
      if (exportCsvButton) {
        exportCsvButton.addEventListener('click', () => this.exportLog('csv'));
      }
      
      const exportJsonButton = document.getElementById('export-json');
      if (exportJsonButton) {
        exportJsonButton.addEventListener('click', () => this.exportLog('json'));
      }
      
      const exportXesButton = document.getElementById('export-xes');
      if (exportXesButton) {
        exportXesButton.addEventListener('click', () => this.exportLog('xes'));
      }
      

      const closeEventLogButton = document.getElementById('close-event-log');
      if (closeEventLogButton) {
        closeEventLogButton.addEventListener('click', () => this.closeEventLogPanel());
      }
    }
    
    openDialog() {
      this.dialog.classList.remove('hidden');
    }
    
    closeDialog() {
      this.dialog.classList.add('hidden');
    }
    
    switchTab(tabId) {

      const tabButtons = document.querySelectorAll('.form-tab');
      tabButtons.forEach(button => {
        button.classList.toggle('active', button.getAttribute('data-tab') === tabId);
      });
      

      const tabContents = document.querySelectorAll('.form-tab-content');
      tabContents.forEach(content => {
        content.classList.toggle('active', content.getAttribute('data-tab') === tabId);
      });
    }
    
    resetOptions() {

      document.getElementById('num-cases').value = 10;
      document.getElementById('max-steps').value = 100;
      document.getElementById('case-name').value = 'Case';
      document.getElementById('transition-strategy').value = 'priority';
      document.getElementById('event-log-format').value = 'lifecycle';
      document.getElementById('time-unit').value = 'minutes';
      document.getElementById('time-scale').value = 1;
      document.getElementById('transition-duration').value = 1000;
      document.getElementById('case-arrival-rate').value = 10;
      document.getElementById('arrival-distribution').value = 'exponential';
      document.getElementById('stddev').value = 3;
      document.getElementById('random-seed').value = '';
      document.getElementById('start-places').value = '';
      document.getElementById('end-places').value = '';
      document.getElementById('initial-marking').value = '';
      

      const normalParams = document.querySelector('.normal-params');
      if (normalParams) {
        normalParams.classList.add('hidden');
      }
      

      const startTimestampInput = document.getElementById('start-timestamp');
      if (startTimestampInput) {
        const now = new Date();
        const year = now.getFullYear();
        const month = String(now.getMonth() + 1).padStart(2, '0');
        const day = String(now.getDate()).padStart(2, '0');
        const hours = String(now.getHours()).padStart(2, '0');
        const minutes = String(now.getMinutes()).padStart(2, '0');
        
        startTimestampInput.value = `${year}-${month}-${day}T${hours}:${minutes}`;
      }
    }
    
    collectOptions() {

      const options = {
        numCases: parseInt(document.getElementById('num-cases').value, 10),
        maxSteps: parseInt(document.getElementById('max-steps').value, 10),
        caseName: document.getElementById('case-name').value,
        transitionSelectionStrategy: document.getElementById('transition-strategy').value,
        eventLogFormat: document.getElementById('event-log-format').value,
        timeUnit: document.getElementById('time-unit').value,
        timeScale: parseFloat(document.getElementById('time-scale').value),
        defaultTransitionDuration: parseInt(document.getElementById('transition-duration').value, 10),
        startTimestamp: new Date(document.getElementById('start-timestamp').value),
        caseArrivalRate: parseFloat(document.getElementById('case-arrival-rate').value),
        arrivalDistribution: document.getElementById('arrival-distribution').value,
        arrivalParams: {}
      };
      

      if (options.arrivalDistribution === 'normal') {
        options.arrivalParams.stddev = parseFloat(document.getElementById('stddev').value);
      }
      

      const seedInput = document.getElementById('random-seed').value;
      if (seedInput.trim() !== '') {
        options.seed = parseInt(seedInput, 10);
      } else {
        options.seed = null;
      }
      

      const startPlacesInput = document.getElementById('start-places').value;
      if (startPlacesInput.trim() !== '') {
        options.startPlaces = startPlacesInput.split(',').map(id => id.trim());
      } else {
        options.startPlaces = [];
      }
      
      const endPlacesInput = document.getElementById('end-places').value;
      if (endPlacesInput.trim() !== '') {
        options.endPlaces = endPlacesInput.split(',').map(id => id.trim());
      } else {
        options.endPlaces = [];
      }
      

      const initialMarkingInput = document.getElementById('initial-marking').value;
      if (initialMarkingInput.trim() !== '') {
        try {
          options.initialMarking = JSON.parse(initialMarkingInput);
        } catch (error) {
          alert('Invalid JSON for initial marking. Using current marking instead.');
          options.initialMarking = null;
        }
      } else {
        options.initialMarking = null;
      }
      
      return options;
    }
    
    async runSimulation() {
      try {
        // Collect options from UI
        const options = this.collectOptions();
        this.simulationOptions = { ...this.simulationOptions, ...options };
        
        // Get the Petri Net (now with potential DPN support)
        const petriNetJson = this.app.api.exportAsJSON();
        
        // Try to parse as DataPetriNet first, fall back to regular PetriNet
        let petriNet;
        try {
          const jsonData = JSON.parse(petriNetJson);
          if (jsonData.dataVariables && jsonData.dataVariables.length > 0) {
            petriNet = DataPetriNet.fromJSON(petriNetJson);
          } else {
            petriNet = PetriNet.fromJSON(petriNetJson);
          }
        } catch (e) {
          petriNet = PetriNet.fromJSON(petriNetJson);
        }
        
        if (!petriNet) {
          throw new Error('Petri Net is not defined or invalid');
        }
        const res = this.validatePetriNet(petriNet);          
        if (res.error !== null) {
          throw new Error(res.error);
        }

        this.eventLogGenerator = new EventLogGenerator(petriNet, this.simulationOptions);
        
        // Run simulation (now async for DPN support)
        this.eventLog = await this.eventLogGenerator.simulateCases(
          this.simulationOptions.numCases,
          this.simulationOptions.maxSteps
        );
        
        // Close dialog
        this.closeDialog();
        
        // Display results
        this.displayEventLog();
      } catch (error) {
        console.error('Error running simulation:', error);
        alert('An error occurred while running the simulation: ' + error.message);
      }
    }
        /**
     * Validates the Petri net to ensure it's suitable for simulation
     * @private
     * @returns {Object} error - Error message if validation fails
    */
    validatePetriNet(petriNet) {

      if (petriNet.places.size === 0 || petriNet.transitions.size === 0) {
        return { error: 'Petri net must have at least one place and one transition' };
      }

      let has_atleast_one_marking =  false;
      petriNet.places.forEach(place => {
        if (place.tokens > 0) {
          has_atleast_one_marking = true;
        }
      });

      if (this.simulationOptions.initialMarking === null && !has_atleast_one_marking ) {
        return { error: 'Petri net must have at least one place with initial tokens or an initial marking' };
      }

      return { error: null };
    }
    
    displayEventLog() {
      if (!this.eventLog || this.eventLog.length === 0) {
        alert('No events were generated. Please check your Petri net and simulation settings.');
        return;
      }
      

      this.eventLogPanel.classList.remove('hidden');
      

      this.displayStatistics();
      
      // Determine the format and set up table headers accordingly
      const isClassicFormat = this.simulationOptions.eventLogFormat === 'classic';
      
      // Get table header and body
      const tableHead = document.querySelector('#event-log-table thead tr');
      const tableBody = document.getElementById('event-log-table-body');
      
      // Clear existing content
      tableBody.innerHTML = '';
      
      if (isClassicFormat) {
        // For classic format, dynamically create columns based on all keys in the log
        const allKeys = new Set();
        this.eventLog.forEach(event => {
          Object.keys(event).forEach(key => allKeys.add(key));
        });
        
        // Order: case:concept:name, concept:name, time:timestamp, then variables alphabetically
        const standardKeys = ['case:concept:name', 'concept:name', 'time:timestamp'];
        const variableKeys = Array.from(allKeys).filter(k => !standardKeys.includes(k)).sort();
        const orderedKeys = [...standardKeys, ...variableKeys];
        
        // Update table header
        tableHead.innerHTML = orderedKeys.map(key => {
          // Make headers more readable
          let displayName = key;
          if (key === 'case:concept:name') displayName = 'Case';
          else if (key === 'concept:name') displayName = 'Activity';
          else if (key === 'time:timestamp') displayName = 'Timestamp';
          return `<th>${displayName}</th>`;
        }).join('');
        
        // Add rows (limit to 250)
        const eventsToShow = this.eventLog.slice(0, 250);
        eventsToShow.forEach(event => {
          const row = document.createElement('tr');
          row.innerHTML = orderedKeys.map(key => {
            let value = event[key];
            
            // Format timestamp
            if (key === 'time:timestamp' && value) {
              try {
                const date = new Date(value);
                value = `${date.toLocaleDateString()} ${date.toLocaleTimeString()}`;
              } catch (e) { /* keep original */ }
            }
            
            // Handle undefined/null/empty
            if (value === undefined || value === null || value === '') {
              return '<td></td>';
            }
            
            return `<td>${value}</td>`;
          }).join('');
          tableBody.appendChild(row);
        });
      } else {
        // Lifecycle format - use original column structure
        tableHead.innerHTML = `
          <th>Case</th>
          <th>Activity</th>
          <th>Timestamp</th>
          <th>Lifecycle</th>
          <th>Resource</th>
          <th>Data</th>
        `;
        
        // Add rows (limit to 250)
        const eventsToShow = this.eventLog.slice(0, 250);
        eventsToShow.forEach(event => {
          const row = document.createElement('tr');
          
          const caseId = event['case:concept:name'] || '';
          const activity = event['concept:name'] || '';
          const timestamp = event['time:timestamp'] || '';
          const lifecycle = event['lifecycle:transition'] || '';
          const resource = event['org:resource'] || '';
          
          // Collect data fields
          const dataFields = {};
          for (const [key, value] of Object.entries(event)) {
            if (!['case:concept:name', 'concept:name', 'time:timestamp', 'lifecycle:transition', 'org:resource'].includes(key)) {
              dataFields[key] = value;
            }
          }
          
          // Format timestamp
          let formattedTimestamp = timestamp;
          try {
            const date = new Date(timestamp);
            formattedTimestamp = `${date.toLocaleDateString()} ${date.toLocaleTimeString()}`;
          } catch (e) { /* keep original */ }
          
          row.innerHTML = `
            <td>${caseId}</td>
            <td>${activity}</td>
            <td>${formattedTimestamp}</td>
            <td>${lifecycle}</td>
            <td>${resource}</td>
            <td>${Object.keys(dataFields).length > 0 ? JSON.stringify(dataFields) : ''}</td>
          `;
          
          tableBody.appendChild(row);
        });
      }
      
      // Show message if truncated
      if (this.eventLog.length > 250) {
        const message = document.createElement('tr');
        const colspan = isClassicFormat ? 
          document.querySelectorAll('#event-log-table thead th').length : 6;
        message.innerHTML = `<td colspan="${colspan}" class="message">Showing 250 of ${this.eventLog.length} events. Export to see all events.</td>`;
        tableBody.appendChild(message);
      }
    }
    
    displayStatistics() {
      if (!this.eventLogGenerator) return;
      
      const stats = this.eventLogGenerator.getStatistics();
      const statsContainer = document.getElementById('event-log-stats-content');
      

      const formatDuration = (ms) => {
        if (isNaN(ms)) return 'N/A';
        
        const seconds = Math.floor(ms / 1000);
        const minutes = Math.floor(seconds / 60);
        const hours = Math.floor(minutes / 60);
        
        if (hours > 0) {
          return `${hours}h ${minutes % 60}m ${seconds % 60}s`;
        } else if (minutes > 0) {
          return `${minutes}m ${seconds % 60}s`;
        } else {
          return `${seconds}s ${ms % 1000}ms`;
        }
      };
      

      let html = `
        <div class="stats-grid">
          <div class="stat-item">
            <div class="stat-label">Total Cases</div>
            <div class="stat-value">${stats.totalCases}</div>
          </div>
          <div class="stat-item">
            <div class="stat-label">Total Events</div>
            <div class="stat-value">${stats.totalEvents}</div>
          </div>
          <div class="stat-item">
            <div class="stat-label">Avg. Case Duration</div>
            <div class="stat-value">${formatDuration(stats.avgCaseDuration)}</div>
          </div>
          <div class="stat-item">
            <div class="stat-label">Min Duration</div>
            <div class="stat-value">${formatDuration(stats.minDuration)}</div>
          </div>
          <div class="stat-item">
            <div class="stat-label">Max Duration</div>
            <div class="stat-value">${formatDuration(stats.maxDuration)}</div>
          </div>
          <div class="stat-item">
            <div class="stat-label">Avg. Events per Case</div>
            <div class="stat-value">${stats.avgCaseLength.toFixed(1)}</div>
          </div>
        </div>
        
        <div class="stats-section">
          <h4>Activity Frequency</h4>
          <div class="activity-chart">
      `;
      

      const activities = Object.entries(stats.activityFrequency)
        .filter(([name]) => !name.startsWith('Case_')) // Filter out case start/end events
        .sort((a, b) => b[1] - a[1]); // Sort by frequency
      

      const maxFrequency = activities.length > 0 ? activities[0][1] : 0;
      
      activities.forEach(([name, count]) => {
        const percentage = maxFrequency > 0 ? (count / maxFrequency) * 100 : 0;
        html += `
          <div class="activity-item">
            <div class="activity-name" title="${name}">${name}</div>
            <div class="activity-bar">
              <div class="activity-bar-fill" style="width: ${percentage}%"></div>
            </div>
            <div class="activity-count">${count}</div>
          </div>
        `;
      });
      
      html += `
          </div>
        </div>
      `;
      
      statsContainer.innerHTML = html;
    }
    
    exportLog(format) {
      if (!this.eventLogGenerator || !this.eventLog || this.eventLog.length === 0) {
        alert('No event log data to export.');
        return;
      }
      
      let data, fileName, mimeType;
      
      switch (format) {
        case 'csv':
          data = this.eventLogGenerator.exportToCSV();
          fileName = 'event_log.csv';
          mimeType = 'text/csv';
          break;
        case 'json':
          data = this.eventLogGenerator.exportToJSON();
          fileName = 'event_log.json';
          mimeType = 'application/json';
          break;
        case 'xes':
          data = this.eventLogGenerator.exportToXES();
          fileName = 'event_log.xes';
          mimeType = 'application/xml';
          break;
        default:
          alert('Unsupported export format.');
          return;
      }
      

      const blob = new Blob([data], { type: mimeType });
      const url = URL.createObjectURL(blob);
      
      const a = document.createElement('a');
      a.href = url;
      a.download = fileName;
      a.click();
      
      URL.revokeObjectURL(url);
    }
    
    closeEventLogPanel() {
      this.eventLogPanel.classList.add('hidden');
    }
  }
  

  document.addEventListener('DOMContentLoaded', () => {

    const initEventLogTimer = setInterval(() => {
      if (window.petriApp) {
        window.eventLogIntegration = new EventLogIntegration(window.petriApp);
        clearInterval(initEventLogTimer);
      }
    }, 100);
  });


  export { EventLogIntegration };