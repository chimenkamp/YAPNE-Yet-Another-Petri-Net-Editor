# YAPNE - Yet Another Petri Net Editor

⚠️ **Warning:** This software is in early development and may contain bugs. Use with caution and report any issues you encounter.

A web-based, dependency-free, editor and simulator for Petri nets and data Petri nets with features for creating, editing, simulating, and analyzing Petri net models.

Inspired by [I ❤ Petri Nets](https://www.fernuni-hagen.de/ilovepetrinets/fapra/wise23/rot/index.html)

## Description

This project provides a complete solution for working with Petri nets, including a reusable JavaScript library for Petri net operations and a web-based user interface. The editor supports visual editing, simulation, and analysis of Petri nets, as well as event log generation for process mining.

## Functionalities

### Core Features
- Create and edit Petri nets with places, transitions, and arcs
- Support for different arc types (regular, inhibitor, reset, read)
- Assign tokens, weights, and other properties to Petri net elements
- Pan and zoom navigation
- Snap-to-grid functionality
- Automatic layout of Petri net elements

### Simulation
- Step-by-step simulation of Petri net execution
- Automatic simulation with priorities and delays
- Visual indication of enabled transitions
- Tokens display and tracking

### Data Petri Net Extension
- Support for data variables with different types (number, string, boolean)
- Data-aware transitions with preconditions (guards) and postconditions (updates)
- Variable tracking and history during simulation
- Visual indicators for data transitions
- Expression validation

### Analysis and Export
- Export to JSON and PNML formats
- Import from JSON format
- Event log generation for process mining
- Configuration options for event log simulation
- Export event logs in CSV, JSON, and XES formats

### User Interface
- Properties panel for editing element attributes
- Template library for common Petri net patterns
- File operations (save, load, export)
- Fullscreen mode
- Customizable simulation parameters

## Project Structure

The project is structured in two main parts:

### Petri Net Library (`petri-net-simulator.js`)
A standalone JavaScript library that provides the core functionality for Petri nets:

- Core classes for Petri net elements (Place, Transition, Arc)
- PetriNet class for the model
- PetriNetRenderer for visualization
- PetriNetEditor for user interaction
- PetriNetAPI for high-level operations

### Extensions Architecture
The application supports extensions that can enhance the core functionality:

#### Data Petri Net Extension
Located in the `src/extensions/` directory:
- `dpn-model.js` - Data variables and data-aware transitions
- `dpn-api.js` - Extended API for data Petri nets
- `dpn-renderer.js` - Custom rendering for data transitions
- `dpn-ui.js` - UI components for data variables management
- `dpn-integration.js` - Main integration module
- `variable-tracking.js` - Variable history tracking

### Web Application
Front-end components that use the library:

- `app.js` - Main application logic and UI integration
- `index.html` - Application structure and UI layout
- `event-log-generator.js` - Module for generating event logs from Petri net simulations
- `event-log-integration.js` - UI integration for the event log generator

## Extension Integration

### Integrating Extensions

Extensions are integrated into the main application using a modular approach:

1. **Include Extension Scripts**: Add extension scripts in the HTML file after the core library
   ```html
   <!-- Core library -->
   <script src="src/petri-net-simulator.js"></script>
   
   <!-- Extensions -->
   <script src="src/extensions/dpn-model.js"></script>
   <script src="src/extensions/dpn-api.js"></script>
   <script src="src/extensions/dpn-renderer.js"></script>
   <script src="src/extensions/dpn-ui.js"></script>
   <script src="src/extensions/dpn-integration.js"></script>
   ```

2. **Integration Pattern**: Each extension has an integration module that handles:
   - Extending the core API class with new functionality
   - Replacing or extending rendering functionality
   - Adding new UI components
   - Preserving compatibility with the core application

3. **Initialization**: Extensions are initialized after the main application loads
   ```javascript
   document.addEventListener('DOMContentLoaded', () => {
     // Wait for the main application to initialize
     const initTimer = setInterval(() => {
       if (window.petriApp) {
         window.dataPetriNetIntegration = new DataPetriNetIntegration(window.petriApp);
         clearInterval(initTimer);
       }
     }, 100);
   });
   ```

### Creating New Extensions

To create a new extension:

1. Create JavaScript files for your extension components
2. Extend the appropriate core classes (API, Renderer, Editor)
3. Create an integration module that:
   - Injects styles if needed
   - Extends the API with new functionality
   - Extends or replaces the renderer if needed
   - Initializes UI components
   - Extends application event handlers
4. Include your extension scripts in the HTML after the core library
5. Initialize your extension after the main application loads

## API Reference

### PetriNetAPI

The main interface for working with Petri nets.

#### Initialization
```javascript
// Create a new Petri net
const api = new PetriNetAPI();

// Attach to a canvas element
const editor = api.attachEditor(canvasElement);
```

#### Petri Net Structure
```javascript
// Add elements
const placeId = api.createPlace(x, y, label, tokens);
const transitionId = api.createTransition(x, y, label);
const arcId = api.createArc(sourceId, targetId, weight, type);

// Remove elements
api.removeElement(id);

// Modify elements
api.setLabel(id, label);
api.setPosition(id, x, y);
api.setPlaceTokens(id, tokens);
api.setArcWeight(id, weight);
api.setArcType(id, type);
```

#### Simulation
```javascript
// Check and fire transitions
const enabledTransitions = api.getEnabledTransitions();
api.fireTransition(id);
api.autoFireEnabledTransitions(maxSteps);
```

#### Analysis
```javascript
// Detect deadlocks
const deadlocks = api.detectDeadlocks();
```

#### Layout
```javascript
// Auto-layout the Petri net
api.autoLayout({
  horizontalSpacing: 150,
  verticalSpacing: 100,
  direction: 'horizontal'
});
```

#### Import/Export
```javascript
// Export as JSON
const json = api.exportAsJSON();

// Import from JSON
const newApi = PetriNetAPI.importFromJSON(json);

// Export as PNML
const pnml = api.exportAsPNML();
```

### DataPetriNetAPI (Extension)

Extended API for working with Data Petri Nets.

```javascript
// Create a new Data Petri Net
const api = new DataPetriNetAPI();

// Data variables
const varId = api.createDataVariable('counter', 'number', 0, 'Counter variable');
api.updateDataVariableValue(varId, 10);
const variables = api.getDataVariables();

// Data transitions
const transId = api.createDataTransition(x, y, 'Process', 'counter > 0', 'counter\' = counter - 1;');
api.setTransitionPrecondition(transId, 'counter >= 5');
api.setTransitionPostcondition(transId, 'counter\' = counter - 1; status\' = "processed";');

// Validation
const result = api.validatePrecondition('counter > 0', ['counter', 'status']);
```

### PetriNetEditor

Handles user interaction with the Petri net.

```javascript
// Set editing mode
editor.setMode('select'); // 'select', 'addPlace', 'addTransition', 'addArc'

// Selection
editor.selectElement(id, type);
editor.deleteSelected();

// View control
editor.resetView();
editor.setSnapToGrid(enabled, gridSize);

// Event callbacks
editor.setOnChangeCallback(callback);
editor.setOnSelectCallback(callback);
```

### EventLogGenerator

Generates event logs from Petri net simulations.

```javascript
// Create a generator with options
const generator = new EventLogGenerator(petriNet, {
  startTimestamp: new Date(),
  timeUnit: 'minutes',
  caseArrivalRate: 10,
  arrivalDistribution: 'exponential',
  caseName: 'Case'
});

// Run simulation
const eventLog = generator.simulateCases(numCases, maxSteps);

// Export results
const csv = generator.exportToCSV();
const json = generator.exportToJSON();
const xes = generator.exportToXES();
```

## Usage

1. Include the Petri net library and extensions in your HTML:
```html
<script src="src/petri-net-simulator.js"></script>
<script src="src/extensions/dpn-model.js"></script>
<script src="src/extensions/dpn-api.js"></script>
<script src="src/extensions/dpn-renderer.js"></script>
<script src="src/extensions/dpn-ui.js"></script>
<script src="src/extensions/dpn-integration.js"></script>
```

2. Initialize the application:
```javascript
const app = new PetriNetApp();
```

3. Use the UI to create and simulate Petri nets, or programmatically interact with the API.
