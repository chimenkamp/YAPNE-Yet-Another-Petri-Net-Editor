# Petri Net Editor

A web-based editor and simulator for Petri nets with features for creating, editing, simulating, and analyzing Petri net models.

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

### Web Application
Front-end components that use the library:

- `app.js` - Main application logic and UI integration
- `index.html` - Application structure and UI layout
- `event-log-generator.js` - Module for generating event logs from Petri net simulations
- `event-log-integration.js` - UI integration for the event log generator

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

1. Include the Petri net library in your HTML:
```html
<script src="src/petri-net-simulator.js"></script>
```

2. Initialize the application:
```javascript
const app = new PetriNetApp();
```

3. Use the UI to create and simulate Petri nets, or programmatically interact with the API.