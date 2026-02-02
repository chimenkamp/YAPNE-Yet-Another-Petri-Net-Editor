# WebPPL Integration Design Document

## Probabilistic Programming for Data Petri Nets in YAPNE

This document describes the implementation of probabilistic programming capabilities in YAPNE, following the formal translation from **"Data Petri Nets Meet Probabilistic Programming"** (Kuhn et al., BPM 2024).

---

## Table of Contents

1. [Overview](#1-overview)
2. [Architecture](#2-architecture)
3. [Module Descriptions](#3-module-descriptions)
4. [Translation Algorithm (Csim)](#4-translation-algorithm-csim)
5. [Data Flow](#5-data-flow)
6. [Integration Points](#6-integration-points)
7. [What is Sent to WebPPL](#7-what-is-sent-to-webppl)
8. [What is Returned](#8-what-is-returned)
9. [Usage Examples](#9-usage-examples)

---

## 1. Overview

### Purpose

The implementation enables YAPNE to:
1. **Generate executable WebPPL code** from Data Petri Nets (DPNs)
2. **Execute probabilistic simulations** following formal DPN semantics
3. **Produce event logs** with correct probability distributions

### Paper Reference

The implementation follows the **Csim translation** from Section 5 of the paper:

```
Csim: Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
```

Where:
- **Cinit**: Initializes marking M and valuation α
- **Benabled(t)**: Checks if transition t is enabled (tokens + guard)
- **Cfire(t)**: Fires transition t (token movement + variable sampling + observe postcondition)
- **isGoal**: Boolean formula for goal states G (defined by `finalMarking`)

### Key Paper Definitions Used

| Definition | Description | Implementation Location |
|------------|-------------|-------------------------|
| **Def. 1** | DPN = (P, T, F, l, A, V, Δ, pre, post) | `webppl-code-generator.js:normalizeNet()` |
| **Def. 2** | Transition Enabling | `webppl-code-generator.js:generateEnablingFunctions()` |
| **Def. 3** | Scheduler S = (ST, SV) | `webppl-code-generator.js:generateScheduler()` |
| **Def. 6** | Run Probability P_S^N(ρ) | Event log statistical analysis |
| **Fig. 5** | Csim structure | `webppl-code-generator.js:generateMainLoop()` |
| **Thm. 1** | Correctness guarantee | Proven by following the translation exactly |

---

## 2. Architecture

### Module Dependency Graph

```
┌─────────────────────────────────────────────────────────────────────┐
│                         User Interface                               │
│  ┌─────────────────┐  ┌────────────────────┐  ┌─────────────────┐   │
│  │ Simulation      │  │ Event Log          │  │ WebPPL Code     │   │
│  │ Controls        │  │ Generator Dialog   │  │ Viewer Dialog   │   │
│  └────────┬────────┘  └────────┬───────────┘  └────────┬────────┘   │
└───────────┼─────────────────────┼───────────────────────┼───────────┘
            │                     │                       │
            ▼                     ▼                       ▼
┌───────────────────────────────────────────────────────────────────────┐
│                probabilistic-integration.js                           │
│  ┌────────────────────────────────────────────────────────────────┐  │
│  │ ProbabilisticExecutionIntegration                              │  │
│  │  - Extends PetriNetApp with probabilistic methods              │  │
│  │  - Sets up UI button handlers                                  │  │
│  │  - Bridges app ↔ engine                                        │  │
│  └────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────┬─────────────────────────────────────────┘
                              │
            ┌─────────────────┴─────────────────┐
            ▼                                   ▼
┌────────────────────────────────┐   ┌──────────────────────────────────┐
│  probabilistic-execution.js    │   │ probabilistic-event-log-        │
│                                │   │ generator.js                     │
│  ProbabilisticExecutionEngine  │   │                                  │
│  ┌──────────────────────────┐  │   │ ProbabilisticEventLogGenerator  │
│  │ - Dual mode: native/     │  │   │ ┌──────────────────────────────┐│
│  │   webppl                 │  │   │ │ - Generate N traces          ││
│  │ - Step simulation        │  │   │ │ - XES/CSV export             ││
│  │ - Full simulation        │  │   │ │ - Uses engine for each case  ││
│  │ - Goal state detection   │  │   │ └──────────────────────────────┘│
│  └────────────┬─────────────┘  │   └────────────────┬─────────────────┘
└───────────────┼────────────────┘                    │
                │                                     │
                ▼                                     │
┌────────────────────────────────┐                    │
│  webppl-code-generator.js      │◄───────────────────┘
│                                │
│  WebPPLCodeGenerator           │
│  ┌──────────────────────────┐  │
│  │ Csim Translation:        │  │
│  │  - generateInitialization│  │
│  │  - generateGoalStateCheck│  │
│  │  - generateEnablingFuncs │  │
│  │  - generateFiringFuncs   │  │
│  │  - generateScheduler     │  │
│  │  - generateMainLoop      │  │
│  └──────────────────────────┘  │
└────────────────┬───────────────┘
                 │
                 ▼
        ┌────────────────┐
        │  WebPPL npm    │
        │  package       │
        │  (runtime)     │
        └────────────────┘
```

---

## 3. Module Descriptions

### 3.1 `webppl-code-generator.js`

**Purpose**: Generates WebPPL code from a DPN following the paper's formal Csim translation.

**Key Class**: `WebPPLCodeGenerator`

```javascript
class WebPPLCodeGenerator {
    constructor(options = {}) {
        this.schedulerType = options.schedulerType ?? 'uniform';
        this.transitionWeights = options.transitionWeights ?? {};
        this.variableDistributions = options.variableDistributions ?? {};
        this.maxSteps = options.maxSteps ?? 10000;
    }
    
    generateCode(net, options = {}) → string  // Main entry point
}
```

**Code Generation Methods**:

| Method | Paper Reference | Description |
|--------|-----------------|-------------|
| `generateHeader()` | Metadata | Comments with DPN statistics |
| `generateInitialization()` | Cinit (§5.2) | Initial marking M₀ and valuation α₀ |
| `generateGoalStateCheck()` | isGoal (§5.1) | Goal state formula from finalMarking |
| `generateEnablingFunctions()` | Benabled(t) (Def. 2) | Token check + precondition guard |
| `generateFiringFunctions()` | Cfire(t) (§5.2) | Token movement + variable sampling + observe |
| `generateScheduler()` | ST (Def. 3) | Transition selection distribution |
| `generateMainLoop()` | Cloop (Fig. 5) | Recursive simulation loop |

---

### 3.2 `probabilistic-execution.js`

**Purpose**: Execution engine that provides both native JavaScript and WebPPL-based simulation.

**Key Class**: `ProbabilisticExecutionEngine`

```javascript
class ProbabilisticExecutionEngine {
    constructor(options = {}) {
        this.executionMode = options.executionMode ?? 'auto';  // 'native' | 'webppl' | 'auto'
        this.scheduler = options.scheduler ?? 'uniform';
        this.codeGenerator = new WebPPLCodeGenerator({...});
    }
}
```

**Execution Modes**:

| Mode | When Used | Characteristics |
|------|-----------|-----------------|
| **Native** | Simple nets without constraint postconditions | Fast, step-by-step UI updates |
| **WebPPL** | DPNs with constraint postconditions (e.g., `x' > 10`) | Accurate sampling via `observe` |
| **Auto** | Default | Analyzes net, picks best mode |

**Key Methods**:

```javascript
// Single step (always native for UI responsiveness)
async step(net) → { fired, transitionId, status }

// Full simulation 
async runFullSimulation(net, options) → { status, trace, finalState }

// WebPPL-specific simulation
async runWebPPLSimulation(net, options) → { status, trace, finalState }

// Code generation
generateWebPPLCode(net, options) → string

// Check if WebPPL is needed
netRequiresWebPPL(net) → boolean
```

---

### 3.3 `probabilistic-event-log-generator.js`

**Purpose**: Generates N probabilistic traces for event log analysis.

**Key Class**: `ProbabilisticEventLogGenerator`

```javascript
class ProbabilisticEventLogGenerator {
    constructor(petriNet, options = {}) {
        this.engine = new ProbabilisticExecutionEngine({...});
        this.codeGenerator = new WebPPLCodeGenerator({...});
    }
    
    async generateEventLog(numberOfCases, options) → eventLog[]
}
```

**Features**:
- Generates independent runs using different seeds
- Supports XES and CSV export formats
- Can use WebPPL mode for batch generation
- Tracks variable values in events

---

### 3.4 `probabilistic-integration.js`

**Purpose**: Integrates the probabilistic engine with the PetriNetApp and UI.

**Key Class**: `ProbabilisticExecutionIntegration`

**Methods Added to `app`**:

```javascript
app.stepSimulation()           // Probabilistic step using scheduler ST
app.stepSimulationProbabilistic()  // Explicit PP step
app.runFullSimulationProbabilistic()  // Full playout to goal
app.generateWebPPLCode(options)  // Get generated code
app.showWebPPLCodeDialog()       // Display code in modal
app.recommendsWebPPLMode()       // Check if WebPPL is recommended
```

---

## 4. Translation Algorithm (Csim)

### 4.1 Overall Structure

The Csim program follows Figure 5 from the paper:

```
Csim: Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
```

### 4.2 Generated Code Structure

```javascript
// ═══════════════════════════════════════════════════════════════════
// [Section 5.2] Cinit - Initialization
// ═══════════════════════════════════════════════════════════════════
var initialState = {
    marking: { p1: 1, p2: 0, p3: 0 },  // M₀
    valuation: { x: 0, y: 0 }          // α₀
};
var finalMarkingSpec = { p3: 1 };       // Goal places
var maxSteps = 10000;

// ═══════════════════════════════════════════════════════════════════
// [Section 5.1] isGoal - Goal state check
// ═══════════════════════════════════════════════════════════════════
var isGoalState = function(state) {
    return state.marking['p3'] >= 1;
};

// ═══════════════════════════════════════════════════════════════════
// [Definition 2] Benabled(t) - Transition enabling
// ═══════════════════════════════════════════════════════════════════
var isTransitionEnabled = function(state, transitionId) {
    if (transitionId === 't1') {
        var tokenCheck = state.marking['p1'] >= 1;
        var guardCheck = state.valuation['x'] < 10;  // precondition
        return tokenCheck && guardCheck;
    }
    // ... more transitions
};

var getEnabledTransitions = function(state) {
    var enabled = [];
    if (isTransitionEnabled(state, 't1')) { enabled.push('t1'); }
    // ... more transitions
    return enabled;
};

// ═══════════════════════════════════════════════════════════════════
// [Section 5.2] Cfire(t) - Transition firing
// ═══════════════════════════════════════════════════════════════════
var fire_t1 = function(state) {
    // For constraint postconditions: sample + observe
    var sampledValues = {
        'x': sample(uniform(0, 100))  // SV scheduler
    };
    observe(sampledValues['x'] > state.valuation['x']);  // postcondition constraint
    
    return {
        marking: {
            'p1': state.marking['p1'] - 1,  // Remove from preset
            'p2': state.marking['p2'] + 1   // Add to postset
        },
        valuation: {
            'x': sampledValues['x']  // Update valuation
        }
    };
};

var fireTransition = function(state, transitionId) {
    if (transitionId === 't1') { return fire_t1(state); }
    // ... dispatch to other transitions
    return state;
};

// ═══════════════════════════════════════════════════════════════════
// [Definition 3] Scheduler ST - Transition selection
// ═══════════════════════════════════════════════════════════════════
var selectTransition = function(enabledTransitions) {
    if (enabledTransitions.length === 0) return null;
    return uniformDraw(enabledTransitions);  // Uniform scheduler
};

// ═══════════════════════════════════════════════════════════════════
// [Figure 5] Main simulation loop - Cloop
// ═══════════════════════════════════════════════════════════════════
var simulationStep = function(state, trace, stepCount) {
    if (isGoalState(state)) {
        return { state: state, trace: trace, status: 'goal', steps: stepCount };
    }
    
    if (stepCount >= maxSteps) {
        return { state: state, trace: trace, status: 'max_steps', steps: stepCount };
    }
    
    var enabledTransitions = getEnabledTransitions(state);
    
    if (enabledTransitions.length === 0) {
        return { state: state, trace: trace, status: 'deadlock', steps: stepCount };
    }
    
    var chosenTransition = selectTransition(enabledTransitions);
    var newState = fireTransition(state, chosenTransition);
    var newTrace = trace.concat([chosenTransition]);
    
    return simulationStep(newState, newTrace, stepCount + 1);
};

var simulateDPN = function() {
    return simulationStep(initialState, [], 0);
};

simulateDPN()
```

---

## 5. Data Flow

### 5.1 Step Simulation Flow

```
User clicks "Step"
       │
       ▼
┌──────────────────────┐
│ app.stepSimulation() │
└──────────┬───────────┘
           │
           ▼
┌──────────────────────────────────┐
│ ProbabilisticExecutionEngine     │
│        .stepNative(net)          │
│  ┌────────────────────────────┐  │
│  │ 1. checkGoalState(net)     │  │
│  │ 2. getEnabledTransitions() │  │
│  │ 3. selectTransition()      │  │  ← Uses scheduler ST (uniform)
│  │ 4. net.fireTransition()    │  │
│  └────────────────────────────┘  │
└──────────────────┬───────────────┘
                   │
                   ▼
            ┌──────────────┐
            │ Update UI    │
            │ - Render net │
            │ - Show tokens│
            │ - Log fired  │
            └──────────────┘
```

### 5.2 Full Simulation Flow (WebPPL Mode)

```
User clicks "Run Full Simulation"
       │
       ▼
┌───────────────────────────────────────┐
│ app.runFullSimulationProbabilistic()  │
└──────────────────┬────────────────────┘
                   │
                   ▼
┌──────────────────────────────────────────────────────────┐
│ ProbabilisticExecutionEngine.runFullSimulation(net)      │
│  ┌────────────────────────────────────────────────────┐  │
│  │ determineExecutionMode() → 'webppl' if constraints │  │
│  └────────────────────────────────────────────────────┘  │
└──────────────────┬───────────────────────────────────────┘
                   │
    ┌──────────────┴──────────────┐
    │ mode === 'webppl'           │
    ▼                             ▼
┌────────────────────┐    ┌─────────────────────┐
│ runWebPPLSimulation│    │ runNativeSimulation │
└─────────┬──────────┘    └─────────────────────┘
          │
          ▼
┌─────────────────────────────────────┐
│ 1. generateWebPPLCode(net)          │
│    ↓                                │
│    WebPPLCodeGenerator.generateCode │
│    ↓                                │
│    Returns: string (WebPPL program) │
└─────────────────┬───────────────────┘
                  │
                  ▼
┌─────────────────────────────────────┐
│ 2. webppl.run(code, callback)       │  ← WebPPL npm package
│    ↓                                │
│    Executes probabilistic inference │
│    ↓                                │
│    Returns: { state, trace, status }│
└─────────────────┬───────────────────┘
                  │
                  ▼
┌─────────────────────────────────────┐
│ 3. applyStateToNet(net, result)     │
│    - Update tokens                  │
│    - Update data variables          │
│    - Refresh enabled transitions    │
└─────────────────────────────────────┘
```

### 5.3 Event Log Generation Flow

```
User configures event log options
       │
       ▼
┌─────────────────────────────────────────────┐
│ ProbabilisticEventLogGenerator              │
│   .generateEventLog(numberOfCases, options) │
└──────────────────┬──────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────┐
│ For each case i = 1 to N:                   │
│  ┌───────────────────────────────────────┐  │
│  │ 1. Clone net                          │  │
│  │ 2. engine.reseed(baseSeed + i)        │  │
│  │ 3. runSimulation() until goal/deadlock│  │
│  │ 4. Collect trace events               │  │
│  │ 5. Add timestamps                     │  │
│  └───────────────────────────────────────┘  │
└──────────────────┬──────────────────────────┘
                   │
                   ▼
┌─────────────────────────────────────────────┐
│ Export as:                                  │
│  - XES (eXtensible Event Stream)            │
│  - CSV                                      │
│  - JSON                                     │
└─────────────────────────────────────────────┘
```

---

## 6. Integration Points

### 6.1 With Existing Simulation

The probabilistic engine **overrides** the default simulation behavior:

```javascript
// In probabilistic-integration.js
app.stepSimulation = async function() {
    return await this.stepSimulationProbabilistic();
};
```

This ensures the **uniform scheduler ST** is always used for transition selection (Definition 3).

### 6.2 With Data Petri Net Model

The engine works with `DataPetriNet` from `dpn-model.js`:

```javascript
// Reading state
net.places.get(id).tokens           // Marking M
net.dataVariables.get(id).currentValue  // Valuation α
net.transitions.get(id).precondition   // pre(t)
net.transitions.get(id).postcondition  // post(t)

// Modifying state
net.fireTransition(transitionId)    // Cfire(t)
net.updateEnabledTransitions()      // Recompute frontier
```

### 6.3 With UI Components

| Component | Integration Point |
|-----------|------------------|
| Step button | `app.stepSimulation()` |
| Auto-run | `app.startAutoRun()` |
| Event log dialog | `ProbabilisticEventLogGenerator` |
| "View WebPPL Code" button | `app.showWebPPLCodeDialog()` |
| Token display | Updated after each step |
| Variable tracking | `triggerVariableHistoryUpdate()` |

---

## 7. What is Sent to WebPPL

### 7.1 Input Data

The `WebPPLCodeGenerator.generateCode(net)` method receives:

```javascript
{
    // From net.places Map
    places: [
        { id: 'p1', label: 'Start', tokens: 1, finalMarking: 0 },
        { id: 'p2', label: 'Processing', tokens: 0, finalMarking: 0 },
        { id: 'p3', label: 'End', tokens: 0, finalMarking: 1 }
    ],
    
    // From net.transitions Map
    transitions: [
        { 
            id: 't1', 
            label: 'Begin', 
            precondition: 'x < 10',      // Guard pre(t)
            postcondition: "x' = x + 1"  // Effect post(t)
        },
        // ...
    ],
    
    // From net.arcs Map
    arcs: [
        { id: 'a1', source: 'p1', target: 't1', weight: 1, type: 'regular' },
        { id: 'a2', source: 't1', target: 'p2', weight: 1, type: 'regular' },
        // ...
    ],
    
    // From net.dataVariables Map
    dataVariables: [
        { id: 'v1', name: 'x', type: 'int', currentValue: 0 },
        { id: 'v2', name: 'y', type: 'int', currentValue: 0 }
    ]
}
```

### 7.2 Generated WebPPL Code

A complete WebPPL program string (typically 100-500 lines) containing:

1. **State representation** as immutable objects
2. **Helper functions** for enabling checks
3. **Fire functions** for each transition
4. **Scheduler function** (uniform or weighted)
5. **Recursive simulation loop**
6. **Entry point** that runs the simulation

### 7.3 Constraint Handling

For postconditions with constraints like `x' > x && x' < 100`:

```javascript
var fire_t1 = function(state) {
    // Sample from scheduler SV
    var sampledValues = {
        'x': sample(uniform(0, 1000))
    };
    
    // Condition on postcondition (rejection sampling)
    observe(sampledValues['x'] > state.valuation['x'] && 
            sampledValues['x'] < 100);
    
    return { marking: {...}, valuation: { 'x': sampledValues['x'] } };
};
```

---

## 8. What is Returned

### 8.1 From WebPPL Execution

```javascript
{
    state: {
        marking: { p1: 0, p2: 0, p3: 1 },
        valuation: { x: 42, y: 7 }
    },
    trace: ['t1', 't2', 't3', 't1', 't4'],  // Sequence of fired transitions
    status: 'goal',  // 'goal' | 'deadlock' | 'max_steps'
    steps: 5
}
```

### 8.2 Processed Simulation Result

The engine transforms the WebPPL result into:

```javascript
{
    status: 'goal',
    trace: [
        { step: 1, transitionId: 't1', transition: 'Begin' },
        { step: 2, transitionId: 't2', transition: 'Process' },
        { step: 3, transitionId: 't3', transition: 'Check' },
        { step: 4, transitionId: 't1', transition: 'Begin' },
        { step: 5, transitionId: 't4', transition: 'Complete' }
    ],
    traceLength: 5,
    finalState: {
        marking: { p1: 0, p2: 0, p3: 1 },
        valuation: { x: 42, y: 7 }
    },
    goalDetails: { p3: { expected: 1, actual: 1, reached: true } },
    executionMode: 'webppl'
}
```

### 8.3 Event Log Format

For event log generation, each trace becomes events:

```javascript
// XES format
<trace>
    <string key="concept:name" value="case_001"/>
    <event>
        <string key="concept:name" value="Begin"/>
        <date key="time:timestamp" value="2026-01-30T06:00:00.000Z"/>
        <string key="lifecycle:transition" value="complete"/>
        <int key="x" value="1"/>
    </event>
    <!-- more events -->
</trace>
```

---

## 9. Usage Examples

### 9.1 Step-by-Step Simulation

```javascript
// User clicks "Step" button
await app.stepSimulation();

// Internally:
// 1. Computes frontier (enabled transitions)
// 2. Selects ONE transition using uniform scheduler
// 3. Fires selected transition
// 4. Updates display
```

### 9.2 Generate WebPPL Code

```javascript
// From code or via UI button
const code = app.generateWebPPLCode({ includeComments: true });
console.log(code);

// Or show in dialog
app.showWebPPLCodeDialog();
```

### 9.3 Full Simulation

```javascript
// Run until goal or deadlock
const result = await app.runFullSimulationProbabilistic();

// result.status: 'goal' | 'deadlock' | 'max_steps_exceeded'
// result.trace: Array of fired transitions
// result.finalState: Final marking and valuation
```

### 9.4 Event Log Generation

```javascript
const generator = new ProbabilisticEventLogGenerator(net, {
    seed: 12345,
    maxStepsPerCase: 1000,
    useWebPPL: true  // For complex DPNs
});

const eventLog = await generator.generateEventLog(100);  // 100 traces
const xes = generator.exportToXES();
```

---

## Appendix: File Locations

| File | Purpose |
|------|---------|
| `src/extensions/webppl-code-generator.js` | Csim translation to WebPPL |
| `src/extensions/probabilistic-execution.js` | Execution engine (native + WebPPL) |
| `src/extensions/probabilistic-event-log-generator.js` | Event log generation |
| `src/extensions/probabilistic-integration.js` | App integration and UI |
| `src/extensions/dpn-model.js` | Data Petri Net model |
| `tests/webppl-to-dpn.js` | Test suite with Fibonacci example |
| `docs/Translating Data Petri Nets to PPL.md` | Paper translation guide |
