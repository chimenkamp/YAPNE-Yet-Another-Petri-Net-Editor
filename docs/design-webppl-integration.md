# WebPPL Integration Design

Implementation of probabilistic programming for Data Petri Nets as described in:

> **"Data Petri Nets Meet Probabilistic Programming"**  
> Kuhn et al., BPM 2024  
> https://doi.org/10.1007/978-3-031-70396-6_2

## Overview

This document describes the WebPPL integration that enables true probabilistic inference for Data Petri Net simulations in YAPNE.

## Architecture

### Browser Bundle

WebPPL is a Node.js-based probabilistic programming language. To use it in the browser:

1. **Build Script**: `scripts/bundle-webppl.js`
   - Uses Browserify with WebPPL's transforms
   - Outputs to `public/webppl/webppl-bundle.js`
   - Run with: `npm run bundle:webppl`

2. **Loading**: The bundle is loaded via `<script>` tag in `index.html`
   - Exposes `window.webppl` global
   - API: `window.webppl.run(code, callback)`

### Code Generation

`src/extensions/webppl-code-generator.js` generates WebPPL code following the paper's Csim structure:

```
Csim: Cinit; do ¬isGoal → (Benabled(t1) → Cfire(t1) [] ... [] Benabled(tn) → Cfire(tn)) od
```

Key sections (per Figure 5 of the paper):

1. **Cinit** - Initializes marking M and valuation α
2. **isGoal** - Boolean formula for goal states G
3. **Benabled(t)** - Guard checking if transition t is enabled
4. **Cfire(t)** - Fires transition t, samples variables, observes postcondition
5. **Scheduler** - ST (transition selection) and SV (variable sampling)

### Execution Modes

`src/extensions/probabilistic-execution.js` supports:

1. **Native Mode** - Direct JavaScript execution (fast, for simple nets)
2. **WebPPL Mode** - Full probabilistic programming (accurate, for DPNs with constraints)

Selection is automatic based on whether the net has constraint-style postconditions.

## Paper Alignment

### Definition References

| Definition | Implementation |
|------------|----------------|
| **Def 1**: DPN structure | `normalizeNet()` in webppl-code-generator.js |
| **Def 2**: Enabled transitions | `generateEnablingFunctions()` |
| **Def 3**: Scheduler S | `generateScheduler()` + `selectTransition()` |
| **Def 4**: Step semantics | `generateFiringFunctions()` |
| **Def 5**: Run probability | Captured by `Infer()` wrapper |
| **Def 6**: Goal state probability | `generateGoalStateCheck()` |

### Theorem 1 (Correctness)

> "For every initial net state (M,α), executing the main loop of Csim on s(M,α) produces the same distribution over runs as the encoded net N under scheduler S."

Implementation via `generateMainLoop()` with inference mode:

```javascript
var inferenceResult = Infer({
    method: 'rejection',
    samples: 1000,
    maxScore: 0
}, simulateDPN);

sample(inferenceResult)
```

### Section 5.2 Alignment

- **log step(t)**: Transition firing is recorded in trace array
- **condition(post(t))**: Postcondition constraints use WebPPL's `condition()`
- **v' := SV(v')**: Variable sampling from configured distributions

## Usage

### Building the Bundle

```bash
npm run bundle:webppl
```

### Testing in Browser

```javascript
// In browser console:
window.webpplTests.runAllTests()
```

Or import the test module:

```javascript
import { runAllTests } from './tests/webppl-browser-test.js';
await runAllTests();
```

### Using the Execution Engine

```javascript
import { ProbabilisticExecutionEngine } from './src/extensions/probabilistic-execution.js';

const engine = new ProbabilisticExecutionEngine({
    executionMode: 'webppl',  // or 'native' or 'auto'
    scheduler: 'uniform',
    maxSteps: 10000
});

// Run simulation
const result = await engine.runWebPPLSimulation(net);
console.log(result.trace);
console.log(result.finalState);
```

## File Structure

```
YAPNE/
├── scripts/
│   └── bundle-webppl.js          # WebPPL browser bundling script
├── public/
│   └── webppl/
│       └── webppl-bundle.js      # Generated browser bundle (2.25 MB)
├── src/extensions/
│   ├── webppl-code-generator.js  # Csim code generation (Figure 5)
│   └── probabilistic-execution.js # Execution engine
├── tests/
│   ├── webppl-browser-test.js    # Browser integration tests
│   └── webppl-to-dpn.js          # Node.js tests
└── docs/
    └── design-webppl-integration.md  # This document
```

## Troubleshooting

### WebPPL not available in browser

1. Ensure bundle exists: `ls public/webppl/webppl-bundle.js`
2. Rebuild: `npm run bundle:webppl`
3. Check browser console for script loading errors

### Bundle build fails

1. Install dependencies: `npm install --save-dev browserify brfs`
2. Check WebPPL installation: `ls node_modules/webppl/src/browser.js`

### Execution falls back to native mode

Check console for: `[PP Engine] WebPPL unavailable, falling back to native simulation`

Solution: Ensure bundle is loaded before app scripts in index.html.
