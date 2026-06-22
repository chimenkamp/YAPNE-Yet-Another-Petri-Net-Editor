# YAPNE feature inventory and compatibility map

This document inventories the features implemented in the Petri net editor source tree as of this analysis. It distinguishes active frontend features from modules that exist in the repository but are not loaded by `index.html`.

## Legend

| Column | Meaning |
| --- | --- |
| Datatype | `PN` means ordinary place/transition Petri nets. `DPN` means Data Petri Nets with variables, guards, or postconditions. `PN or DPN` means the feature works for both. `UI/source` means the feature is editor infrastructure rather than a Petri-net analysis. |
| Final marking | `No` means not needed. `Optional` means displayed or preserved when present. `Required` means the feature needs at least one positive final marking to be meaningful or to run. |
| Compatibility | `Full` means the feature honors the relevant PN/DPN semantics. `PN projection` means it can be launched on a DPN but ignores data variables, guards, and postconditions. `Partial` means important metadata is not round-tripped or not all semantics are modeled. |

## Global compatibility rules

1. DPN guards and postconditions are compatible with manual simulation, probabilistic step execution, WebPPL constraint solving, event-log generation, JSON persistence, PNG export, animation export, Python import, and the formal DPN verifier.
2. Marking graphs, coverability trees, S-components, S-coverability, and free-choice analysis are PN/token-structure analyses. They can be executed while a DPN is open, but the result is only for the underlying PN projection unless the DPN data layer is irrelevant.
3. S-components and S-coverability are not defined for data Petri nets in the implemented structural analysis. They should be treated as PN workflow-net structure checks, not DPN verification.
4. Event-log generation and full probabilistic playout require a positive final marking. Single-step simulation and ordinary auto-run do not require final markings; they stop at a final marking when one is reached, or at deadlock.
5. Formal Suvorov-Lomazova soundness verification is DPN-oriented and checks P1, P2, and P3 against final markings. A meaningful positive final marking should be set before running it.
6. JSON is the most complete persistence format. PNML import reads several YAPNE/DPN extensions, but PNML export currently does not write final markings and is therefore lossy for workflows that depend on final markings.
7. Fusion sets share markings between places. Token simulation and conflict detection know about them. Formal structural analyses should be interpreted carefully because fusion-set semantics are not part of the classical S-component/free-choice definitions.
8. Special arcs are available in the editor and runtime. Some analyses support them as token effects, but classical structural properties are primarily defined for regular arcs.

## Active feature map

### Graphical editor and modeling

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F1 | Place/transition modeling | PN or DPN | No | Full. Create, move, select, rename, and delete nodes on the canvas. | `src/petri-net-simulator.js`, `src/petri-net-app.js` |
| F2 | Regular weighted arcs | PN or DPN | No | Full. Arc weights affect token consumption/production. | `src/petri-net-simulator.js` |
| F3 | Special arc types: inhibitor, reset, read | PN or DPN | No | Partial across analyses. Runtime and DPN verifier support these as token effects. Marking graph/coverability support them, but inhibitor threshold is fixed to 1 there. Classical S-components/free-choice should be read as regular-arc structure only. | `src/petri-net-simulator.js`, `src/petri-net-analysis.js`, `src/extensions/soundness-verification/.../DPN-refinement-engine.js` |
| F4 | Place tokens and capacity | PN or DPN | No | Full in runtime. Capacity can disable firings that would overflow a place. | `src/petri-net-simulator.js`, `src/petri-net-app.js` |
| F5 | Place final marking | PN or DPN | Optional | Required by goal-based features. Displayed in the editor and used by probabilistic/event-log/soundness workflows. | `src/petri-net-simulator.js`, `src/petri-net-app.js` |
| F6 | Fusion places/fusion sets | PN or DPN | No | Full for editor/runtime token synchronization. Structural verification should be interpreted with care because classical PN definitions do not include fusion-set marking identity. | `src/petri-net-simulator.js`, `src/petri-net-app.js` |
| F7 | Transition label, priority, delay | PN or DPN | No | Runtime stores all three. Priority is used by synchronous conflict resolution; delay is mainly metadata in the current UI/runtime. | `src/petri-net-simulator.js`, `src/petri-net-app.js` |
| F8 | Silent transitions | PN or DPN | No | Full. Rendered differently, labels disabled/hidden, and skipped in event logs. | `src/petri-net-simulator.js`, `src/petri-net-app.js`, `src/extensions/probabilistic-event-log-generator.js` |
| F9 | Data-aware transition creation | DPN | No | Full. Adds a toolbar mode for creating DPN transitions. | `src/extensions/dpn-integration.js`, `src/extensions/dpn-ui.js` |
| F10 | Convert ordinary transition to data transition | DPN | No | Full. Adds DPN pre/postcondition editing to an existing transition. | `src/extensions/dpn-ui.js` |
| F11 | Data variable management | DPN | No | Full for `int`, `real`, and `bool`. Legacy aliases are normalized; `string` is treated as an integer encoding and should not be considered a current first-class datatype. | `src/extensions/dpn-model.js`, `src/extensions/dpn-ui.js` |
| F12 | Guard/precondition editor | DPN | No | Full. Supports infix and SMT-LIB-style built-in operators, live validation, declared-variable checks, and no primed variables in preconditions. | `src/extensions/dpn-ui.js`, `src/extensions/guard-language/*` |
| F13 | Postcondition/update editor | DPN | No | Full. Supports direct assignments such as `x' = x + 1` and constraint-style updates such as `x' > 0 and x' < x`. Non-empty postconditions must reference at least one primed variable. | `src/extensions/dpn-ui.js`, `src/extensions/guard-language/*` |
| F14 | Constraint-based postcondition solving | DPN | No | Full for numeric/bool variables within implemented solver bounds. Uses WebPPL when available and native fallback otherwise. | `src/extensions/dpn-model.js`, `src/extensions/probabilistic-execution.js` |
| F15 | DPN visual status and overlays | DPN | No | Full. Data transitions use guard-aware colors and optional variable/effect overlays while the simulation dashboard is open. | `src/extensions/dpn-renderer.js`, `src/simulation-dashboard.js` |
| F16 | Canvas pan, zoom, reset view, fit to canvas | UI/source | No | Full. Includes wheel zoom, button zoom, middle mouse or modifier drag panning. | `src/petri-net-simulator.js`, `src/petri-net-app.js`, `app.js` |
| F17 | Grid, snap-to-grid, grid size, show grid | UI/source | No | Full. Settings are persisted in localStorage. | `src/editor-settings.js`, `src/petri-net-app.js`, `app.js` |
| F18 | Editor color inversion | UI/source | No | Full for active app setting. This is not the dormant WCAG high-contrast module. | `src/editor-settings.js`, `src/petri-net-app.js`, `app.js` |
| F19 | Auto-connect while modeling | PN or DPN | No | Full. Creates/preview links between compatible nearby nodes, including pasted or moved selections. | `src/petri-net-simulator.js`, `src/editor-settings.js` |
| F20 | Ghost creation and arc-drop node creation | PN or DPN | No | Full. Shift-based ghost preview and dropping an arc on empty canvas create a compatible opposite node. | `src/petri-net-simulator.js`, `app.js` |
| F21 | Multi-selection and box selection | PN or DPN | No | Full. Supports grouped selection and grouped operations. | `src/petri-net-simulator.js` |
| F22 | Copy/paste selected subnets | PN or DPN | No | Full for selected places/transitions and internal arcs. | `src/petri-net-simulator.js` |
| F23 | Delete, clear net, and selected-element deletion | PN or DPN | No | Full. Clear prompts for confirmation. | `src/petri-net-app.js`, `src/petri-net-simulator.js` |
| F24 | Undo, redo, and history dialog | UI/source | No | Full for snapshot-based editor changes. History dialog mirrors undo/redo stacks. | `src/petri-net-app.js`, `src/action-history.js`, `src/history-dialog.js` |
| F25 | Automatic layout | PN or DPN | No | Full for graph layout. It repositions elements but does not change semantics. | `src/petri-net-app.js`, `src/petri-net-simulator.js` |
| F26 | Named graphical views | PN or DPN | No | Full. Views share the same canonical net but keep independent visible subsets, layout, and viewport. | `src/views-panel.js`, `src/petri-net-simulator.js` |
| F27 | Selection views and transition-neighborhood views | PN or DPN | No | Full. Creates child views from selected elements or selected transitions. | `src/views-panel.js`, `src/petri-net-simulator.js` |
| F28 | Add/remove selection from active child view | PN or DPN | No | Full. Removes only from the view, not from the canonical net. | `src/views-panel.js`, `src/petri-net-simulator.js` |
| F29 | Side panel layout/stacking | UI/source | No | Full. Properties, Views, Simulation, Verification, Generation, and Animation panels coordinate layout. | `src/petri-net-app.js` |
| F30 | Template/example loading | PN or DPN | Optional | Full for JSON examples. Loads shipped examples from `public/examples/example-config.json`. | `app.js`, `public/examples/*` |
| F31 | Help dialog and first-run welcome | UI/source | No | Full. Stored in localStorage after first display. | `app.js`, `index.html` |
| F32 | Guided workflow tutorials | UI/source | No | Full. Includes workflows for modeling, import/export, simulation, verification, and log generation. | `src/workflow-tutorial.js`, `src/workflow-definitions.js` |

### Simulation and probabilistic execution

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F33 | Single-step simulation | PN or DPN | No | Full. Active app overrides the old synchronous step with probabilistic single-transition selection using the uniform scheduler. | `src/extensions/probabilistic-integration.js`, `src/simulation-dashboard.js` |
| F34 | Fire selected/specific transition | PN or DPN | No | Full. Honors token, guard, and postcondition semantics. | `src/petri-net-app.js`, `src/simulation-dashboard.js`, `src/extensions/dpn-model.js` |
| F35 | Auto-run simulation | PN or DPN | No | Full. Repeats probabilistic steps until stopped, final marking is reached, deadlock occurs, or the dashboard limit is hit. | `src/extensions/probabilistic-integration.js`, `src/simulation-dashboard.js` |
| F36 | Reset to captured initial simulation state | PN or DPN | No | Full for tokens. The code has an intended DPN-variable reset path, but the active integration does not expose the referenced `dataVariables` field, so variable reset should be verified before relying on it. Captures state on first step/run/fire. | `src/petri-net-app.js`, `src/simulation-dashboard.js`, `src/extensions/dpn-integration.js` |
| F37 | Simulation dashboard | PN or DPN | Optional | Full. Provides Step/Run/Reset, speed, max steps, active transitions, token grid, trace log, and final-marking progress when defined. | `src/simulation-dashboard.js` |
| F38 | Runtime DPN guards | DPN | No | Full for supported guard language. Disabled guards prevent transitions from firing. | `src/extensions/dpn-model.js`, `src/extensions/guard-language/*` |
| F39 | Runtime DPN postconditions | DPN | No | Full for direct assignments and implemented constraint solving. Updates variables after token firing. | `src/extensions/dpn-model.js` |
| F40 | Native probabilistic playout | PN or DPN | Required | Full. Runs until positive final marking, deadlock, or max steps. Requires final marking validation by default. | `src/extensions/probabilistic-execution.js` |
| F41 | WebPPL playout mode | DPN | Required | Full where WebPPL is available. Used for complex probabilistic/constraint behavior and can fall back to native mode. | `src/extensions/probabilistic-execution.js` |
| F42 | WebPPL Csim code viewer | PN or DPN | Required for meaningful goal code | Full for code generation. Shows generated WebPPL code with basic syntax highlighting. | `src/extensions/probabilistic-integration.js`, `src/extensions/webppl-code-generator.js` |
| F43 | Core synchronous firing/conflict API | PN or DPN | No | Full as a library/API feature. The active UI step is probabilistic, but the core model still has synchronous planning, priority conflict resolution, and random tie breaking. | `src/petri-net-simulator.js`, `src/extensions/dpn-model.js` |
| F44 | Goal-state checking | PN or DPN | Optional/Required by playouts | Full for probabilistic workflows. A goal is positive final marking reached, or deadlock. Final marking reached uses `tokens >= finalMarking`. | `src/extensions/probabilistic-execution.js` |

### Verification and analysis

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F45 | Formal Suvorov-Lomazova soundness verification | DPN, PN as DPN | Required | Full for the implemented DPN algorithm. Checks boundedness/refinement/LTS and P1/P2/P3. Meaningful positive final marking should be defined before use. | `src/verification-panel.js`, `src/extensions/soundness-verification/suvorov-lomazova/*` |
| F46 | P1 deadlock freedom | DPN | Required | Full. Checks that every reachable state can reach a final marking. | `src/extensions/soundness-verification/suvorov-lomazova/suvorov-lomazova-verifier.js` |
| F47 | P2 no overfinal markings | DPN | Required | Full. Detects reachable markings that strictly cover the final marking. | `src/extensions/soundness-verification/suvorov-lomazova/suvorov-lomazova-verifier.js` |
| F48 | P3 no dead transitions | DPN | Required | Full. Checks that every original transition has a firing refined copy in the LTS. | `src/extensions/soundness-verification/suvorov-lomazova/suvorov-lomazova-verifier.js` |
| F49 | Z3-backed boundedness check | DPN | No | Full as part of formal verification. Uses coverability over symbolic LTS states. | `src/extensions/soundness-verification/suvorov-lomazova/suvorov-lomazova-verifier.js` |
| F50 | DPN refinement and tau-transition construction | DPN | Required for soundness workflow | Full within verifier. Adds tau transitions and refines DPN behavior before final checks. | `src/extensions/soundness-verification/suvorov-lomazova/DPN-refinement-engine.js` |
| F51 | Counterexample reporting | DPN | Required for soundness workflow | Full. Reports traces, dead transitions, overfinal nodes, and offending states. | `src/extensions/soundness-verification/suvorov-lomazova/verification-ui.js` |
| F52 | Counterexample overlay visualization | DPN | Required for soundness workflow | Full. Displays draggable HTML overlays on the canvas for verification counterexamples. | `src/extensions/soundness-verification/suvorov-lomazova/trace-visualization-renderer.js` |
| F53 | Marking graph | PN | No | PN projection on DPN. Explores finite reachable markings from the initial marking with max-state and token-cap limits. | `src/generation-panel.js`, `src/petri-net-analysis.js` |
| F54 | Coverability tree | PN | No | PN projection on DPN. Uses omega-style acceleration for unbounded growth. | `src/generation-panel.js`, `src/petri-net-analysis.js` |
| F55 | Workflow-net structural check | PN | No | PN projection on DPN. Requires one source place, one sink place, and source/sink reachability. | `src/petri-net-analysis.js` |
| F56 | S-components | PN | No | Not defined for DPN in this editor's analysis. Intended for workflow-net structure over regular arcs. | `src/petri-net-analysis.js`, `src/generation-panel.js` |
| F57 | S-coverability | PN | No | Not defined for DPN in this editor's analysis. Reports uncovered places from detected S-components. | `src/petri-net-analysis.js`, `src/generation-panel.js` |
| F58 | Free-choice analysis | PN | No | PN projection on DPN. Checks shared-choice preset compatibility structurally. | `src/petri-net-analysis.js`, `src/generation-panel.js` |
| F59 | Analysis SVG visualizations | PN | No | Full for PN projection. Renders marking graph, coverability tree, and structural summaries. | `src/petri-net-analysis.js`, `src/generation-panel.js` |
| F60 | Structural highlights in model | PN | No | Full for structural-analysis output. Highlights selected S-components on the canvas. | `src/generation-panel.js`, `src/petri-net-simulator.js` |
| F61 | Guard expression validation | DPN | No | Full. Validates syntax, declared variables, primed-variable restrictions, and postcondition write presence. | `src/extensions/guard-language/guard-validator.js`, `src/extensions/dpn-api.js` |

### Import, export, and persistence

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F62 | JSON save/load | PN or DPN | Optional | Full. Best round-trip format: places, transitions, arcs, views, arc semantics, final markings, fusion sets, silent flags, and DPN variables/conditions. | `src/petri-net-app.js`, `src/petri-net-simulator.js`, `src/extensions/dpn-model.js` |
| F63 | PNML import | PN or DPN | Optional | Partial. Reads PNML/XML, initial markings, final markings if present, positions, arc types, fusion sets, silent flags, DPN variables, and guard/update metadata. Can relayout before import. | `src/extensions/pnml-importer.js` |
| F64 | PNML export | PN or DPN | Optional but lossy | Partial. Exports PN/DPN structure and YAPNE metadata, but current exporter does not write final markings. Use JSON when final markings are required. | `src/petri-net-simulator.js`, `src/extensions/dpn-model.js`, `src/petri-net-app.js` |
| F65 | PNG export | PN or DPN | No | Full visual export. Supports sizing, padding, transparent/background color, colors, labels/tokens, grid, DPI scale, and DPN guard/update rendering. | `src/extensions/png-exporter.js` |
| F66 | Python import as DPN | DPN | Generated automatically | Partial/Beta. Converts supported Python control flow into a DPN and sets generated end places as final markings. Unsupported constructs are warned. | `src/extensions/python-import-dialog.js`, `src/extensions/python-dpn-transpiler.js` |
| F67 | Python examples and import settings | DPN | Generated automatically | Partial/Beta. Includes examples, code/file input, generalization slider, and function inlining depth. | `src/extensions/python-import-dialog.js` |
| F68 | Editor settings persistence | UI/source | No | Full. Stores zoom/pan sensitivity, snap/grid, color inversion, and auto-connect settings. | `src/editor-settings.js`, `app.js` |
| F69 | Loaded example catalog | PN or DPN | Optional | Full for shipped JSON examples. Includes soundness examples with final markings. | `public/examples/example-config.json`, `app.js` |

### Event logs and process-mining output

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F70 | Event-log generation dialog | PN or DPN | Required | Full. Requires at least one place, one transition, an initial token, and a positive final marking. | `src/event-log-integration.js` |
| F71 | Probabilistic case generation | PN or DPN | Required | Full. Generates independent cases with uniform scheduler and max-step protection. | `src/extensions/probabilistic-event-log-generator.js` |
| F72 | Classic event log format | PN or DPN | Required | Full. One row per activity, with variable columns when available. | `src/extensions/probabilistic-event-log-generator.js` |
| F73 | Lifecycle event log format | PN or DPN | Required | Full. Emits start/complete lifecycle events suitable for XES-style logs. | `src/extensions/probabilistic-event-log-generator.js` |
| F74 | CSV, JSON, and XES export | PN or DPN | Required | Full for generated event logs. | `src/event-log-integration.js`, `src/extensions/probabilistic-event-log-generator.js` |
| F75 | Data attributes in logs | DPN | Required | Full for current/after variable values captured by generated events. | `src/extensions/probabilistic-event-log-generator.js`, `src/event-log-integration.js` |
| F76 | Variable distribution summaries | DPN | Required | Full for numeric and boolean variables. Shows min, max, mean, std-dev, histograms/bars, and true/false shares. | `src/event-log-integration.js` |
| F77 | Activity and duration statistics | PN or DPN | Required | Full. Reports cases, events, duration stats, average case length, and activity frequency. | `src/event-log-integration.js`, `src/extensions/probabilistic-event-log-generator.js` |
| F78 | Event-log WebPPL progress/code preview | DPN | Required | Full. Shows active WebPPL solver/program code and WebPPL call count during generation. | `src/event-log-integration.js`, `src/extensions/probabilistic-execution.js` |
| F79 | Silent-transition filtering in logs | PN or DPN | Required | Full. Silent transitions can fire but do not become log events. | `src/extensions/probabilistic-event-log-generator.js` |

### Animation and presentation export

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F80 | Animation Studio | PN or DPN | Optional | Full visual feature. Loads visible net, variables, markings, labels, and final-marking rings. | `src/animation-panel.js` |
| F81 | Animation presets | PN or DPN | Optional | Full. Presets include Reveal Net, Animate Flow, and DPN Story. | `src/animation-panel.js` |
| F82 | Timeline clips and inspector | PN or DPN | No | Full. Effects include appear, disappear, highlight, pulse, focus, token flow, caption, and data callout. | `src/animation-panel.js` |
| F83 | Animation preview playback | PN or DPN | No | Full. Canvas preview with play/stop and scrubber. | `src/animation-panel.js` |
| F84 | Animation export | PN or DPN | No | Full. Exports WebM, GIF, or a single PNG frame with configurable duration, FPS, resolution, background, labels, captions, data strip, data callouts, progress bar, and grid. | `src/animation-panel.js` |

### Keyboard, accessibility-adjacent, and UI behavior

| ID | Feature | Datatype | Final marking | Compatibility and notes | Main implementation |
| --- | --- | --- | --- | --- | --- |
| F85 | Toolbar keyboard shortcuts | UI/source | No | Full. Includes undo/redo, temporary arc mode with Space, delete, Ctrl/Cmd+A, copy/paste, token adjustment, and view removal shortcuts in active editor code. | `src/petri-net-app.js`, `src/petri-net-simulator.js` |
| F86 | Sidebar Tab toggle | UI/source | No | Full. Tab toggles the File/Help/Settings sidebar when no input is focused. | `app.js` |
| F87 | Input-safe keyboard handling | UI/source | No | Full. Global shortcuts avoid hijacking focused inputs, textareas, and selects. | `src/petri-net-app.js`, `app.js` |
| F88 | Local UI state persistence | UI/source | No | Full. Stores sidebar visibility, active tab, collapsed sections, first-run help status, and editor settings. | `app.js`, `src/editor-settings.js` |

## Source-only or currently inactive features

These modules exist in the repository but are not active in the current `index.html` or active app initialization path.

| Feature | Datatype | Final marking | Status and compatibility notes | Source |
| --- | --- | --- | --- | --- |
| Random Petri net generator | PN | Optional | Implemented but the script tag is commented out in `index.html`. Generates simple/medium/complex/custom nets, topology variants, special arc probabilities, token strategies, seeded output, preview, and optional property enforcement heuristics. | `src/extensions/random-petri-net-generator.js` |
| WCAG canvas accessibility layer | UI/source | No | Implemented but not imported/initialized by the active app. Would add screen-reader DOM mirrors, live announcements, keyboard canvas navigation, high contrast mode, skip links, and an accessibility menu. | `src/accessibility/accessibility-integration.js`, `src/accessibility/wcag-canvas-accessibility.js` |
| Auto-save manager | UI/source | No | Implemented but not imported/initialized by the active app. Would periodically save dirty JSON to localStorage and offer restore. | `src/auto-save.js` |
| Legacy/general event-log generator | PN or DPN | Configurable | Library module is loaded but the active UI uses `ProbabilisticEventLogGenerator`. The legacy class contains additional library-level options such as arrival distributions and transition strategies. | `src/event-log-generator.js` |

## Compatibility matrix

| Feature family | PN | DPN | Requires final marking | Notes |
| --- | --- | --- | --- | --- |
| Modeling/editing, views, layout, JSON, PNG, animation | Yes | Yes | No/Optional | DPN metadata is preserved by JSON and visual exports. |
| Manual step/fire/auto-run simulation | Yes | Yes | No | Final marking is only a stop/status condition. |
| Full probabilistic playout/WebPPL run | Yes | Yes | Yes | Goal states are defined by positive final markings; deadlock is also treated as a goal/end state during execution. |
| Event-log generation | Yes | Yes | Yes | Uses probabilistic execution and skips silent transitions. |
| Formal soundness verification | PN as data-free DPN | Yes | Yes | Checks DPN soundness P1/P2/P3 using Z3/refinement/LTS. |
| Marking graph and coverability tree | Yes | PN projection only | No | Ignores DPN data guards/postconditions. |
| S-components and S-coverability | Yes | No semantic DPN support | No | Intended for workflow-net structure; not defined for DPNs. |
| Free-choice analysis | Yes | PN projection only | No | Structural preset check; ignores DPN data. |
| PNML import | Yes | Partial DPN support | Optional | Reads final markings if present. |
| PNML export | Yes | Partial DPN support | Not preserved | Does not currently export final markings. |
| Python import | No direct PN output | Yes | Generated | Produces a DPN JSON model and sets generated final places. |
| Random generation | Source-only | No | Optional | Implemented PN generator but inactive in current frontend. |

## Source files reviewed

- Active app and editor: `app.js`, `index.html`, `src/petri-net-app.js`, `src/petri-net-simulator.js`
- DPN implementation: `src/extensions/dpn-model.js`, `src/extensions/dpn-api.js`, `src/extensions/dpn-ui.js`, `src/extensions/dpn-renderer.js`, `src/extensions/dpn-integration.js`, `src/extensions/guard-language/*`
- Simulation/probabilistic execution: `src/simulation-dashboard.js`, `src/extensions/probabilistic-integration.js`, `src/extensions/probabilistic-execution.js`, `src/extensions/webppl-code-generator.js`
- Verification and analysis: `src/verification-panel.js`, `src/generation-panel.js`, `src/petri-net-analysis.js`, `src/extensions/soundness-verification/suvorov-lomazova/*`
- Import/export: `src/extensions/pnml-importer.js`, `src/extensions/png-exporter.js`, `src/extensions/python-import-dialog.js`, `src/extensions/python-dpn-transpiler.js`
- Event logs and animation: `src/event-log-integration.js`, `src/extensions/probabilistic-event-log-generator.js`, `src/event-log-generator.js`, `src/animation-panel.js`
- Source-only modules: `src/extensions/random-petri-net-generator.js`, `src/accessibility/*`, `src/auto-save.js`
