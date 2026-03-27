/**
 * Workflow Definitions for YAPNE Tutorial System
 *
 * Defines five guided workflows matching YAPNE's feature categories:
 *   1. Modeling   (F21–F26)
 *   2. Import/Export (F9–F12)
 *   3. Simulation (F1–F5)
 *   4. Verification (F6–F8)
 *   5. Log Generation (F13–F15)
 *
 * Each step includes an `editorState` object that ensures the editor
 * is in the correct state before the step is displayed:
 *   - mode           — editor mode: 'select', 'addPlace', 'addTransition', 'addArc'
 *   - loadExample    — path to an example JSON to load (relative to BASE_PATH)
 *   - sidebar        — 'open' | 'close' | null  (left sidebar)
 *   - sidebarTab     — 'file' | 'help' | null
 *   - propsPanel     — 'open' | 'close' | null  (right Properties panel)
 *   - simPanel       — 'open' | 'close' | null  (right Simulation panel)
 *   - selectElement  — 'firstPlace' | 'firstTransition' | 'firstArc' | null
 */

export const WORKFLOW_DEFINITIONS = [
  /* ─────────────────────────  1. MODELING  ───────────────────────── */
  {
    id: 'modeling',
    title: 'Modeling Workflow',
    icon: '🎨',
    description: 'Design Petri nets and Data Petri Nets (DPNs) with places, transitions, arcs, guards, and data variables.',
    features: ['F21', 'F22', 'F23', 'F24', 'F25', 'F26'],
    color: '#A3BE8C',
    steps: [
      {
        title: 'Select Tool Mode',
        description: 'Use the vertical toolbar on the left to pick an editing tool. The <strong>Select (✓)</strong> tool lets you move and select elements.',
        highlight: '#btn-select',
        position: 'right',
        tip: 'Keyboard shortcut: press Escape to return to Select mode at any time.',
        editorState: { mode: 'select', sidebar: 'close', simPanel: 'close' }
      },
      {
        title: 'Add a Place',
        description: 'Click the <strong>Place (○)</strong> button, then click on the canvas to add a place. Places represent conditions or states.',
        highlight: '#btn-add-place',
        position: 'right',
        editorState: { mode: 'addPlace', sidebar: 'close', simPanel: 'close' }
      },
      {
        title: 'Add a Transition',
        description: 'Click the <strong>Transition (□)</strong> button, then click on the canvas to create a transition. Transitions represent activities.',
        highlight: '#btn-add-transition',
        position: 'right',
        editorState: { mode: 'addTransition', sidebar: 'close', simPanel: 'close' }
      },
      {
        title: 'Connect with Arcs',
        description: 'Click the <strong>Arc (→)</strong> button, then click a source element and drag to a target to connect them. Arcs define the flow.',
        highlight: '#btn-add-arc',
        position: 'right',
        tip: 'Hotkey: hold <kbd>Space</kbd> to temporarily switch to Arc mode.',
        editorState: { mode: 'addArc', sidebar: 'close', simPanel: 'close' }
      },
      {
        title: 'Rapid Modeling with Ghost Mode (F22)',
        description: 'Switch to <strong>Select mode</strong>, click a place or transition to select it, then hold <strong>Shift</strong> and move your mouse. A "ghost" of the alternate element type appears — click to place it with an automatic arc connection.',
        highlight: '#petri-canvas',
        position: 'bottom',
        tip: 'Ghost Mode is the fastest way to build net graphs. You must be in Select mode with an element selected.',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-simple-sound.json',
          selectElement: 'firstPlace',
          sidebar: 'close',
          simPanel: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Edit Element Properties',
        description: 'Click on any element to select it, then open the <strong>Properties</strong> panel on the right. For places: set marking, bounds, and final marking. For transitions: set guards, priority, and delay.',
        highlight: '#props-panel-toggle',
        position: 'left',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-simple-sound.json',
          selectElement: 'firstPlace',
          propsPanel: 'open',
          sidebar: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Define Data Variables (F23)',
        description: 'In the Properties panel, scroll to the <strong>Data Variables</strong> section. Add global DPN variables with a name, type (boolean, integer, float, string), and initial value.',
        highlight: '#props-data-vars-section',
        position: 'left',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-choice-sound.json',
          propsPanel: 'open',
          sidebar: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Set Guards & Post-conditions (F26)',
        description: 'Select a transition and use the guard editor in the Properties panel to specify pre-conditions and post-conditions using the supported expression syntax.',
        highlight: '#props-panel-toggle',
        position: 'left',
        tip: 'YAPNE provides comprehensive syntax help for guard expressions.',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-choice-sound.json',
          selectElement: 'firstTransition',
          propsPanel: 'open',
          sidebar: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Change Arc Types (F24)',
        description: 'Select an arc and change its type in the Properties panel. YAPNE supports <strong>regular</strong>, <strong>inhibitor</strong>, <strong>reset</strong>, and <strong>read</strong> arcs.',
        highlight: '#props-panel-toggle',
        position: 'left',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-simple-sound.json',
          selectElement: 'firstArc',
          propsPanel: 'open',
          sidebar: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Use Auto-Layout',
        description: 'Click the <strong>Auto-Layout (🪄)</strong> button to automatically arrange elements in a left-to-right order while minimizing arc crossings.',
        highlight: '#btn-auto-layout',
        position: 'right',
        editorState: {
          mode: 'select',
          sidebar: 'close',
          simPanel: 'close',
          propsPanel: 'close'
        }
      }
    ]
  },

  /* ──────────────────────  2. IMPORT / EXPORT  ──────────────────── */
  {
    id: 'import-export',
    title: 'Import/Export Workflow',
    icon: '📁',
    description: 'Save and load models in JSON or PNML format, import from other tools, and export as PNG images.',
    features: ['F9', 'F10', 'F11', 'F12'],
    color: '#81A1C1',
    steps: [
      {
        title: 'Open the File Sidebar',
        description: 'Click the <strong>sidebar toggle (▶)</strong> to open the sidebar, then select the <strong>File</strong> tab to access all import/export operations.',
        highlight: '#sidebar-toggle',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file', simPanel: 'close', propsPanel: 'close' }
      },
      {
        title: 'Load a JSON Model (F9)',
        description: 'Click <strong>Load (JSON)</strong> to open a previously saved model. YAPNE\'s native JSON format preserves all properties including DPN extensions, arc types, and styling.',
        highlight: '#btn-load',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Save as JSON (F9)',
        description: 'Click <strong>Save (JSON)</strong> to download the current model. This is the recommended format for preserving all model properties.',
        highlight: '#btn-save',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Load an Example',
        description: 'Use the <strong>Examples</strong> dropdown to load a built-in example model. This is a great way to explore different Petri net patterns.',
        highlight: '#template-select',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Export as PNML (F11)',
        description: 'Click <strong>Save (PNML)</strong> to export in the standard PNML format (ISO/IEC 15909-2:2011) for interoperability with other Petri net tools like ProM.',
        highlight: '#btn-export-pnml',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Export as PNG (F12)',
        description: 'Use the PNG export to create a rasterized image of the current canvas view, preserving element positions, labels, token counts, and arc decorations.',
        highlight: '#btn-export-pnml',
        position: 'right',
        tip: 'Great for including Petri net diagrams in presentations and papers.',
        editorState: {
          sidebar: 'open',
          sidebarTab: 'file',
          loadExample: 'examples/DPN-Emergency-Triage.json'
        }
      }
    ]
  },

  /* ───────────────────────  3. SIMULATION  ──────────────────────── */
  {
    id: 'simulation',
    title: 'Simulation Workflow',
    icon: '▶️',
    description: 'Execute Petri nets step-by-step or automatically, track variable changes, and observe system behavior.',
    features: ['F1', 'F2', 'F3', 'F4', 'F5'],
    color: '#EBCB8B',
    steps: [
      {
        title: 'Open the Simulation Panel',
        description: 'Click the <strong>Simulation</strong> toggle button on the right side of the canvas to open the simulation dashboard.',
        highlight: '#sim-panel-toggle',
        position: 'left',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-simple-sound.json',
          simPanel: 'open',
          sidebar: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Step Execution (F1)',
        description: 'Click <strong>Step</strong> in the simulation panel to fire a single enabled transition. The first step captures the initial state for later reset.',
        highlight: '#btn-step',
        position: 'left',
        tip: 'Enabled transitions are highlighted on the canvas. Click directly on a transition to fire it.',
        editorState: { simPanel: 'open', sidebar: 'close', propsPanel: 'close' }
      },
      {
        title: 'Auto-Run Simulation (F2)',
        description: 'Click <strong>Auto Run</strong> to continuously fire transitions automatically. Use the speed slider to control the execution delay between steps.',
        highlight: '#btn-auto-run',
        position: 'left',
        editorState: { simPanel: 'open', sidebar: 'close', propsPanel: 'close' }
      },
      {
        title: 'Observe Variable Tracking (F3)',
        description: 'During simulation of DPNs, YAPNE tracks all variable value changes. Variable popups appear on the canvas next to transitions showing current values and histories.',
        highlight: '#sim-panel-toggle',
        position: 'left',
        editorState: {
          loadExample: 'examples/soundness-test-choice-sound.json',
          simPanel: 'open',
          sidebar: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Conflict Resolution (F4)',
        description: 'When multiple transitions are enabled simultaneously, YAPNE uses transition <strong>priorities</strong> to resolve conflicts. Check the active transitions list in the simulation panel.',
        highlight: '#sim-panel-toggle',
        position: 'left',
        editorState: { simPanel: 'open', sidebar: 'close' }
      },
      {
        title: 'Reset Simulation',
        description: 'Click <strong>Reset</strong> to return to the captured initial state — tokens and data variables are restored to their original values.',
        highlight: '#btn-reset',
        position: 'left',
        editorState: { simPanel: 'open', sidebar: 'close', propsPanel: 'close' }
      },
      {
        title: 'View WebPPL Code (F5)',
        description: 'Open the File sidebar and click <strong>View WebPPL Code</strong> to export the model as a WebPPL probabilistic program for probabilistic analysis.',
        highlight: '#btn-view-webppl',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file', simPanel: 'close', propsPanel: 'close' }
      }
    ]
  },

  /* ──────────────────────  4. VERIFICATION  ─────────────────────── */
  {
    id: 'verification',
    title: 'Verification Workflow',
    icon: '🔬',
    description: 'Formally verify soundness properties (P1–P3) using symbolic state-space exploration with Z3.',
    features: ['F6', 'F7', 'F8'],
    color: '#BF616A',
    steps: [
      {
        title: 'Prepare Your Model',
        description: 'Ensure your Petri net has a proper structure: an <strong>initial place</strong> with tokens and a designated <strong>final place</strong>. Set these in the Properties panel by selecting a place.',
        highlight: '#props-panel-toggle',
        position: 'left',
        editorState: {
          mode: 'select',
          loadExample: 'examples/soundness-test-simple-sound.json',
          selectElement: 'firstPlace',
          propsPanel: 'open',
          sidebar: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Open Verification Panel',
        description: 'Click the <strong>Verification</strong> toggle button on the right side of the canvas to open the <strong>Verification panel</strong>.',
        highlight: '#verify-panel-toggle',
        position: 'left',
        editorState: {
          verifyPanel: 'open',
          sidebar: 'close',
          propsPanel: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Run Formal Verification (F6)',
        description: 'Click <strong>Run Formal Verification</strong> to check all three soundness properties using the Suvorov & Lomazova algorithms with Z3 SMT solver.',
        highlight: '#btn-sl-verify-panel',
        position: 'left',
        editorState: { verifyPanel: 'open' }
      },
      {
        title: 'Understanding Property P1: Reachability',
        description: '<strong>P1</strong> checks that every reachable state can eventually reach the designated final state. A violation indicates a <em>deadlock</em>. This example demonstrates a P1 violation.',
        highlight: '#petri-canvas',
        position: 'bottom',
        tip: 'Notice how one branch leads to a state with no path to the final marking.',
        editorState: {
          loadExample: 'examples/soundness-test-p1-violation-deadlock.json',
          sidebar: 'close',
          propsPanel: 'close',
          simPanel: 'close'
        }
      },
      {
        title: 'Understanding Property P2: Proper Termination',
        description: '<strong>P2</strong> ensures that upon reaching the final marking, no transitions remain enabled. A violation means <em>improper termination</em> with residual tokens.',
        highlight: '#petri-canvas',
        position: 'bottom',
        tip: 'This example has extra tokens remaining after reaching the final state.',
        editorState: {
          loadExample: 'examples/soundness-test-p2-violation-overfinal.json',
          sidebar: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Understanding Property P3: No Dead Transitions',
        description: '<strong>P3</strong> verifies that every transition can fire in at least one reachable state. A dead transition signals unreachable logic.',
        highlight: '#petri-canvas',
        position: 'bottom',
        tip: 'In this example, a transition can never fire due to conflicting data constraints.',
        editorState: {
          loadExample: 'examples/soundness-test-p3-violation-dead-transition.json',
          sidebar: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Inspect Counterexamples (F7)',
        description: 'For each violated property, YAPNE generates a <strong>counterexample trace</strong> showing the execution path that leads to the violating state. Click on a violation to see the trace visualized on the canvas.',
        highlight: '#btn-sl-verify-panel',
        position: 'left',
        editorState: { verifyPanel: 'open' }
      },
      {
        title: 'Guard Analysis (F8)',
        description: 'The verifier also detects <strong>unsatisfiable guards</strong> — preconditions that can never be met, making their transition effectively dead.',
        highlight: '#btn-sl-verify-panel',
        position: 'left',
        editorState: {
          loadExample: 'examples/soundness-test-choice-sound.json',
          verifyPanel: 'open'
        }
      }
    ]
  },

  /* ─────────────────────  5. LOG GENERATION  ────────────────────── */
  {
    id: 'log-generation',
    title: 'Log Generation Workflow',
    icon: '📊',
    description: 'Generate event logs from simulations for process mining analysis, supporting XES, CSV, and JSON formats.',
    features: ['F13', 'F14', 'F15'],
    color: '#B48EAD',
    steps: [
      {
        title: 'Open Event Log Generator',
        description: 'Open the <strong>sidebar (File tab)</strong>, find the <strong>Generation</strong> section, and click <strong>Generate Event Log</strong> to open the log generator dialog.',
        highlight: '#btn-event-log',
        position: 'right',
        editorState: {
          loadExample: 'examples/soundness-test-simple-sound.json',
          sidebar: 'open',
          sidebarTab: 'file',
          simPanel: 'close',
          propsPanel: 'close'
        }
      },
      {
        title: 'Configure Trace Count (F13)',
        description: 'Set the <strong>number of process instances</strong> to simulate. Each instance runs independently through the net, producing a separate trace.',
        highlight: '#btn-event-log',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Set Arrival Distributions',
        description: 'Configure the <strong>arrival distribution</strong> for process instances: choose between fixed, exponential, or normal distributions to control timing.',
        highlight: '#btn-event-log',
        position: 'right',
        tip: 'Transition delays (set in Properties) affect event timestamps.',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Include Data Attributes (F15)',
        description: 'For DPNs, the generated logs automatically include <strong>data attributes</strong> derived from variable values at each simulation step.',
        highlight: '#btn-event-log',
        position: 'right',
        editorState: {
          loadExample: 'examples/soundness-test-choice-sound.json',
          sidebar: 'open',
          sidebarTab: 'file'
        }
      },
      {
        title: 'Choose Export Format (F14)',
        description: 'Select the output format: <strong>XES</strong> (for ProM, PM4Py), <strong>CSV</strong>, or <strong>JSON</strong>. Each format includes the full trace with event names and timestamps.',
        highlight: '#btn-event-log',
        position: 'right',
        tip: 'XES is the standard format for most process mining tools.',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      },
      {
        title: 'Analyze the Results',
        description: 'After generation, review the simulation report showing the generated event log, variable distributions, and trace statistics.',
        highlight: '#btn-event-log',
        position: 'right',
        editorState: { sidebar: 'open', sidebarTab: 'file' }
      }
    ]
  }
];
