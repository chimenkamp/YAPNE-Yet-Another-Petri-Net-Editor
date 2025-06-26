# YAPNE User Manual

## 1. Overview

YAPNE (Yet Another Petri Net Editor) is a web-based tool for creating, editing, simulating, and analyzing Petri nets. It features extensions for handling data-aware Petri nets (DPNs). This manual provides a detailed guide to all its functionalities.



## 2. Controls

This section details the controls available in the YAPNE interface for creating and interacting with your models.

### 2.1 Main Toolbar (Vertical)

The primary editing tools are located in the vertical toolbar to the left of the canvas.

| Icon | Name | Key | Description |
| :--- | :--- | :-- | :--- |
| ✓ | Select | | Select, move, and edit elements on the canvas. |
| ○ | Add Place | | Add a new place to the canvas. |
| □ | Add Transition | | Add a new standard transition to the canvas. |
| ⊞ | Add Data Transition | | Add a new data-aware transition. |
| → | Add Arc | `Space` | Hold to connect elements with an arc. |
| 🗑️ | Delete | | Delete the currently selected element. |
| 🧹 | Clear | | Clears the entire canvas after confirmation. |
| 🪄 | Auto-Layout | | Automatically arranges all elements on the canvas. |
| 📏 | Toggle Snap to Grid | | Toggles snap-to-grid for precise alignment. |

### 2.2 Keyboard & Mouse Shortcuts

| Action | Control |
| :--- | :--- |
| **Quick Connect** | Hold the `Space` key to temporarily switch to "Add Arc" mode. |
| **Ghost Mode** | Select a place or transition, then hold `Shift` and move the mouse to create and place a connected element. |
| **Pan Canvas** | Hold the middle mouse button and drag, or use `Alt/Cmd + Drag`. |
| **Zoom Canvas** | Use the mouse scroll wheel. |

### 2.3 Canvas Controls

These controls, located at the bottom left of the canvas, help you navigate your model.

| Icon | Name | Key | Description |
| :--- | :--- | :-- | :--- |
| + | Zoom In | | Zooms into the canvas. |
| - | Zoom Out | | Zooms out of the canvas. |
| ↺ | Reset View | | Resets zoom and pan to the default view. |
| ⛶ | Toggle Full Screen | `F` | Toggles fullscreen mode for the editor. |



## 3. Features

### 3.1 Petri Net Editing

#### 3.1.1 Creating and Managing Elements
-   **Adding Elements:** Use the vertical toolbar to add places and transitions. Click on the canvas to place them.
-   **Connecting Elements (Arcs):** Use the "Add Arc" tool or the `Space` key to connect elements. YAPNE supports multiple arc types:
    -   **Regular Arc:** The standard arc for consuming and producing tokens.
    -   **Inhibitor Arc:** Prevents a transition from firing if the source place has sufficient tokens.
    -   **Reset Arc:** Empties all tokens from a place when the transition fires.
    -   **Read Arc:** Checks for tokens without consuming them.
-   **Properties Panel:** Select any element to view and edit its properties (label, initial tokens, capacity, arc weight, etc.) in the "Model" tab of the sidebar.

#### 3.1.2 File Operations
Located in the "File" tab of the sidebar:
-   **Save/Load (JSON):** Save your model to a `.json` file or load a previously saved one.
-   **Export (PNML):** Export your model to the standard PNML format.
-   **Load (PNML):** Import models from `.pnml` files.

### 3.2 PNML Importer with Auto-Layout

YAPNE includes a PNML importer with an integrated layout algorithm to automatically arrange imported models.

-   **Accessing the Importer:** In the "File" tab, click the "Load (PNML)" button.
-   **Import Process:**
    1.  **Upload:** Drag-and-drop or browse for your `.pnml` file.
    2.  **Layout Settings:** Before importing, you can configure the layout algorithm. You can choose to preserve the positions from the file or apply the automatic layout. Settings include element spacing, size, centering, and overlap prevention.
    3.  **Preview:** A preview of the layout is shown on a mini-canvas.
    4.  **Import:** Click "Import to Editor" to load the model onto the main canvas.
-   **Layout Algorithm:** The importer uses an algorithm based on the principles of the "Simple Algorithm for Automatic Layout of BPMN Processes". It performs a modified topological sort to arrange elements in a logical flow from left to right, minimizing crossed arcs and applying heuristics for compaction and clarity.


### 3.3 Simulation

The "Simulation" tab provides all the tools needed to execute and analyze your model.

-   **Controls:**
    -   **Step:** Fires all enabled transition.
    -   **Auto Run:** Continuously fires enabled transitions with a configurable delay.
    -   **Reset:** Resets the simulation to its initial state, restoring token markings and data variables.
-   **State Display:**
    -   **Token Marking:** Shows the current token count for each place.
    -   **Data Values:** Displays the current values of all defined data variables.
    -   **Variable History:** Tracks and logs changes to data variables at each step of the simulation.

### 3.4 Data-Aware Petri Nets (DPN)

YAPNE's DPN extension allows for modeling with data variables and conditions.

#### 3.4.1 Data Variables
-   **Management:** In the "Model" tab, the "Data Variables" panel allows you to create, edit, and delete variables.
-   **Types:** Supported types include `int`, `float`, `string`, and `boolean`.

#### 3.4.2 Pre- and Postconditions
Data-aware transitions are controlled by expressions in their properties panel:
-   **Precondition (Guard):** A JavaScript expression that must evaluate to `true` for the transition to be enabled. It can reference any data variable (e.g., `counter > 0 && status === "active"`).
-   **Postcondition (Update):** Defines how data variables change when the transition fires.
    -   **Direct Assignment:** Use a prime (`'`) to denote the new value (e.g., `counter' = counter - 1;`).
    -   **Constraint-based Assignment:** Define a logical constraint for the new value (e.g., `x' > 0 && x' < x*2;`).

#### 3.4.3 Condition Evaluation with Z3
To handle complex constraint-based postconditions, YAPNE integrates the **Z3 SMT Solver**.
-   **How It Works:** When a postcondition contains a constraint (not a direct assignment), YAPNE's expression evaluation engine:
    1.  Parses the expression into a format Z3 understands.
    2.  Provides the solver with the current values of all non-primed variables.
    3.  Asks the solver to find a value for the primed variable(s) that satisfies the constraint.
    4.  If a range of valid values exists (for `int` or `float`), a random value within that range is chosen.
-   **Purpose:** This allows for non-deterministic modeling where the system, rather than the user, finds a valid subsequent state based on logical rules.

### 3.5 Soundness Checker

YAPNE includes a data-aware soundness checker to verify the correctness of your DPN models. It is inspired on the algorithm described in "Verification of data-aware process models: Checking soundness of data Petri nets" by Suvorov & Lomazova.

#### 3.5.1 The Verification Process
When you run the "Soundness Verification" from the "Model" tab, the tool performs a systematic check of your model's properties through **state-space exploration**.

1.  **State Definition:** A "state" in the context of a DPN is not just the token marking but a combination of **(Marking, Data Valuation)**. The marking is the distribution of tokens, and the data valuation is the set of current values for all data variables.
2.  **State-Space Exploration:** The verifier starts from the initial state `(Initial Marking, Initial Data Values)` and systematically explores all reachable states. It does this by:
    a.  Identifying all enabled transitions in the current state.
    b.  For each enabled transition, "firing" it to compute the next state. This involves updating both the token marking and the data valuation (using the postconditions).
    c.  The process is repeated for each new state discovered until no new states can be reached. This creates a Labeled Transition System (LTS), which is a graph of all possible states and the transitions between them.
3.  **Property Checking:** Once the state space is explored, the verifier checks it against three fundamental soundness properties:

    -   **P1: Reachability & Deadlock Freedom:** It verifies that every reachable state in the model can eventually reach a designated final state. If a state is found that has no enabled transitions and is not a final state, it is considered a **deadlock**.
    -   **P2: Proper Termination:** This property ensures that once the model reaches a final state, no transitions are still enabled. It checks for states where the token marking *strictly covers* the final marking (i.e., has more tokens) but still has enabled transitions, which would be an improper termination.
    -   **P3: No Dead Transitions:** The verifier checks if every single transition in the model can be fired in at least one reachable state. A transition that can never be fired under any circumstance is considered **dead** and usually indicates a flaw in the model's logic.

#### 3.5.2 Interpreting Results and Counterexamples
If the verifier finds a violation of any property, it declares the model **"Unsound"** and provides one or more **counterexamples**.

-   **What is a Counterexample?** A counterexample is a specific trace (a sequence of transition firings) from the initial state to a problematic state that demonstrates the flaw.
-   **Visualization in the Editor:** When you click to analyze a counterexample:
    1.  **Trace Highlighting:** The editor highlights the sequence of places and transitions that form the counterexample trace.
    2.  **Problematic State Display:** The verifier sets the editor's state to the problematic marking and data valuation found at the end of the trace.
    3.  **Reason and Value Display:** Special overlays appear on the canvas to explain *why* the state is problematic.
        -   For a **deadlock (P1)**, it will show which input places lack tokens or which data guards failed for all outgoing transitions.
        -   For an **improper termination (P2)**, it will highlight places with excess tokens.
        -   For a **dead transition (P3)**, it will highlight the transition and its input places, explaining why it could never be fired (e.g., "place X never has more than 2 tokens, but 3 are required").

#### 3.5.3 Data-Aware Verification Challenges

Data adds significant complexity to verification. A model can be unsound due to data-related issues even if the token flow appears correct.

A key example is the **unsatisfiable guard condition**. A transition might be considered "dead" (violating P3) not because its input places can never get enough tokens, but because its data-aware guard (precondition) can **never be satisfied**.

-   **How it's Detected:** During state-space exploration, the verifier tracks the range of all possible values for each data variable. When checking for dead transitions, if it finds a transition that has never been fired, it analyzes the reason. The tool will check if the transition's guard expression is logically impossible given the reachable data values. For instance, a guard `x > 10` is unsatisfiable if the analysis shows that the value of `x` can never exceed 5.
-   **Counterexample Feedback:** If an unsatisfiable guard is the cause of a dead transition, the counterexample will:
    -   Highlight the dead transition.
    -   Provide a reason in the overlay, such as: "Dead transition: data guard 'x > 10' is never satisfied."
    -   Display the computed range of the problematic variable(s) (e.g., "Variable 'x' was found to only have values between 0 and 5.").

