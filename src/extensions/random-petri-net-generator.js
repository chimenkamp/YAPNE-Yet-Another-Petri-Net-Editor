/**
 * Random Petri Net Generator Extension
 * 
 * This extension adds random Petri net generation capabilities to the Petri Net Editor.
 * It provides a configurable interface for creating nets with various complexities,
 * topologies, and characteristics, including soundness property checking.
 */

class PetriNetGenerator {
    /**
     * Constructor for the generator
     * @param {PetriNetApp} app - Reference to the main application
     */
    constructor(app) {
      this.app = app;
      this.dialog = null;
      

      this.options = {
        complexity: 'medium',    // 'simple', 'medium', 'complex'
        places: 5,               // Number of places to generate
        transitions: 5,          // Number of transitions to generate
        maxArcsPerNode: 3,       // Maximum arcs per node
        arcProbability: 0.7,     // Probability of creating an arc between eligible nodes
        initialTokens: {
          strategy: 'random',    // 'random', 'source_only', 'uniform'
          maxPerPlace: 3,        // Maximum tokens per place
          probability: 0.6       // Probability of a place having tokens
        },
        specialArcs: {
          inhibitor: 0.1,        // Probability of an arc being inhibitor
          reset: 0.05,           // Probability of an arc being reset
          read: 0.05             // Probability of an arc being read
        },
        topology: 'mixed',       // 'workflow', 'state_machine', 'marked_graph', 'free_choice', 'mixed'
        connectedness: 0.8,      // How connected the net should be (0-1)
        symmetry: 0.5,           // How symmetrical the net should be (0-1)
        useGridLayout: true,     // Whether to use a grid layout
        layoutSpacing: 120,      // Spacing between nodes in layout
        seed: null,              // Random seed for reproducibility
        enforceProperties: {     // Property enforcement options
          soundness: false,      // Whether to enforce soundness property
          liveness: false,       // Whether to enforce liveness property
          boundedness: false,    // Whether to enforce boundedness
          maxAttempts: 10        // Max attempts to generate a net with required properties
        }
      };
      

      this.complexityLevels = {
        simple: {
          places: { min: 3, max: 7 },
          transitions: { min: 2, max: 5 }
        },
        medium: {
          places: { min: 5, max: 15 },
          transitions: { min: 4, max: 12 }
        },
        complex: {
          places: { min: 10, max: 30 },
          transitions: { min: 8, max: 25 }
        }
      };
      

      this.topologyCharacteristics = {
        workflow: {
          description: "Directed path with clear start and end",
          maxArcsPerNode: 2,
          inhibitorAllowed: false,
          resetAllowed: false
        },
        state_machine: {
          description: "Each transition has exactly one input and one output",
          maxInputsPerTransition: 1,
          maxOutputsPerTransition: 1
        },
        marked_graph: {
          description: "Each place has exactly one input and one output",
          maxInputsPerPlace: 1,
          maxOutputsPerPlace: 1
        },
        free_choice: {
          description: "Shared places have identical output transitions",
          enforceSharedPlaceRule: true
        },
        mixed: {
          description: "No specific topology restrictions",
        }
      };
      
      this.initialize();
    }
    
    /**
     * Initialize the generator
     */
    initialize() {

      if (document.getElementById('btn-random-net')) {
        console.log("Random net generator button already exists");
        return;
      }
      

      this.addGeneratorButton();
      

      this.createDialog();
    }
    
    /**
     * Add the random net generator button to the toolbar
     */
    addGeneratorButton() {
      const toolbar = document.querySelector('.vertical-toolbar .toolbar-group');
      if (toolbar) {

        const autoLayoutBtn = document.getElementById('btn-auto-layout');
        
        if (autoLayoutBtn) {
          const randomNetBtn = document.createElement('button');
          randomNetBtn.id = 'btn-random-net';
          randomNetBtn.className = 'blue';
          randomNetBtn.title = 'Generate random Petri net';
          randomNetBtn.innerHTML = '🎲'; // Dice emoji
          

          autoLayoutBtn.insertAdjacentElement('afterend', randomNetBtn);
          

          randomNetBtn.addEventListener('click', () => this.openDialog());
        }
      }
    }
    
    /**
     * Create the dialog for configuring and generating random nets
     */
    createDialog() {

      this.dialog = document.createElement('div');
      this.dialog.className = 'modal-overlay hidden';
      this.dialog.id = 'random-net-dialog';
      
      const dialogContent = `
        <div class="modal-container">
          <div class="modal-header">
            <h2>Random Petri Net Generator</h2>
            <button class="close-btn" id="random-net-close">&times;</button>
          </div>
          <div class="modal-body">
            <div class="form-tab-container">
              <div class="form-tabs">
                <button class="form-tab active" data-tab="basic">Basic</button>
                <button class="form-tab" data-tab="topology">Topology</button>
                <button class="form-tab" data-tab="tokens">Tokens</button>
                <button class="form-tab" data-tab="advanced">Advanced</button>
              </div>
              
              <div class="form-tab-content active" data-tab="basic">
                <div class="form-group">
                  <label for="complexity">Complexity Level</label>
                  <select id="complexity">
                    <option value="simple">Simple (3-7 places, 2-5 transitions)</option>
                    <option value="medium" selected>Medium (5-15 places, 4-12 transitions)</option>
                    <option value="complex">Complex (10-30 places, 8-25 transitions)</option>
                    <option value="custom">Custom</option>
                  </select>
                </div>
                
                <div class="form-group custom-counts hidden">
                  <label for="place-count">Number of Places</label>
                  <input type="number" id="place-count" min="1" max="50" value="5">
                </div>
                
                <div class="form-group custom-counts hidden">
                  <label for="transition-count">Number of Transitions</label>
                  <input type="number" id="transition-count" min="1" max="50" value="5">
                </div>
                
                <div class="form-group">
                  <label for="max-arcs">Maximum Arcs per Node</label>
                  <input type="number" id="max-arcs" min="1" max="10" value="3">
                </div>
                
                <div class="form-group">
                  <label for="arc-probability">Arc Probability (0-1)</label>
                  <input type="number" id="arc-probability" min="0.1" max="1" step="0.1" value="0.7">
                  <small>Higher values create more densely connected nets</small>
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="topology">
                <div class="form-group">
                  <label for="topology">Petri Net Topology</label>
                  <select id="topology">
                    <option value="mixed" selected>Mixed (No specific restrictions)</option>
                    <option value="workflow">Workflow Net (Clear start/end)</option>
                    <option value="state_machine">State Machine (1 input/output per transition)</option>
                    <option value="marked_graph">Marked Graph (1 input/output per place)</option>
                    <option value="free_choice">Free Choice Net</option>
                  </select>
                </div>
                
                <div class="form-group">
                  <label for="connectedness">Connectedness (0-1)</label>
                  <input type="range" id="connectedness" min="0" max="1" step="0.1" value="0.8">
                  <span id="connectedness-value">0.8</span>
                  <small>How strongly connected the nodes should be</small>
                </div>
                
                <div class="form-group">
                  <label for="symmetry">Symmetry (0-1)</label>
                  <input type="range" id="symmetry" min="0" max="1" step="0.1" value="0.5">
                  <span id="symmetry-value">0.5</span>
                  <small>How symmetrical the net layout should be</small>
                </div>
                
                <div class="form-group">
                  <label>Special Arc Types:</label>
                  <div class="special-arc-controls">
                    <div>
                      <label for="inhibitor-prob">Inhibitor</label>
                      <input type="range" id="inhibitor-prob" min="0" max="0.5" step="0.05" value="0.1">
                      <span id="inhibitor-value">0.1</span>
                    </div>
                    <div>
                      <label for="reset-prob">Reset</label>
                      <input type="range" id="reset-prob" min="0" max="0.5" step="0.05" value="0.05">
                      <span id="reset-value">0.05</span>
                    </div>
                    <div>
                      <label for="read-prob">Read</label>
                      <input type="range" id="read-prob" min="0" max="0.5" step="0.05" value="0.05">
                      <span id="read-value">0.05</span>
                    </div>
                  </div>
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="tokens">
                <div class="form-group">
                  <label for="token-strategy">Initial Token Strategy</label>
                  <select id="token-strategy">
                    <option value="random" selected>Random (Based on probability)</option>
                    <option value="source_only">Source Places Only</option>
                    <option value="uniform">Uniform (All places get same tokens)</option>
                  </select>
                </div>
                
                <div class="form-group" id="token-probability-group">
                  <label for="token-probability">Token Probability (0-1)</label>
                  <input type="range" id="token-probability" min="0" max="1" step="0.1" value="0.6">
                  <span id="token-probability-value">0.6</span>
                  <small>Probability of a place having tokens</small>
                </div>
                
                <div class="form-group">
                  <label for="max-tokens">Maximum Tokens Per Place</label>
                  <input type="number" id="max-tokens" min="1" max="20" value="3">
                </div>
                
                <div class="form-group uniform-tokens hidden">
                  <label for="uniform-token-count">Tokens Per Place</label>
                  <input type="number" id="uniform-token-count" min="0" max="10" value="1">
                </div>
              </div>
              
              <div class="form-tab-content" data-tab="advanced">
                <div class="form-group">
                  <label for="use-grid">Use Grid Layout</label>
                  <input type="checkbox" id="use-grid" checked>
                  <small>Arranges nodes in a grid pattern</small>
                </div>
                
                <div class="form-group">
                  <label for="layout-spacing">Layout Spacing</label>
                  <input type="number" id="layout-spacing" min="50" max="300" value="120">
                  <small>Spacing between nodes in pixels</small>
                </div>
                
                <div class="form-group">
                  <label for="random-seed">Random Seed (optional)</label>
                  <input type="text" id="random-seed" placeholder="Leave empty for random">
                  <small>Using the same seed generates the same net</small>
                </div>
                
                <div class="form-group">
                  <label>Petri Net Properties:</label>
                  <div class="property-controls">
                    <div>
                      <input type="checkbox" id="enforce-soundness">
                      <label for="enforce-soundness">Enforce Soundness</label>
                      <small>Ensures the net is a sound workflow net (has proper termination)</small>
                    </div>
                    <div>
                      <input type="checkbox" id="enforce-liveness">
                      <label for="enforce-liveness">Enforce Liveness</label>
                      <small>Ensures all transitions can eventually fire</small>
                    </div>
                    <div>
                      <input type="checkbox" id="enforce-boundedness">
                      <label for="enforce-boundedness">Enforce Boundedness</label>
                      <small>Ensures places don't accumulate unlimited tokens</small>
                    </div>
                  </div>
                </div>
                
                <div class="form-group">
                  <div id="preview-container" style="height: 200px; background-color: #2E3440; border-radius: 4px; display: flex; align-items: center; justify-content: center;">
                    <p id="preview-placeholder">Generation preview will appear here</p>
                    <canvas id="preview-canvas" width="300" height="180" style="display: none;"></canvas>
                  </div>
                </div>
              </div>
            </div>
          </div>
          <div class="modal-footer">
            <button class="btn" id="btn-generate-preview">Generate Preview</button>
            <button class="btn" id="btn-generate-net">Generate Petri Net</button>
            <button class="btn" id="btn-reset-options">Reset Options</button>
          </div>
        </div>
      `;
      
      this.dialog.innerHTML = dialogContent;
      document.body.appendChild(this.dialog);
      

      this.setupEventListeners();
    }
    
    /**
     * Set up event listeners for the dialog
     */
    setupEventListeners() {

      const closeButton = document.getElementById('random-net-close');
      if (closeButton) {
        closeButton.addEventListener('click', () => this.closeDialog());
      }
      

      const tabButtons = document.querySelectorAll('.form-tab');
      tabButtons.forEach(button => {
        button.addEventListener('click', (e) => {
          const tab = e.target.getAttribute('data-tab');
          this.switchTab(tab);
        });
      });
      

      const complexitySelect = document.getElementById('complexity');
      if (complexitySelect) {
        complexitySelect.addEventListener('change', (e) => {
          const customFields = document.querySelectorAll('.custom-counts');
          customFields.forEach(field => {
            field.classList.toggle('hidden', e.target.value !== 'custom');
          });
          

          if (e.target.value !== 'custom') {
            const complexity = this.complexityLevels[e.target.value];
            const placeCount = document.getElementById('place-count');
            const transitionCount = document.getElementById('transition-count');
            
            if (placeCount && complexity) {
              placeCount.value = Math.floor((complexity.places.min + complexity.places.max) / 2);
            }
            
            if (transitionCount && complexity) {
              transitionCount.value = Math.floor((complexity.transitions.min + complexity.transitions.max) / 2);
            }
          }
        });
      }
      

      const tokenStrategySelect = document.getElementById('token-strategy');
      if (tokenStrategySelect) {
        tokenStrategySelect.addEventListener('change', (e) => {
          const uniformFields = document.querySelectorAll('.uniform-tokens');
          uniformFields.forEach(field => {
            field.classList.toggle('hidden', e.target.value !== 'uniform');
          });
          
          const probabilityGroup = document.getElementById('token-probability-group');
          if (probabilityGroup) {
            probabilityGroup.classList.toggle('hidden', e.target.value === 'uniform');
          }
        });
      }
      

      const soundnessCheckbox = document.getElementById('enforce-soundness');
      if (soundnessCheckbox) {
        soundnessCheckbox.addEventListener('change', (e) => {
          if (e.target.checked) {

            const topologySelect = document.getElementById('topology');
            if (topologySelect && topologySelect.value !== 'workflow') {
              topologySelect.value = 'workflow';
              alert("Setting topology to 'workflow' as required for soundness property.");
            }
          }
        });
      }
      

      const rangeSliders = {
        'connectedness': 'connectedness-value',
        'symmetry': 'symmetry-value',
        'inhibitor-prob': 'inhibitor-value',
        'reset-prob': 'reset-value',
        'read-prob': 'read-value',
        'token-probability': 'token-probability-value'
      };
      
      for (const [sliderId, valueId] of Object.entries(rangeSliders)) {
        const slider = document.getElementById(sliderId);
        const valueDisplay = document.getElementById(valueId);
        
        if (slider && valueDisplay) {
          slider.addEventListener('input', (e) => {
            valueDisplay.textContent = e.target.value;
          });
        }
      }
      

      const previewButton = document.getElementById('btn-generate-preview');
      if (previewButton) {
        previewButton.addEventListener('click', () => this.generatePreview());
      }
      

      const generateButton = document.getElementById('btn-generate-net');
      if (generateButton) {
        generateButton.addEventListener('click', () => this.generateNet());
      }
      

      const resetButton = document.getElementById('btn-reset-options');
      if (resetButton) {
        resetButton.addEventListener('click', () => this.resetOptions());
      }
    }
    
    /**
     * Open the generator dialog
     */
    openDialog() {
      this.dialog.classList.remove('hidden');
    }
    
    /**
     * Close the generator dialog
     */
    closeDialog() {
      this.dialog.classList.add('hidden');
    }
    
    /**
     * Switch between tabs in the dialog
     * @param {string} tabId - ID of the tab to switch to
     */
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
    
    /**
     * Collect options from the form inputs
     * @returns {Object} Options for generating the Petri net
     */
    collectOptions() {
      const options = { ...this.options }; // Start with defaults
      

      const complexity = document.getElementById('complexity').value;
      options.complexity = complexity;
      
      if (complexity === 'custom') {
        options.places = parseInt(document.getElementById('place-count').value, 10);
        options.transitions = parseInt(document.getElementById('transition-count').value, 10);
      } else {

        const range = this.complexityLevels[complexity];
        const randomIntInRange = (min, max) => 
          Math.floor(Math.random() * (max - min + 1) + min);
        
        options.places = randomIntInRange(range.places.min, range.places.max);
        options.transitions = randomIntInRange(range.transitions.min, range.transitions.max);
      }
      
      options.maxArcsPerNode = parseInt(document.getElementById('max-arcs').value, 10);
      options.arcProbability = parseFloat(document.getElementById('arc-probability').value);
      

      options.topology = document.getElementById('topology').value;
      options.connectedness = parseFloat(document.getElementById('connectedness').value);
      options.symmetry = parseFloat(document.getElementById('symmetry').value);
      
      options.specialArcs = {
        inhibitor: parseFloat(document.getElementById('inhibitor-prob').value),
        reset: parseFloat(document.getElementById('reset-prob').value),
        read: parseFloat(document.getElementById('read-prob').value)
      };
      

      options.initialTokens = {
        strategy: document.getElementById('token-strategy').value,
        maxPerPlace: parseInt(document.getElementById('max-tokens').value, 10),
        probability: parseFloat(document.getElementById('token-probability').value)
      };
      
      if (options.initialTokens.strategy === 'uniform') {
        options.initialTokens.uniformCount = parseInt(document.getElementById('uniform-token-count').value, 10);
      }
      

      options.useGridLayout = document.getElementById('use-grid').checked;
      options.layoutSpacing = parseInt(document.getElementById('layout-spacing').value, 10);
      

      options.enforceProperties = {
        soundness: document.getElementById('enforce-soundness').checked,
        liveness: document.getElementById('enforce-liveness').checked,
        boundedness: document.getElementById('enforce-boundedness').checked,
        maxAttempts: 10
      };
      
      const seedValue = document.getElementById('random-seed').value.trim();
      options.seed = seedValue === '' ? null : seedValue;
      
      return options;
    }
    
    /**
     * Reset form to default options
     */
    resetOptions() {

      document.getElementById('complexity').value = 'medium';
      document.querySelectorAll('.custom-counts').forEach(field => {
        field.classList.add('hidden');
      });
      

      document.getElementById('place-count').value = 5;
      document.getElementById('transition-count').value = 5;
      document.getElementById('max-arcs').value = 3;
      document.getElementById('arc-probability').value = 0.7;
      

      document.getElementById('topology').value = 'mixed';
      document.getElementById('connectedness').value = 0.8;
      document.getElementById('connectedness-value').textContent = '0.8';
      document.getElementById('symmetry').value = 0.5;
      document.getElementById('symmetry-value').textContent = '0.5';
      

      document.getElementById('inhibitor-prob').value = 0.1;
      document.getElementById('inhibitor-value').textContent = '0.1';
      document.getElementById('reset-prob').value = 0.05;
      document.getElementById('reset-value').textContent = '0.05';
      document.getElementById('read-prob').value = 0.05;
      document.getElementById('read-value').textContent = '0.05';
      

      document.getElementById('token-strategy').value = 'random';
      document.getElementById('token-probability-group').classList.remove('hidden');
      document.getElementById('token-probability').value = 0.6;
      document.getElementById('token-probability-value').textContent = '0.6';
      document.getElementById('max-tokens').value = 3;
      document.getElementById('uniform-token-count').value = 1;
      document.querySelectorAll('.uniform-tokens').forEach(field => {
        field.classList.add('hidden');
      });
      

      document.getElementById('use-grid').checked = true;
      document.getElementById('layout-spacing').value = 120;
      document.getElementById('random-seed').value = '';
      

      document.getElementById('enforce-soundness').checked = false;
      document.getElementById('enforce-liveness').checked = false;
      document.getElementById('enforce-boundedness').checked = false;
      

      const previewCanvas = document.getElementById('preview-canvas');
      const previewPlaceholder = document.getElementById('preview-placeholder');
      if (previewCanvas && previewPlaceholder) {
        previewCanvas.style.display = 'none';
        previewPlaceholder.style.display = 'block';
      }
    }
    
    /**
     * Generate a preview of the Petri net
     */
    generatePreview() {
      const options = this.collectOptions();
      const previewCanvas = document.getElementById('preview-canvas');
      const previewPlaceholder = document.getElementById('preview-placeholder');
      
      if (!previewCanvas || !previewPlaceholder) return;
      
      try {

        const previewNet = this.generatePetriNet(options, true);
        

        previewCanvas.style.display = 'block';
        previewPlaceholder.style.display = 'none';
        

        const renderer = new PetriNetRenderer(previewCanvas, previewNet);
        

        renderer.zoomFactor = 0.5;

        const width = previewCanvas.width;
        const height = previewCanvas.height;
        renderer.panOffset = {
          x: width / 2 - 100,
          y: height / 2 - 100
        };
        

        renderer.render();
      } catch (error) {
        console.error("Error generating preview:", error);
        alert(`Error generating preview: ${error.message}`);
        

        previewCanvas.style.display = 'none';
        previewPlaceholder.style.display = 'block';
        previewPlaceholder.textContent = 'Error generating preview';
      }
    }
    /**
   * Generate a Petri net with the collected options
   */
  generateNet() {
    try {
      const options = this.collectOptions();
      

      if (options.enforceProperties.soundness && options.topology !== 'workflow') {
        options.topology = 'workflow';
        alert("Setting topology to 'workflow' as required for soundness property.");
      }
      

      const petriNet = this.generatePetriNet(options);
      

      this.app.resetPetriNet();
      

      this.app.api.petriNet = petriNet;
      

      this.app.editor = this.app.api.attachEditor(this.app.canvas);
      

      this.app.editor.setOnSelectCallback(this.app.handleElementSelected.bind(this.app));
      this.app.editor.setOnChangeCallback(this.app.handleNetworkChanged.bind(this.app));
      this.app.editor.setSnapToGrid(this.app.gridEnabled);
      this.app.editor.setMode('select');
      this.app.updateActiveButton('btn-select');
      

      this.app.editor.render();
      this.app.updateTokensDisplay();
      this.app.updateZoomDisplay();
      this.app.propertiesPanel.innerHTML = '<p>No element selected.</p>';
      

      this.closeDialog();
    } catch (error) {
      console.error("Error generating Petri net:", error);
      alert(`Error generating Petri net: ${error.message}`);
    }
  }
  
  /**
   * Generate a PetriNet object based on the specified options
   * @param {Object} options - Generation options
   * @param {boolean} isPreview - Whether this is for preview only
   * @param {number} attemptsCount - Number of generation attempts (for property enforcement)
   * @returns {PetriNet} The generated Petri net
   */
  generatePetriNet(options, isPreview = false, attemptsCount = 0) {

    let random;
    if (options.seed) {
      random = this.createSeededRandom(options.seed);
    } else {
      random = Math.random;
    }
    

    const petriNet = new PetriNet(
      this.app.api.generateUUID(),
      `Random Petri Net ${new Date().toLocaleString()}`,
      `Generated with complexity: ${options.complexity}, topology: ${options.topology}`
    );
    

    const placeIds = [];
    for (let i = 0; i < options.places; i++) {
      const id = this.app.api.generateUUID();
      const position = this.calculateNodePosition(i, options, 'place', random);
      
      const place = new Place(
        id,
        position,
        `P${i + 1}`,
        0 // Initial tokens will be set later
      );
      
      petriNet.addPlace(place);
      placeIds.push(id);
    }
    

    const transitionIds = [];
    for (let i = 0; i < options.transitions; i++) {
      const id = this.app.api.generateUUID();
      const position = this.calculateNodePosition(i, options, 'transition', random);
      
      const transition = new Transition(
        id,
        position,
        `T${i + 1}`,
        1, // Default priority
        0  // Default delay
      );
      
      petriNet.addTransition(transition);
      transitionIds.push(id);
    }
    

    this.generateArcs(petriNet, placeIds, transitionIds, options, random);
    

    this.setInitialTokens(petriNet, placeIds, options, random);
    

    petriNet.updateEnabledTransitions();
    

    if (options.enforceProperties.soundness || 
        options.enforceProperties.liveness ||
        options.enforceProperties.boundedness) {
      

      const propertiesResult = this.checkPetriNetProperties(petriNet, options);
      

      if (!propertiesResult.satisfiesAll && !isPreview && attemptsCount < options.enforceProperties.maxAttempts) {
        console.log(`Attempt ${attemptsCount + 1}: Net doesn't satisfy required properties, generating again...`);
        attemptsCount++;
        return this.generatePetriNet(options, isPreview, attemptsCount);
      }
      

      petriNet.description += '\nProperty checks: ' + 
        (propertiesResult.isSoundWorkflowNet ? '✓ Sound' : '✗ Not Sound') +
        (options.enforceProperties.liveness ? (propertiesResult.isLive ? ', ✓ Live' : ', ✗ Not Live') : '') +
        (options.enforceProperties.boundedness ? (propertiesResult.isBounded ? ', ✓ Bounded' : ', ✗ Not Bounded') : '');
    }
    
    return petriNet;
  }
  
  /**
   * Calculate position for a node based on the layout strategy
   * @param {number} index - Index of the node
   * @param {Object} options - Generation options
   * @param {string} type - Type of node ('place' or 'transition')
   * @param {Function} random - Random function to use
   * @returns {Object} Position {x, y}
   */
  calculateNodePosition(index, options, type, random) {
    const spacing = options.layoutSpacing;
    
    if (options.useGridLayout) {

      let cols, rows;
      
      if (type === 'place') {

        cols = Math.ceil(Math.sqrt(options.places));
        rows = Math.ceil(options.places / cols);
        

        const col = index % cols;
        const row = Math.floor(index / cols);
        

        const jitter = (1 - options.symmetry) * spacing * 0.4;
        const jitterX = jitter > 0 ? (random() * jitter * 2 - jitter) : 0;
        const jitterY = jitter > 0 ? (random() * jitter * 2 - jitter) : 0;
        

        return {
          x: 100 + col * spacing + jitterX,
          y: 100 + row * spacing + jitterY
        };
      } else {

        cols = Math.ceil(Math.sqrt(options.transitions));
        rows = Math.ceil(options.transitions / cols);
        

        const col = index % cols;
        const row = Math.floor(index / cols);
        

        const jitter = (1 - options.symmetry) * spacing * 0.4;
        const jitterX = jitter > 0 ? (random() * jitter * 2 - jitter) : 0;
        const jitterY = jitter > 0 ? (random() * jitter * 2 - jitter) : 0;
        


        if (options.topology === 'workflow') {
          return {
            x: 100 + spacing/2 + col * spacing + jitterX,
            y: 100 + spacing/2 + row * spacing + jitterY
          };
        } else {

          const baseX = 100 + spacing + (options.places > options.transitions ? spacing : 0);
          return {
            x: baseX + col * spacing + jitterX,
            y: 100 + row * spacing + jitterY
          };
        }
      }
    } else {

      const totalNodes = options.places + options.transitions;
      let angle, radius;
      
      if (options.topology === 'workflow') {

        if (type === 'place') {
          const totalPlaces = options.places;
          const layerRadius = 150;
          const angleStep = (2 * Math.PI) / totalPlaces;
          angle = index * angleStep;
          radius = layerRadius;
        } else {
          const totalTransitions = options.transitions;
          const layerRadius = 250;
          const angleStep = (2 * Math.PI) / totalTransitions;
          angle = index * angleStep + (Math.PI / totalTransitions); // Offset transitions
          radius = layerRadius;
        }
      } else {

        const angleStep = (2 * Math.PI) / totalNodes;
        const nodeIndex = type === 'place' ? index : index + options.places;
        angle = nodeIndex * angleStep;
        radius = 200;
      }
      

      const radiusJitter = (1 - options.symmetry) * radius * 0.2;
      const angleJitter = (1 - options.symmetry) * (Math.PI / 12);
      
      const jitteredRadius = radius + (radiusJitter > 0 ? (random() * radiusJitter * 2 - radiusJitter) : 0);
      const jitteredAngle = angle + (angleJitter > 0 ? (random() * angleJitter * 2 - angleJitter) : 0);
      
      return {
        x: 300 + jitteredRadius * Math.cos(jitteredAngle),
        y: 300 + jitteredRadius * Math.sin(jitteredAngle)
      };
    }
  }
  
  /**
   * Generate arcs between places and transitions
   * @param {PetriNet} petriNet - The Petri net to add arcs to
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Array<string>} transitionIds - Array of transition IDs
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   */
  generateArcs(petriNet, placeIds, transitionIds, options, random) {

    const nodeArcs = new Map();
    placeIds.concat(transitionIds).forEach(id => nodeArcs.set(id, { inputs: 0, outputs: 0 }));
    

    if (options.topology === 'workflow') {

      const sourceId = placeIds[0];
      

      const sinkId = placeIds[placeIds.length - 1];
      

      this.createWorkflowPath(petriNet, placeIds, transitionIds, sourceId, sinkId, options, random, nodeArcs);
    } else {

      this.createArcsForTopology(petriNet, placeIds, transitionIds, options, random, nodeArcs);
    }
    

    this.ensureConnectedness(petriNet, placeIds, transitionIds, options, random, nodeArcs);
    

    this.createSpecialArcs(petriNet, options, random);
  }
  
  /**
   * Create a workflow path from source to sink
   * @param {PetriNet} petriNet - The Petri net
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Array<string>} transitionIds - Array of transition IDs
   * @param {string} sourceId - ID of the source place
   * @param {string} sinkId - ID of the sink place
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   * @param {Map} nodeArcs - Map of node IDs to arc counts
   */
  createWorkflowPath(petriNet, placeIds, transitionIds, sourceId, sinkId, options, random, nodeArcs) {

    let currentId = sourceId;
    const path = [currentId];
    const usedIds = new Set([currentId]);
    

    while (currentId !== sinkId) {
      let nextId;
      
      if (placeIds.includes(currentId)) {


        const availableTransitions = transitionIds.filter(id => !usedIds.has(id));
        
        if (availableTransitions.length > 0) {
          nextId = availableTransitions[Math.floor(random() * availableTransitions.length)];
        } else {

          nextId = transitionIds[Math.floor(random() * transitionIds.length)];
        }
      } else {


        const pathLength = path.length;
        const minPathLength = Math.min(placeIds.length + transitionIds.length - 2, Math.max(4, placeIds.length));
        
        if (pathLength >= minPathLength && random() < 0.7) {
          nextId = sinkId;
        } else {

          const availablePlaces = placeIds.filter(id => !usedIds.has(id) && id !== sinkId);
          
          if (availablePlaces.length > 0) {
            nextId = availablePlaces[Math.floor(random() * availablePlaces.length)];
          } else {

            const otherPlaces = placeIds.filter(id => id !== sinkId);
            
            if (otherPlaces.length > 0) {
              nextId = otherPlaces[Math.floor(random() * otherPlaces.length)];
            } else {

              nextId = sinkId;
            }
          }
        }
      }
      

      const arcId = this.app.api.generateUUID();
      const arc = new Arc(arcId, currentId, nextId, 1, "regular");
      petriNet.addArc(arc);
      

      nodeArcs.get(currentId).outputs++;
      nodeArcs.get(nextId).inputs++;
      

      currentId = nextId;
      path.push(currentId);
      usedIds.add(currentId);
    }
    

    const unusedPlaces = placeIds.filter(id => !usedIds.has(id));
    const unusedTransitions = transitionIds.filter(id => !usedIds.has(id));
    

    unusedPlaces.forEach(placeId => {

      const pathTransitions = path.filter(id => transitionIds.includes(id));
      
      if (pathTransitions.length > 0) {
        const transitionId = pathTransitions[Math.floor(random() * pathTransitions.length)];
        

        if (random() < 0.5 && nodeArcs.get(transitionId).outputs < options.maxArcsPerNode) {

          const arcId = this.app.api.generateUUID();
          const arc = new Arc(arcId, transitionId, placeId, 1, "regular");
          petriNet.addArc(arc);
          
          nodeArcs.get(transitionId).outputs++;
          nodeArcs.get(placeId).inputs++;
        } else if (nodeArcs.get(placeId).outputs < options.maxArcsPerNode) {

          const arcId = this.app.api.generateUUID();
          const arc = new Arc(arcId, placeId, transitionId, 1, "regular");
          petriNet.addArc(arc);
          
          nodeArcs.get(placeId).outputs++;
          nodeArcs.get(transitionId).inputs++;
        }
      }
    });
    
    unusedTransitions.forEach(transitionId => {

      const pathPlaces = path.filter(id => placeIds.includes(id));
      
      if (pathPlaces.length > 0) {
        const placeId = pathPlaces[Math.floor(random() * pathPlaces.length)];
        

        if (random() < 0.5 && nodeArcs.get(placeId).outputs < options.maxArcsPerNode) {

          const arcId = this.app.api.generateUUID();
          const arc = new Arc(arcId, placeId, transitionId, 1, "regular");
          petriNet.addArc(arc);
          
          nodeArcs.get(placeId).outputs++;
          nodeArcs.get(transitionId).inputs++;
        } else if (nodeArcs.get(transitionId).outputs < options.maxArcsPerNode) {

          const arcId = this.app.api.generateUUID();
          const arc = new Arc(arcId, transitionId, placeId, 1, "regular");
          petriNet.addArc(arc);
          
          nodeArcs.get(transitionId).outputs++;
          nodeArcs.get(placeId).inputs++;
        }
      }
    });
  }
  
  /**
   * Create arcs based on the selected topology
   * @param {PetriNet} petriNet - The Petri net
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Array<string>} transitionIds - Array of transition IDs
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   * @param {Map} nodeArcs - Map of node IDs to arc counts
   */
  createArcsForTopology(petriNet, placeIds, transitionIds, options, random, nodeArcs) {

    const topology = options.topology;
    

    const potentialArcs = [];
    

    for (const placeId of placeIds) {
      for (const transitionId of transitionIds) {

        let canCreate = true;
        
        if (topology === 'state_machine' && nodeArcs.get(transitionId).inputs > 0) {

          canCreate = false;
        } else if (topology === 'marked_graph' && nodeArcs.get(placeId).outputs > 0) {

          canCreate = false;
        }
        
        if (canCreate) {
          potentialArcs.push({
            from: placeId,
            to: transitionId,
            probability: random()
          });
        }
      }
    }
    

    for (const transitionId of transitionIds) {
      for (const placeId of placeIds) {

        let canCreate = true;
        
        if (topology === 'state_machine' && nodeArcs.get(transitionId).outputs > 0) {

          canCreate = false;
        } else if (topology === 'marked_graph' && nodeArcs.get(placeId).inputs > 0) {

          canCreate = false;
        }
        
        if (canCreate) {
          potentialArcs.push({
            from: transitionId,
            to: placeId,
            probability: random()
          });
        }
      }
    }
    

    potentialArcs.sort((a, b) => a.probability - b.probability);
    

    for (const arc of potentialArcs) {
      const fromNode = arc.from;
      const toNode = arc.to;
      

      if (nodeArcs.get(fromNode).outputs >= options.maxArcsPerNode ||
          nodeArcs.get(toNode).inputs >= options.maxArcsPerNode) {
        continue;
      }
      

      if (arc.probability < options.arcProbability) {

        if (topology === 'free_choice') {

          const sourceIsPlace = placeIds.includes(fromNode);
          
          if (sourceIsPlace) {

            const hasViolation = Array.from(petriNet.arcs.values()).some(existingArc => 
              existingArc.source === fromNode && 
              existingArc.target !== toNode &&
              Array.from(petriNet.arcs.values()).some(otherArc => 
                otherArc.target === existingArc.target && otherArc.source !== fromNode
              )
            );
            

            if (hasViolation) {
              continue;
            }
          }
        }
        

        const arcId = this.app.api.generateUUID();
        const newArc = new Arc(arcId, fromNode, toNode, 1, "regular");
        
        if (petriNet.addArc(newArc)) {

          nodeArcs.get(fromNode).outputs++;
          nodeArcs.get(toNode).inputs++;
        }
      }
    }
  }
  
  /**
   * Ensure the Petri net has the minimum connectedness
   * @param {PetriNet} petriNet - The Petri net
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Array<string>} transitionIds - Array of transition IDs
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   * @param {Map} nodeArcs - Map of node IDs to arc counts
   */
  ensureConnectedness(petriNet, placeIds, transitionIds, options, random, nodeArcs) {

    const disconnectedNodes = [];
    
    for (const nodeId of [...placeIds, ...transitionIds]) {
      const arcCounts = nodeArcs.get(nodeId);
      
      if (arcCounts.inputs === 0 && arcCounts.outputs === 0) {
        disconnectedNodes.push(nodeId);
      }
    }
    

    for (const nodeId of disconnectedNodes) {
      const isPlace = placeIds.includes(nodeId);
      

      let connected = false;
      
      if (isPlace) {

        for (const transitionId of transitionIds) {
          if (nodeArcs.get(transitionId).inputs < options.maxArcsPerNode && random() < options.connectedness) {

            const arcId = this.app.api.generateUUID();
            const arc = new Arc(arcId, nodeId, transitionId, 1, "regular");
            
            if (petriNet.addArc(arc)) {
              nodeArcs.get(nodeId).outputs++;
              nodeArcs.get(transitionId).inputs++;
              connected = true;
              break;
            }
          }
        }
        

        if (!connected) {
          for (const transitionId of transitionIds) {
            if (nodeArcs.get(transitionId).outputs < options.maxArcsPerNode && random() < options.connectedness) {

              const arcId = this.app.api.generateUUID();
              const arc = new Arc(arcId, transitionId, nodeId, 1, "regular");
              
              if (petriNet.addArc(arc)) {
                nodeArcs.get(nodeId).inputs++;
                nodeArcs.get(transitionId).outputs++;
                connected = true;
                break;
              }
            }
          }
        }
      } else {

        for (const placeId of placeIds) {
          if (nodeArcs.get(placeId).inputs < options.maxArcsPerNode && random() < options.connectedness) {

            const arcId = this.app.api.generateUUID();
            const arc = new Arc(arcId, nodeId, placeId, 1, "regular");
            
            if (petriNet.addArc(arc)) {
              nodeArcs.get(nodeId).outputs++;
              nodeArcs.get(placeId).inputs++;
              connected = true;
              break;
            }
          }
        }
        

        if (!connected) {
          for (const placeId of placeIds) {
            if (nodeArcs.get(placeId).outputs < options.maxArcsPerNode && random() < options.connectedness) {

              const arcId = this.app.api.generateUUID();
              const arc = new Arc(arcId, placeId, nodeId, 1, "regular");
              
              if (petriNet.addArc(arc)) {
                nodeArcs.get(nodeId).inputs++;
                nodeArcs.get(placeId).outputs++;
                connected = true;
                break;
              }
            }
          }
        }
      }
    }
    

    if (options.connectedness > 0.7) {
      this.connectIsolatedSubgraphs(petriNet, placeIds, transitionIds, options, random, nodeArcs);
    }
  }
  
  /**
   * Connect isolated subgraphs in the Petri net
   * @param {PetriNet} petriNet - The Petri net
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Array<string>} transitionIds - Array of transition IDs
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   * @param {Map} nodeArcs - Map of node IDs to arc counts
   */
  connectIsolatedSubgraphs(petriNet, placeIds, transitionIds, options, random, nodeArcs) {

    const connectionAttempts = Math.floor(options.connectedness * 10);
    
    for (let i = 0; i < connectionAttempts; i++) {

      const placeId = placeIds[Math.floor(random() * placeIds.length)];
      const transitionId = transitionIds[Math.floor(random() * transitionIds.length)];
      

      if (nodeArcs.get(placeId).outputs >= options.maxArcsPerNode || 
          nodeArcs.get(transitionId).inputs >= options.maxArcsPerNode) {
        continue;
      }
      

      if (random() < 0.5) {

        const arcId = this.app.api.generateUUID();
        const arc = new Arc(arcId, placeId, transitionId, 1, "regular");
        
        if (petriNet.addArc(arc)) {
          nodeArcs.get(placeId).outputs++;
          nodeArcs.get(transitionId).inputs++;
        }
      } else {


        if (nodeArcs.get(transitionId).outputs >= options.maxArcsPerNode || 
            nodeArcs.get(placeId).inputs >= options.maxArcsPerNode) {
          continue;
        }
        
        const arcId = this.app.api.generateUUID();
        const arc = new Arc(arcId, transitionId, placeId, 1, "regular");
        
        if (petriNet.addArc(arc)) {
          nodeArcs.get(transitionId).outputs++;
          nodeArcs.get(placeId).inputs++;
        }
      }
    }
  }
  
  /**
   * Convert some regular arcs to special types
   * @param {PetriNet} petriNet - The Petri net
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   */
  createSpecialArcs(petriNet, options, random) {

    if (options.topology === 'workflow') {
      return;
    }
    

    for (const [id, arc] of petriNet.arcs) {

      const sourceIsPlace = petriNet.places.has(arc.source);
      const targetIsTransition = petriNet.transitions.has(arc.target);
      
      if (!sourceIsPlace || !targetIsTransition) continue;
      

      let arcType = "regular";
      

      const r = random();
      if (r < options.specialArcs.inhibitor) {
        arcType = "inhibitor";
      } else if (r < options.specialArcs.inhibitor + options.specialArcs.reset) {
        arcType = "reset";
      } else if (r < options.specialArcs.inhibitor + options.specialArcs.reset + options.specialArcs.read) {
        arcType = "read";
      }
      

      if (arcType !== "regular") {
        arc.type = arcType;
        

        if (arcType === "inhibitor" || arcType === "read") {
          arc.weight = 1; // These typically have weight 1
        }
        

        switch (arcType) {
          case "inhibitor":
            arc.label = "I";
            break;
          case "reset":
            arc.label = "R";
            break;
          case "read":
            arc.label = "?";
            break;
        }
      }
    }
  }
  
  /**
   * Set initial token distribution
   * @param {PetriNet} petriNet - The Petri net
   * @param {Array<string>} placeIds - Array of place IDs
   * @param {Object} options - Generation options
   * @param {Function} random - Random function to use
   */
  setInitialTokens(petriNet, placeIds, options, random) {
    const strategy = options.initialTokens.strategy;
    
    if (strategy === 'uniform') {

      const tokenCount = options.initialTokens.uniformCount || 1;
      
      for (const placeId of placeIds) {
        const place = petriNet.places.get(placeId);
        if (place) {
          place.tokens = tokenCount;
        }
      }
    } else if (strategy === 'source_only') {

      for (const placeId of placeIds) {
        const place = petriNet.places.get(placeId);
        if (!place) continue;
        

        const isSource = !Array.from(petriNet.arcs.values())
          .some(arc => arc.target === placeId);
        
        if (isSource) {

          place.tokens = Math.floor(random() * options.initialTokens.maxPerPlace) + 1;
        } else {
          place.tokens = 0;
        }
      }
    } else {

      for (const placeId of placeIds) {
        const place = petriNet.places.get(placeId);
        if (!place) continue;
        
        if (random() < options.initialTokens.probability) {

          place.tokens = Math.floor(random() * options.initialTokens.maxPerPlace) + 1;
        } else {
          place.tokens = 0;
        }
      }
    }
    

    if (options.topology === 'workflow' && placeIds.length > 0) {
      const sourcePlace = petriNet.places.get(placeIds[0]);
      if (sourcePlace && sourcePlace.tokens === 0) {
        sourcePlace.tokens = 1;
      }
    }
  }
  
  /**
   * Checks if a Petri net satisfies certain properties like soundness, liveness, and boundedness
   * @param {PetriNet} petriNet - The Petri net to check
   * @param {Object} options - Generation options with enforceProperties settings
   * @returns {Object} Results of property checks
   */
  checkPetriNetProperties(petriNet, options) {

    const result = {
      isSoundWorkflowNet: false,
      isLive: false,
      isBounded: false,
      satisfiesAll: false
    };
    

    const isWorkflowNet = this.isWorkflowNet(petriNet);
    

    if (isWorkflowNet && options.enforceProperties.soundness) {
      result.isSoundWorkflowNet = this.isSoundWorkflowNet(petriNet);
    }
    

    if (options.enforceProperties.liveness) {
      result.isLive = this.isLiveNet(petriNet);
    }
    

    if (options.enforceProperties.boundedness) {
      result.isBounded = this.isBoundedNet(petriNet);
    }
    

    result.satisfiesAll = 
      (!options.enforceProperties.soundness || result.isSoundWorkflowNet) &&
      (!options.enforceProperties.liveness || result.isLive) &&
      (!options.enforceProperties.boundedness || result.isBounded);
    
    return result;
  }

  /**
   * Checks if a Petri net is a workflow net
   * @param {PetriNet} petriNet - The Petri net to check
   * @returns {boolean} True if it's a workflow net
   */
  isWorkflowNet(petriNet) {

    let sourcePlace = null;
    let sinkPlace = null;
    
    for (const [id, place] of petriNet.places) {

      const hasIncoming = Array.from(petriNet.arcs.values())
        .some(arc => arc.target === id);
      

      const hasOutgoing = Array.from(petriNet.arcs.values())
        .some(arc => arc.source === id);
      
      if (!hasIncoming && hasOutgoing) {
        if (sourcePlace) return false; // Only one source allowed
        sourcePlace = id;
      }
      
      if (!hasOutgoing && hasIncoming) {
        if (sinkPlace) return false; // Only one sink allowed
        sinkPlace = id;
      }
    }
    

    if (!sourcePlace || !sinkPlace) return false;
    


    for (const [id] of petriNet.places) {
      if (id === sourcePlace || id === sinkPlace) continue;
      
      const hasConnection = Array.from(petriNet.arcs.values())
        .some(arc => arc.source === id || arc.target === id);
      
      if (!hasConnection) return false;
    }
    
    for (const [id] of petriNet.transitions) {
      const hasConnection = Array.from(petriNet.arcs.values())
        .some(arc => arc.source === id || arc.target === id);
      
      if (!hasConnection) return false;
    }
    
    return true;
  }

  /**
   * Checks if a workflow net is sound
   * @param {PetriNet} petriNet - The Petri net to check
   * @returns {boolean} True if it's a sound workflow net
   */
  isSoundWorkflowNet(petriNet) {


    if (!this.isWorkflowNet(petriNet)) return false;
    


    

    const simulationNet = this.clonePetriNetForSimulation(petriNet);
    

    for (const [id, place] of simulationNet.places) {
      const hasIncoming = Array.from(simulationNet.arcs.values())
        .some(arc => arc.target === id);
      
      if (!hasIncoming) {
        place.tokens = 1; // Set initial token
        break;
      }
    }
    

    let changed = true;
    const maxIterations = 100; // Prevent infinite loops
    let iterations = 0;
    
    const transitionsFired = new Set();
    
    while (changed && iterations < maxIterations) {
      changed = false;
      iterations++;
      

      for (const [id] of simulationNet.transitions) {
        if (simulationNet.isTransitionEnabled(id)) {
          simulationNet.fireTransition(id);
          transitionsFired.add(id);
          changed = true;
        }
      }
    }
    

    return transitionsFired.size === simulationNet.transitions.size;
  }

  /**
   * Checks if a Petri net is live
   * @param {PetriNet} petriNet - The Petri net to check
   * @returns {boolean} True if it's a live Petri net
   */
  isLiveNet(petriNet) {

    const simulationNet = this.clonePetriNetForSimulation(petriNet);
    

    for (const [id, place] of simulationNet.places) {
      const hasIncoming = Array.from(simulationNet.arcs.values())
        .some(arc => arc.target === id);
      
      if (!hasIncoming) {
        place.tokens = 1; // Set initial token
      }
    }
    

    let hasTokens = false;
    for (const [, place] of simulationNet.places) {
      if (place.tokens > 0) {
        hasTokens = true;
        break;
      }
    }
    
    if (!hasTokens && simulationNet.places.size > 0) {
      const firstPlace = simulationNet.places.values().next().value;
      if (firstPlace) firstPlace.tokens = 1;
    }
    

    let changed = true;
    const maxIterations = 100;
    let iterations = 0;
    
    const transitionsFired = new Set();
    
    while (changed && iterations < maxIterations) {
      changed = false;
      iterations++;
      

      for (const [id] of simulationNet.transitions) {
        if (simulationNet.isTransitionEnabled(id)) {
          simulationNet.fireTransition(id);
          transitionsFired.add(id);
          changed = true;
        }
      }
    }
    

    return transitionsFired.size === simulationNet.transitions.size;
  }

  /**
   * Checks if a Petri net is bounded
   * @param {PetriNet} petriNet - The Petri net to check
   * @returns {boolean} True if it's a bounded Petri net
   */
  isBoundedNet(petriNet) {


    const simulationNet = this.clonePetriNetForSimulation(petriNet);
    

    for (const [id, place] of simulationNet.places) {
      const hasIncoming = Array.from(simulationNet.arcs.values())
        .some(arc => arc.target === id);
      
      if (!hasIncoming) {
        place.tokens = 1;
      }
    }
    

    const maxIterations = 50;
    const maxTokensPerPlace = 5; // Threshold for unboundedness detection
    
    for (let i = 0; i < maxIterations; i++) {

      simulationNet.updateEnabledTransitions();
      

      for (const [, place] of simulationNet.places) {
        if (place.tokens > maxTokensPerPlace) {
          return false; // Likely unbounded
        }
      }
      

      let fired = false;
      for (const [id] of simulationNet.transitions) {
        if (simulationNet.isTransitionEnabled(id)) {
          simulationNet.fireTransition(id);
          fired = true;
          break;
        }
      }
      
      if (!fired) break; // No more enabled transitions
    }
    
    return true; // Likely bounded
  }

  /**
   * Creates a clone of the Petri net for simulation purposes
   * @param {PetriNet} petriNet - The original Petri net
   * @returns {PetriNet} A cloned Petri net for simulation
   */
  clonePetriNetForSimulation(petriNet) {

    const clone = new PetriNet(
      petriNet.id,
      petriNet.name,
      petriNet.description
    );
    

    for (const [id, place] of petriNet.places) {
      const placeClone = new Place(
        id,
        { x: place.position.x, y: place.position.y },
        place.label,
        place.tokens,
        place.capacity
      );
      clone.places.set(id, placeClone);
    }
    

    for (const [id, transition] of petriNet.transitions) {
      const transitionClone = new Transition(
        id,
        { x: transition.position.x, y: transition.position.y },
        transition.label,
        transition.priority,
        transition.delay
      );
      clone.transitions.set(id, transitionClone);
    }
    

    for (const [id, arc] of petriNet.arcs) {
      const arcClone = new Arc(
        id,
        arc.source,
        arc.target,
        arc.weight,
        arc.type,
        [...arc.points],
        arc.label
      );
      clone.arcs.set(id, arcClone);
    }
    
    return clone;
  }
  
  /**
   * Create a seeded random number generator
   * @param {string|number} seed - Seed for the random number generator
   * @returns {Function} A function that returns random numbers between 0 and 1
   */
  createSeededRandom(seed) {

    let numericSeed;
    if (typeof seed === 'string') {

      numericSeed = Array.from(seed).reduce(
        (acc, char) => (acc * 31 + char.charCodeAt(0)) & 0x7fffffff, 0
      );
    } else {
      numericSeed = seed;
    }
    

    return function() {
      numericSeed = (numericSeed * 9301 + 49297) % 233280;
      return numericSeed / 233280;
    };
  }
}


document.addEventListener('DOMContentLoaded', () => {

  const initTimer = setInterval(() => {
    if (window.petriApp) {
      window.petriNetGenerator = new PetriNetGenerator(window.petriApp);
      clearInterval(initTimer);
      console.log("Petri Net Generator extension loaded");
    }
  }, 100);
});