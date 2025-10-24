/**
 * WCAG 2.0 Canvas Accessibility Layer
 * 
 * This module provides comprehensive accessibility features for the canvas-based
 * Petri Net Editor, following WCAG 2.0 guidelines including:
 * - Perceivable: Alternative text, keyboard navigation
 * - Operable: Keyboard-only operation, focus management
 * - Understandable: Clear instructions, consistent behavior
 * - Robust: Screen reader compatibility, ARIA support
 */

class CanvasAccessibilityLayer {
  constructor(app) {
    this.app = app;
    this.canvas = app.canvas;
    this.isEnabled = true;
    
    // Virtual focus for canvas elements
    this.focusedElement = null;
    this.focusHistory = [];
    
    // Announcement queue for screen readers
    this.announcementQueue = [];
    
    // Keyboard navigation state
    this.keyboardMode = false;
    this.gridNavigationEnabled = false;
    
    // High contrast mode
    this.highContrastMode = false;
    
    // Screen reader mode
    this.screenReaderMode = false;
    
    this.initialize();
  }

  initialize() {
    this.createAccessibilityStructure();
    this.setupKeyboardNavigation();
    this.setupScreenReaderSupport();
    this.setupFocusManagement();
    this.addAccessibilityControls();
    this.createSkipLinks();
    this.enhanceExistingElements();
    
    console.log('✅ WCAG 2.0 Accessibility Layer initialized');
  }

  /**
   * Create invisible DOM structure that mirrors canvas content for screen readers
   */
  createAccessibilityStructure() {
    // Main accessibility container
    const container = document.createElement('div');
    container.id = 'canvas-accessibility-layer';
    container.className = 'sr-only';
    container.setAttribute('role', 'application');
    container.setAttribute('aria-label', 'Petri Net Editor Canvas');
    
    // Live region for announcements
    const liveRegion = document.createElement('div');
    liveRegion.id = 'accessibility-announcer';
    liveRegion.setAttribute('role', 'status');
    liveRegion.setAttribute('aria-live', 'polite');
    liveRegion.setAttribute('aria-atomic', 'true');
    liveRegion.className = 'sr-only';
    
    // Assertive announcer for important updates
    const assertiveRegion = document.createElement('div');
    assertiveRegion.id = 'accessibility-announcer-assertive';
    assertiveRegion.setAttribute('role', 'alert');
    assertiveRegion.setAttribute('aria-live', 'assertive');
    assertiveRegion.setAttribute('aria-atomic', 'true');
    assertiveRegion.className = 'sr-only';
    
    // Canvas description
    const description = document.createElement('div');
    description.id = 'canvas-description';
    description.textContent = 'Interactive Petri Net Editor. Use Tab to navigate elements, Arrow keys to move, Enter to select, and keyboard shortcuts for actions.';
    
    container.appendChild(description);
    document.body.appendChild(container);
    document.body.appendChild(liveRegion);
    document.body.appendChild(assertiveRegion);
    
    // Make canvas focusable and add description
    this.canvas.setAttribute('tabindex', '0');
    this.canvas.setAttribute('role', 'img');
    this.canvas.setAttribute('aria-label', 'Petri Net Canvas - Press Tab to navigate elements');
    this.canvas.setAttribute('aria-describedby', 'canvas-description');
    
    this.liveRegion = liveRegion;
    this.assertiveRegion = assertiveRegion;
    this.accessibilityContainer = container;
  }

  /**
   * Setup comprehensive keyboard navigation
   */
  setupKeyboardNavigation() {
    const handlers = {
      // Tab navigation
      'Tab': (e) => this.handleTabNavigation(e),
      
      // Arrow key navigation
      'ArrowUp': (e) => this.handleArrowNavigation(e, 0, -1),
      'ArrowDown': (e) => this.handleArrowNavigation(e, 0, 1),
      'ArrowLeft': (e) => this.handleArrowNavigation(e, -1, 0),
      'ArrowRight': (e) => this.handleArrowNavigation(e, 1, 0),
      
      // Action keys
      'Enter': (e) => this.handleEnterKey(e),
      'Space': (e) => this.handleSpaceKey(e),
      'Delete': (e) => this.handleDeleteKey(e),
      'Backspace': (e) => this.handleBackspaceKey(e),
      'Escape': (e) => this.handleEscapeKey(e),
      
      // Tool shortcuts (with Alt modifier for accessibility)
      'p': (e) => this.handleToolShortcut(e, 'place'),
      't': (e) => this.handleToolShortcut(e, 'transition'),
      'a': (e) => this.handleToolShortcut(e, 'arc'),
      's': (e) => this.handleToolShortcut(e, 'select'),
      
      // Zoom shortcuts
      '+': (e) => this.handleZoomIn(e),
      '=': (e) => this.handleZoomIn(e),
      '-': (e) => this.handleZoomOut(e),
      '0': (e) => this.handleResetView(e),
      
      // Token manipulation
      'i': (e) => this.handleIncrementTokens(e),
      'd': (e) => this.handleDecrementTokens(e),
      
      // Simulation
      'r': (e) => this.handleRunSimulation(e),
      
      // Help
      'h': (e) => this.handleShowHelp(e),
      '?': (e) => this.handleShowHelp(e),
    };

    this.canvas.addEventListener('keydown', (e) => {
      const key = e.key;
      const handler = handlers[key];
      
      if (handler) {
        // Enable keyboard mode indicator
        this.keyboardMode = true;
        document.body.classList.add('keyboard-navigation-active');
        
        handler(e);
      }
    });

    // Track when user switches to mouse
    this.canvas.addEventListener('mousedown', () => {
      this.keyboardMode = false;
      document.body.classList.remove('keyboard-navigation-active');
    });
  }

  /**
   * Handle Tab navigation through canvas elements
   */
  handleTabNavigation(e) {
    e.preventDefault();
    
    const elements = this.getAllNavigableElements();
    if (elements.length === 0) {
      this.announce('No elements to navigate. Press Alt+P to add a place, or Alt+T to add a transition.');
      return;
    }
    
    const currentIndex = this.focusedElement 
      ? elements.findIndex(el => el.id === this.focusedElement.id)
      : -1;
    
    const nextIndex = e.shiftKey 
      ? (currentIndex - 1 + elements.length) % elements.length
      : (currentIndex + 1) % elements.length;
    
    this.setFocusedElement(elements[nextIndex]);
  }

  /**
   * Handle arrow key navigation for moving elements or navigating
   */
  handleArrowNavigation(e, dx, dy) {
    if (!this.focusedElement) {
      // Navigate to nearest element in direction
      e.preventDefault();
      this.navigateInDirection(dx, dy);
      return;
    }
    
    e.preventDefault();
    
    const moveDistance = e.shiftKey ? 1 : 10; // Fine control with Shift
    const element = this.getElementFromPetriNet(this.focusedElement);
    
    if (!element) return;
    
    element.position.x += dx * moveDistance;
    element.position.y += dy * moveDistance;
    
    this.app.editor.render();
    this.announce(`Moved ${this.getElementDescription(this.focusedElement)} to position ${Math.round(element.position.x)}, ${Math.round(element.position.y)}`);
  }

  /**
   * Navigate to nearest element in a direction
   */
  navigateInDirection(dx, dy) {
    const elements = this.getAllNavigableElements();
    if (elements.length === 0) return;
    
    const currentPos = this.focusedElement 
      ? this.getElementFromPetriNet(this.focusedElement).position
      : { x: this.canvas.width / 2, y: this.canvas.height / 2 };
    
    // Find nearest element in direction
    let nearest = null;
    let minDistance = Infinity;
    
    elements.forEach(el => {
      const element = this.getElementFromPetriNet(el);
      const relX = element.position.x - currentPos.x;
      const relY = element.position.y - currentPos.y;
      
      // Check if in right direction
      const inDirection = (dx * relX + dy * relY) > 0;
      if (!inDirection) return;
      
      const distance = Math.sqrt(relX * relX + relY * relY);
      if (distance < minDistance) {
        minDistance = distance;
        nearest = el;
      }
    });
    
    if (nearest) {
      this.setFocusedElement(nearest);
    }
  }

  /**
   * Handle Enter key - select/activate element
   */
  handleEnterKey(e) {
    e.preventDefault();
    
    if (!this.focusedElement) {
      this.announce('No element focused. Use Tab to navigate to elements.');
      return;
    }
    
    // Simulate click on element
    this.app.editor.selectedElement = this.focusedElement;
    this.app.handleElementSelected(this.focusedElement.id, this.focusedElement.type);
    this.app.editor.render();
    
    this.announceAssertive(`Selected ${this.getElementDescription(this.focusedElement)}`);
  }

  /**
   * Handle Space key - context actions
   */
  handleSpaceKey(e) {
    if (this.focusedElement && this.focusedElement.type === 'transition') {
      e.preventDefault();
      
      // Fire transition
      const transitionId = this.focusedElement.id;
      if (this.app.api.petriNet.isTransitionEnabled(transitionId)) {
        this.app.api.petriNet.fireTransition(transitionId);
        this.app.editor.render();
        this.app.updateTokensDisplay();
        this.announceAssertive(`Fired transition ${this.focusedElement.label || this.focusedElement.id}`);
      } else {
        this.announce('Transition is not enabled');
      }
    }
  }

  /**
   * Handle Delete/Backspace - delete focused element
   */
  handleDeleteKey(e) {
    this.deleteCurrentElement(e);
  }

  handleBackspaceKey(e) {
    this.deleteCurrentElement(e);
  }

  deleteCurrentElement(e) {
    if (!this.focusedElement) return;
    
    e.preventDefault();
    const desc = this.getElementDescription(this.focusedElement);
    
    if (this.focusedElement.type === 'place') {
      this.app.api.removePlace(this.focusedElement.id);
    } else if (this.focusedElement.type === 'transition') {
      this.app.api.removeTransition(this.focusedElement.id);
    } else if (this.focusedElement.type === 'arc') {
      this.app.api.removeArc(this.focusedElement.id);
    }
    
    this.focusedElement = null;
    this.app.editor.render();
    this.announceAssertive(`Deleted ${desc}`);
  }

  /**
   * Handle Escape - clear selection
   */
  handleEscapeKey(e) {
    e.preventDefault();
    
    if (this.focusedElement) {
      this.announce('Cleared selection');
      this.focusedElement = null;
      this.app.editor.selectedElement = null;
      this.app.editor.render();
    }
  }

  /**
   * Handle tool shortcuts
   */
  handleToolShortcut(e, tool) {
    if (!e.altKey) return;
    
    e.preventDefault();
    
    const toolMap = {
      'place': 'btn-add-place',
      'transition': 'btn-add-transition',
      'arc': 'btn-add-arc',
      'select': 'btn-select'
    };
    
    const button = document.getElementById(toolMap[tool]);
    if (button) {
      button.click();
      this.announce(`Activated ${tool} tool. Click on canvas to place.`);
    }
  }

  /**
   * Zoom controls
   */
  handleZoomIn(e) {
    if (e.ctrlKey || e.metaKey) {
      e.preventDefault();
      const centerX = this.canvas.width / 2;
      const centerY = this.canvas.height / 2;
      this.app.editor.renderer.adjustZoom(1.2, centerX, centerY);
      this.app.editor.render();
      this.app.updateZoomDisplay();
      this.announce(`Zoomed in to ${Math.round(this.app.editor.renderer.zoomFactor * 100)}%`);
    }
  }

  handleZoomOut(e) {
    if (e.ctrlKey || e.metaKey) {
      e.preventDefault();
      const centerX = this.canvas.width / 2;
      const centerY = this.canvas.height / 2;
      this.app.editor.renderer.adjustZoom(0.8, centerX, centerY);
      this.app.editor.render();
      this.app.updateZoomDisplay();
      this.announce(`Zoomed out to ${Math.round(this.app.editor.renderer.zoomFactor * 100)}%`);
    }
  }

  handleResetView(e) {
    if (e.ctrlKey || e.metaKey) {
      e.preventDefault();
      this.app.editor.resetView();
      this.app.updateZoomDisplay();
      this.announce('Reset view to 100%');
    }
  }

  /**
   * Token manipulation
   */
  handleIncrementTokens(e) {
    if (!this.focusedElement || this.focusedElement.type !== 'place') return;
    
    e.preventDefault();
    const place = this.app.api.petriNet.places.get(this.focusedElement.id);
    if (place) {
      place.tokens++;
      this.app.editor.render();
      this.app.updateTokensDisplay();
      this.announce(`Increased tokens to ${place.tokens}`);
    }
  }

  handleDecrementTokens(e) {
    if (!this.focusedElement || this.focusedElement.type !== 'place') return;
    
    e.preventDefault();
    const place = this.app.api.petriNet.places.get(this.focusedElement.id);
    if (place && place.tokens > 0) {
      place.tokens--;
      this.app.editor.render();
      this.app.updateTokensDisplay();
      this.announce(`Decreased tokens to ${place.tokens}`);
    }
  }

  /**
   * Simulation shortcuts
   */
  handleRunSimulation(e) {
    if (e.ctrlKey || e.metaKey) {
      e.preventDefault();
      const stepButton = document.getElementById('btn-step');
      if (stepButton) {
        stepButton.click();
        this.announce('Executed simulation step');
      }
    }
  }

  /**
   * Help
   */
  handleShowHelp(e) {
    e.preventDefault();
    this.showAccessibilityHelp();
  }

  /**
   * Setup screen reader support
   */
  setupScreenReaderSupport() {
    // Update live region when network changes
    const originalOnChange = this.app.editor.onChangeCallback;
    this.app.editor.setOnChangeCallback(() => {
      if (originalOnChange) originalOnChange();
      this.updateAccessibilityTree();
    });

    // Announce when elements are selected
    const originalOnSelect = this.app.editor.onSelectCallback;
    this.app.editor.setOnSelectCallback((id, type) => {
      if (originalOnSelect) originalOnSelect(id, type);
      
      if (id && type) {
        const element = { id, type };
        this.announce(`Selected ${this.getElementDescription(element)}`);
      }
    });
  }

  /**
   * Update accessibility tree to mirror canvas state
   */
  updateAccessibilityTree() {
    const container = this.accessibilityContainer;
    
    // Clear existing elements (keep description)
    while (container.children.length > 1) {
      container.removeChild(container.lastChild);
    }
    
    // Create accessible list of elements
    const elementsList = document.createElement('ul');
    elementsList.setAttribute('role', 'list');
    elementsList.setAttribute('aria-label', 'Petri Net Elements');
    
    // Add places
    this.app.api.petriNet.places.forEach(place => {
      const item = this.createAccessibleElement(place, 'place');
      elementsList.appendChild(item);
    });
    
    // Add transitions
    this.app.api.petriNet.transitions.forEach(transition => {
      const item = this.createAccessibleElement(transition, 'transition');
      elementsList.appendChild(item);
    });
    
    // Add arcs
    this.app.api.petriNet.arcs.forEach(arc => {
      const item = this.createAccessibleElement(arc, 'arc');
      elementsList.appendChild(item);
    });
    
    container.appendChild(elementsList);
    
    // Update canvas label with count
    const placeCount = this.app.api.petriNet.places.size;
    const transitionCount = this.app.api.petriNet.transitions.size;
    const arcCount = this.app.api.petriNet.arcs.size;
    
    this.canvas.setAttribute('aria-label', 
      `Petri Net Canvas with ${placeCount} places, ${transitionCount} transitions, and ${arcCount} arcs. Press Tab to navigate.`
    );
  }

  /**
   * Create accessible DOM element for canvas element
   */
  createAccessibleElement(element, type) {
    const item = document.createElement('li');
    item.setAttribute('role', 'listitem');
    item.setAttribute('data-element-id', element.id);
    item.setAttribute('data-element-type', type);
    
    const description = this.getElementDetailedDescription(element, type);
    item.textContent = description;
    
    return item;
  }

  /**
   * Focus management
   */
  setupFocusManagement() {
    // Visual focus indicator
    this.app.editor.renderer.renderFocusIndicator = (ctx, element) => {
      if (!this.focusedElement || element.id !== this.focusedElement.id) return;
      
      ctx.save();
      ctx.strokeStyle = '#0066CC';
      ctx.lineWidth = 3;
      ctx.setLineDash([5, 5]);
      
      if (element.type === 'place') {
        ctx.beginPath();
        ctx.arc(element.position.x, element.position.y, element.radius + 5, 0, 2 * Math.PI);
        ctx.stroke();
      } else if (element.type === 'transition') {
        ctx.strokeRect(
          element.position.x - element.width / 2 - 5,
          element.position.y - element.height / 2 - 5,
          element.width + 10,
          element.height + 10
        );
      }
      
      ctx.restore();
    };
    
    // Enhance renderer to draw focus indicators
    const originalRender = this.app.editor.render.bind(this.app.editor);
    this.app.editor.render = () => {
      originalRender();
      
      if (this.focusedElement && this.keyboardMode) {
        const ctx = this.canvas.getContext('2d');
        const element = this.getElementFromPetriNet(this.focusedElement);
        if (element) {
          this.app.editor.renderer.renderFocusIndicator(ctx, element);
        }
      }
    };
  }

  /**
   * Set focused element and announce
   */
  setFocusedElement(element) {
    this.focusedElement = element;
    this.focusHistory.push(element);
    
    const description = this.getElementDetailedDescription(
      this.getElementFromPetriNet(element),
      element.type
    );
    
    this.announce(description);
    this.app.editor.render();
  }

  /**
   * Get all navigable elements
   */
  getAllNavigableElements() {
    const elements = [];
    
    this.app.api.petriNet.places.forEach(place => {
      elements.push({ id: place.id, type: 'place', position: place.position });
    });
    
    this.app.api.petriNet.transitions.forEach(transition => {
      elements.push({ id: transition.id, type: 'transition', position: transition.position });
    });
    
    // Sort by position (top to bottom, left to right)
    elements.sort((a, b) => {
      const pos1 = this.getElementFromPetriNet(a).position;
      const pos2 = this.getElementFromPetriNet(b).position;
      
      if (Math.abs(pos1.y - pos2.y) < 50) {
        return pos1.x - pos2.x;
      }
      return pos1.y - pos2.y;
    });
    
    return elements;
  }

  /**
   * Get element from Petri Net
   */
  getElementFromPetriNet(element) {
    if (element.type === 'place') {
      return this.app.api.petriNet.places.get(element.id);
    } else if (element.type === 'transition') {
      return this.app.api.petriNet.transitions.get(element.id);
    } else if (element.type === 'arc') {
      return this.app.api.petriNet.arcs.get(element.id);
    }
    return null;
  }

  /**
   * Get element description
   */
  getElementDescription(element) {
    const el = this.getElementFromPetriNet(element);
    if (!el) return 'Unknown element';
    
    if (element.type === 'place') {
      return `Place ${el.label || el.id} with ${el.tokens} token${el.tokens !== 1 ? 's' : ''}`;
    } else if (element.type === 'transition') {
      const enabled = el.isEnabled ? 'enabled' : 'disabled';
      return `Transition ${el.label || el.id}, ${enabled}`;
    } else if (element.type === 'arc') {
      return `Arc from ${el.source} to ${el.target}, weight ${el.weight}`;
    }
  }

  /**
   * Get detailed element description
   */
  getElementDetailedDescription(element, type) {
    if (!element) return 'Unknown element';
    
    if (type === 'place') {
      let desc = `Place ${element.label || element.id}, ${element.tokens} token${element.tokens !== 1 ? 's' : ''}`;
      if (element.capacity !== null) {
        desc += `, capacity ${element.capacity}`;
      }
      desc += `, at position ${Math.round(element.position.x)}, ${Math.round(element.position.y)}`;
      return desc;
    } else if (type === 'transition') {
      const enabled = element.isEnabled ? 'enabled' : 'disabled';
      let desc = `Transition ${element.label || element.id}, ${enabled}`;
      if (element.priority > 1) {
        desc += `, priority ${element.priority}`;
      }
      desc += `, at position ${Math.round(element.position.x)}, ${Math.round(element.position.y)}`;
      return desc;
    } else if (type === 'arc') {
      return `Arc from ${element.source} to ${element.target}, weight ${element.weight}, type ${element.type}`;
    }
  }

  /**
   * Announce to screen readers (polite)
   */
  announce(message, delay = 100) {
    setTimeout(() => {
      this.liveRegion.textContent = message;
    }, delay);
  }

  /**
   * Announce to screen readers (assertive)
   */
  announceAssertive(message, delay = 100) {
    setTimeout(() => {
      this.assertiveRegion.textContent = message;
    }, delay);
  }

  /**
   * Add accessibility controls to UI
   */
  addAccessibilityControls() {
    const controlsHTML = `
      <div class="accessibility-controls" id="accessibility-controls">
        <button class="accessibility-toggle" id="accessibility-menu-toggle" 
                aria-label="Accessibility Options" 
                aria-expanded="false"
                aria-controls="accessibility-menu">
          ♿ Accessibility
        </button>
        <div class="accessibility-menu" id="accessibility-menu" role="menu" hidden>
          <div class="accessibility-menu-item" role="menuitem">
            <label>
              <input type="checkbox" id="high-contrast-toggle" />
              High Contrast Mode
            </label>
          </div>
          <div class="accessibility-menu-item" role="menuitem">
            <label>
              <input type="checkbox" id="screen-reader-mode-toggle" />
              Enhanced Screen Reader Mode
            </label>
          </div>
          <div class="accessibility-menu-item" role="menuitem">
            <label>
              <input type="checkbox" id="keyboard-hints-toggle" checked />
              Show Keyboard Hints
            </label>
          </div>
          <div class="accessibility-menu-item" role="menuitem">
            <button id="accessibility-help-button" class="btn">
              View Keyboard Shortcuts
            </button>
          </div>
          <div class="accessibility-menu-item" role="menuitem">
            <button id="describe-canvas-button" class="btn">
              Describe Canvas Content
            </button>
          </div>
        </div>
      </div>
    `;
    
    const container = document.querySelector('.canvas-container');
    container.insertAdjacentHTML('afterbegin', controlsHTML);
    
    // Setup event handlers
    this.setupAccessibilityControls();
  }

  setupAccessibilityControls() {
    const toggle = document.getElementById('accessibility-menu-toggle');
    const menu = document.getElementById('accessibility-menu');
    
    toggle.addEventListener('click', () => {
      const isExpanded = toggle.getAttribute('aria-expanded') === 'true';
      toggle.setAttribute('aria-expanded', !isExpanded);
      menu.hidden = isExpanded;
    });
    
    // High contrast mode
    document.getElementById('high-contrast-toggle').addEventListener('change', (e) => {
      this.toggleHighContrast(e.target.checked);
    });
    
    // Screen reader mode
    document.getElementById('screen-reader-mode-toggle').addEventListener('change', (e) => {
      this.toggleScreenReaderMode(e.target.checked);
    });
    
    // Keyboard hints
    document.getElementById('keyboard-hints-toggle').addEventListener('change', (e) => {
      document.body.classList.toggle('show-keyboard-hints', e.target.checked);
    });
    
    // Help button
    document.getElementById('accessibility-help-button').addEventListener('click', () => {
      this.showAccessibilityHelp();
    });
    
    // Describe canvas
    document.getElementById('describe-canvas-button').addEventListener('click', () => {
      this.describeCanvasContent();
    });
  }

  /**
   * Toggle high contrast mode
   */
  toggleHighContrast(enabled) {
    this.highContrastMode = enabled;
    document.body.classList.toggle('high-contrast-mode', enabled);
    this.app.editor.render();
    this.announce(enabled ? 'High contrast mode enabled' : 'High contrast mode disabled');
  }

  /**
   * Toggle enhanced screen reader mode
   */
  toggleScreenReaderMode(enabled) {
    this.screenReaderMode = enabled;
    
    if (enabled) {
      this.updateAccessibilityTree();
      this.announce('Enhanced screen reader mode enabled. Canvas elements are now listed in a screen reader accessible format.');
    } else {
      this.announce('Enhanced screen reader mode disabled');
    }
  }

  /**
   * Describe canvas content
   */
  describeCanvasContent() {
    const places = this.app.api.petriNet.places.size;
    const transitions = this.app.api.petriNet.transitions.size;
    const arcs = this.app.api.petriNet.arcs.size;
    const totalTokens = Array.from(this.app.api.petriNet.places.values())
      .reduce((sum, p) => sum + p.tokens, 0);
    
    const description = `The Petri Net contains ${places} place${places !== 1 ? 's' : ''}, ${transitions} transition${transitions !== 1 ? 's' : ''}, and ${arcs} arc${arcs !== 1 ? 's' : ''}. Total tokens: ${totalTokens}. Press Tab to navigate through elements.`;
    
    this.announceAssertive(description);
  }

  /**
   * Show accessibility help dialog
   */
  showAccessibilityHelp() {
    const helpDialog = document.createElement('div');
    helpDialog.className = 'accessibility-help-dialog';
    helpDialog.setAttribute('role', 'dialog');
    helpDialog.setAttribute('aria-labelledby', 'accessibility-help-title');
    helpDialog.setAttribute('aria-modal', 'true');
    
    helpDialog.innerHTML = `
      <div class="accessibility-help-content">
        <h2 id="accessibility-help-title">Keyboard Shortcuts & Accessibility</h2>
        <button class="close-btn" aria-label="Close dialog">×</button>
        
        <div class="help-sections">
          <section>
            <h3>Navigation</h3>
            <dl>
              <dt>Tab / Shift+Tab</dt>
              <dd>Navigate through elements</dd>
              
              <dt>Arrow Keys</dt>
              <dd>Move focused element (hold Shift for fine control)</dd>
              
              <dt>Enter</dt>
              <dd>Select focused element</dd>
              
              <dt>Escape</dt>
              <dd>Clear selection</dd>
            </dl>
          </section>
          
          <section>
            <h3>Tools (Alt + Key)</h3>
            <dl>
              <dt>Alt+P</dt>
              <dd>Add Place tool</dd>
              
              <dt>Alt+T</dt>
              <dd>Add Transition tool</dd>
              
              <dt>Alt+A</dt>
              <dd>Add Arc tool</dd>
              
              <dt>Alt+S</dt>
              <dd>Select tool</dd>
            </dl>
          </section>
          
          <section>
            <h3>Actions</h3>
            <dl>
              <dt>Space</dt>
              <dd>Fire focused transition</dd>
              
              <dt>Delete / Backspace</dt>
              <dd>Delete focused element</dd>
              
              <dt>I</dt>
              <dd>Increment tokens (place)</dd>
              
              <dt>D</dt>
              <dd>Decrement tokens (place)</dd>
              
              <dt>Ctrl+R</dt>
              <dd>Run simulation step</dd>
            </dl>
          </section>
          
          <section>
            <h3>View Controls</h3>
            <dl>
              <dt>Ctrl/Cmd + Plus</dt>
              <dd>Zoom in</dd>
              
              <dt>Ctrl/Cmd + Minus</dt>
              <dd>Zoom out</dd>
              
              <dt>Ctrl/Cmd + 0</dt>
              <dd>Reset zoom</dd>
            </dl>
          </section>
          
          <section>
            <h3>Help</h3>
            <dl>
              <dt>? or H</dt>
              <dd>Show this help dialog</dd>
            </dl>
          </section>
        </div>
        
        <div class="help-footer">
          <button class="btn btn-primary" id="close-help-dialog">Close</button>
        </div>
      </div>
    `;
    
    document.body.appendChild(helpDialog);
    
    // Focus trap
    const closeBtn = helpDialog.querySelector('.close-btn');
    const closeButton = helpDialog.querySelector('#close-help-dialog');
    
    const closeDialog = () => {
      document.body.removeChild(helpDialog);
      this.canvas.focus();
    };
    
    closeBtn.addEventListener('click', closeDialog);
    closeButton.addEventListener('click', closeDialog);
    
    // ESC to close
    helpDialog.addEventListener('keydown', (e) => {
      if (e.key === 'Escape') {
        closeDialog();
      }
    });
    
    // Focus the close button
    closeButton.focus();
  }

  /**
   * Create skip links for keyboard navigation
   */
  createSkipLinks() {
    const skipLinks = document.createElement('div');
    skipLinks.className = 'skip-links';
    skipLinks.innerHTML = `
      <a href="#petri-canvas" class="skip-link">Skip to canvas</a>
      <a href="#properties-content" class="skip-link">Skip to properties</a>
      <a href="#btn-select" class="skip-link">Skip to tools</a>
    `;
    
    document.body.insertBefore(skipLinks, document.body.firstChild);
  }

  /**
   * Enhance existing elements with ARIA attributes
   */
  enhanceExistingElements() {
    // Enhance all buttons with proper labels
    document.querySelectorAll('button[id^="btn-"]').forEach(btn => {
      if (!btn.hasAttribute('aria-label') && btn.title) {
        btn.setAttribute('aria-label', btn.title);
      }
    });
    
    // Enhance panels
    const propertiesPanel = document.getElementById('properties-content');
    if (propertiesPanel) {
      propertiesPanel.setAttribute('role', 'region');
      propertiesPanel.setAttribute('aria-label', 'Element Properties');
    }
    
    // Enhance sidebar tabs
    document.querySelectorAll('.sidebar-tab').forEach(tab => {
      tab.setAttribute('role', 'tab');
      const tabName = tab.getAttribute('data-tab');
      tab.setAttribute('aria-label', `${tabName.charAt(0).toUpperCase() + tabName.slice(1)} tab`);
    });
    
    // Enhance zoom display
    const zoomDisplay = document.getElementById('zoom-display');
    if (zoomDisplay) {
      zoomDisplay.setAttribute('role', 'status');
      zoomDisplay.setAttribute('aria-label', 'Current zoom level');
      zoomDisplay.setAttribute('aria-live', 'polite');
    }
    
    // Enhance tokens display
    const tokensDisplay = document.getElementById('tokens-display');
    if (tokensDisplay) {
      tokensDisplay.setAttribute('role', 'status');
      tokensDisplay.setAttribute('aria-label', 'Total tokens in network');
      tokensDisplay.setAttribute('aria-live', 'polite');
    }
  }
}

export default CanvasAccessibilityLayer;
