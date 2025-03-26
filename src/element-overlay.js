/**
 * ElementOverlay class for the Petri Net Editor
 * Adds directional arrows around selected elements to create new connected elements
 */
class ElementOverlay {
  constructor(editor, api) {
    this.editor = editor;
    this.api = api;
    this.canvas = editor.canvas;
    this.isVisible = false;
    this.selectedElement = null;
    this.selectedElementType = null;
    this.arrowSize = 7;
    this.arrowDistance = 50;
    this.arrowColor = '#81A1C1'; // Nord theme blue
    this.arrowHoverColor = '#88C0D0'; // Nord theme lighter blue
    this.arrowStrokeColor = '#2E3440'; // Nord theme background
    this.arrowLineWidth = 2;
    this.newElementDistance = 120; // Fixed distance to create new element
    
    // Container for arrow elements
    this.arrowContainer = document.createElement('div');
    this.arrowContainer.className = 'petri-overlay-container';
    this.arrowContainer.style.position = 'absolute';
    this.arrowContainer.style.pointerEvents = 'none'; // Initially no pointer events
    this.arrowContainer.style.top = '0';
    this.arrowContainer.style.left = '0';
    
    // Create arrow elements
    this.arrowElements = {
      top: this.createArrowElement('top'),
      right: this.createArrowElement('right'),
      bottom: this.createArrowElement('bottom'),
      left: this.createArrowElement('left')
    };
    
    // Add arrow elements to container
    Object.values(this.arrowElements).forEach(arrow => {
      this.arrowContainer.appendChild(arrow);
    });
    
    // Add container to document
    this.canvas.parentElement.appendChild(this.arrowContainer);
    
    // Keep reference to render method for animation frame
    this.render = this.render.bind(this);
  }
  
  /**
   * Create an arrow element with appropriate styling and event listeners
   * @param {string} direction - Arrow direction ('top', 'right', 'bottom', 'left')
   * @returns {HTMLElement} The created arrow element
   */
  createArrowElement(direction) {
    const arrow = document.createElement('div');
    arrow.className = `petri-overlay-arrow petri-overlay-arrow-${direction}`;
    arrow.style.position = 'absolute';
    arrow.style.width = `${this.arrowSize * 3}px`;
    arrow.style.height = `${this.arrowSize * 3}px`;
    arrow.style.backgroundColor = this.arrowColor;
    arrow.style.border = `1px solid ${this.arrowStrokeColor}`;
    arrow.style.transform = 'translate(22%, 15%)';
    arrow.style.pointerEvents = 'auto';
    arrow.style.cursor = 'pointer';
    arrow.style.display = 'none';
    
    // Set different shape based on direction
    switch(direction) {
      case 'top':
        arrow.style.clipPath = 'polygon(50% 0%, 100% 100%, 0% 100%)';
        break;
      case 'right':
        arrow.style.clipPath = 'polygon(100% 50%, 0% 0%, 0% 100%)';
        break;
      case 'bottom':
        arrow.style.clipPath = 'polygon(50% 100%, 0% 0%, 100% 0%)';
        break;
      case 'left':
        arrow.style.clipPath = 'polygon(0% 50%, 100% 0%, 100% 100%)';
        break;
    }
    
    // Add event listeners
    arrow.addEventListener('mouseenter', () => this.handleArrowHover(direction, true));
    arrow.addEventListener('mouseleave', () => this.handleArrowHover(direction, false));
    arrow.addEventListener('click', (event) => this.handleArrowClick(direction, event));
    
    return arrow;
  }
  
  /**
   * Handle arrow hover events
   * @param {string} direction - Arrow direction
   * @param {boolean} isHovering - Whether the arrow is being hovered
   */
  handleArrowHover(direction, isHovering) {
    const arrow = this.arrowElements[direction];
    arrow.style.backgroundColor = isHovering ? this.arrowHoverColor : this.arrowColor;
  }
  
  /**
   * Handle arrow click events
   * @param {string} direction - Arrow direction
   * @param {MouseEvent} event - Click event
   */
  handleArrowClick(direction, event) {
    if (!this.isVisible || !this.selectedElement) return;
    
    // Get position of currently selected element
    const { x, y } = this.selectedElement.position;
    
    // Calculate new element position based on fixed distance in the arrow direction
    const newPos = { x, y };
    switch (direction) {
      case 'top':
        newPos.y -= this.newElementDistance;
        break;
      case 'right':
        newPos.x += this.newElementDistance;
        break;
      case 'bottom':
        newPos.y += this.newElementDistance;
        break;
      case 'left':
        newPos.x -= this.newElementDistance;
        break;
    }
    
    // Apply grid snapping if enabled
    if (this.editor.snapToGrid) {
      newPos.x = Math.round(newPos.x / this.editor.gridSize) * this.editor.gridSize;
      newPos.y = Math.round(newPos.y / this.editor.gridSize) * this.editor.gridSize;
    }
    
    // Create the new opposite element (place -> transition, transition -> place)
    let newElementId;
    
    if (this.selectedElementType === 'place') {
      // Create a transition
      newElementId = this.api.createTransition(
        newPos.x, 
        newPos.y, 
        `T${this.api.petriNet.transitions.size + 1}`
      );
      
      // Create an arc from place to transition
      this.api.createArc(this.selectedElement.id, newElementId);
    } else {
      // Create a place
      newElementId = this.api.createPlace(
        newPos.x, 
        newPos.y, 
        `P${this.api.petriNet.places.size + 1}`
      );
      
      // Create an arc from transition to place
      this.api.createArc(this.selectedElement.id, newElementId);
    }
    
    // Select the new element
    this.editor.selectElement(newElementId, this.selectedElementType === 'place' ? 'transition' : 'place');
  }
  
  /**
   * Update the overlay when an element is selected
   * @param {string} id - ID of the selected element
   * @param {string} type - Type of the selected element ('place' or 'transition')
   */
  updateSelection(id, type) {
    if (!id || (type !== 'place' && type !== 'transition')) {
      this.isVisible = false;
      this.selectedElement = null;
      this.selectedElementType = null;
      this.hideArrows();
      return;
    }
    
    this.isVisible = true;
    this.selectedElement = type === 'place' 
      ? this.api.petriNet.places.get(id) 
      : this.api.petriNet.transitions.get(id);
    this.selectedElementType = type;
    
    // Update positions immediately
    this.updateArrowPositions();
  }
  
  /**
   * Hide all arrow elements
   */
  hideArrows() {
    Object.values(this.arrowElements).forEach(arrow => {
      arrow.style.display = 'none';
    });
  }
  
  /**
   * Update positions of all arrow elements based on selected element
   */
  updateArrowPositions() {
    if (!this.isVisible || !this.selectedElement) {
      this.hideArrows();
      return;
    }
    
    // Get element position
    const { x, y } = this.selectedElement.position;
    
    // Convert world coordinates to screen coordinates
    const screenPos = this.editor.renderer.worldToScreen(x, y);
    
    // Calculate arrow positions (in screen coordinates)
    const positions = {
      top: {
        x: screenPos.x,
        y: screenPos.y - this.arrowDistance * this.editor.renderer.zoomFactor
      },
      right: {
        x: screenPos.x + this.arrowDistance * this.editor.renderer.zoomFactor,
        y: screenPos.y
      },
      bottom: {
        x: screenPos.x,
        y: screenPos.y + this.arrowDistance * this.editor.renderer.zoomFactor
      },
      left: {
        x: screenPos.x - this.arrowDistance * this.editor.renderer.zoomFactor,
        y: screenPos.y
      }
    };
    
    // Update arrow positions
    Object.entries(positions).forEach(([direction, pos]) => {
      const arrow = this.arrowElements[direction];
      arrow.style.left = `${pos.x}px`;
      arrow.style.top = `${pos.y}px`;
      arrow.style.display = 'block';
      
      // Scale arrows with zoom
      const scaleFactor = Math.max(0.5, Math.min(2, this.editor.renderer.zoomFactor));
      arrow.style.transform = `translate(22%, 15%) scale(${scaleFactor})`;
    });
  }
  
  /**
   * Render the overlay arrows
   */
  render() {
    if (this.isVisible && this.selectedElement) {
      this.updateArrowPositions();
    }
  }
  
  /**
   * Clean up resources
   */
  destroy() {
    if (this.arrowContainer && this.arrowContainer.parentNode) {
      this.arrowContainer.parentNode.removeChild(this.arrowContainer);
    }
  }
}