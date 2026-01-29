/**
 * Trace Visualization Renderer for Suvorov-Lomazova Verification
 * Single-canvas version: draw overlays AFTER the base renderer, fully sandboxed.
 * - Does NOT wrap the base render in a global save/restore
 * - World-space highlights respect pan/zoom
 * - Screen-space tooltips reset transform to identity
 */
class SuvorovLomazovaTraceVisualizationRenderer {
  constructor(app) {
    this.app = app;
    this.canvas = app.canvas;

    // Visualization state
    this.highlightedElements = new Set();
    this.highlightedArcs = new Set();
    this.dataOverlays = new Map();
    this.problematicPlaces = new Map();
    this.responsibleVariables = new Map();
    this.violationInfo = null;
    this.isActive = false;

    // HTML overlay management
    this.overlayContainer = null;
    this.htmlOverlays = new Map(); // overlayId -> HTML element
    this.overlayPositions = new Map(); // overlayId -> {worldX, worldY, offsetX, offsetY}

    // Animation
    this.animationTime = 0;
    this.animationFrame = null;
    this.updateInterval = null;

    this.setupHTMLOverlaySystem();
    this.setupEventListeners();
  }

  /**
   * Setup the HTML overlay system
   */
  setupHTMLOverlaySystem() {
    // Create overlay container
    this.overlayContainer = document.createElement('div');
    this.overlayContainer.id = 'sl-overlay-container';
    this.overlayContainer.style.cssText = `
      position: absolute;
      top: 0;
      left: 0;
      width: 100%;
      height: 100%;
      pointer-events: none;
      z-index: 100;
      overflow: hidden;
    `;

    // Position container relative to canvas
    const canvasContainer = this.canvas.parentElement;
    if (canvasContainer) {
      canvasContainer.style.position = 'relative';
      canvasContainer.appendChild(this.overlayContainer);
    }

    // Add styles for overlays
    this.injectOverlayStyles();
  }

  /**
   * Setup event listeners for canvas updates
   */
  setupEventListeners() {
    // Listen for canvas events that might change positioning
    this.canvas.addEventListener('wheel', () => this.scheduleUpdate());
    this.canvas.addEventListener('mousedown', () => this.scheduleUpdate());
    this.canvas.addEventListener('mousemove', () => this.scheduleUpdate());
    
    // Listen for window resize
    window.addEventListener('resize', () => this.scheduleUpdate());
    
    // Store references for cleanup
    this.boundEvents = {
      wheel: () => this.scheduleUpdate(),
      mousedown: () => this.scheduleUpdate(),
      mousemove: () => this.scheduleUpdate(),
      resize: () => this.scheduleUpdate()
    };
  }

  /**
   * Schedule an update (debounced)
   */
  scheduleUpdate() {
    if (!this.isActive) return;
    
    // Use requestAnimationFrame for smooth updates
    if (this.updateFrame) {
      cancelAnimationFrame(this.updateFrame);
    }
    
    this.updateFrame = requestAnimationFrame(() => {
      this.updateHTMLOverlays();
    });
  }

  /**
   * Inject CSS styles for HTML overlays
   */
  injectOverlayStyles() {
    if (document.getElementById("sl-overlay-styles")) return;

    const style = document.createElement("style");
    style.id = "sl-overlay-styles";
    style.textContent = `
      .sl-html-overlay {
        position: absolute;
        background: rgba(46, 52, 64, 0.95);
        border: 2px solid;
        border-radius: 8px;
        padding: 12px;
        color: #ECEFF4;
        font-family: -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, sans-serif;
        font-size: 13px;
        line-height: 1.4;
        max-width: 250px;
        min-width: 150px;
        box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
        backdrop-filter: blur(10px);
        transform-origin: top left;
        transition: all 0.3s ease;
        pointer-events: auto;
        cursor: move;
        z-index: 101;
      }

      .sl-html-overlay:hover {
        transform: scale(1.05);
        box-shadow: 0 6px 16px rgba(0, 0, 0, 0.4);
      }

      .sl-html-overlay.dragging {
        transition: none;
        transform: scale(1.1);
        z-index: 102;
      }

      .sl-html-overlay.deadTransition {
        border-color: #BF616A;
        background: linear-gradient(135deg, rgba(191, 97, 106, 0.9), rgba(46, 52, 64, 0.95));
        wdith: 10px;
      }

      .sl-html-overlay.overfinal {
        border-color: #D08770;
        background: linear-gradient(135deg, rgba(208, 135, 112, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-html-overlay.traceStep {
        border-color: #88C0D0;
        background: linear-gradient(135deg, rgba(136, 192, 208, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-html-overlay.deadlockMarking {
        border-color: #B48EAD;
        background: linear-gradient(135deg, rgba(180, 142, 173, 0.9), rgba(46, 52, 64, 0.95));
      }

      .sl-overlay-header {
        font-weight: bold;
        margin-bottom: 8px;
        display: flex;
        align-items: center;
        gap: 6px;
      }

      .sl-overlay-content {
        font-size: 12px;
      }

      .sl-overlay-icon {
        font-size: 16px;
      }

      .sl-overlay-close {
        position: absolute;
        top: 4px;
        right: 4px;
        background: none;
        border: none;
        color: #ECEFF4;
        cursor: pointer;
        font-size: 14px;
        width: 20px;
        height: 20px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        opacity: 0.7;
        transition: all 0.2s ease;
      }

      .sl-overlay-close:hover {
        opacity: 1;
        background: rgba(255, 255, 255, 0.1);
      }

      .sl-data-values {
        margin-top: 8px;
        padding-top: 8px;
        border-top: 1px solid rgba(236, 239, 244, 0.2);
      }

      .sl-data-value {
        display: flex;
        justify-content: space-between;
        margin-bottom: 4px;
        font-family: 'Courier New', monospace;
        font-size: 11px;
      }

      .sl-data-value .variable {
        color: #8FBCBB;
      }

      .sl-data-value .value {
        color: #A3BE8C;
        font-weight: bold;
      }

      /* Highlight styles for elements */
      .sl-element-highlight {
        position: absolute;
        border: 3px solid;
        border-radius: 50%;
        pointer-events: none;
        animation: sl-pulse 2s infinite;
        z-index: 98;
      }

      .sl-element-highlight.transition {
        border-radius: 4px;
      }

      .sl-element-highlight.dead-transition {
        border-color: #BF616A;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(191,97,106,0.12);
      }

      .sl-element-highlight.overfinal {
        border-color: #D08770;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(208,135,112,0.12);
      }

      .sl-element-highlight.trace-step {
        border-color: #88C0D0;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(136,192,208,0.12);
      }

      .sl-element-highlight.deadlock {
        border-color: #B48EAD;
        box-shadow: 0px 0px 26px 11px rgba(191,97,106,0.58), 0px 0px 16px 11px rgba(180,142,173,0.12);
      }

      @keyframes sl-pulse {
        0%, 100% { 
          opacity: 0.5;
          transform: scale(1);
        }
        50% { 
          opacity: 0.8;
          transform: scale(1.1);
        }
      }
    `;
    document.head.appendChild(style);
  }

  /**
   * Update positions and visibility of HTML overlays
   */
  updateHTMLOverlays() {
    if (!this.isActive) return;
    
    this.updateAnimation();
    this.updateOverlayPositions();
    this.updateElementHighlights();
  }

  updateAnimation() {
    this.animationTime += 0.05;
  }

  /**
   * Get the canvas position relative to its container
   */
  getCanvasOffset() {
    const canvasRect = this.canvas.getBoundingClientRect();
    const containerRect = this.canvas.parentElement.getBoundingClientRect();
    
    return {
      x: canvasRect.left - containerRect.left,
      y: canvasRect.top - containerRect.top
    };
  }

  /**
   * Get zoom factor from renderer
   */
  getZoomFactor() {
    return this.app.editor?.renderer?.zoomFactor || 1.0;
  }

  /**
   * Get pan offset from renderer
   */
  getPanOffset() {
    return this.app.editor?.renderer?.panOffset || { x: 0, y: 0 };
  }

  /**
   * Convert world coordinates to screen coordinates
   * This must exactly match the renderer's coordinate transformation
   */
  worldToScreen(worldX, worldY) {
    const zoomFactor = this.getZoomFactor();
    const panOffset = this.getPanOffset();
    
    // Apply the same transformation as the renderer:
    // 1. Scale by zoom factor
    // 2. Translate by pan offset
    const canvasX = worldX * zoomFactor + panOffset.x;
    const canvasY = worldY * zoomFactor + panOffset.y;
    
    // Convert from canvas coordinates to CSS coordinates
    // Account for devicePixelRatio scaling
    const canvasRect = this.canvas.getBoundingClientRect();
    const scaleX = canvasRect.width / this.canvas.width;
    const scaleY = canvasRect.height / this.canvas.height;
    
    // Convert to screen coordinates relative to the canvas
    const screenX = canvasX * scaleX;
    const screenY = canvasY * scaleY;
    
    // Add canvas offset within its container
    const canvasOffset = this.getCanvasOffset();
    
    return {
      x: screenX + canvasOffset.x,
      y: screenY + canvasOffset.y
    };
  }

  /**
   * Update positions of all HTML overlays based on world coordinates
   */
  updateOverlayPositions() {
    for (const [overlayId, overlay] of this.htmlOverlays) {
      const position = this.overlayPositions.get(overlayId);
      if (!position) continue;

      // Convert world coordinates to screen coordinates
      const screenPos = this.worldToScreen(position.worldX, position.worldY);
      
      // Apply user offset (for dragged overlays)
      const finalX = screenPos.x + position.offsetX;
      const finalY = screenPos.y + position.offsetY;

      // Update overlay position
      overlay.style.left = `${finalX}px`;
      overlay.style.top = `${finalY}px`;

      // Hide overlay if it's outside the visible area
      const containerRect = this.overlayContainer.getBoundingClientRect();
      const isVisible = finalX > -overlay.offsetWidth && 
                       finalY > -overlay.offsetHeight &&
                       finalX < containerRect.width + overlay.offsetWidth &&
                       finalY < containerRect.height + overlay.offsetHeight;
      
      overlay.style.display = isVisible ? 'block' : 'none';
    }
  }

  /**
   * Update element highlights (ring around places/transitions)
   */
  updateElementHighlights() {
    // Remove existing highlights
    const existingHighlights = this.overlayContainer.querySelectorAll('.sl-element-highlight');
    existingHighlights.forEach(highlight => highlight.remove());

    // Add new highlights
    for (const elementId of this.highlightedElements) {
      this.createElementHighlight(elementId);
    }
  }

  /**
   * Create a highlight ring around an element
   */
  createElementHighlight(elementId) {
    const element = this.getElementById(elementId);
    if (!element) return;

    const highlight = document.createElement('div');
    highlight.className = 'sl-element-highlight';
    
    // Determine element type and styling
    const isTransition = this.app.api.petriNet.transitions.has(elementId);
    if (isTransition) {
      highlight.classList.add('transition');
    }

    // Add specific styling based on violation type
    if (this.isDeadTransition(elementId)) {
      highlight.classList.add('dead-transition');
    } else if (this.isOverfinalPlace(elementId)) {
      highlight.classList.add('overfinal');
    } else if (this.isTraceElement(elementId)) {
      highlight.classList.add('trace-step');
    } else {
      highlight.classList.add('deadlock');
    }

    const worldPos = { x: element.position.x, y: element.position.y };
    const screenPos = this.worldToScreen(worldPos.x, worldPos.y);
    
    const highlightPadding = 15; // Extra space around element (in world units)
    let worldSize, borderRadius;
    if (isTransition) {
      worldSize = Math.max(element.width, element.height) + highlightPadding;
      borderRadius = '4px';
    } else {
      worldSize = element.radius * 2 + highlightPadding;
      borderRadius = '50%';
    }
    
    // Apply zoom to the size
    const screenSize = worldSize * this.getZoomFactor() * (this.canvas.getBoundingClientRect().width / this.canvas.width);

    highlight.style.cssText += `
      left: ${screenPos.x - (isTransition? screenSize*0.3: screenSize*0.6)}px;
      top: ${screenPos.y - (isTransition? screenSize*0.4: screenSize*0.6)}px;
      width: ${isTransition ? (screenSize / 2) : screenSize}px;
      height: ${screenSize}px;
      border-radius: ${borderRadius};
    `;

    this.overlayContainer.appendChild(highlight);
  }

  /**
   * Create an HTML overlay for a specific data overlay
   */
  createHTMLOverlay(overlayId, overlayData) {
    const element = this.getElementById(overlayData.elementId);
    if (!element) return;

    // Store overlay data
    this.dataOverlays.set(overlayId, overlayData);

    // Create HTML element
    const overlay = document.createElement('div');
    overlay.className = `sl-html-overlay ${overlayData.type}`;
    overlay.id = `overlay-${overlayId}`;

    // Set content
    overlay.innerHTML = this.formatOverlayHTML(overlayData);

    // Position overlay
    const worldPos = { x: element.position.x, y: element.position.y };
    const screenPos = this.worldToScreen(worldPos.x, worldPos.y);
    const defaultOffset = this.calculateDefaultOffset(overlayData.elementType);

    // Store position data
    this.overlayPositions.set(overlayId, {
      worldX: worldPos.x,
      worldY: worldPos.y,
      offsetX: defaultOffset.x,
      offsetY: defaultOffset.y
    });

    // Set initial position
    overlay.style.left = `${screenPos.x + defaultOffset.x}px`;
    overlay.style.top = `${screenPos.y + defaultOffset.y}px`;

    // Add drag functionality
    this.makeDraggable(overlay, overlayId);

    // Add close button functionality
    const closeBtn = overlay.querySelector('.sl-overlay-close');
    if (closeBtn) {
      closeBtn.addEventListener('click', (e) => {
        e.stopPropagation();
        this.removeHTMLOverlay(overlayId);
      });
    }

    // Add to container and map
    this.overlayContainer.appendChild(overlay);
    this.htmlOverlays.set(overlayId, overlay);
  }

  /**
   * Calculate default offset for overlay positioning
   */
  calculateDefaultOffset(elementType) {
    if (elementType === 'transition') {
      return { x: 30, y: -60 };
    } else {
      return { x: 30, y: -30 };
    }
  }

  /**
   * Make an overlay draggable
   */
  makeDraggable(overlay, overlayId) {
    let isDragging = false;
    let startX, startY, startOffsetX, startOffsetY;

    overlay.addEventListener('mousedown', (e) => {
      if (e.target.classList.contains('sl-overlay-close')) return;
      
      isDragging = true;
      startX = e.clientX;
      startY = e.clientY;
      
      const position = this.overlayPositions.get(overlayId);
      startOffsetX = position.offsetX;
      startOffsetY = position.offsetY;
      
      overlay.classList.add('dragging');
      document.addEventListener('mousemove', onMouseMove);
      document.addEventListener('mouseup', onMouseUp);
      e.preventDefault();
    });

    const onMouseMove = (e) => {
      if (!isDragging) return;
      
      const deltaX = e.clientX - startX;
      const deltaY = e.clientY - startY;
      
      const position = this.overlayPositions.get(overlayId);
      position.offsetX = startOffsetX + deltaX;
      position.offsetY = startOffsetY + deltaY;
      
      this.updateOverlayPositions();
    };

    const onMouseUp = () => {
      isDragging = false;
      overlay.classList.remove('dragging');
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('mouseup', onMouseUp);
    };
  }

  // [Rest of the methods remain the same - visualizeCheck, clearHighlights, etc.]
  
  /**
   * Public: visualize a check result
   */
  visualizeCheck(check) {
    this.clearHighlights(true);
    this.isActive = true;
    this.violationInfo = check;

    if (check.problematicPlaces) {
      for (const place of check.problematicPlaces) {
        this.problematicPlaces.set(place.placeId, place);
      }
    }
    if (check.responsibleVariables) {
      for (const variable of check.responsibleVariables) {
        this.responsibleVariables.set(variable.variable, variable);
      }
    }

    if (!check.satisfied) {
      switch (true) {
        case check.name.includes("Deadlock") || check.name.includes("P1"):
          this.visualizeDeadlockViolation(check);
          break;
        case check.name.includes("Overfinal") || check.name.includes("P2"):
          this.visualizeOverfinalViolation(check);
          break;
        case check.name.includes("Dead") || check.name.includes("P3"):
          this.visualizeDeadTransitionViolation(check);
          break;
        case check.name.includes("Boundedness"):
          this.visualizeBoundednessViolation(check);
          break;
        default:
          this.visualizeGenericViolation(check);
          break;
      }
    }

    this.startAnimation();
  }

  startAnimation() {
    if (this.animationFrame) return;
    
    const animate = () => {
      if (!this.isActive) {
        this.animationFrame = null;
        return;
      }
      this.updateHTMLOverlays();
      this.animationFrame = requestAnimationFrame(animate);
    };
    this.animationFrame = requestAnimationFrame(animate);
  }

  stopAnimation() {
    if (this.animationFrame) {
      cancelAnimationFrame(this.animationFrame);
      this.animationFrame = null;
    }
    if (this.updateFrame) {
      cancelAnimationFrame(this.updateFrame);
      this.updateFrame = null;
    }
  }

  visualizeDeadlockViolation(check) {
    if (check.trace && check.trace.length > 0) {
      this.visualizeTracePath(check.trace, "deadlock");
    }
    if (check.offendingState?.marking) {
      Object.entries(check.offendingState.marking).forEach(([placeId, tokens]) => {
        if (tokens > 0) {
          this.highlightedElements.add(placeId);
          this.createHTMLOverlay(`deadlock_${placeId}`, {
            type: "deadlockMarking",
            elementId: placeId,
            elementType: "place",
            tokens,
            data: check.offendingState,
          });
        }
      });
    }
  }

  visualizeOverfinalViolation(check) {
    if (check.overfinalNodes?.length) {
      check.overfinalNodes.forEach((node, index) => {
        if (!node.marking) return;
        Object.entries(node.marking).forEach(([placeId, tokens]) => {
          if (tokens > 0) {
            this.highlightedElements.add(placeId);
            this.createHTMLOverlay(`overfinal_${placeId}_${index}`, {
              type: "overfinal",
              elementId: placeId,
              elementType: "place",
              tokens,
              nodeData: node,
              formula: node.formula,
            });
          }
        });
      });
    }
    if (check.trace) this.visualizeTracePath(check.trace, "overfinal");
  }

  visualizeDeadTransitionViolation(check) {
    const list = check.deadTransitions || (check.deadTransition ? [check.deadTransition] : []);
    list.forEach((deadTransition) => {
      const id = deadTransition.transitionId;
      if (!id) return;
      this.highlightedElements.add(id);
      this.highlightConnectedElements(id);
      this.createHTMLOverlay(`dead_transition_${id}`, {
        type: "deadTransition",
        elementId: id,
        elementType: "transition",
        data: deadTransition,
        variants: deadTransition.variants || [],
      });
    });
    if (check.trace) this.visualizeTracePath(check.trace, "deadTransition");
  }

  visualizeBoundednessViolation(check) {
    if (check.trace?.length) this.visualizeTracePath(check.trace, "boundedness");
  }

  visualizeGenericViolation(check) {
    if (check.trace) this.visualizeTracePath(check.trace, "generic");
  }

  visualizeTracePath(trace, violationType) {
    if (!trace?.length) return;
    trace.forEach((step, stepIndex) => {
      const transitionId = this.findTransitionId(step.transitionId);
      if (!transitionId) return;
      this.highlightedElements.add(transitionId);
      this.highlightConnectedElements(transitionId);
      this.createHTMLOverlay(`trace_step_${stepIndex}`, {
        type: "traceStep",
        elementId: transitionId,
        elementType: "transition",
        stepIndex,
        violationType,
        data: step,
        vars: step.vars || {},
        formula: step.formula || '',
        marking: step.marking || {},
      });
    });
  }

  /**
   * Remove an HTML overlay
   */
  removeHTMLOverlay(overlayId) {
    const overlay = this.htmlOverlays.get(overlayId);
    if (overlay) {
      overlay.remove();
      this.htmlOverlays.delete(overlayId);
    }
    this.overlayPositions.delete(overlayId);
    this.dataOverlays.delete(overlayId);
  }

  /**
   * Format overlay content as HTML
   */
  formatOverlayHTML(overlayData) {
    const content = this.formatOverlayContent(overlayData);
    const lines = content.split('\n');
    const header = lines[0];
    const body = lines.slice(1).join('\n');

    let html = `
      <button class="sl-overlay-close">×</button>
      <div class="sl-overlay-header">
        <span class="sl-overlay-icon">${this.getOverlayIcon(overlayData.type)}</span>
        <span>${header}</span>
      </div>
    `;

    if (body.trim()) {
      html += `<div class="sl-overlay-content">${this.formatContentAsHTML(body)}</div>`;
    }

    // Add data values if present
    if (overlayData.vars && Object.keys(overlayData.vars).length > 0) {
      html += '<div class="sl-data-values">';
      html += '<strong>Data State:</strong>';
      for (const [variable, value] of Object.entries(overlayData.vars)) {
        html += `
          <div class="sl-data-value">
            <span class="variable">${variable}</span>
            <span class="value">${value}</span>
          </div>
        `;
      }
      html += '</div>';
    }

    // Add formula (data constraint) if present
    if (overlayData.formula && overlayData.formula !== 'true' && overlayData.formula.trim()) {
      html += `
        <div class="sl-data-values" style="border-top-color: #5E81AC;">
          <strong style="color: #88C0D0;">Data Constraint:</strong>
          <div style="font-family: monospace; font-size: 10px; color: #8FBCBB; word-break: break-all; margin-top: 4px;">
            ${this.formatFormulaForOverlay(overlayData.formula)}
          </div>
        </div>
      `;
    }

    return html;
  }

  /**
   * Format formula for overlay display (truncate if too long)
   */
  formatFormulaForOverlay(formula) {
    if (!formula) return '';
    // Escape HTML and truncate if too long
    const escaped = formula
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;');
    
    if (escaped.length > 150) {
      return escaped.substring(0, 150) + '...';
    }
    return escaped;
  }

  /**
   * Get icon for overlay type
   */
  getOverlayIcon(type) {
    switch (type) {
      case "deadTransition":
      case "deadlockMarking":
        return "⚠️";
      case "overfinal":
        return "🔥";
      case "traceStep":
        return "🔄";
      default:
        return "❌";
    }
  }

  /**
   * Format content as HTML
   */
  formatContentAsHTML(content) {
    return content
      .split('\n')
      .map(line => line.trim())
      .filter(line => line.length > 0)
      .map(line => `<div>${line}</div>`)
      .join('');
  }

  /**
   * Format overlay content
   */
  formatOverlayContent(overlay) {
    switch (overlay.type) {
      case "deadTransition":
        return `DEAD TRANSITION\n${overlay.data?.transitionLabel || overlay.elementId}\nNever enabled in any reachable state`;
      case "overfinal":
        return `OVERFINAL MARKING\nPlace: ${overlay.elementId}\nTokens: ${overlay.tokens}\nExceeds final marking`;
      case "traceStep": {
        const lines = [`Step ${overlay.stepIndex + 1}: Fire ${overlay.elementId}`];
        return lines.join('\n');
      }
      case "deadlockMarking":
        return `DEADLOCK STATE\nPlace: ${overlay.elementId}\nTokens: ${overlay.tokens}\nCannot reach final marking`;
      default:
        return `Violation detected\n${overlay.elementId}`;
    }
  }

  // Helper methods
  findTransitionId(stepTransitionId) {
    if (!this.app.api?.petriNet) return null;
    if (this.app.api.petriNet.transitions.has(stepTransitionId)) return stepTransitionId;
    for (const [id, transition] of this.app.api.petriNet.transitions) {
      if (
        transition.label === stepTransitionId ||
        id.includes(stepTransitionId) ||
        stepTransitionId?.includes?.(id)
      ) return id;
    }
    return null;
  }

  highlightConnectedElements(transitionId) {
    if (!this.app.api?.petriNet) return;
    for (const arc of this.app.api.petriNet.arcs.values()) {
      if (arc.source === transitionId || arc.target === transitionId) {
        this.highlightedArcs.add(arc.id);
        const connected = arc.source === transitionId ? arc.target : arc.source;
        this.highlightedElements.add(connected);
      }
    }
  }

  getElementById(elementId) {
    if (this.app.api?.petriNet?.places?.has(elementId)) {
      return this.app.api.petriNet.places.get(elementId);
    }
    if (this.app.api?.petriNet?.transitions?.has(elementId)) {
      return this.app.api.petriNet.transitions.get(elementId);
    }
    return null;
  }

  isDeadTransition(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "deadTransition" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  isOverfinalPlace(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "overfinal" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  isTraceElement(elementId) {
    for (const [, overlay] of this.dataOverlays) {
      if (overlay.type === "traceStep" && overlay.elementId === elementId) return true;
    }
    return false;
  }

  /**
   * Clear state and remove all overlays
   */
  clearHighlights(keepInactive = false) {
    this.highlightedElements.clear();
    this.highlightedArcs.clear();
    this.dataOverlays.clear();
    this.problematicPlaces.clear();
    this.responsibleVariables.clear();
    this.violationInfo = null;

    // Clear all HTML overlays
    for (const [overlayId] of this.htmlOverlays) {
      this.removeHTMLOverlay(overlayId);
    }

    if (!keepInactive) this.isActive = false;
    this.stopAnimation();
  }

  /**
   * Cleanup when component is destroyed
   */
  destroy() {
    this.clearHighlights(false);
    
    // Remove event listeners
    if (this.boundEvents) {
      this.canvas.removeEventListener('wheel', this.boundEvents.wheel);
      this.canvas.removeEventListener('mousedown', this.boundEvents.mousedown);
      this.canvas.removeEventListener('mousemove', this.boundEvents.mousemove);
      window.removeEventListener('resize', this.boundEvents.resize);
    }
    
    // Remove overlay container
    if (this.overlayContainer && this.overlayContainer.parentNode) {
      this.overlayContainer.parentNode.removeChild(this.overlayContainer);
    }

    // Remove styles
    const styles = document.getElementById("sl-overlay-styles");
    if (styles && styles.parentNode) {
      styles.parentNode.removeChild(styles);
    }
  }
}

export { SuvorovLomazovaTraceVisualizationRenderer };
