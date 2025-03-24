/**
 * Petri Net Editor
 * A standalone JavaScript implementation of a Petri net editor with a sophisticated API.
 */

// Core Types
// type UUID = string;
// type Position = { x: number; y: number };

// Petri Net Elements
class PetriNetElement {
  constructor(id, position, label = "") {
    this.id = id;
    this.position = position;
    this.label = label;
  }
}

class Place extends PetriNetElement {
  constructor(id, position, label = "", tokens = 0, capacity = null) {
    super(id, position, label);
    this.tokens = tokens;
    this.capacity = capacity;
    this.radius = 20;
  }

  addTokens(count) {
    if (this.capacity !== null && this.tokens + count > this.capacity) {
      return false;
    }
    this.tokens += count;
    return true;
  }

  removeTokens(count) {
    if (this.tokens - count < 0) {
      return false;
    }
    this.tokens -= count;
    return true;
  }
}

class Transition extends PetriNetElement {
  constructor(
    id,
    position,
    label = "",
    priority = 1,
    delay = 0
  ) {
    super(id, position, label);
    this.width = 20;
    this.height = 50;
    this.isEnabled = false;
    this.priority = priority;
    this.delay = delay;
  }
}

// type ArcType = "regular" | "inhibitor" | "reset" | "read";

class Arc {
  constructor(
    id,
    source,
    target,
    weight = 1,
    type = "regular",
    points = [],
    label = ""
  ) {
    this.id = id;
    this.source = source;
    this.target = target;
    this.weight = weight;
    this.type = type;
    this.points = points;
    this.label = label || `${weight}`;
  }
}

// Main Petri Net Model
class PetriNet {
  constructor(id, name = "New Petri Net", description = "") {
    this.id = id;
    this.name = name;
    this.places = new Map();
    this.transitions = new Map();
    this.arcs = new Map();
    this.description = description;
  }

  // Basic CRUD operations
  addPlace(place) {
    this.places.set(place.id, place);
  }

  getPlace(id) {
    return this.places.get(id);
  }

  removePlace(id) {
    // Also remove connected arcs
    this.arcs.forEach((arc, arcId) => {
      if (arc.source === id || arc.target === id) {
        this.arcs.delete(arcId);
      }
    });
    return this.places.delete(id);
  }

  addTransition(transition) {
    this.transitions.set(transition.id, transition);
  }

  getTransition(id) {
    return this.transitions.get(id);
  }

  removeTransition(id) {
    // Also remove connected arcs
    this.arcs.forEach((arc, arcId) => {
      if (arc.source === id || arc.target === id) {
        this.arcs.delete(arcId);
      }
    });
    return this.transitions.delete(id);
  }

  addArc(arc) {
    // Validate that source and target exist
    const sourceExists = this.places.has(arc.source) || this.transitions.has(arc.source);
    const targetExists = this.places.has(arc.target) || this.transitions.has(arc.target);

    if (!sourceExists || !targetExists) {
      return false;
    }

    // Ensure the arc connects a place to a transition or vice versa
    const sourceIsPlace = this.places.has(arc.source);
    const targetIsPlace = this.places.has(arc.target);

    if (sourceIsPlace === targetIsPlace) {
      return false; // Both are places or both are transitions - invalid
    }

    this.arcs.set(arc.id, arc);
    return true;
  }

  getArc(id) {
    return this.arcs.get(id);
  }

  removeArc(id) {
    return this.arcs.delete(id);
  }

  // Simulation related methods
  updateEnabledTransitions() {
    for (const [id, transition] of this.transitions) {
      transition.isEnabled = this.isTransitionEnabled(id);
    }
  }

  isTransitionEnabled(transitionId) {
    const incomingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.target === transitionId);

    for (const arc of incomingArcs) {
      const place = this.places.get(arc.source);
      if (!place) continue;

      if (arc.type === "inhibitor") {
        // Inhibitor arc: transition enabled only if place has fewer tokens than arc weight
        if (place.tokens >= arc.weight) return false;
      } else if (arc.type === "regular") {
        // Regular arc: transition enabled only if place has enough tokens
        if (place.tokens < arc.weight) return false;
      }
      // Read arcs don't affect enabling
    }

    return true;
  }

  fireTransition(transitionId) {
    if (!this.isTransitionEnabled(transitionId)) {
      return false;
    }

    // Step 1: Collect incoming and outgoing arcs
    const incomingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outgoingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.source === transitionId);

    // Step 2: Remove tokens from input places
    for (const arc of incomingArcs) {
      const place = this.places.get(arc.source);
      if (!place) continue;

      if (arc.type === "regular") {
        place.removeTokens(arc.weight);
      } else if (arc.type === "reset") {
        place.tokens = 0;
      }
      // Inhibitor and read arcs don't remove tokens
    }

    // Step 3: Add tokens to output places
    for (const arc of outgoingArcs) {
      const place = this.places.get(arc.target);
      if (!place) continue;

      place.addTokens(arc.weight);
    }

    return true;
  }

  // Analysis methods
  getReachabilityGraph() {
    // Implementation of reachability graph analysis
    // This would return a graph of all possible markings
    // For simplicity, returning a placeholder
    return { nodes: [], edges: [] };
  }

  detectDeadlocks() {
    // Implementation of deadlock detection
    // Returns IDs of deadlocked transitions
    const deadlockedTransitions = [];

    // Simple implementation: transitions that can never be enabled
    for (const [id, transition] of this.transitions) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === id && arc.type === "regular");

      // Check if any incoming place has capacity less than the arc weight
      let potentiallyDeadlocked = false;
      for (const arc of incomingArcs) {
        const place = this.places.get(arc.source);
        if (place && place.capacity !== null && place.capacity < arc.weight) {
          potentiallyDeadlocked = true;
          break;
        }
      }

      if (potentiallyDeadlocked) {
        deadlockedTransitions.push(id);
      }
    }

    return deadlockedTransitions;
  }

  // Import/Export methods
  toJSON() {
    return JSON.stringify({
      id: this.id,
      name: this.name,
      description: this.description,
      places: Array.from(this.places.values()),
      transitions: Array.from(this.transitions.values()),
      arcs: Array.from(this.arcs.values())
    });
  }

  static fromJSON(json) {
    const data = JSON.parse(json);
    const net = new PetriNet(data.id, data.name, data.description);

    // Recreate places
    data.places.forEach((placeData) => {
      const place = new Place(
        placeData.id,
        placeData.position,
        placeData.label,
        placeData.tokens,
        placeData.capacity
      );
      net.places.set(place.id, place);
    });

    // Recreate transitions
    data.transitions.forEach((transitionData) => {
      const transition = new Transition(
        transitionData.id,
        transitionData.position,
        transitionData.label,
        transitionData.priority,
        transitionData.delay
      );
      net.transitions.set(transition.id, transition);
    });

    // Recreate arcs
    data.arcs.forEach((arcData) => {
      const arc = new Arc(
        arcData.id,
        arcData.source,
        arcData.target,
        arcData.weight,
        arcData.type,
        arcData.points,
        arcData.label
      );
      net.arcs.set(arc.id, arc);
    });

    return net;
  }

  // PNML export (Petri Net Markup Language)
  toPNML() {
    let pnml = `<?xml version="1.0" encoding="UTF-8"?>
  <pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
    <net id="${this.id}" type="http://www.pnml.org/version-2009/grammar/ptnet">
      <n>
        <text>${this.name}</text>
      </n>`;

    // Places
    for (const [id, place] of this.places) {
      pnml += `
      <place id="${id}">
        <n>
          <text>${place.label}</text>
        </n>
        <initialMarking>
          <text>${place.tokens}</text>
        </initialMarking>
        <graphics>
          <position x="${place.position.x}" y="${place.position.y}"/>
        </graphics>
      </place>`;
    }

    // Transitions
    for (const [id, transition] of this.transitions) {
      pnml += `
      <transition id="${id}">
        <n>
          <text>${transition.label}</text>
        </n>
        <graphics>
          <position x="${transition.position.x}" y="${transition.position.y}"/>
        </graphics>
      </transition>`;
    }

    // Arcs
    for (const [id, arc] of this.arcs) {
      pnml += `
      <arc id="${id}" source="${arc.source}" target="${arc.target}">
        <inscription>
          <text>${arc.weight}</text>
        </inscription>`;

      if (arc.points.length > 0) {
        pnml += `
        <graphics>`;
        for (const point of arc.points) {
          pnml += `
          <position x="${point.x}" y="${point.y}"/>`;
        }
        pnml += `
        </graphics>`;
      }

      pnml += `
      </arc>`;
    }

    pnml += `
    </net>
  </pnml>`;

    return pnml;
  }
}

// Renderer class for the Petri net
class PetriNetRenderer {
  constructor(canvas, petriNet) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.petriNet = petriNet;

    // Pan and zoom properties
    this.panOffset = { x: 0, y: 0 };
    this.zoomFactor = 1.0;
    this.minZoom = 0.1;
    this.maxZoom = 3.0;

    // Default theme
    this.theme = {
      placeColor: '#ffffff',
      placeStroke: '#000000',
      tokenColor: '#000000',
      transitionColor: '#d3d3d3',
      transitionStroke: '#000000',
      enabledTransitionColor: '#90ee90',
      arcColor: '#000000',
      selectedColor: '#4682b4',
      textColor: '#000000',
      backgroundColor: '#ffffff'
    };
  }

  render() {
    this.clear();
    
    // Apply transformations for pan and zoom
    this.ctx.save();
    this.ctx.translate(this.panOffset.x, this.panOffset.y);
    this.ctx.scale(this.zoomFactor, this.zoomFactor);
    
    this.drawArcs();
    this.drawPlaces();
    this.drawTransitions();
    
    // Restore the canvas state
    this.ctx.restore();
  }

  clear() {
    this.ctx.fillStyle = this.theme.backgroundColor;
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
  }

  drawPlaces() {
    for (const [id, place] of this.petriNet.places) {
      // Draw place circle
      this.ctx.beginPath();
      this.ctx.arc(place.position.x, place.position.y, place.radius, 0, Math.PI * 2);
      this.ctx.fillStyle = this.theme.placeColor;
      this.ctx.fill();
      this.ctx.strokeStyle = this.theme.placeStroke;
      this.ctx.lineWidth = 2;
      this.ctx.stroke();

      // Draw tokens
      this.drawTokens(place);

      // Draw label
      this.ctx.fillStyle = this.theme.textColor;
      this.ctx.font = '12px Arial';
      this.ctx.textAlign = 'center';
      this.ctx.fillText(place.label, place.position.x, place.position.y + place.radius + 15);
    }
  }

  drawTokens(place) {
    const { x, y } = place.position;
    this.ctx.fillStyle = this.theme.tokenColor;

    // For 1-3 tokens, draw them as dots
    if (place.tokens <= 3) {
      const tokenRadius = 4;
      for (let i = 0; i < place.tokens; i++) {
        let tokenX = x;
        let tokenY = y;

        // Position tokens according to their count
        if (place.tokens === 1) {
          // Center the single token
        } else if (place.tokens === 2) {
          tokenX = i === 0 ? x - 5 : x + 5;
        } else if (place.tokens === 3) {
          if (i === 0) {
            tokenX = x;
            tokenY = y - 5;
          } else {
            tokenX = i === 1 ? x - 5 : x + 5;
            tokenY = y + 5;
          }
        }

        this.ctx.beginPath();
        this.ctx.arc(tokenX, tokenY, tokenRadius, 0, Math.PI * 2);
        this.ctx.fill();
      }
    } else {
      // For 4+ tokens, draw the number
      this.ctx.font = '14px Arial';
      this.ctx.textAlign = 'center';
      this.ctx.textBaseline = 'middle';
      this.ctx.fillText(place.tokens.toString(), x, y);
    }
  }

  drawTransitions() {
    for (const [id, transition] of this.petriNet.transitions) {
      // Draw transition rectangle
      this.ctx.beginPath();
      this.ctx.rect(
        transition.position.x - transition.width / 2,
        transition.position.y - transition.height / 2,
        transition.width,
        transition.height
      );
      this.ctx.fillStyle = transition.isEnabled ?
        this.theme.enabledTransitionColor : this.theme.transitionColor;
      this.ctx.fill();
      this.ctx.strokeStyle = this.theme.transitionStroke;
      this.ctx.lineWidth = 2;
      this.ctx.stroke();

      // Draw label
      this.ctx.fillStyle = this.theme.textColor;
      this.ctx.font = '12px Arial';
      this.ctx.textAlign = 'center';
      this.ctx.fillText(
        transition.label,
        transition.position.x,
        transition.position.y + transition.height / 2 + 15
      );
    }
  }

  drawArcs() {
    for (const [id, arc] of this.petriNet.arcs) {
      // Find the source and target elements
      let sourceElement;
      let targetElement;

      sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
      targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

      if (!sourceElement || !targetElement) continue;

      // Calculate start and end points based on shape of source and target
      const { start, end } = this.calculateArcEndpoints(sourceElement, targetElement);

      // Draw the arc path
      this.ctx.beginPath();
      this.ctx.moveTo(start.x, start.y);

      // If there are intermediate points, draw through them
      if (arc.points.length > 0) {
        for (const point of arc.points) {
          this.ctx.lineTo(point.x, point.y);
        }
      }

      this.ctx.lineTo(end.x, end.y);
      this.ctx.strokeStyle = this.theme.arcColor;
      this.ctx.lineWidth = 1.5;
      this.ctx.stroke();

      // Draw arrowhead
      this.drawArrowhead(end, this.calculateArcDirection(arc.points.length > 0 ?
        arc.points[arc.points.length - 1] : start, end));

      // Draw weight (if > 1 or always for special arcs)
      if (arc.weight > 1 || arc.type !== "regular") {
        const midpoint = this.calculateArcMidpoint(arc, start, end);
        this.ctx.fillStyle = this.theme.textColor;
        this.ctx.font = '12px Arial';
        this.ctx.textAlign = 'center';
        this.ctx.textBaseline = 'middle';

        let arcLabel = arc.label || arc.weight.toString();
        if (arc.type === "inhibitor") {
          arcLabel = "○" + arcLabel; // Circle for inhibitor
        } else if (arc.type === "reset") {
          arcLabel = "R" + arcLabel; // R for reset
        } else if (arc.type === "read") {
          arcLabel = "?" + arcLabel; // ? for read
        }

        this.ctx.fillText(arcLabel, midpoint.x, midpoint.y);
      }

      // Special arc types
      if (arc.type === "inhibitor") {
        // Draw a small circle at the end of the arc
        const circleRadius = 5;
        const circlePos = this.interpolatePoints(end, start, 10);

        this.ctx.beginPath();
        this.ctx.arc(circlePos.x, circlePos.y, circleRadius, 0, Math.PI * 2);
        this.ctx.strokeStyle = this.theme.arcColor;
        this.ctx.stroke();
      }
    }
  }

  calculateArcEndpoints(source, target) {
    let start = { x: source.position.x, y: source.position.y };
    let end = { x: target.position.x, y: target.position.y };

    // Adjust starting point if source is a place
    if (source instanceof Place) {
      const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);
      start.x = source.position.x + Math.cos(angle) * source.radius;
      start.y = source.position.y + Math.sin(angle) * source.radius;
    }
    // Adjust starting point if source is a transition
    else if (source instanceof Transition) {
      const dx = target.position.x - source.position.x;
      const dy = target.position.y - source.position.y;
      const angle = Math.atan2(dy, dx);

      // Calculate intersection with the rectangle
      if (Math.abs(dx) * source.height > Math.abs(dy) * source.width) {
        // Intersect with left or right edge
        const side = dx > 0 ? 1 : -1;
        start.x = source.position.x + side * source.width / 2;
        start.y = source.position.y + dy * (source.width / 2) / Math.abs(dx);
      } else {
        // Intersect with top or bottom edge
        const side = dy > 0 ? 1 : -1;
        start.y = source.position.y + side * source.height / 2;
        start.x = source.position.x + dx * (source.height / 2) / Math.abs(dy);
      }
    }

    // Adjust ending point if target is a place
    if (target instanceof Place) {
      const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);
      end.x = target.position.x - Math.cos(angle) * target.radius;
      end.y = target.position.y - Math.sin(angle) * target.radius;
    }
    // Adjust ending point if target is a transition
    else if (target instanceof Transition) {
      const dx = target.position.x - source.position.x;
      const dy = target.position.y - source.position.y;
      const angle = Math.atan2(dy, dx);

      // Calculate intersection with the rectangle
      if (Math.abs(dx) * target.height > Math.abs(dy) * target.width) {
        // Intersect with left or right edge
        const side = dx > 0 ? 1 : -1;
        end.x = target.position.x - side * target.width / 2;
        end.y = target.position.y - dy * (target.width / 2) / Math.abs(dx);
      } else {
        // Intersect with top or bottom edge
        const side = dy > 0 ? 1 : -1;
        end.y = target.position.y - side * target.height / 2;
        end.x = target.position.x - dx * (target.height / 2) / Math.abs(dy);
      }
    }

    return { start, end };
  }

  calculateArcDirection(from, to) {
    return Math.atan2(to.y - from.y, to.x - from.x);
  }

  drawArrowhead(position, angle) {
    const arrowSize = 10;
    const arrowAngle = Math.PI / 6; // 30 degrees

    this.ctx.beginPath();
    this.ctx.moveTo(position.x, position.y);
    this.ctx.lineTo(
      position.x - arrowSize * Math.cos(angle - arrowAngle),
      position.y - arrowSize * Math.sin(angle - arrowAngle)
    );
    this.ctx.lineTo(
      position.x - arrowSize * Math.cos(angle + arrowAngle),
      position.y - arrowSize * Math.sin(angle + arrowAngle)
    );
    this.ctx.closePath();
    this.ctx.fillStyle = this.theme.arcColor;
    this.ctx.fill();
  }

  calculateArcMidpoint(arc, start, end) {
    if (arc.points.length > 0) {
      // If there are intermediate points, use one near the middle
      const middleIndex = Math.floor(arc.points.length / 2);
      return arc.points[middleIndex];
    } else {
      // Otherwise use the midpoint of the direct line
      return {
        x: (start.x + end.x) / 2,
        y: (start.y + end.y) / 2
      };
    }
  }

  interpolatePoints(p1, p2, distance) {
    const dx = p2.x - p1.x;
    const dy = p2.y - p1.y;
    const length = Math.sqrt(dx * dx + dy * dy);

    if (length === 0) return p1;

    const t = distance / length;
    return {
      x: p1.x + dx * t,
      y: p1.y + dy * t
    };
  }

  // Pan and zoom methods
  setPan(x, y) {
    this.panOffset.x = x;
    this.panOffset.y = y;
  }

  adjustPan(dx, dy) {
    this.panOffset.x += dx;
    this.panOffset.y += dy;
  }

  setZoom(zoom, centerX, centerY) {
    // Store the position under the mouse before zooming
    const oldZoom = this.zoomFactor;
    const mouseWorldX = (centerX - this.panOffset.x) / oldZoom;
    const mouseWorldY = (centerY - this.panOffset.y) / oldZoom;
    
    // Clamp zoom factor
    this.zoomFactor = Math.max(this.minZoom, Math.min(this.maxZoom, zoom));
    
    // Calculate new pan offset to keep the point under the mouse fixed
    this.panOffset.x = centerX - mouseWorldX * this.zoomFactor;
    this.panOffset.y = centerY - mouseWorldY * this.zoomFactor;
  }

  adjustZoom(factor, centerX, centerY) {
    this.setZoom(this.zoomFactor * factor, centerX, centerY);
  }

  resetView() {
    this.panOffset = { x: 0, y: 0 };
    this.zoomFactor = 1.0;
  }

  // Convert screen coordinates to world coordinates
  screenToWorld(screenX, screenY) {
    return {
      x: (screenX - this.panOffset.x) / this.zoomFactor,
      y: (screenY - this.panOffset.y) / this.zoomFactor
    };
  }

  // Convert world coordinates to screen coordinates
  worldToScreen(worldX, worldY) {
    return {
      x: worldX * this.zoomFactor + this.panOffset.x,
      y: worldY * this.zoomFactor + this.panOffset.y
    };
  }

  // Additional theme settings
  setTheme(theme) {
    this.theme = { ...this.theme, ...theme };
  }
}

// Editor class for user interaction
class PetriNetEditor {
  
  constructor(canvas, petriNet) {
    this.canvas = canvas;
    this.petriNet = petriNet;
    this.renderer = new PetriNetRenderer(canvas, petriNet);
    this.mode = 'select';
    this.selectedElement = null;
    this.arcDrawing = null;
    this.dragStart = null;
    this.dragOffset = null; // Add dragOffset property for absolute positioning
    this.eventListeners = new Map();
    this.gridSize = 10; // Grid size for snap to grid
    this.snapToGrid = true;
    this.callbacks = {
      onChange: null,
      onSelect: null
    };

    const isMac = navigator.userAgent.includes('Mac');
    this.PAN_KEY_BUTTON_CODE = isMac ? 'MetaLeft' : 'AltLeft';

    // Pan and zoom state
    this.isPanning = false;
    this.lastPanPosition = null;

    this.setupEventListeners();
  }

  setupEventListeners() {
    // Mouse down event for selecting/placing elements or starting panning
    const mouseDownHandler = (event) => {
      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;

      // Middle mouse button or space + left mouse button for panning
      if (event.button === 1 || (event.button === 0 && this.isPanningKeyPressed)) {
        this.isPanning = true;
        this.lastPanPosition = { x, y };
        this.canvas.style.cursor = 'grabbing';
        event.preventDefault();
        return;
      }

      // Convert screen coordinates to world coordinates
      const worldPos = this.renderer.screenToWorld(x, y);

      if (this.mode === 'select') {
        this.handleSelection(worldPos.x, worldPos.y);
      } else if (this.mode === 'addPlace') {
        this.addPlace(worldPos.x, worldPos.y);
      } else if (this.mode === 'addTransition') {
        this.addTransition(worldPos.x, worldPos.y);
      } else if (this.mode === 'addArc') {
        this.startArcDrawing(worldPos.x, worldPos.y);
      }

      this.dragStart = worldPos;
      this.render();
    };

    const mouseMoveHandler = (event) => {
      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;
    
      // Handle panning
      if (this.isPanning && this.lastPanPosition) {
        const dx = x - this.lastPanPosition.x;
        const dy = y - this.lastPanPosition.y;
        this.renderer.adjustPan(dx, dy);
        this.lastPanPosition = { x, y };
        this.render();
        return;
      }
    
      // Convert screen coordinates to world coordinates
      const worldPos = this.renderer.screenToWorld(x, y);
    
      if (this.mode === 'select' && this.selectedElement) {
        this.handleDrag(worldPos.x, worldPos.y);
        this.render();
      } else if (this.mode === 'addArc' && this.arcDrawing) {
        // Temporary rendering of arc during drawing
        this.render();
        this.renderArcDrawing(worldPos.x, worldPos.y);
      }
    };

    // Mouse up event for completing drag, arc drawing, or panning
    const mouseUpHandler = (event) => {
      // Handle end of panning
      if (this.isPanning) {
        this.isPanning = false;
        this.lastPanPosition = null;
        this.canvas.style.cursor = 'default';
        this.render();
        return;
      }

      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;

      // Convert screen coordinates to world coordinates
      const worldPos = this.renderer.screenToWorld(x, y);

      if (this.mode === 'addArc' && this.arcDrawing) {
        this.completeArcDrawing(worldPos.x, worldPos.y);
      }

      // Reset drag variables
      this.dragStart = null;
      this.dragOffset = null; // Reset dragOffset when done dragging
      
      this.render();

      if (this.callbacks.onChange) {
        this.callbacks.onChange();
      }
    };

    // Mouse wheel event for zooming
    const mouseWheelHandler = (event) => {
      event.preventDefault();
      
      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;
      
      // Determine zoom direction and factor
      const delta = event.deltaY < 0 ? 1.1 : 0.9;
      
      // Adjust zoom centered on the mouse position
      this.renderer.adjustZoom(delta, x, y);
      this.render();
    };

    // Keyboard events for panning with space bar
    const keyDownHandler = (event) => {
      // Space key
      if (event.code === this.PAN_KEY_BUTTON_CODE) {
        this.isPanningKeyPressed = true;
        this.canvas.style.cursor = 'grab';
      }
    };

    const keyUpHandler = (event) => {
      // Space key
      if (event.code === this.PAN_KEY_BUTTON_CODE) {
        this.isPanningKeyPressed = false;
        this.canvas.style.cursor = 'default';
      }
    };

    // Add all event listeners
    this.canvas.addEventListener('mousedown', mouseDownHandler);
    this.canvas.addEventListener('mousemove', mouseMoveHandler);
    this.canvas.addEventListener('mouseup', mouseUpHandler);
    this.canvas.addEventListener('wheel', mouseWheelHandler, { passive: false });
    document.addEventListener('keydown', keyDownHandler);
    document.addEventListener('keyup', keyUpHandler);

    // Store event listeners so they can be removed later
    this.eventListeners.set('mousedown', mouseDownHandler);
    this.eventListeners.set('mousemove', mouseMoveHandler);
    this.eventListeners.set('mouseup', mouseUpHandler);
    this.eventListeners.set('wheel', mouseWheelHandler);
    this.eventListeners.set('keydown', keyDownHandler);
    this.eventListeners.set('keyup', keyUpHandler);
  }

  handleSelection(x, y) {
    // Try to select a place
    for (const [id, place] of this.petriNet.places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= place.radius) {
        this.selectedElement = { id, type: 'place' };
        // Calculate and store drag offset
        this.dragOffset = {
          x: x - place.position.x,
          y: y - place.position.y
        };
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(id, 'place');
        }
        return;
      }
    }

    // Try to select a transition
    for (const [id, transition] of this.petriNet.transitions) {
      const halfWidth = transition.width / 2;
      const halfHeight = transition.height / 2;

      if (
        x >= transition.position.x - halfWidth &&
        x <= transition.position.x + halfWidth &&
        y >= transition.position.y - halfHeight &&
        y <= transition.position.y + halfHeight
      ) {
        this.selectedElement = { id, type: 'transition' };
        // Calculate and store drag offset
        this.dragOffset = {
          x: x - transition.position.x,
          y: y - transition.position.y
        };
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(id, 'transition');
        }
        return;
      }
    }

    // Try to select an arc (more complex, simplified here)
    for (const [id, arc] of this.petriNet.arcs) {
      // Simple linear distance check - in a real implementation, this would need to be more sophisticated
      const sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
      const targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

      if (!sourceElement || !targetElement) continue;

      const sx = sourceElement.position.x;
      const sy = sourceElement.position.y;
      const tx = targetElement.position.x;
      const ty = targetElement.position.y;

      // Check if the point is close to the line
      const lineLength = Math.sqrt((tx - sx) * (tx - sx) + (ty - sy) * (ty - sy));
      const distance = Math.abs((ty - sy) * x - (tx - sx) * y + tx * sy - ty * sx) / lineLength;

      // Also check if the point is between the endpoints (projection onto the line segment)
      const dotProduct = ((x - sx) * (tx - sx) + (y - sy) * (ty - sy)) / (lineLength * lineLength);

      if (distance < 10 && dotProduct >= 0 && dotProduct <= 1) {
        this.selectedElement = { id, type: 'arc' };
        // For arcs, we don't need dragOffset as they're handled differently
        this.dragOffset = null;
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(id, 'arc');
        }
        return;
      }
    }

    // If we got here, nothing was selected
    this.selectedElement = null;
    this.dragOffset = null;
    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(null, null);
    }
  }

  handleDrag(x, y) {
    if (!this.selectedElement) return;

    // For arcs, keep the old differential movement approach
    if (this.selectedElement.type === 'arc') {
      if (!this.dragStart) return;
      
      const dx = x - this.dragStart.x;
      const dy = y - this.dragStart.y;
      
      // Arc handling code here (not implemented in this example)
      
      this.dragStart = { x, y };
      return;
    }

    // For places and transitions, use the absolute positioning with dragOffset
    if (!this.dragOffset) return;

    // Calculate new position using absolute positioning with offset
    const newX = x - this.dragOffset.x;
    const newY = y - this.dragOffset.y;

    if (this.selectedElement.type === 'place') {
      const place = this.petriNet.places.get(this.selectedElement.id);
      if (place) {
        place.position.x = newX;
        place.position.y = newY;

        if (this.snapToGrid) {
          place.position.x = Math.round(place.position.x / this.gridSize) * this.gridSize;
          place.position.y = Math.round(place.position.y / this.gridSize) * this.gridSize;
        }
      }
    } else if (this.selectedElement.type === 'transition') {
      const transition = this.petriNet.transitions.get(this.selectedElement.id);
      if (transition) {
        transition.position.x = newX;
        transition.position.y = newY;

        if (this.snapToGrid) {
          transition.position.x = Math.round(transition.position.x / this.gridSize) * this.gridSize;
          transition.position.y = Math.round(transition.position.y / this.gridSize) * this.gridSize;
        }
      }
    }
  }

  addPlace(x, y) {
    if (this.snapToGrid) {
      x = Math.round(x / this.gridSize) * this.gridSize;
      y = Math.round(y / this.gridSize) * this.gridSize;
    }

    const id = this.generateUUID();
    const place = new Place(id, { x, y }, `P${this.petriNet.places.size + 1}`);
    this.petriNet.addPlace(place);
    this.selectedElement = { id, type: 'place' };

    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(id, 'place');
    }
  }

  addTransition(x, y) {
    if (this.snapToGrid) {
      x = Math.round(x / this.gridSize) * this.gridSize;
      y = Math.round(y / this.gridSize) * this.gridSize;
    }

    const id = this.generateUUID();
    const transition = new Transition(id, { x, y }, `T${this.petriNet.transitions.size + 1}`);
    this.petriNet.addTransition(transition);
    this.selectedElement = { id, type: 'transition' };

    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(id, 'transition');
    }
  }

  startArcDrawing(x, y) {
    // Try to find a source element for the arc
    for (const [id, place] of this.petriNet.places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= place.radius) {
        this.arcDrawing = { sourceId: id, sourceType: 'place' };
        return;
      }
    }

    for (const [id, transition] of this.petriNet.transitions) {
      const halfWidth = transition.width / 2;
      const halfHeight = transition.height / 2;

      if (
        x >= transition.position.x - halfWidth &&
        x <= transition.position.x + halfWidth &&
        y >= transition.position.y - halfHeight &&
        y <= transition.position.y + halfHeight
      ) {
        this.arcDrawing = { sourceId: id, sourceType: 'transition' };
        return;
      }
    }
  }

  renderArcDrawing(x, y) {
    if (!this.arcDrawing) return;

    const sourceElement = this.arcDrawing.sourceType === 'place'
      ? this.petriNet.places.get(this.arcDrawing.sourceId)
      : this.petriNet.transitions.get(this.arcDrawing.sourceId);

    if (!sourceElement) return;

    // Save the current state, apply transforms, and restore after drawing
    this.renderer.ctx.save();
    this.renderer.ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    this.renderer.ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    this.renderer.ctx.beginPath();
    this.renderer.ctx.moveTo(sourceElement.position.x, sourceElement.position.y);
    this.renderer.ctx.lineTo(x, y);
    this.renderer.ctx.strokeStyle = 'rgba(0, 0, 0, 0.5)';
    this.renderer.ctx.lineWidth = 1.5;
    this.renderer.ctx.stroke();

    // Draw arrowhead
    const angle = Math.atan2(y - sourceElement.position.y, x - sourceElement.position.x);
    const arrowSize = 10;
    const arrowAngle = Math.PI / 6; // 30 degrees

    this.renderer.ctx.beginPath();
    this.renderer.ctx.moveTo(x, y);
    this.renderer.ctx.lineTo(
      x - arrowSize * Math.cos(angle - arrowAngle),
      y - arrowSize * Math.sin(angle - arrowAngle)
    );
    this.renderer.ctx.lineTo(
      x - arrowSize * Math.cos(angle + arrowAngle),
      y - arrowSize * Math.sin(angle + arrowAngle)
    );
    this.renderer.ctx.closePath();
    this.renderer.ctx.fillStyle = 'rgba(0, 0, 0, 0.5)';
    this.renderer.ctx.fill();

    this.renderer.ctx.restore();
  }

  completeArcDrawing(x, y) {
    if (!this.arcDrawing) return;

    // Find target element
    let targetId = null;
    let targetType = null;

    // Try to find a place as the target
    for (const [id, place] of this.petriNet.places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= place.radius) {
        targetId = id;
        targetType = 'place';
        break;
      }
    }

    // If no place found, try to find a transition
    if (!targetId) {
      for (const [id, transition] of this.petriNet.transitions) {
        const halfWidth = transition.width / 2;
        const halfHeight = transition.height / 2;

        if (
          x >= transition.position.x - halfWidth &&
          x <= transition.position.x + halfWidth &&
          y >= transition.position.y - halfHeight &&
          y <= transition.position.y + halfHeight
        ) {
          targetId = id;
          targetType = 'transition';
          break;
        }
      }
    }

    // Validate that we have a valid arc (place -> transition or transition -> place)
    if (targetId && targetType &&
      ((this.arcDrawing.sourceType === 'place' && targetType === 'transition') ||
        (this.arcDrawing.sourceType === 'transition' && targetType === 'place'))) {

      const arcId = this.generateUUID();
      const arc = new Arc(
        arcId,
        this.arcDrawing.sourceId,
        targetId,
        1, // default weight
        "regular", // default type
        [], // no control points by default
        "" // default label
      );

      if (this.petriNet.addArc(arc)) {
        this.selectedElement = { id: arcId, type: 'arc' };
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(arcId, 'arc');
        }
      }
    }

    this.arcDrawing = null;
  }

  render() {
    this.petriNet.updateEnabledTransitions();
    this.renderer.render();
    this.renderSelection();
  }

  renderSelection() {
    if (!this.selectedElement) return;

    const ctx = this.canvas.getContext('2d');
    
    // Save the context, apply transformations, and restore after drawing
    ctx.save();
    ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    if (this.selectedElement.type === 'place') {
      const place = this.petriNet.places.get(this.selectedElement.id);
      if (place) {
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 4, 0, Math.PI * 2);
        ctx.strokeStyle = this.renderer.theme.selectedColor;
        ctx.lineWidth = 2;
        ctx.stroke();
      }
    } else if (this.selectedElement.type === 'transition') {
      const transition = this.petriNet.transitions.get(this.selectedElement.id);
      if (transition) {
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 4,
          transition.position.y - transition.height / 2 - 4,
          transition.width + 8,
          transition.height + 8
        );
        ctx.strokeStyle = this.renderer.theme.selectedColor;
        ctx.lineWidth = 2;
        ctx.stroke();
      }
    } else if (this.selectedElement.type === 'arc') {
      const arc = this.petriNet.arcs.get(this.selectedElement.id);
      if (arc) {
        const sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
        const targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

        if (sourceElement && targetElement) {
          const { start, end } = this.renderer.calculateArcEndpoints(sourceElement, targetElement);

          ctx.beginPath();
          ctx.moveTo(start.x, start.y);
          if (arc.points.length > 0) {
            for (const point of arc.points) {
              ctx.lineTo(point.x, point.y);
            }
          }
          ctx.lineTo(end.x, end.y);
          ctx.strokeStyle = this.renderer.theme.selectedColor;
          ctx.lineWidth = 3;
          ctx.stroke();
        }
      }
    }
    
    ctx.restore();
  }

  // API methods for editor
  setMode(mode) {
    this.mode = mode;
    this.arcDrawing = null;
  }

  selectElement(id, type) {
    if (id && type) {
      this.selectedElement = { id, type };
      
      // Set dragOffset if selecting a place or transition programmatically
      if (type === 'place') {
        const place = this.petriNet.places.get(id);
        if (place) {
          this.dragOffset = { x: 0, y: 0 }; // Default offset
        }
      } else if (type === 'transition') {
        const transition = this.petriNet.transitions.get(id);
        if (transition) {
          this.dragOffset = { x: 0, y: 0 }; // Default offset
        }
      } else {
        this.dragOffset = null;
      }
    } else {
      this.selectedElement = null;
      this.dragOffset = null;
    }
    this.render();

    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(id, type);
    }
  }

  deleteSelected() {
    if (!this.selectedElement) return false;

    let success = false;
    if (this.selectedElement.type === 'place') {
      success = this.petriNet.removePlace(this.selectedElement.id);
    } else if (this.selectedElement.type === 'transition') {
      success = this.petriNet.removeTransition(this.selectedElement.id);
    } else if (this.selectedElement.type === 'arc') {
      success = this.petriNet.removeArc(this.selectedElement.id);
    }

    if (success) {
      this.selectedElement = null;
      this.dragOffset = null;
      this.render();

      if (this.callbacks.onChange) {
        this.callbacks.onChange();
      }

      if (this.callbacks.onSelect) {
        this.callbacks.onSelect(null, null);
      }
    }

    return success;
  }

  updatePlaceTokens(id, tokens) {
    const place = this.petriNet.places.get(id);
    if (!place) return false;

    place.tokens = tokens;
    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }

    return true;
  }

  updateArcWeight(id, weight) {
    const arc = this.petriNet.arcs.get(id);
    if (!arc) return false;

    arc.weight = weight;
    arc.label = weight.toString();
    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }

    return true;
  }

  updateArcType(id, type) {
    const arc = this.petriNet.arcs.get(id);
    if (!arc) return false;

    arc.type = type;
    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }

    return true;
  }

  updateElementLabel(id, type, label) {
    let element;

    if (type === 'place') {
      element = this.petriNet.places.get(id);
    } else if (type === 'transition') {
      element = this.petriNet.transitions.get(id);
    } else {
      element = this.petriNet.arcs.get(id);
    }

    if (!element) return false;

    element.label = label;
    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }

    return true;
  }

  setSnapToGrid(enabled, gridSize) {
    this.snapToGrid = enabled;
    if (gridSize !== undefined) {
      this.gridSize = gridSize;
    }
  }

  fireTransition(id) {
    const success = this.petriNet.fireTransition(id);
    if (success) {
      this.render();

      if (this.callbacks.onChange) {
        this.callbacks.onChange();
      }
    }
    return success;
  }

  resetSimulation() {
    // This would reset token counts to initial state
    // For simplicity, not fully implemented
    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }
  }

  // Pan and zoom controls
  resetView() {
    this.renderer.resetView();
    this.render();
  }

  // Event callbacks
  setOnChangeCallback(callback) {
    this.callbacks.onChange = callback;
  }

  setOnSelectCallback(callback) {
    this.callbacks.onSelect = callback;
  }

  // Clean up event listeners
  destroy() {
    for (const [event, listener] of this.eventListeners) {
      if (event === 'keydown' || event === 'keyup') {
        document.removeEventListener(event, listener);
      } else {
        this.canvas.removeEventListener(event, listener);
      }
    }
    this.eventListeners.clear();
  }

  // Utility methods
  generateUUID() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}

// Main PetriNetAPI Class
class PetriNetAPI {
  constructor(id, name, description) {
    this.petriNet = new PetriNet(
      id || this.generateUUID(),
      name || "New Petri Net",
      description || ""
    );
    this.editor = null;
    this.canvas = null;
  }

  // Setup methods
  attachEditor(canvasElement) {
    this.canvas = canvasElement;
    this.editor = new PetriNetEditor(canvasElement, this.petriNet);
    return this.editor;
  }

  getEditor() {
    return this.editor;
  }

  // Petri net structure manipulation
  createPlace(x, y, label, tokens = 0) {
    const id = this.generateUUID();
    const place = new Place(id, { x, y }, label || `P${this.petriNet.places.size + 1}`, tokens);
    this.petriNet.addPlace(place);
    if (this.editor) this.editor.render();
    return id;
  }

  createTransition(x, y, label) {
    const id = this.generateUUID();
    const transition = new Transition(
      id,
      { x, y },
      label || `T${this.petriNet.transitions.size + 1}`
    );
    this.petriNet.addTransition(transition);
    if (this.editor) this.editor.render();
    return id;
  }

  createArc(sourceId, targetId, weight = 1, type = "regular") {
    const id = this.generateUUID();
    const arc = new Arc(id, sourceId, targetId, weight, type);

    if (this.petriNet.addArc(arc)) {
      if (this.editor) this.editor.render();
      return id;
    }

    return null;
  }

  removeElement(id) {
    if (this.petriNet.places.has(id)) {
      const success = this.petriNet.removePlace(id);
      if (success && this.editor) this.editor.render();
      return success;
    }

    if (this.petriNet.transitions.has(id)) {
      const success = this.petriNet.removeTransition(id);
      if (success && this.editor) this.editor.render();
      return success;
    }

    if (this.petriNet.arcs.has(id)) {
      const success = this.petriNet.removeArc(id);
      if (success && this.editor) this.editor.render();
      return success;
    }

    return false;
  }

  // Element property manipulation
  setLabel(id, label) {
    let element;

    if (this.petriNet.places.has(id)) {
      element = this.petriNet.places.get(id);
    } else if (this.petriNet.transitions.has(id)) {
      element = this.petriNet.transitions.get(id);
    } else if (this.petriNet.arcs.has(id)) {
      element = this.petriNet.arcs.get(id);
    }

    if (!element) return false;

    element.label = label;
    if (this.editor) this.editor.render();
    return true;
  }

  setPosition(id, x, y) {
    let element;

    if (this.petriNet.places.has(id)) {
      element = this.petriNet.places.get(id);
    } else if (this.petriNet.transitions.has(id)) {
      element = this.petriNet.transitions.get(id);
    } else {
      return false;
    }

    element.position = { x, y };
    if (this.editor) this.editor.render();
    return true;
  }

  setPlaceTokens(id, tokens) {
    const place = this.petriNet.places.get(id);
    if (!place) return false;

    place.tokens = tokens;
    if (this.editor) this.editor.render();
    return true;
  }

  setArcWeight(id, weight) {
    const arc = this.petriNet.arcs.get(id);
    if (!arc) return false;

    arc.weight = weight;
    arc.label = weight.toString();
    if (this.editor) this.editor.render();
    return true;
  }

  setArcType(id, type) {
    const arc = this.petriNet.arcs.get(id);
    if (!arc) return false;

    arc.type = type;
    if (this.editor) this.editor.render();
    return true;
  }

  // Simulation methods
  fireTransition(id) {
    const success = this.petriNet.fireTransition(id);
    if (success && this.editor) this.editor.render();
    return success;
  }

  autoFireEnabledTransitions(maxSteps = 10) {
    let steps = 0;
    let firedAny = false;

    do {
      firedAny = false;

      // Find all enabled transitions
      this.petriNet.updateEnabledTransitions();
      const enabledTransitions = [];

      for (const [id, transition] of this.petriNet.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }

      // Sort by priority
      enabledTransitions.sort((a, b) => {
        const transA = this.petriNet.transitions.get(a);
        const transB = this.petriNet.transitions.get(b);
        return (transB?.priority || 0) - (transA?.priority || 0);
      });

      // Fire the highest priority transition
      if (enabledTransitions.length > 0) {
        firedAny = this.petriNet.fireTransition(enabledTransitions[0]);
        if (firedAny) steps++;
      }
    } while (firedAny && steps < maxSteps);

    if (this.editor) this.editor.render();
    return steps;
  }

  // Analysis methods
  getEnabledTransitions() {
    this.petriNet.updateEnabledTransitions();
    const enabled = [];

    for (const [id, transition] of this.petriNet.transitions) {
      if (transition.isEnabled) {
        enabled.push(id);
      }
    }

    return enabled;
  }

  detectDeadlocks() {
    return this.petriNet.detectDeadlocks();
  }

  // Pan and zoom methods
  resetView() {
    if (this.editor) {
      this.editor.resetView();
    }
  }

  // Import/Export methods
  exportAsJSON() {
    return this.petriNet.toJSON();
  }

  static importFromJSON(json) {
    const petriNet = PetriNet.fromJSON(json);
    const api = new PetriNetAPI();
    api.petriNet = petriNet;
    return api;
  }

  exportAsPNML() {
    return this.petriNet.toPNML();
  }

  // Utility methods
  generateUUID() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }


  /**
  * Performs automatic layout of the Petri net elements.
  * @param {Object} options - Layout options
  * @param {number} [options.horizontalSpacing=150] - Horizontal spacing between nodes
  * @param {number} [options.verticalSpacing=100] - Vertical spacing between layers
  * @param {number} [options.startX=100] - Starting X coordinate
  * @param {number} [options.startY=100] - Starting Y coordinate
  * @param {string} [options.direction='horizontal'] - Layout direction ('horizontal' or 'vertical')
  * @param {boolean} [options.centerGraph=true] - Whether to center the graph in the canvas
  * @returns {boolean} - Success of the operation
  */
  autoLayout(options = {}) {
    // Default options
    const opts = {
      horizontalSpacing: options.horizontalSpacing || 150,
      verticalSpacing: options.verticalSpacing || 100,
      startX: options.startX || 100,
      startY: options.startY || 100,
      direction: options.direction || 'horizontal',
      centerGraph: options.centerGraph !== undefined ? options.centerGraph : true
    };

    // If the graph is empty, nothing to do
    if (this.petriNet.places.size === 0 && this.petriNet.transitions.size === 0) {
      return false;
    }

    // Step 1: Create a layered representation of the graph
    const { layers, nodeToLayer } = this.calculateLayers();

    // Step 2: Assign positions based on layers
    this.assignPositions(layers, nodeToLayer, opts);

    // Step 3: Center the graph in the canvas if requested
    if (opts.centerGraph && this.canvas) {
      this.centerGraph();
    }

    // Step 4: Update the view
    if (this.editor) {
      this.editor.render();
    }

    return true;
  }

  /**
   * Calculates layers for the Petri net based on a topological sort
   * @returns {Object} layers and nodeToLayer mapping
   * @private
   */
  calculateLayers() {
    // Create a map to track each node's layer
    const nodeToLayer = new Map();

    // Create a map to track dependencies (incoming edges count)
    const incomingEdges = new Map();

    // Map to collect all nodes (places and transitions)
    const allNodes = new Map();

    // Initialize all places and transitions as nodes
    for (const [id, place] of this.petriNet.places) {
      allNodes.set(id, place);
      incomingEdges.set(id, 0);
    }

    for (const [id, transition] of this.petriNet.transitions) {
      allNodes.set(id, transition);
      incomingEdges.set(id, 0);
    }

    // Count incoming edges for each node
    for (const [id, arc] of this.petriNet.arcs) {
      const targetId = arc.target;
      incomingEdges.set(targetId, (incomingEdges.get(targetId) || 0) + 1);
    }

    // Find nodes with no incoming edges (sources)
    const sources = [];
    for (const [id] of allNodes) {
      if (incomingEdges.get(id) === 0) {
        sources.push(id);
      }
    }

    // If no sources found (might be a cycle), pick a random node as source
    if (sources.length === 0 && allNodes.size > 0) {
      const someNodeId = allNodes.keys().next().value;
      sources.push(someNodeId);
    }

    // Build layers using a breadth-first approach
    const layers = [];
    const visited = new Set();
    let currentLayer = [...sources];

    while (currentLayer.length > 0) {
      layers.push([...currentLayer]);

      // Assign layer number to nodes
      currentLayer.forEach((nodeId) => {
        nodeToLayer.set(nodeId, layers.length - 1);
        visited.add(nodeId);
      });

      // Find next layer nodes
      const nextLayer = [];
      for (const nodeId of currentLayer) {
        // Find all outgoing arcs from this node
        const outgoingArcs = Array.from(this.petriNet.arcs.values())
          .filter(arc => arc.source === nodeId);

        // Add targets to next layer if all dependencies are visited
        for (const arc of outgoingArcs) {
          const targetId = arc.target;
          if (!visited.has(targetId)) {
            // Decrement incoming edge count
            incomingEdges.set(targetId, incomingEdges.get(targetId) - 1);

            // If all dependencies are processed, add to next layer
            if (incomingEdges.get(targetId) === 0) {
              nextLayer.push(targetId);
            }
          }
        }
      }

      // Use next layer for next iteration
      currentLayer = nextLayer;
    }

    // Handle nodes not yet visited (might be disconnected or in cycles)
    const unvisitedNodes = Array.from(allNodes.keys()).filter(id => !visited.has(id));
    if (unvisitedNodes.length > 0) {
      // Add them to a new layer or distribute them among existing layers
      // For simplicity, we'll add them to a new layer
      layers.push(unvisitedNodes);
      unvisitedNodes.forEach(nodeId => {
        nodeToLayer.set(nodeId, layers.length - 1);
      });
    }

    return { layers, nodeToLayer };
  }

  /**
   * Assigns positions to all nodes based on their layers
   * @param {Array<Array<string>>} layers - Array of layers, each containing node IDs
   * @param {Map<string, number>} nodeToLayer - Map from node ID to layer number
   * @param {Object} options - Layout options
   * @private
   */
  assignPositions(layers, nodeToLayer, options) {
    const isHorizontal = options.direction === 'horizontal';
    const { horizontalSpacing, verticalSpacing, startX, startY } = options;

    // Calculate node positions within each layer
    layers.forEach((layerNodes, layerIndex) => {
      // Separate places and transitions for better visual grouping
      const places = layerNodes.filter(id => this.petriNet.places.has(id));
      const transitions = layerNodes.filter(id => this.petriNet.transitions.has(id));

      // Position places and transitions in their layer
      let nodeIndex = 0;

      // First position places
      places.forEach(placeId => {
        const place = this.petriNet.places.get(placeId);
        if (place) {
          if (isHorizontal) {
            place.position.x = startX + layerIndex * horizontalSpacing;
            place.position.y = startY + nodeIndex * verticalSpacing;
          } else {
            place.position.x = startX + nodeIndex * horizontalSpacing;
            place.position.y = startY + layerIndex * verticalSpacing;
          }
          nodeIndex++;
        }
      });

      // Then position transitions
      transitions.forEach(transitionId => {
        const transition = this.petriNet.transitions.get(transitionId);
        if (transition) {
          if (isHorizontal) {
            transition.position.x = startX + layerIndex * horizontalSpacing;
            transition.position.y = startY + nodeIndex * verticalSpacing;
          } else {
            transition.position.x = startX + nodeIndex * horizontalSpacing;
            transition.position.y = startY + layerIndex * verticalSpacing;
          }
          nodeIndex++;
        }
      });
    });

    // Optionally apply a second pass to improve layout by considering connected nodes
    this.optimizeNodePositions(nodeToLayer, options);
  }

  /**
   * Optimizes node positions to reduce edge crossings and improve layout
   * @param {Map<string, number>} nodeToLayer - Map from node ID to layer number
   * @param {Object} options - Layout options
   * @private
   */
  optimizeNodePositions(nodeToLayer, options) {
    // For each node, try to position it close to the average Y position of its connected nodes
    const isHorizontal = options.direction === 'horizontal';

    // First collect all connected nodes information
    const connections = new Map();

    // Process each arc to build connection info
    for (const [id, arc] of this.petriNet.arcs) {
      const sourceId = arc.source;
      const targetId = arc.target;

      // Add connection to source node
      if (!connections.has(sourceId)) {
        connections.set(sourceId, []);
      }
      connections.get(sourceId).push(targetId);

      // Add reverse connection to target node
      if (!connections.has(targetId)) {
        connections.set(targetId, []);
      }
      connections.get(targetId).push(sourceId);
    }

    // Optimize positions within each layer by considering connected nodes
    // For simplicity, we'll just do a single pass - more complex algorithms would do multiple passes
    for (const [nodeId, connectedIds] of connections) {
      let element;
      if (this.petriNet.places.has(nodeId)) {
        element = this.petriNet.places.get(nodeId);
      } else if (this.petriNet.transitions.has(nodeId)) {
        element = this.petriNet.transitions.get(nodeId);
      } else {
        continue;
      }

      // Get all connected nodes that exist
      const connectedElements = connectedIds
        .map(id => {
          if (this.petriNet.places.has(id)) return this.petriNet.places.get(id);
          if (this.petriNet.transitions.has(id)) return this.petriNet.transitions.get(id);
          return null;
        })
        .filter(e => e !== null);

      // If there are connected nodes, adjust position to be closer to their average position
      if (connectedElements.length > 0) {
        // Only adjust nodes within the same column/row if we're doing horizontal/vertical layout
        const currentLayer = nodeToLayer.get(nodeId);

        // Get connected nodes from different layers
        const otherLayerNodes = connectedElements.filter(e => {
          const elementId = this.findElementId(e);
          if (!elementId) return false;
          return nodeToLayer.get(elementId) !== currentLayer;
        });

        if (otherLayerNodes.length > 0) {
          // Calculate average position of connected nodes from other layers
          const positionSum = otherLayerNodes.reduce((sum, e) => {
            const pos = isHorizontal ? e.position.y : e.position.x;
            return sum + pos;
          }, 0);

          const avgPosition = positionSum / otherLayerNodes.length;

          // Adjust this node's position to be closer to the average
          // Use a damping factor to avoid extreme changes
          const damping = 0.5;
          if (isHorizontal) {
            element.position.y = element.position.y * (1 - damping) + avgPosition * damping;
          } else {
            element.position.x = element.position.x * (1 - damping) + avgPosition * damping;
          }
        }
      }
    }
  }

  /**
   * Centers the graph in the canvas
   * @private
   */
  centerGraph() {
    if (!this.canvas) return;

    // Get bounding box of the entire graph
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

    // Check all places
    for (const [, place] of this.petriNet.places) {
      minX = Math.min(minX, place.position.x - place.radius);
      minY = Math.min(minY, place.position.y - place.radius);
      maxX = Math.max(maxX, place.position.x + place.radius);
      maxY = Math.max(maxY, place.position.y + place.radius);
    }

    // Check all transitions
    for (const [, transition] of this.petriNet.transitions) {
      minX = Math.min(minX, transition.position.x - transition.width / 2);
      minY = Math.min(minY, transition.position.y - transition.height / 2);
      maxX = Math.max(maxX, transition.position.x + transition.width / 2);
      maxY = Math.max(maxY, transition.position.y + transition.height / 2);
    }

    // Calculate center offset
    const graphWidth = maxX - minX;
    const graphHeight = maxY - minY;
    const canvasWidth = this.canvas.width;
    const canvasHeight = this.canvas.height;

    const offsetX = (canvasWidth - graphWidth) / 2 - minX;
    const offsetY = (canvasHeight - graphHeight) / 2 - minY;

    // Apply offset to all elements
    for (const [, place] of this.petriNet.places) {
      place.position.x += offsetX;
      place.position.y += offsetY;
    }

    for (const [, transition] of this.petriNet.transitions) {
      transition.position.x += offsetX;
      transition.position.y += offsetY;
    }
  }

  /**
   * Helper method to find the ID of a place or transition element
   * @param {Object} element - The element to find
   * @returns {string|null} - The ID of the element or null if not found
   * @private
   */
  findElementId(element) {
    // Find the ID of a place
    for (const [id, place] of this.petriNet.places) {
      if (place === element) return id;
    }

    // Find the ID of a transition
    for (const [id, transition] of this.petriNet.transitions) {
      if (transition === element) return id;
    }

    return null;
  }

}

// Export the main classes
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    PetriNetAPI,
    PetriNetEditor,
    PetriNetRenderer,
    PetriNet,
    Place,
    Transition,
    Arc
  };
}