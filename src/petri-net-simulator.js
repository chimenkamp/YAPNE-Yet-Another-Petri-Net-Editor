/**
 * Petri Net Editor
 * A standalone JavaScript implementation of a Petri net editor.
 */






class PetriNetElement {
  constructor(id, position, label = "") {
    this.id = id;
    this.position = position;
    this.label = label;
  }
}

class Place extends PetriNetElement {
  constructor(id, position, label = "", tokens = 0, capacity = null, finalMarking = null) {
    super(id, position, label);
    this.tokens = tokens;
    this.capacity = capacity;
    this.finalMarking = finalMarking;
    this.radius = 20;
  }

  // Add these new methods
  hasReachedFinalMarking() {
    return this.finalMarking !== null && this.tokens === this.finalMarking;
  }

  hasFinalMarking() {
    return this.finalMarking !== null && this.finalMarking >= 0;
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


class PetriNet {
  constructor(id, name = "New Petri Net", description = "") {
    this.id = id;
    this.name = name;
    this.places = new Map();
    this.transitions = new Map();
    this.arcs = new Map();
    this.description = description;
  }


  addPlace(place) {
    this.places.set(place.id, place);
  }

  getPlace(id) {
    return this.places.get(id);
  }

  removePlace(id) {

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

    this.arcs.forEach((arc, arcId) => {
      if (arc.source === id || arc.target === id) {
        this.arcs.delete(arcId);
      }
    });
    return this.transitions.delete(id);
  }

  addArc(arc) {

    const sourceExists = this.places.has(arc.source) || this.transitions.has(arc.source);
    const targetExists = this.places.has(arc.target) || this.transitions.has(arc.target);

    if (!sourceExists || !targetExists) {
      return false;
    }


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

        if (place.tokens >= arc.weight) return false;
      } else if (arc.type === "regular") {

        if (place.tokens < arc.weight) return false;
      }

    }

    return true;
  }

  fireTransition(transitionId) {
    if (!this.isTransitionEnabled(transitionId)) {
      return false;
    }


    const incomingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.target === transitionId);
    const outgoingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.source === transitionId);


    for (const arc of incomingArcs) {
      const place = this.places.get(arc.source);
      if (!place) continue;

      if (arc.type === "regular") {
        place.removeTokens(arc.weight);
      } else if (arc.type === "reset") {
        place.tokens = 0;
      }

    }


    for (const arc of outgoingArcs) {
      const place = this.places.get(arc.target);
      if (!place) continue;

      place.addTokens(arc.weight);
    }

    return true;
  }


  getReachabilityGraph() {



    return { nodes: [], edges: [] };
  }

  detectDeadlocks() {


    const deadlockedTransitions = [];


    for (const [id, transition] of this.transitions) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === id && arc.type === "regular");


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


  toPNML() {
    let pnml = `<?xml version="1.0" encoding="UTF-8"?>
  <pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
    <net id="${this.id}" type="http://www.pnml.org/version-2009/grammar/ptnet">
      <n>
        <text>${this.name}</text>
      </n>`;


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



class PetriNetRenderer {
  constructor(canvas, petriNet) {
    this.canvas = canvas;
    this.ctx = canvas.getContext('2d');
    this.petriNet = petriNet;


    this.panOffset = { x: 0, y: 0 };
    this.zoomFactor = 1.0;
    this.minZoom = 0.1;
    this.maxZoom = 3.0;
    this.zoomSensitivity = 0.1; // Default zoom sensitivity


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
      backgroundColor: '#ffffff',
      ghostColor: 'rgba(0, 0, 0, 0.3)',
      ghostFillColor: 'rgba(255, 255, 255, 0.5)'
    };
  }

  clone() {
    const cloned = new PetriNetRenderer(this.canvas, this.petriNet);
    cloned.panOffset = { ...this.panOffset };
    cloned.zoomFactor = this.zoomFactor;
    cloned.theme = { ...this.theme };
    return cloned;
  }

  render() {
    this.clear();
    

    this.ctx.save();
    this.ctx.translate(this.panOffset.x, this.panOffset.y);
    this.ctx.scale(this.zoomFactor, this.zoomFactor);
    
    this.drawArcs();
    this.drawPlaces();
    this.drawTransitions();
    

    this.ctx.restore();
  }

  clear() {
    this.ctx.fillStyle = this.theme.backgroundColor;
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
  }

drawPlaces() {
  for (const [id, place] of this.petriNet.places) {
    // Main place circle
    this.ctx.beginPath();
    this.ctx.arc(place.position.x, place.position.y, place.radius, 0, Math.PI * 2);
    this.ctx.fillStyle = this.theme.placeColor;
    this.ctx.fill();
    
    // Base stroke
    this.ctx.strokeStyle = this.theme.placeStroke;
    this.ctx.lineWidth = 2;
    this.ctx.stroke();

    // Draw final marking indicator if place has final marking
    if (place.hasFinalMarking()) {
      // Draw double border for final marking places
      this.ctx.beginPath();
      this.ctx.arc(place.position.x, place.position.y, place.radius + 3, 0, Math.PI * 2);
      
      // Color based on whether final marking is reached
      if (place.hasReachedFinalMarking()) {
        this.ctx.strokeStyle = '#A3BE8C'; // Green - final marking reached
      } else {
        this.ctx.strokeStyle = '#EBCB8B'; // Yellow - final marking not reached
      }
      this.ctx.lineWidth = 2;
      this.ctx.stroke();
      
      // Draw final marking number in top-right corner
      this.ctx.fillStyle = place.hasReachedFinalMarking() ? '#A3BE8C' : '#EBCB8B';
      this.ctx.font = 'bold 12px Arial';
      this.ctx.textAlign = 'center';
      this.ctx.textBaseline = 'middle';
      
      // Background circle for the final marking number
      const fmX = place.position.x + place.radius * 0.7;
      const fmY = place.position.y - place.radius * 0.7;
      
      this.ctx.beginPath();
      this.ctx.arc(fmX, fmY, 8, 0, Math.PI * 2);
      this.ctx.fill();
      
      // Final marking number text
      this.ctx.fillStyle = this.theme.backgroundColor;
      this.ctx.fillText(place.finalMarking.toString(), fmX, fmY);
    }

    // Draw tokens (keep existing drawTokens call)
    this.drawTokens(place);

    // Draw label (keep existing label drawing)
    this.ctx.fillStyle = this.theme.textColor;
    this.ctx.font = '12px Arial';
    this.ctx.textAlign = 'center';
    this.ctx.fillText(place.label, place.position.x, place.position.y + place.radius + 15);
  }
}

  drawTokens(place) {
    const { x, y } = place.position;
    this.ctx.fillStyle = this.theme.tokenColor;


    if (place.tokens <= 3) {
      const tokenRadius = 4;
      for (let i = 0; i < place.tokens; i++) {
        let tokenX = x;
        let tokenY = y;


        if (place.tokens === 1) {

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

      this.ctx.font = '14px Arial';
      this.ctx.textAlign = 'center';
      this.ctx.textBaseline = 'middle';
      this.ctx.fillText(place.tokens.toString(), x, y);
    }
  }

  drawTransitions() {
    for (const [id, transition] of this.petriNet.transitions) {

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
      let sourceElement;
      let targetElement;

      sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
      targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

      if (!sourceElement || !targetElement) continue;

      const { start, end } = this.calculateArcEndpoints(sourceElement, targetElement);

      // Set line style based on arc type
      this.ctx.save();
      
      // Modifier arcs use dotted lines
      if (arc.type === "modifier") {
        this.ctx.setLineDash([5, 5]);
      } else {
        this.ctx.setLineDash([]);
      }

      // Draw the arc line
      this.ctx.beginPath();
      this.ctx.moveTo(start.x, start.y);

      if (arc.points.length > 0) {
        for (const point of arc.points) {
          this.ctx.lineTo(point.x, point.y);
        }
      }

      this.ctx.lineTo(end.x, end.y);
      this.ctx.strokeStyle = this.theme.arcColor;
      this.ctx.lineWidth = 1.5;
      this.ctx.stroke();

      // Calculate direction for arc endings
      const direction = this.calculateArcDirection(
        arc.points.length > 0 ? arc.points[arc.points.length - 1] : start, 
        end
      );

      // Draw different endings based on arc type
      switch (arc.type) {
        case "inhibitor":
          this.drawInhibitorEnding(end, direction);
          break;
        case "read":
          this.drawReadArcEnding(end, direction);
          break;
        case "reset":
          this.drawResetArcEnding(end, direction);
          break;
        case "modifier":
          this.drawModifierArcEnding(end, direction);
          break;
        default: // regular arc
          this.drawArrowhead(end, direction);
          break;
      }

      this.ctx.restore();

      // Draw arc weight/label if needed
      if (arc.weight > 1 || arc.label) {
        const midpoint = this.calculateArcMidpoint(arc, start, end);
        this.ctx.fillStyle = this.theme.textColor;
        this.ctx.font = '12px Arial';
        this.ctx.textAlign = 'center';
        this.ctx.textBaseline = 'middle';
        
        // Create background for better readability
        const label = arc.label || arc.weight.toString();
        const metrics = this.ctx.measureText(label);
        const padding = 3;
        
        this.ctx.fillStyle = this.theme.backgroundColor;
        this.ctx.fillRect(
          midpoint.x - metrics.width / 2 - padding,
          midpoint.y - 7 - padding,
          metrics.width + padding * 2,
          14 + padding * 2
        );
        
        this.ctx.fillStyle = this.theme.textColor;
        this.ctx.fillText(label, midpoint.x, midpoint.y);
      }
    }
  }

  /**
   * Draws inhibitor arc ending (hollow circle)
   */
  drawInhibitorEnding(position, angle) {
    const circleRadius = 6;
    const offset = 10;
    
    // Position the circle slightly before the endpoint
    const circleX = position.x - Math.cos(angle) * offset;
    const circleY = position.y - Math.sin(angle) * offset;
    
    this.ctx.beginPath();
    this.ctx.arc(circleX, circleY, circleRadius, 0, Math.PI * 2);
    this.ctx.fillStyle = this.theme.backgroundColor;
    this.ctx.fill();
    this.ctx.strokeStyle = this.theme.arcColor;
    this.ctx.lineWidth = 1.5;
    this.ctx.stroke();
  }

  /**
   * Draws read arc ending (filled dot before arrow)
   */
  drawReadArcEnding(position, angle) {
    const dotRadius = 4;
    const dotOffset = 15;
    
    // Draw the arrow first
    this.drawArrowhead(position, angle);
    
    // Position the dot before the arrowhead
    const dotX = position.x - Math.cos(angle) * dotOffset;
    const dotY = position.y - Math.sin(angle) * dotOffset;
    
    this.ctx.beginPath();
    this.ctx.arc(dotX, dotY, dotRadius, 0, Math.PI * 2);
    this.ctx.fillStyle = this.theme.arcColor;
    this.ctx.fill();
  }

  /**
   * Draws reset arc ending (double arrow or special symbol)
   */
  drawResetArcEnding(position, angle) {
    // Draw double arrowhead for reset arc
    this.drawArrowhead(position, angle);
    
    // Draw second arrowhead slightly behind
    const offset = 8;
    const secondPos = {
      x: position.x - Math.cos(angle) * offset,
      y: position.y - Math.sin(angle) * offset
    };
    this.drawArrowhead(secondPos, angle);
  }

  /**
   * Draws modifier arc ending (dotted line with arrow)
   */
  drawModifierArcEnding(position, angle) {
    // Just draw a regular arrowhead, the line is already dotted
    this.drawArrowhead(position, angle);
  }

  /**
   * Enhanced arrowhead drawing
   */
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

  drawGhostPlace(position, isGhost = true) {
    const radius = 20;
    const alpha = isGhost ? 0.5 : 1.0;
    
    this.ctx.save();
    this.ctx.globalAlpha = alpha;
    
    this.ctx.beginPath();
    this.ctx.arc(position.x, position.y, radius, 0, Math.PI * 2);
    this.ctx.fillStyle = isGhost ? this.theme.ghostFillColor : this.theme.placeColor;
    this.ctx.fill();
    this.ctx.strokeStyle = isGhost ? this.theme.ghostColor : this.theme.placeStroke;
    this.ctx.lineWidth = 2;
    this.ctx.stroke();
    
    this.ctx.restore();
  }

  drawGhostTransition(position, isGhost = true) {
    const width = 20;
    const height = 50;
    const alpha = isGhost ? 0.5 : 1.0;
    
    this.ctx.save();
    this.ctx.globalAlpha = alpha;
    
    this.ctx.beginPath();
    this.ctx.rect(
      position.x - width / 2,
      position.y - height / 2,
      width,
      height
    );
    this.ctx.fillStyle = isGhost ? this.theme.ghostFillColor : this.theme.transitionColor;
    this.ctx.fill();
    this.ctx.strokeStyle = isGhost ? this.theme.ghostColor : this.theme.transitionStroke;
    this.ctx.lineWidth = 2;
    this.ctx.stroke();
    
    this.ctx.restore();
  }

  drawGhostArc(start, end, isGhost = true, arcType = "regular") {
    const alpha = isGhost ? 0.5 : 1.0;
    
    this.ctx.save();
    this.ctx.globalAlpha = alpha;
    
    // Set line style based on arc type
    if (arcType === "modifier") {
      this.ctx.setLineDash([5, 5]);
    } else {
      this.ctx.setLineDash([]);
    }
    
    this.ctx.beginPath();
    this.ctx.moveTo(start.x, start.y);
    this.ctx.lineTo(end.x, end.y);
    this.ctx.strokeStyle = isGhost ? this.theme.ghostColor : this.theme.arcColor;
    this.ctx.lineWidth = 1.5;
    this.ctx.stroke();

    // Draw appropriate ending based on type
    const angle = this.calculateArcDirection(start, end);
    
    switch (arcType) {
      case "inhibitor":
        this.drawInhibitorEnding(end, angle);
        break;
      case "read":
        this.drawReadArcEnding(end, angle);
        break;
      case "reset":
        this.drawResetArcEnding(end, angle);
        break;
      default:
        this.drawGhostArrowhead(end, angle, isGhost);
        break;
    }
    
    this.ctx.restore();
  }

  drawGhostArrowhead(position, angle, isGhost = true) {
    const arrowSize = 10;
    const arrowAngle = Math.PI / 6; // 30 degrees
    const alpha = isGhost ? 0.5 : 1.0;

    this.ctx.save();
    this.ctx.globalAlpha = alpha;

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
    this.ctx.fillStyle = isGhost ? this.theme.ghostColor : this.theme.arcColor;
    this.ctx.fill();

    this.ctx.restore();
  }

  calculateArcEndpoints(source, target) {


    let start = { x: source.position.x, y: source.position.y };
    let end = { x: target.position.x , y: target.position.y };


    if (source instanceof Place) {
      const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);
      start.x = source.position.x + Math.cos(angle) * source.radius;
      start.y = source.position.y + Math.sin(angle) * source.radius;
    }

    else if (source instanceof Transition) {
      const dx = target.position.x - source.position.x;
      const dy = target.position.y - source.position.y;
      const angle = Math.atan2(dy, dx);


      if (Math.abs(dx) * source.height > Math.abs(dy) * source.width) {

        const side = dx > 0 ? 1 : -1;
        start.x = source.position.x + side * source.width / 2;
        start.y = source.position.y + dy * (source.width / 2) / Math.abs(dx);
      } else {

        const side = dy > 0 ? 1 : -1;
        start.y = source.position.y + side * source.height / 2;
        start.x = source.position.x + dx * (source.height / 2) / Math.abs(dy);
      }
    }


    if (target instanceof Place) {
      const angle = Math.atan2(target.position.y - source.position.y, target.position.x - source.position.x);
      end.x = target.position.x - Math.cos(angle) * target.radius;
      end.y = target.position.y - Math.sin(angle) * target.radius;
    }

    else if (target instanceof Transition) {
      const dx = target.position.x - source.position.x;
      const dy = target.position.y - source.position.y;
      const angle = Math.atan2(dy, dx);


      if (Math.abs(dx) * target.height > Math.abs(dy) * target.width) {

        const side = dx > 0 ? 1 : -1;
        end.x = target.position.x - side * target.width / 2;
        end.y = target.position.y - dy * (target.width / 2) / Math.abs(dx);
      } else {

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

      const middleIndex = Math.floor(arc.points.length / 2);
      return arc.points[middleIndex];
    } else {

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


  setPan(x, y) {
    this.panOffset.x = x;
    this.panOffset.y = y;
  }

  adjustPan(dx, dy) {
    this.panOffset.x += dx * this.zoomFactor;
    this.panOffset.y += dy * this.zoomFactor;
  }

  setZoom(zoom, centerX, centerY) {

    const oldZoom = this.zoomFactor;
    const mouseWorldX = (centerX - this.panOffset.x) / oldZoom;
    const mouseWorldY = (centerY - this.panOffset.y) / oldZoom;
    

    this.zoomFactor = Math.max(this.minZoom, Math.min(this.maxZoom, zoom));
    

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


screenToWorld(screenX, screenY) {
    const rect = this.canvas.getBoundingClientRect();
    if (rect.width === 0 || rect.height === 0) {
        // Avoid division by zero if canvas is not visible
        return { x: 0, y: 0 };
    }

    // Calculate the scaling ratio between the drawing buffer and the CSS display size.
    const scaleX = this.canvas.width / rect.width;
    const scaleY = this.canvas.height / rect.height;

    // Scale the mouse coordinates to the drawing buffer's coordinate system.
    const canvasX = screenX * scaleX;
    const canvasY = screenY * scaleY;
    
    // Now, transform from the drawing buffer's coordinates to the panned/zoomed "world" coordinates.
    const worldX = (canvasX - this.panOffset.x) / this.zoomFactor;
    const worldY = (canvasY - this.panOffset.y) / this.zoomFactor;

    return { x: worldX, y: worldY };
  }



  worldToScreen(worldX, worldY) {
    return {
      x: worldX * this.zoomFactor + this.panOffset.x,
      y: worldY * this.zoomFactor + this.panOffset.y
    };
  }


  setZoomSensitivity(sensitivity) {
    this.zoomSensitivity = sensitivity;
  }


  setTheme(theme) {
    this.theme = { ...this.theme, ...theme };
  }
}


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

    // Ghost element feature
    this.isShiftPressed = false;
    this.ghostElement = null;
    this.ghostPosition = null;

    const isMac = navigator.userAgent.includes('Mac');
    this.PAN_KEY_BUTTON_CODE = isMac ? 'MetaLeft' : 'AltLeft';


    this.isPanning = false;
    this.lastPanPosition = null;

    this.setupEventListeners();
  }

  setupEventListeners() {

    const mouseDownHandler = (event) => {
      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;

      // Handle ghost element placement
      if (this.isShiftPressed && this.selectedElement && this.ghostElement && this.ghostPosition) {
        this.placeGhostElement();
        return;
      }

      if (event.button === 1 || (event.button === 0 && this.isPanningKeyPressed)) {
        this.isPanning = true;
        this.lastPanPosition = { x, y };
        this.canvas.style.cursor = 'grabbing';
        event.preventDefault();
        return;
      }


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
    

      if (this.isPanning && this.lastPanPosition) {
        const dx = x - this.lastPanPosition.x;
        const dy = y - this.lastPanPosition.y;
        this.renderer.adjustPan(dx, dy);
        this.lastPanPosition = { x, y };
        this.render();
        return;
      }
    

      const worldPos = this.renderer.screenToWorld(x, y);

      // Handle ghost element tracking
      if (this.isShiftPressed && this.selectedElement && this.mode === 'select') {
        this.updateGhostElement(worldPos);
        this.render();
        return;
      }
    
      if (this.mode === 'select' && this.selectedElement) {
        this.handleDrag(worldPos.x, worldPos.y);
        this.render();
      } else if (this.mode === 'addArc' && this.arcDrawing) {

        this.render();
        this.renderArcDrawing(worldPos.x, worldPos.y);
      }
    };


    const mouseUpHandler = (event) => {

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


      const worldPos = this.renderer.screenToWorld(x, y);

      if (this.mode === 'addArc' && this.arcDrawing) {
        this.completeArcDrawing(worldPos.x, worldPos.y);
      }


      this.dragStart = null;
      this.dragOffset = null; // Reset dragOffset when done dragging
      
      this.render();

      if (this.callbacks.onChange) {
        this.callbacks.onChange();
      }
    };


    const mouseWheelHandler = (event) => {
      event.preventDefault();
      
      const rect = this.canvas.getBoundingClientRect();
      const x = event.clientX - rect.left;
      const y = event.clientY - rect.top;
      

      const direction = event.deltaY < 0 ? 1 : -1;
      const zoomChange = 1 + (direction * this.renderer.zoomSensitivity);
      const factor = Math.max(0.9, Math.min(1.1, zoomChange)); // Limit to reasonable range
      

      this.renderer.adjustZoom(factor, x, y);
      this.render();

      if (this.app && this.app.updateZoomDisplay) {
        this.app.updateZoomDisplay();
      }
    };


    const keyDownHandler = (event) => {
      // Delete currently selected element
      if (event.code === 'Delete' && this.selectedElement) {
        if (this.selectedElement.type === 'place') {
          this.petriNet.removePlace(this.selectedElement.id);
        } else if (this.selectedElement.type === 'transition') {
          this.petriNet.removeTransition(this.selectedElement.id);
        } else if (this.selectedElement.type === 'arc') {
          this.petriNet.removeArc(this.selectedElement.id);
        }
        this.selectedElement = null;
        this.dragOffset = null;
        if (this.callbacks.onChange) {
          this.callbacks.onChange();
        }
        this.render();
        return;
      }

      if (event.code === this.PAN_KEY_BUTTON_CODE) {
        this.isPanningKeyPressed = true;
      }

      // Handle Shift key press (ghost mode)
      if (event.code === 'ShiftLeft' || event.code === 'ShiftRight') {
        this.isShiftPressed = true;
        if (this.selectedElement) {
          this.canvas.style.cursor = 'crosshair';
        }
      }
    };


    const keyUpHandler = (event) => {

      if (event.code === this.PAN_KEY_BUTTON_CODE) {
        this.isPanningKeyPressed = false;
        this.canvas.style.cursor = 'default';
      }

      // Handle Shift key release
      if (event.code === 'ShiftLeft' || event.code === 'ShiftRight') {
        this.isShiftPressed = false;
        this.ghostElement = null;
        this.ghostPosition = null;
        this.canvas.style.cursor = 'default';
        this.render();
      }
    };


    this.canvas.addEventListener('mousedown', mouseDownHandler);
    this.canvas.addEventListener('mousemove', mouseMoveHandler);
    this.canvas.addEventListener('mouseup', mouseUpHandler);
    this.canvas.addEventListener('wheel', mouseWheelHandler, { passive: false });
    document.addEventListener('keydown', keyDownHandler);
    document.addEventListener('keyup', keyUpHandler);


    this.eventListeners.set('mousedown', mouseDownHandler);
    this.eventListeners.set('mousemove', mouseMoveHandler);
    this.eventListeners.set('mouseup', mouseUpHandler);
    this.eventListeners.set('wheel', mouseWheelHandler);
    this.eventListeners.set('keydown', keyDownHandler);
    this.eventListeners.set('keyup', keyUpHandler);
  }

  updateGhostElement(worldPos) {
    if (!this.selectedElement) return;

    this.ghostPosition = { x: worldPos.x, y: worldPos.y };

    // Apply grid snapping to ghost position if enabled
    if (this.snapToGrid) {
      this.ghostPosition.x = Math.round(this.ghostPosition.x / this.gridSize) * this.gridSize;
      this.ghostPosition.y = Math.round(this.ghostPosition.y / this.gridSize) * this.gridSize;
    }

    // Determine ghost element type (opposite of selected)
    if (this.selectedElement.type === 'place') {
      this.ghostElement = {
        type: 'transition',
        position: this.ghostPosition
      };
    } else if (this.selectedElement.type === 'transition') {
      this.ghostElement = {
        type: 'place',
        position: this.ghostPosition
      };
    }
  }

  placeGhostElement() {
    if (!this.ghostElement || !this.ghostPosition || !this.selectedElement) return;

    const ghostPos = { ...this.ghostPosition };
    let newElementId;

    // Create the new element based on ghost type
    if (this.ghostElement.type === 'place') {
      newElementId = this.generateUUID();
      const newPlace = new Place(
        newElementId, 
        ghostPos, 
        `P${this.petriNet.places.size + 1}`
      );
      this.petriNet.addPlace(newPlace);
    } else if (this.ghostElement.type === 'transition') {
      newElementId = this.generateUUID();
      const newTransition = new Transition(
        newElementId, 
        ghostPos, 
        `T${this.petriNet.transitions.size + 1}`
      );
      this.petriNet.addTransition(newTransition);
    }

    // Create arc between selected element and new element
    if (newElementId) {
      const arcId = this.generateUUID();
      const arc = new Arc(
        arcId,
        this.selectedElement.id,
        newElementId,
        1, // default weight
        "regular", // default type
        [], // no control points
        "1" // default label
      );

      if (this.petriNet.addArc(arc)) {
        // Select the new element
        this.selectedElement = { id: newElementId, type: this.ghostElement.type };
        this.dragOffset = { x: 0, y: 0 };

        // Clear ghost state
        this.ghostElement = null;
        this.ghostPosition = null;

        // Update callbacks
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(newElementId, this.ghostElement?.type || this.selectedElement.type);
        }

        if (this.callbacks.onChange) {
          this.callbacks.onChange();
        }

        this.render();
      }
    }
  }

  handleSelection(x, y) {

    for (const [id, place] of this.petriNet.places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= place.radius) {
        this.selectedElement = { id, type: 'place' };

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


    for (const [id, arc] of this.petriNet.arcs) {

      const sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
      const targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

      if (!sourceElement || !targetElement) continue;

      const sx = sourceElement.position.x;
      const sy = sourceElement.position.y;
      const tx = targetElement.position.x;
      const ty = targetElement.position.y;


      const lineLength = Math.sqrt((tx - sx) * (tx - sx) + (ty - sy) * (ty - sy));
      const distance = Math.abs((ty - sy) * x - (tx - sx) * y + tx * sy - ty * sx) / lineLength;


      const dotProduct = ((x - sx) * (tx - sx) + (y - sy) * (ty - sy)) / (lineLength * lineLength);

      if (distance < 10 && dotProduct >= 0 && dotProduct <= 1) {
        this.selectedElement = { id, type: 'arc' };

        this.dragOffset = null;
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(id, 'arc');
        }
        return;
      }
    }


    this.selectedElement = null;
    this.dragOffset = null;
    this.ghostElement = null;
    this.ghostPosition = null;
    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(null, null);
    }
  }

  handleDrag(x, y) {
    if (!this.selectedElement) return;


    if (this.selectedElement.type === 'arc') {
      if (!this.dragStart) return;
      
      const dx = x - this.dragStart.x;
      const dy = y - this.dragStart.y;
      

      
      this.dragStart = { x, y };
      return;
    }


    if (!this.dragOffset) return;


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


    this.renderer.ctx.save();
    this.renderer.ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    this.renderer.ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    this.renderer.ctx.beginPath();
    this.renderer.ctx.moveTo(sourceElement.position.x, sourceElement.position.y);
    this.renderer.ctx.lineTo(x, y);
    this.renderer.ctx.strokeStyle = 'rgba(0, 0, 0, 0.5)';
    this.renderer.ctx.lineWidth = 1.5;
    this.renderer.ctx.stroke();


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


    let targetId = null;
    let targetType = null;


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
    this.renderGhost();
    if (this.app && this.app.overlay) {
      this.app.overlay.render();
    }
  }

  renderGhost() {
    if (!this.isShiftPressed || !this.selectedElement || !this.ghostElement || !this.ghostPosition) {
      return;
    }

    // Get the selected element for arc drawing
    let selectedElementObj;
    if (this.selectedElement.type === 'place') {
      selectedElementObj = this.petriNet.places.get(this.selectedElement.id);
    } else if (this.selectedElement.type === 'transition') {
      selectedElementObj = this.petriNet.transitions.get(this.selectedElement.id);
    }

    if (!selectedElementObj) return;

    this.renderer.ctx.save();
    this.renderer.ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    this.renderer.ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    // Draw ghost element
    if (this.ghostElement.type === 'place') {
      this.renderer.drawGhostPlace(this.ghostPosition, true);
    } else if (this.ghostElement.type === 'transition') {
      this.renderer.drawGhostTransition(this.ghostPosition, true);
    }

    // Draw ghost arc
    const start = { x: selectedElementObj.position.x, y: selectedElementObj.position.y };
    const end = { x: this.ghostPosition.x, y: this.ghostPosition.y };
    this.renderer.drawGhostArc(start, end, true);

    this.renderer.ctx.restore();
  }

  renderSelection() {
    if (!this.selectedElement) return;

    const ctx = this.canvas.getContext('2d');
    

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


  setMode(mode) {
    this.mode = mode;
    this.arcDrawing = null;
    this.ghostElement = null;
    this.ghostPosition = null;
  }

  selectElement(id, type) {

    if (id && type) {
      this.selectedElement = { id, type };
      

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

    // Clear ghost state when selecting programmatically
    this.ghostElement = null;
    this.ghostPosition = null;

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
      this.ghostElement = null;
      this.ghostPosition = null;
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


    this.render();

    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }
  }


  resetView() {
    this.renderer.resetView();
    this.render();

     if (this.app && this.app.updateZoomDisplay) {
      this.app.updateZoomDisplay();
    }
  }
  

  setZoomSensitivity(sensitivity) {
    if (this.renderer) {
      this.renderer.setZoomSensitivity(sensitivity);
    }
  }


  setOnChangeCallback(callback) {
    this.callbacks.onChange = callback;
  }

  setOnSelectCallback(callback) {
    this.callbacks.onSelect = callback;
  }


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


  generateUUID() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }
}


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


  attachEditor(canvasElement) {
    this.canvas = canvasElement;
    this.editor = new PetriNetEditor(canvasElement, this.petriNet);
    return this.editor;
  }

  getEditor() {
    return this.editor;
  }

  totalReset() {
    this.petriNet = null;
    this.resetAllCallbacks();
    this.editor = null;
    this.canvas = null;
  } 

  resetAllCallbacks() {
    if (this.editor) {
      this.editor.setOnChangeCallback(null);
      this.editor.setOnSelectCallback(null);
    }
  } 

  createPlace(x, y, label, tokens = 0, finalMarking = null) {
    const id = this.generateUUID();
    const place = new Place(id, { x, y }, label || `P${this.petriNet.places.size + 1}`, tokens, null, finalMarking);
    this.petriNet.addPlace(place);
    if (this.editor) this.editor.render();
    return id;
  }

  setPlaceFinalMarking(id, finalMarking) {
    const place = this.petriNet.places.get(id);
    if (!place) return false;

    place.finalMarking = finalMarking;
    if (this.editor) this.editor.render();
    return true;
  }

  checkFinalMarkings() {
    const results = {
      totalPlaces: 0,
      placesWithFinalMarkings: 0,
      satisfiedFinalMarkings: 0,
      unsatisfiedPlaces: []
    };

    for (const [id, place] of this.petriNet.places) {
      results.totalPlaces++;
      
      if (place.hasFinalMarking()) {
        results.placesWithFinalMarkings++;
        
        if (place.hasReachedFinalMarking()) {
          results.satisfiedFinalMarkings++;
        } else {
          results.unsatisfiedPlaces.push({
            id: id,
            label: place.label,
            currentTokens: place.tokens,
            expectedTokens: place.finalMarking
          });
        }
      }
    }

    results.allSatisfied = results.placesWithFinalMarkings > 0 && 
                          results.satisfiedFinalMarkings === results.placesWithFinalMarkings;

    return results;
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

  
    /**
   * Fits the entire Petri net within the canvas viewport
   * @param {number} padding - Padding around the content in pixels (default: 50)
   * @returns {boolean} - Success of the operation
   */
  fitToCanvas(padding = 50) {
    if (!this.editor || !this.canvas) return false;

    // Get the bounds of all elements
    const bounds = this.getNetworkBounds();
    if (!bounds) return false;

    // Calculate the size of the content
    const contentWidth = bounds.maxX - bounds.minX;
    const contentHeight = bounds.maxY - bounds.minY;

    // Get canvas dimensions
    const canvasWidth = this.canvas.width;
    const canvasHeight = this.canvas.height;

    // Calculate available space (minus padding)
    const availableWidth = canvasWidth - (2 * padding);
    const availableHeight = canvasHeight - (2 * padding);

    // Calculate zoom factor to fit content
    const zoomX = availableWidth / contentWidth;
    const zoomY = availableHeight / contentHeight;
    const targetZoom = Math.min(zoomX, zoomY, 1.0); // Don't zoom in beyond 100%

    // Calculate center of content
    const contentCenterX = (bounds.minX + bounds.maxX) / 2;
    const contentCenterY = (bounds.minY + bounds.maxY) / 2;

    // Apply zoom and center the content
    this.editor.renderer.zoomFactor = targetZoom;
    
    // Calculate pan offset to center the content
    this.editor.renderer.panOffset.x = (canvasWidth / 2) - (contentCenterX * targetZoom);
    this.editor.renderer.panOffset.y = (canvasHeight / 2) - (contentCenterY * targetZoom);

    // Render the changes
    this.editor.render();

    return true;
  }

  /**
   * Gets the bounding box of all elements in the network
   * @returns {Object|null} - Bounds object with minX, minY, maxX, maxY or null if no elements
   */
  getNetworkBounds() {
    let minX = Infinity, minY = Infinity;
    let maxX = -Infinity, maxY = -Infinity;
    let hasElements = false;

    // Check places
    for (const [, place] of this.petriNet.places) {
      hasElements = true;
      minX = Math.min(minX, place.position.x - place.radius);
      minY = Math.min(minY, place.position.y - place.radius);
      maxX = Math.max(maxX, place.position.x + place.radius);
      maxY = Math.max(maxY, place.position.y + place.radius);
    }

    // Check transitions
    for (const [, transition] of this.petriNet.transitions) {
      hasElements = true;
      minX = Math.min(minX, transition.position.x - transition.width / 2);
      minY = Math.min(minY, transition.position.y - transition.height / 2);
      maxX = Math.max(maxX, transition.position.x + transition.width / 2);
      maxY = Math.max(maxY, transition.position.y + transition.height / 2);
    }

    if (!hasElements) return null;

    return { minX, minY, maxX, maxY };
  }


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


      this.petriNet.updateEnabledTransitions();
      const enabledTransitions = [];

      for (const [id, transition] of this.petriNet.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }


      enabledTransitions.sort((a, b) => {
        const transA = this.petriNet.transitions.get(a);
        const transB = this.petriNet.transitions.get(b);
        return (transB?.priority || 0) - (transA?.priority || 0);
      });


      if (enabledTransitions.length > 0) {
        firedAny = this.petriNet.fireTransition(enabledTransitions[0]);
        if (firedAny) steps++;
      }
    } while (firedAny && steps < maxSteps);

    if (this.editor) this.editor.render();
    return steps;
  }


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


  resetView() {
    if (this.editor) {
      this.editor.resetView();
    }
  }
  
  /**
   * Sets the sensitivity of the zoom operation when using the mouse wheel
   * @param {number} sensitivity - Value between 0.01 and 0.5, where higher values make zooming more sensitive
   * @returns {boolean} - Success of the operation
   */
  setZoomSensitivity(sensitivity) {

    const validSensitivity = Math.max(0.01, Math.min(0.5, sensitivity));
    
    if (this.editor) {
      this.editor.setZoomSensitivity(validSensitivity);
      return true;
    }
    return false;
  }


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


  generateUUID() {
    return 'xxxxxxxx-xxxx-4xxx-yxxx-xxxxxxxxxxxx'.replace(/[xy]/g, function (c) {
      const r = Math.random() * 16 | 0;
      const v = c === 'x' ? r : (r & 0x3 | 0x8);
      return v.toString(16);
    });
  }


  /**
   * Performs advanced automatic layout of the Petri net elements using BPMN layout algorithm.
   * @param {Object} options - Layout options
   * @param {number} [options.elementSpacing=150] - Horizontal spacing between elements
   * @param {number} [options.verticalSpacing=100] - Vertical spacing between layers
   * @param {number} [options.startX=100] - Starting X coordinate
   * @param {number} [options.startY=100] - Starting Y coordinate
   * @param {boolean} [options.centerLayout=true] - Whether to center the graph in the canvas
   * @param {boolean} [options.compactLayout=true] - Whether to apply compaction
   * @returns {Promise<boolean>} - Success of the operation
   */
  async autoLayout(options = {}) {
    // Default settings optimized for Petri nets
    const settings = {
      elementSpacing: options.elementSpacing || 150,
      verticalSpacing: options.verticalSpacing || 100,
      startX: options.startX || 100,
      startY: options.startY || 100,
      centerLayout: options.centerLayout !== undefined ? options.centerLayout : true,
      compactLayout: options.compactLayout !== undefined ? options.compactLayout : true
    };

    // Check if there are elements to layout
    if (this.petriNet.places.size === 0 && this.petriNet.transitions.size === 0) {
      return false;
    }

    // Convert PetriNet to format expected by BPMN algorithm
    const netData = {
      places: Array.from(this.petriNet.places.values()),
      transitions: Array.from(this.petriNet.transitions.values()),
      arcs: Array.from(this.petriNet.arcs.values())
    };

    try {
      // Apply the sophisticated BPMN layout algorithm
      const layoutAlgorithm = new BPMNLayoutAlgorithm();
      await layoutAlgorithm.applyLayout(netData, settings);

      // Center the graph in the canvas if requested and canvas is available
      if (settings.centerLayout && this.canvas) {
        this.centerGraphInCanvas();
      }

      // Render the updated layout
      if (this.editor) {
        this.editor.render();
      }

      return true;
    } catch (error) {
      console.error('Layout algorithm error:', error);
      return false;
    }
  }

  // ADD this new method to PetriNetAPI class:
  centerGraphInCanvas() {
    if (!this.canvas) return;

    // Calculate current bounds of all elements
    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;

    // Check places
    for (const [, place] of this.petriNet.places) {
      minX = Math.min(minX, place.position.x - place.radius);
      minY = Math.min(minY, place.position.y - place.radius);
      maxX = Math.max(maxX, place.position.x + place.radius);
      maxY = Math.max(maxY, place.position.y + place.radius);
    }

    // Check transitions
    for (const [, transition] of this.petriNet.transitions) {
      minX = Math.min(minX, transition.position.x - transition.width / 2);
      minY = Math.min(minY, transition.position.y - transition.height / 2);
      maxX = Math.max(maxX, transition.position.x + transition.width / 2);
      maxY = Math.max(maxY, transition.position.y + transition.height / 2);
    }

    // Only proceed if we have valid bounds
    if (minX === Infinity) return;

    // Calculate graph dimensions
    const graphWidth = maxX - minX;
    const graphHeight = maxY - minY;
    const canvasWidth = this.canvas.width;
    const canvasHeight = this.canvas.height;

    // Calculate centering offset with padding
    const padding = 50;
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
   * Calculates layers for the Petri net based on a topological sort
   * @returns {Object} layers and nodeToLayer mapping
   * @private
   */
  calculateLayers() {

    const nodeToLayer = new Map();


    const incomingEdges = new Map();


    const allNodes = new Map();


    for (const [id, place] of this.petriNet.places) {
      allNodes.set(id, place);
      incomingEdges.set(id, 0);
    }

    for (const [id, transition] of this.petriNet.transitions) {
      allNodes.set(id, transition);
      incomingEdges.set(id, 0);
    }


    for (const [id, arc] of this.petriNet.arcs) {
      const targetId = arc.target;
      incomingEdges.set(targetId, (incomingEdges.get(targetId) || 0) + 1);
    }


    const sources = [];
    for (const [id] of allNodes) {
      if (incomingEdges.get(id) === 0) {
        sources.push(id);
      }
    }


    if (sources.length === 0 && allNodes.size > 0) {
      const someNodeId = allNodes.keys().next().value;
      sources.push(someNodeId);
    }


    const layers = [];
    const visited = new Set();
    let currentLayer = [...sources];

    while (currentLayer.length > 0) {
      layers.push([...currentLayer]);


      currentLayer.forEach((nodeId) => {
        nodeToLayer.set(nodeId, layers.length - 1);
        visited.add(nodeId);
      });


      const nextLayer = [];
      for (const nodeId of currentLayer) {

        const outgoingArcs = Array.from(this.petriNet.arcs.values())
          .filter(arc => arc.source === nodeId);


        for (const arc of outgoingArcs) {
          const targetId = arc.target;
          if (!visited.has(targetId)) {

            incomingEdges.set(targetId, incomingEdges.get(targetId) - 1);


            if (incomingEdges.get(targetId) === 0) {
              nextLayer.push(targetId);
            }
          }
        }
      }


      currentLayer = nextLayer;
    }


    const unvisitedNodes = Array.from(allNodes.keys()).filter(id => !visited.has(id));
    if (unvisitedNodes.length > 0) {


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


    layers.forEach((layerNodes, layerIndex) => {

      const places = layerNodes.filter(id => this.petriNet.places.has(id));
      const transitions = layerNodes.filter(id => this.petriNet.transitions.has(id));


      let nodeIndex = 0;


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


    this.optimizeNodePositions(nodeToLayer, options);
  }

  /**
   * Optimizes node positions to reduce edge crossings and improve layout
   * @param {Map<string, number>} nodeToLayer - Map from node ID to layer number
   * @param {Object} options - Layout options
   * @private
   */
  optimizeNodePositions(nodeToLayer, options) {

    const isHorizontal = options.direction === 'horizontal';


    const connections = new Map();


    for (const [id, arc] of this.petriNet.arcs) {
      const sourceId = arc.source;
      const targetId = arc.target;


      if (!connections.has(sourceId)) {
        connections.set(sourceId, []);
      }
      connections.get(sourceId).push(targetId);


      if (!connections.has(targetId)) {
        connections.set(targetId, []);
      }
      connections.get(targetId).push(sourceId);
    }



    for (const [nodeId, connectedIds] of connections) {
      let element;
      if (this.petriNet.places.has(nodeId)) {
        element = this.petriNet.places.get(nodeId);
      } else if (this.petriNet.transitions.has(nodeId)) {
        element = this.petriNet.transitions.get(nodeId);
      } else {
        continue;
      }


      const connectedElements = connectedIds
        .map(id => {
          if (this.petriNet.places.has(id)) return this.petriNet.places.get(id);
          if (this.petriNet.transitions.has(id)) return this.petriNet.transitions.get(id);
          return null;
        })
        .filter(e => e !== null);


      if (connectedElements.length > 0) {

        const currentLayer = nodeToLayer.get(nodeId);


        const otherLayerNodes = connectedElements.filter(e => {
          const elementId = this.findElementId(e);
          if (!elementId) return false;
          return nodeToLayer.get(elementId) !== currentLayer;
        });

        if (otherLayerNodes.length > 0) {

          const positionSum = otherLayerNodes.reduce((sum, e) => {
            const pos = isHorizontal ? e.position.y : e.position.x;
            return sum + pos;
          }, 0);

          const avgPosition = positionSum / otherLayerNodes.length;



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


    let minX = Infinity, minY = Infinity, maxX = -Infinity, maxY = -Infinity;


    for (const [, place] of this.petriNet.places) {
      minX = Math.min(minX, place.position.x - place.radius);
      minY = Math.min(minY, place.position.y - place.radius);
      maxX = Math.max(maxX, place.position.x + place.radius);
      maxY = Math.max(maxY, place.position.y + place.radius);
    }


    for (const [, transition] of this.petriNet.transitions) {
      minX = Math.min(minX, transition.position.x - transition.width / 2);
      minY = Math.min(minY, transition.position.y - transition.height / 2);
      maxX = Math.max(maxX, transition.position.x + transition.width / 2);
      maxY = Math.max(maxY, transition.position.y + transition.height / 2);
    }


    const graphWidth = maxX - minX;
    const graphHeight = maxY - minY;
    const canvasWidth = this.canvas.width;
    const canvasHeight = this.canvas.height;

    const offsetX = (canvasWidth - graphWidth) / 2 - minX;
    const offsetY = (canvasHeight - graphHeight) / 2 - minY;


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

    for (const [id, place] of this.petriNet.places) {
      if (place === element) return id;
    }


    for (const [id, transition] of this.petriNet.transitions) {
      if (transition === element) return id;
    }

    return null;
  }
}

/**
 * BPMN Layout Algorithm Implementation
 * Based on "A Simple Algorithm for Automatic Layout of BPMN Processes" (Kitzmann et al., 2009)
 */
class BPMNLayoutAlgorithm {
  constructor() {
    this.grid = null;
    this.sortedElements = [];
    this.elementTypes = new Map();
  }

  async applyLayout(net, settings) {
    // Step 1: Classify elements
    this.classifyElements(net);
    
    // Step 2: Modified topological sort
    this.sortedElements = this.modifiedTopologicalSort(net);
    
    // Step 3: Initialize grid
    this.grid = new LayoutGrid();
    this.settings = settings;
    
    // Step 4: Position elements
    await this.positionElements(net, settings);
    
    // Step 5: Apply heuristics
    if (settings.compactLayout) {
      this.applyInterleaving();
    }
    
    // Step 6: Calculate final coordinates
    this.calculateFinalCoordinates(net, settings);
  }

  classifyElements(net) {
    this.elementTypes.clear();
    
    [...net.places, ...net.transitions].forEach(element => {
      const types = new Set(['element']);
      
      const incomingArcs = net.arcs.filter(arc => arc.target === element.id);
      const outgoingArcs = net.arcs.filter(arc => arc.source === element.id);
      
      if (incomingArcs.length === 0) types.add('start');
      if (outgoingArcs.length === 0) types.add('end');
      if (incomingArcs.length > 1) types.add('join');
      if (outgoingArcs.length > 1) types.add('split');
      
      this.elementTypes.set(element.id, types);
    });
  }

  modifiedTopologicalSort(net) {
    const elements = [...net.places, ...net.transitions];
    const arcs = net.arcs;
    const incomingCount = new Map();
    const result = [];
    
    elements.forEach(element => {
      const incomingArcs = arcs.filter(arc => arc.target === element.id);
      incomingCount.set(element.id, incomingArcs.length);
    });
    
    const originalIncomingCount = new Map(incomingCount);
    
    while (elements.some(e => !result.includes(e))) {
      const freeNodes = elements.filter(element => 
        !result.includes(element) && incomingCount.get(element.id) === 0
      );
      
      if (freeNodes.length > 0) {
        const node = freeNodes[0];
        result.push(node);
        
        const outgoingArcs = arcs.filter(arc => arc.source === node.id);
        outgoingArcs.forEach(arc => {
          incomingCount.set(arc.target, incomingCount.get(arc.target) - 1);
        });
      } else {
        const remainingElements = elements.filter(e => !result.includes(e));
        
        let loopEntry = remainingElements.find(element => {
          const types = this.elementTypes.get(element.id);
          return types.has('join') && 
                 incomingCount.get(element.id) < originalIncomingCount.get(element.id);
        });
        
        if (!loopEntry) {
          loopEntry = remainingElements[0];
        }
        
        const remainingIncoming = arcs.filter(arc => 
          arc.target === loopEntry.id && 
          !result.find(e => e.id === arc.source)
        );
        
        remainingIncoming.forEach(arc => {
          incomingCount.set(loopEntry.id, incomingCount.get(loopEntry.id) - 1);
        });
      }
    }
    
    return result;
  }

  async positionElements(net, settings) {
    for (let i = 0; i < this.sortedElements.length; i++) {
      const element = this.sortedElements[i];
      const elementTypes = this.elementTypes.get(element.id);
      
      if (elementTypes.has('start')) {
        this.grid.placeElement(element.id, 0, this.grid.getNextAvailableRow(0));
      } else {
        this.positionElementRelativeToPredecessors(element, net);
      }
      
      if (i % 10 === 0) {
        await new Promise(resolve => setTimeout(resolve, 1));
      }
    }
  }

  positionElementRelativeToPredecessors(element, net) {
    const elementTypes = this.elementTypes.get(element.id);
    const incomingArcs = net.arcs.filter(arc => arc.target === element.id);
    
    if (incomingArcs.length === 0) {
      this.grid.placeElement(element.id, 0, 0);
      return;
    }
    
    const predecessorPositions = incomingArcs.map(arc => {
      return this.grid.getElementPosition(arc.source);
    }).filter(pos => pos !== null);
    
    if (predecessorPositions.length === 0) {
      this.grid.placeElement(element.id, 0, 0);
      return;
    }
    
    if (elementTypes.has('join')) {
      const rightmostCol = Math.max(...predecessorPositions.map(pos => pos.col));
      const avgRow = Math.round(
        predecessorPositions.reduce((sum, pos) => sum + pos.row, 0) / predecessorPositions.length
      );
      this.grid.placeElement(element.id, rightmostCol + 1, avgRow);
    } else if (predecessorPositions.length === 1) {
      const predPos = predecessorPositions[0];
      const predElement = [...net.places, ...net.transitions].find(e => e.id === incomingArcs[0].source);
      const predTypes = this.elementTypes.get(predElement.id);
      
      if (predTypes.has('split')) {
        const splitSuccessors = net.arcs.filter(arc => arc.source === predElement.id);
        const thisArcIndex = splitSuccessors.findIndex(arc => arc.target === element.id);
        const targetRow = predPos.row + thisArcIndex - Math.floor(splitSuccessors.length / 2);
        this.grid.placeElement(element.id, predPos.col + 1, targetRow);
      } else {
        this.grid.placeElement(element.id, predPos.col + 1, predPos.row);
      }
    } else {
      const rightmostCol = Math.max(...predecessorPositions.map(pos => pos.col));
      const avgRow = Math.round(
        predecessorPositions.reduce((sum, pos) => sum + pos.row, 0) / predecessorPositions.length
      );
      this.grid.placeElement(element.id, rightmostCol + 1, avgRow);
    }
  }

  applyInterleaving() {
    let changed = true;
    while (changed) {
      changed = false;
      
      for (let row = 0; row < this.grid.getMaxRow(); row++) {
        const nextRow = row + 1;
        if (this.grid.canInterleaveRows(row, nextRow)) {
          this.grid.interleaveRows(row, nextRow);
          changed = true;
          break;
        }
      }
    }
  }

  calculateFinalCoordinates(net, settings) {
    const spacing = settings.elementSpacing || 150;
    const verticalSpacing = settings.verticalSpacing || 100;
    
    [...net.places, ...net.transitions].forEach(element => {
      const gridPos = this.grid.getElementPosition(element.id);
      if (gridPos) {
        const x = (settings.startX || 100) + gridPos.col * spacing;
        const y = (settings.startY || 100) + gridPos.row * verticalSpacing;
        element.position = { x, y };
      }
    });
  }
}

/**
 * Grid data structure for layout positioning
 */
class LayoutGrid {
  constructor() {
    this.cells = new Map();
    this.elementPositions = new Map();
    this.maxCol = 0;
    this.maxRow = 0;
  }

  placeElement(elementId, col, row) {
    while (this.cells.has(`${col},${row}`)) {
      row++;
    }
    
    const key = `${col},${row}`;
    this.cells.set(key, elementId);
    this.elementPositions.set(elementId, { col, row });
    
    this.maxCol = Math.max(this.maxCol, col);
    this.maxRow = Math.max(this.maxRow, row);
  }

  getElementPosition(elementId) {
    return this.elementPositions.get(elementId) || null;
  }

  getNextAvailableRow(col) {
    let row = 0;
    while (this.cells.has(`${col},${row}`)) {
      row++;
    }
    return row;
  }

  getMaxRow() {
    return this.maxRow;
  }

  canInterleaveRows(row1, row2) {
    for (let col = 0; col <= this.maxCol; col++) {
      const key1 = `${col},${row1}`;
      const key2 = `${col},${row2}`;
      
      if (this.cells.has(key1) && this.cells.has(key2)) {
        return false;
      }
    }
    return true;
  }

  interleaveRows(row1, row2) {
    for (let col = 0; col <= this.maxCol; col++) {
      const key2 = `${col},${row2}`;
      if (this.cells.has(key2)) {
        const elementId = this.cells.get(key2);
        this.cells.delete(key2);
        
        const key1 = `${col},${row1}`;
        this.cells.set(key1, elementId);
        this.elementPositions.set(elementId, { col, row: row1 });
      }
    }
    
    for (let row = row2 + 1; row <= this.maxRow; row++) {
      for (let col = 0; col <= this.maxCol; col++) {
        const oldKey = `${col},${row}`;
        if (this.cells.has(oldKey)) {
          const elementId = this.cells.get(oldKey);
          this.cells.delete(oldKey);
          
          const newKey = `${col},${row - 1}`;
          this.cells.set(newKey, elementId);
          this.elementPositions.set(elementId, { col, row: row - 1 });
        }
      }
    }
    
    this.maxRow--;
  }
}


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