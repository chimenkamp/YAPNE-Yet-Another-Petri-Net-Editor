import { PetriNetRenderer } from '../petri-net-simulator.js';

class DataPetriNetRenderer extends PetriNetRenderer {
  /**
   * Create a new Data Petri Net renderer
   * @param {HTMLCanvasElement} canvas - The canvas element
   * @param {DataPetriNet} petriNet - The data Petri net to render
   */
  constructor(canvas, petriNet) {
    super(canvas, petriNet);
    

    this.theme = {
      ...this.theme,
      dataTransitionColor: '#8FBCBB',             // Nord7 - bluish green
      dataTransitionStroke: '#5E81AC',            // Nord10 - blue
      enabledDataTransitionColor: '#A3BE8C',      // Nord14 - green
      disabledDataTransitionColor: '#D08770',     // Nord12 - orange
      dataGuardIndicatorColor: '#EBCB8B',         // Nord13 - yellow
      dataUpdateIndicatorColor: '#B48EAD'         // Nord15 - purple
    };
  }

  /**
   * Override the drawTransitions method to handle data-aware transitions
   */
  drawTransitions() {
    for (const [id, transition] of this.petriNet.transitions.entries()) {

      const isDataAware = typeof transition.evaluatePrecondition === 'function';
      
      if (isDataAware) {
        this.drawDataTransition(transition);
      } else {
        this.drawStandardTransition(transition);
      }
    }
  }

  /**
   * Draw a standard transition (delegating to super's implementation)
   * @param {Transition} transition - The transition to draw
   * @private
   */
  drawStandardTransition(transition) {

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

  /**
   * Draw a data-aware transition with visual indicators for guards and updates
   * @param {DataAwareTransition} transition - The data-aware transition to draw
   * @private
   */
  drawDataTransition(transition) {
    const x = transition.position.x;
    const y = transition.position.y;
    const width = transition.width;
    const height = transition.height;
    

    this.ctx.beginPath();
    this.ctx.rect(
      x - width / 2,
      y - height / 2,
      width,
      height
    );
    

    if (transition.isEnabled) {
      this.ctx.fillStyle = this.theme.enabledDataTransitionColor;
    } else {

      const isTokenEnabled = this.isTransitionTokenEnabled(transition.id);
      this.ctx.fillStyle = isTokenEnabled ? 
        this.theme.disabledDataTransitionColor : // Data guard is preventing firing
        this.theme.dataTransitionColor;          // Not enabled due to tokens
    }
    
    this.ctx.fill();
    this.ctx.strokeStyle = this.theme.dataTransitionStroke;
    this.ctx.lineWidth = 2;
    this.ctx.stroke();
    

    if (transition.precondition) {
      this.drawDataGuardIndicator(x, y - height / 2, width);
    }
    
    if (transition.postcondition) {
      this.drawDataUpdateIndicator(x, y + height / 2, width);
    }
    

    this.ctx.fillStyle = this.theme.textColor;
    this.ctx.font = '12px Arial';
    this.ctx.textAlign = 'center';
    this.ctx.fillText(
      transition.label,
      x,
      y + height / 2 + 15
    );
  }

  /**
   * Draw an indicator for data guards (preconditions)
   * @param {number} x - Center X coordinate
   * @param {number} y - Top Y coordinate
   * @param {number} width - Width of the transition
   * @private
   */
  drawDataGuardIndicator(x, y, width) {
    const indicatorHeight = 5;
    

    this.ctx.beginPath();
    this.ctx.rect(
      x - width / 2,
      y - indicatorHeight,
      width,
      indicatorHeight
    );
    this.ctx.fillStyle = this.theme.dataGuardIndicatorColor;
    this.ctx.fill();
    this.ctx.strokeStyle = this.theme.dataTransitionStroke;
    this.ctx.lineWidth = 1;
    this.ctx.stroke();
  }

  /**
   * Draw an indicator for data updates (postconditions)
   * @param {number} x - Center X coordinate
   * @param {number} y - Bottom Y coordinate
   * @param {number} width - Width of the transition
   * @private
   */
  drawDataUpdateIndicator(x, y, width) {
    const indicatorHeight = 5;
    

    this.ctx.beginPath();
    this.ctx.rect(
      x - width / 2,
      y,
      width,
      indicatorHeight
    );
    this.ctx.fillStyle = this.theme.dataUpdateIndicatorColor;
    this.ctx.fill();
    this.ctx.strokeStyle = this.theme.dataTransitionStroke;
    this.ctx.lineWidth = 1;
    this.ctx.stroke();
  }

  /**
   * Check if a transition is enabled based on token conditions only
   * (ignoring data preconditions)
   * @param {string} transitionId - ID of the transition to check
   * @returns {boolean} Whether the transition would be enabled by tokens
   * @private
   */
  isTransitionTokenEnabled(transitionId) {
    const incomingArcs = Array.from(this.petriNet.arcs.values())
      .filter(arc => arc.target === transitionId);

    for (const arc of incomingArcs) {
      const place = this.petriNet.places.get(arc.source);
      if (!place) continue;

      if (arc.type === "inhibitor") {

        if (place.tokens >= arc.weight) return false;
      } else if (arc.type === "regular") {

        if (place.tokens < arc.weight) return false;
      }

    }

    return true;
  }
}

export { DataPetriNetRenderer };