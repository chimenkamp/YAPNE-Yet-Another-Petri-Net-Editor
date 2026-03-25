import { PetriNetRenderer } from '../petri-net-simulator.js';

class DataPetriNetRenderer extends PetriNetRenderer {
  /**
   * Create a new Data Petri Net renderer
   * @param {HTMLCanvasElement} canvas - The canvas element
   * @param {DataPetriNet} petriNet - The data Petri net to render
   */
  constructor(canvas, petriNet) {
    super(canvas, petriNet);
    
    /** When true, draw variable overlays on transitions during simulation */
    this.showDataOverlays = false;

    /** Cache for overlay data so random expressions aren't re-evaluated on every render */
    this._overlayCache = null;
    this._overlayCacheKey = null;

    this.theme = {
      ...this.theme,
      dataTransitionColor: '#8FBCBB',             // Nord7 - bluish green
      dataTransitionStroke: '#5E81AC',            // Nord10 - blue
      enabledDataTransitionColor: '#A3BE8C',      // Nord14 - green
      disabledDataTransitionColor: '#D08770',     // Nord12 - orange
      dataGuardIndicatorColor: '#EBCB8B',         // Nord13 - yellow
      dataUpdateIndicatorColor: '#B48EAD',        // Nord15 - purple
      // Overlay colours
      overlayBg: 'rgba(46, 52, 64, 0.92)',        // Nord0
      overlayBorder: '#88C0D0',                    // Nord8
      overlayHeaderBg: 'rgba(136, 192, 208, 0.18)',
      overlayText: '#D8DEE9',                      // Nord4
      overlayValueColor: '#A3BE8C',                // Nord14 green
      overlayPostColor: '#B48EAD',                 // Nord15 purple
      overlayGuardColor: '#EBCB8B',                // Nord13 yellow
      overlayArrowColor: '#81A1C1'                 // Nord9
    };
  }

  /**
   * Override render to add data overlay pass after transitions
   */
  render() {
    // Normal render
    super.render();

    // Draw overlays in a second transformed pass so they sit on top of arcs/places too
    if (this.showDataOverlays && this.petriNet.dataVariables && this.petriNet.dataVariables.size > 0) {
      this.ctx.save();
      this.ctx.translate(this.panOffset.x, this.panOffset.y);
      this.ctx.scale(this.zoomFactor, this.zoomFactor);
      this.drawDataOverlays();
      this.ctx.restore();
    }
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
    
    // Silent transitions are always grey
    if (transition.silent) {
      this.ctx.fillStyle = this.theme.silentTransitionColor;
    } else {
      this.ctx.fillStyle = transition.isEnabled ?
        this.theme.enabledTransitionColor : this.theme.transitionColor;
    }
    this.ctx.fill();
    this.ctx.strokeStyle = this.theme.transitionStroke;
    this.ctx.lineWidth = 2;
    this.ctx.stroke();

    // Only draw label for non-silent transitions
    if (!transition.silent) {
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
    
    // Silent transitions are always grey
    if (transition.silent) {
      this.ctx.fillStyle = this.theme.silentTransitionColor;
    } else if (transition.isEnabled) {
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
    
    // Only draw indicators and label for non-silent transitions
    if (!transition.silent) {
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

  // ── Data Overlay Rendering ───────────────────────────────────────────

  /**
   * Draw compact variable value overlays above every data-aware transition
   * that has a precondition or postcondition referencing variables.
   */
  drawDataOverlays() {
    const valuation = this.petriNet.getDataValuation();
    const varNames = Object.keys(valuation);
    if (varNames.length === 0) return;

    // Build a cache key from the current valuation so we only
    // re-evaluate expressions when variable values actually change
    // (prevents Math.random() in postconditions from flickering on every frame).
    const cacheKey = JSON.stringify(valuation);

    if (this._overlayCacheKey !== cacheKey) {
      this._overlayCacheKey = cacheKey;
      this._overlayCache = [];

      for (const [, transition] of this.petriNet.transitions) {
        const isDataAware = typeof transition.evaluatePrecondition === 'function';
        if (!isDataAware) continue;
        if (!transition.precondition && !transition.postcondition) continue;

        const preVars = this._extractReferencedVars(transition.precondition, varNames, valuation);
        const postChanges = this._parsePostconditionChanges(transition.postcondition, varNames, valuation);

        if (preVars.length === 0 && postChanges.length === 0) continue;

        this._overlayCache.push({ transition, preVars, postChanges });
      }
    }

    // Draw from cache
    for (const entry of this._overlayCache) {
      this._drawCompactOverlay(entry.transition, entry.preVars, entry.postChanges);
    }
  }

  /**
   * Invalidate the overlay cache, forcing recalculation on the next render.
   * Call this after a simulation step fires.
   */
  invalidateOverlayCache() {
    this._overlayCache = null;
    this._overlayCacheKey = null;
  }

  /**
   * Draw a compact overlay above a transition showing guard vars and effect results.
   * Layout: small pill positioned above the transition, with a tiny pointer triangle.
   * @private
   */
  _drawCompactOverlay(transition, preVars, postChanges) {
    const ctx = this.ctx;
    const t = this.theme;

    const fontSize = 10;
    const labelFontSize = 8;
    const lineHeight = 14;
    const padX = 6;
    const padY = 4;
    const cornerRadius = 4;
    const pointerSize = 4;
    const sectionGap = 6;

    // ── Build rows ──
    const rows = [];

    if (preVars.length > 0) {
      rows.push({ type: 'label', text: 'GUARD', color: t.overlayGuardColor });
      for (const v of preVars) {
        const valText = v.value !== null && v.value !== undefined ? String(v.value) : '—';
        rows.push({ type: 'guard', name: v.name, value: valText });
      }
    }

    if (postChanges.length > 0) {
      if (rows.length > 0) rows.push({ type: 'gap' });
      rows.push({ type: 'label', text: 'EFFECT', color: t.overlayPostColor });
      for (const pc of postChanges) {
        rows.push({ type: 'effect', name: pc.name, expr: pc.expr, result: pc.result });
      }
    }

    // ── Measure widths ──
    let maxRowW = 0;
    for (const row of rows) {
      if (row.type === 'label') {
        ctx.font = `bold ${labelFontSize}px 'Segoe UI', Arial, sans-serif`;
        maxRowW = Math.max(maxRowW, ctx.measureText(row.text).width);
      } else if (row.type === 'guard') {
        ctx.font = `${fontSize}px 'JetBrains Mono', Consolas, monospace`;
        const txt = `${row.name}  ${row.value}`;
        maxRowW = Math.max(maxRowW, ctx.measureText(txt).width);
      } else if (row.type === 'effect') {
        ctx.font = `${fontSize}px 'JetBrains Mono', Consolas, monospace`;
        const txt = `${row.name}' = ${row.expr}  →  ${row.result}`;
        maxRowW = Math.max(maxRowW, ctx.measureText(txt).width);
      }
    }

    // Cap width to avoid extremely wide overlays
    const maxWidth = 200;
    const cardW = Math.min(maxRowW + padX * 2, maxWidth);

    // Compute height
    let contentH = padY;
    for (const row of rows) {
      if (row.type === 'gap') contentH += sectionGap;
      else if (row.type === 'label') contentH += lineHeight - 2;
      else contentH += lineHeight;
    }
    contentH += padY;

    const cardH = contentH;

    // ── Position: centered above the transition ──
    const gapAbove = 8;
    const cardX = transition.position.x - cardW / 2;
    const cardY = transition.position.y - transition.height / 2 - gapAbove - cardH - pointerSize;

    // ── Card background ──
    this._roundRect(cardX, cardY, cardW, cardH, cornerRadius);
    ctx.fillStyle = t.overlayBg;
    ctx.fill();
    ctx.strokeStyle = t.overlayBorder;
    ctx.lineWidth = 0.8;
    ctx.globalAlpha = 0.95;
    ctx.stroke();
    ctx.globalAlpha = 1.0;

    // ── Pointer triangle pointing down to transition ──
    const ptrX = transition.position.x;
    const ptrY = cardY + cardH;
    ctx.beginPath();
    ctx.moveTo(ptrX - pointerSize, ptrY);
    ctx.lineTo(ptrX + pointerSize, ptrY);
    ctx.lineTo(ptrX, ptrY + pointerSize);
    ctx.closePath();
    ctx.fillStyle = t.overlayBg;
    ctx.fill();

    // ── Render rows ──
    let rowY = cardY + padY;
    ctx.textAlign = 'left';

    for (const row of rows) {
      if (row.type === 'gap') {
        // Draw a subtle divider line
        ctx.beginPath();
        ctx.moveTo(cardX + padX, rowY + sectionGap / 2);
        ctx.lineTo(cardX + cardW - padX, rowY + sectionGap / 2);
        ctx.strokeStyle = 'rgba(136, 192, 208, 0.2)';
        ctx.lineWidth = 0.5;
        ctx.stroke();
        rowY += sectionGap;
      } else if (row.type === 'label') {
        rowY += labelFontSize;
        ctx.font = `bold ${labelFontSize}px 'Segoe UI', Arial, sans-serif`;
        ctx.fillStyle = row.color;
        ctx.globalAlpha = 0.7;
        ctx.fillText(row.text, cardX + padX, rowY);
        ctx.globalAlpha = 1.0;
        rowY += (lineHeight - 2) - labelFontSize;
      } else if (row.type === 'guard') {
        rowY += fontSize;
        ctx.font = `${fontSize}px 'JetBrains Mono', Consolas, monospace`;

        // Variable name
        ctx.fillStyle = t.overlayText;
        const nameW = ctx.measureText(row.name + '  ').width;
        ctx.fillText(row.name, cardX + padX, rowY);

        // Value in green
        ctx.fillStyle = t.overlayValueColor;
        ctx.fillText(row.value, cardX + padX + nameW, rowY);

        rowY += lineHeight - fontSize;
      } else if (row.type === 'effect') {
        rowY += fontSize;
        ctx.font = `${fontSize}px 'JetBrains Mono', Consolas, monospace`;

        // Build the text: "name' = expr  →  result"
        const prefix = `${row.name}' = ${row.expr}`;
        const arrow = '  →  ';
        const resultText = String(row.result);

        // Draw prefix in muted text
        ctx.fillStyle = t.overlayText;
        ctx.globalAlpha = 0.6;
        const prefixW = ctx.measureText(prefix).width;
        const availW = cardW - padX * 2;

        // If full text fits, show it all; otherwise truncate expression
        const fullW = prefixW + ctx.measureText(arrow + resultText).width;
        if (fullW <= availW) {
          ctx.fillText(prefix, cardX + padX, rowY);
          ctx.globalAlpha = 0.4;
          ctx.fillText(arrow, cardX + padX + prefixW, rowY);
          ctx.globalAlpha = 1.0;
          ctx.fillStyle = t.overlayPostColor;
          ctx.fillText(resultText, cardX + padX + prefixW + ctx.measureText(arrow).width, rowY);
        } else {
          // Compact form: "name' → result"
          ctx.globalAlpha = 1.0;
          ctx.fillStyle = t.overlayText;
          const shortPrefix = `${row.name}'`;
          const shortArrow = ' → ';
          ctx.fillText(shortPrefix, cardX + padX, rowY);
          const spW = ctx.measureText(shortPrefix).width;
          ctx.fillStyle = 'rgba(216, 222, 233, 0.4)';
          ctx.fillText(shortArrow, cardX + padX + spW, rowY);
          ctx.fillStyle = t.overlayPostColor;
          ctx.fillText(resultText, cardX + padX + spW + ctx.measureText(shortArrow).width, rowY);
        }

        ctx.globalAlpha = 1.0;
        rowY += lineHeight - fontSize;
      }
    }
  }

  /**
   * Extract variable names referenced in a precondition expression
   * @private
   */
  _extractReferencedVars(expr, varNames, valuation) {
    if (!expr || !expr.trim()) return [];
    const found = [];
    for (const name of varNames) {
      const re = new RegExp('\\b' + name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '\\b');
      if (re.test(expr)) {
        found.push({ name, value: valuation[name] });
      }
    }
    return found;
  }

  /**
   * Parse postcondition to extract variable assignments (x' = expr).
   * Returns objects with { name, expr (raw expression), result (evaluated value) }.
   * @private
   */
  _parsePostconditionChanges(expr, varNames, valuation) {
    if (!expr || !expr.trim()) return [];
    const changes = [];
    const statements = expr.split(';');
    for (const stmt of statements) {
      const trimmed = stmt.trim();
      if (!trimmed) continue;
      const m = trimmed.match(/^([a-zA-Z_][a-zA-Z0-9_]*)'\ *=\ *(.+)$/);
      if (m) {
        const [, varName, rhs] = m;
        if (varNames.includes(varName)) {
          let result = '?';
          try {
            const fn = new Function(...varNames, `return ${rhs};`);
            result = fn(...varNames.map(n => valuation[n]));
          } catch { /* evaluation failed */ }
          changes.push({ name: varName, expr: rhs.trim(), result });
        }
      }
    }
    return changes;
  }

  /**
   * Draw a rounded rectangle path
   * @private
   */
  _roundRect(x, y, w, h, r) {
    const ctx = this.ctx;
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.arcTo(x + w, y, x + w, y + r, r);
    ctx.lineTo(x + w, y + h - r);
    ctx.arcTo(x + w, y + h, x + w - r, y + h, r);
    ctx.lineTo(x + r, y + h);
    ctx.arcTo(x, y + h, x, y + h - r, r);
    ctx.lineTo(x, y + r);
    ctx.arcTo(x, y, x + r, y, r);
    ctx.closePath();
  }
}

export { DataPetriNetRenderer };