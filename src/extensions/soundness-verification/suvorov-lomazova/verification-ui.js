import { SuvorovLomazovaTraceVisualizationRenderer } from './trace-visualization-renderer.js';
import { SuvorovLomazovaVerifier } from './suvorov-lomazova-verifier.js';
/**
 * Enhanced Verification UI for Suvorov-Lomazova Verification
 * Updated to work with the new HTML overlay system
 */
class SuvorovLomazovaVerificationUI {
  constructor(app) {
    this.app = app;
    this.verifier = null;
    this.traceVisualizer = null;
    this.currentResults = null;
    this.activeCheckIndex = -1;
    this.isVisualizationActive = false;

    this.injectStyles();
    this.createVerificationSection();
    this.createVerificationModal();
    this.initializeTraceVisualizer();
  }

  /**
   * Inject CSS styles for the verification UI
   */
  injectStyles() {
    if (document.getElementById("sl-verification-styles")) return;

    const style = document.createElement("style");
    style.id = "sl-verification-styles";
    style.textContent = `
      .sl-verification-modal {
        position: fixed;
        top: 0;
        left: 0;
        width: 100%;
        height: 100%;
        background-color: rgba(0, 0, 0, 0.8);
        display: none;
        z-index: 1000;
        opacity: 0;
        transition: opacity 0.3s ease;
      }

      .sl-verification-modal.show {
        display: flex;
        align-items: center;
        justify-content: center;
        opacity: 1;
      }

      .sl-modal-content {
        background: linear-gradient(145deg, #3B4252, #434C5E);
        color: #ECEFF4;
        max-width: 1000px;
        max-height: 90vh;
        width: 90%;
        border-radius: 12px;
        box-shadow: 0 20px 40px rgba(0, 0, 0, 0.6);
        overflow: hidden;
        transform: scale(0.9);
        transition: transform 0.3s ease;
      }

      .sl-verification-modal.show .sl-modal-content {
        transform: scale(1);
      }

      .sl-modal-header {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
        padding: 20px 25px;
        display: flex;
        justify-content: space-between;
        align-items: center;
        border-bottom: 1px solid #4C566A;
      }

      .sl-modal-title {
        font-size: 20px;
        font-weight: 600;
        margin: 0;
        display: flex;
        align-items: center;
        gap: 10px;
      }

      .sl-close-btn {
        background: none;
        border: none;
        color: #ECEFF4;
        font-size: 28px;
        cursor: pointer;
        width: 40px;
        height: 40px;
        border-radius: 50%;
        display: flex;
        align-items: center;
        justify-content: center;
        transition: background-color 0.2s ease;
      }

      .sl-close-btn:hover {
        background-color: rgba(255, 255, 255, 0.1);
      }

      .sl-modal-body {
        padding: 25px;
        overflow-y: auto;
        max-height: calc(90vh - 80px);
      }

      .sl-verification-status {
        display: flex;
        align-items: center;
        gap: 15px;
        margin-bottom: 25px;
        padding: 20px;
        border-radius: 8px;
        border-left: 5px solid;
        background: rgba(255, 255, 255, 0.05);
      }

      .sl-verification-status.sound {
        border-left-color: #A3BE8C;
        background: rgba(163, 190, 140, 0.1);
      }

      .sl-verification-status.unsound {
        border-left-color: #BF616A;
        background: rgba(191, 97, 106, 0.1);
      }

      .sl-status-icon {
        font-size: 32px;
        animation: pulse 2s infinite;
      }

      @keyframes pulse {
        0%, 100% { transform: scale(1); }
        50% { transform: scale(1.1); }
      }

      .sl-status-details h3 {
        margin: 0 0 8px 0;
        font-size: 18px;
      }

      .sl-status-details p {
        margin: 0;
        color: #D8DEE9;
        font-size: 14px;
      }

      .sl-properties-grid {
        display: grid;
        grid-template-columns: repeat(auto-fit, minmax(300px, 1fr));
        gap: 20px;
        margin-bottom: 25px;
      }

      .sl-property-card {
        background: rgba(67, 76, 94, 0.6);
        border-radius: 8px;
        padding: 20px;
        border: 2px solid transparent;
        transition: all 0.3s ease;
        cursor: pointer;
      }

      .sl-property-card:hover {
        border-color: #88C0D0;
        transform: translateY(-2px);
        box-shadow: 0 8px 16px rgba(0, 0, 0, 0.3);
      }

      .sl-property-card.active {
        border-color: #5E81AC;
        background: rgba(94, 129, 172, 0.2);
      }

      .sl-property-header {
        display: flex;
        justify-content: space-between;
        align-items: flex-start;
        margin-bottom: 12px;
      }

      .sl-property-name {
        font-weight: 600;
        font-size: 16px;
        margin: 0;
        color: #ECEFF4;
      }

      .sl-property-status {
        padding: 4px 12px;
        border-radius: 20px;
        font-size: 12px;
        font-weight: 600;
        text-transform: uppercase;
        letter-spacing: 0.5px;
      }

      .sl-property-status.pass {
        background-color: #A3BE8C;
        color: #2E3440;
      }

      .sl-property-status.fail {
        background-color: #BF616A;
        color: #ECEFF4;
      }

      .sl-property-description {
        color: #D8DEE9;
        font-size: 14px;
        line-height: 1.4;
        margin-bottom: 15px;
      }

      .sl-property-details {
        font-size: 13px;
        color: #81A1C1;
      }

      .sl-counterexample-section {
        background: rgba(76, 86, 106, 0.4);
        border-radius: 6px;
        padding: 15px;
        margin-top: 15px;
        border-left: 3px solid #BF616A;
      }

      .sl-counterexample-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 10px;
      }

      .sl-counterexample-title {
        font-weight: 600;
        color: #ECEFF4;
        margin: 0;
      }

      .sl-visualize-btn {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
        border: none;
        padding: 8px 16px;
        border-radius: 20px;
        cursor: pointer;
        font-size: 12px;
        font-weight: 500;
        transition: all 0.2s ease;
      }

      .sl-visualize-btn:hover {
        transform: translateY(-1px);
        box-shadow: 0 4px 8px rgba(0, 0, 0, 0.3);
      }

      .sl-visualize-btn.active {
        background: linear-gradient(135deg, #A3BE8C, #8FBCBB);
      }

      .sl-trace-info {
        color: #D8DEE9;
        font-size: 13px;
      }

      .sl-control-panel {
        background: rgba(46, 52, 64, 0.8);
        padding: 20px;
        border-top: 1px solid #4C566A;
        display: flex;
        justify-content: space-between;
        align-items: center;
        gap: 15px;
      }

      .sl-control-group {
        display: flex;
        gap: 10px;
        align-items: center;
      }

      .sl-btn {
        padding: 10px 20px;
        border-radius: 6px;
        border: none;
        cursor: pointer;
        font-weight: 500;
        transition: all 0.2s ease;
      }

      .sl-btn-primary {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
      }

      .sl-btn-secondary {
        background: rgba(67, 76, 94, 0.8);
        color: #ECEFF4;
        border: 1px solid #4C566A;
      }

      .sl-btn:hover {
        transform: translateY(-1px);
      }

      .sl-progress {
        text-align: center;
        padding: 60px 20px;
        color: #88C0D0;
      }

      .sl-spinner {
        display: inline-block;
        width: 40px;
        height: 40px;
        border: 4px solid rgba(136, 192, 208, 0.3);
        border-radius: 50%;
        border-top-color: #88C0D0;
        animation: spin 1s linear infinite;
        margin-bottom: 20px;
      }

      @keyframes spin {
        to { transform: rotate(360deg); }
      }

      .sl-timing-info {
        text-align: center;
        color: #81A1C1;
        font-size: 13px;
        margin-top: 20px;
        padding-top: 15px;
        border-top: 1px solid #434C5E;
      }

      .sl-algorithm-info {
        background: rgba(129, 161, 193, 0.1);
        border: 1px solid #81A1C1;
        border-radius: 6px;
        padding: 15px;
        margin-bottom: 20px;
        font-size: 13px;
        color: #D8DEE9;
      }

      .sl-verification-steps {
        max-height: 150px;
        overflow-y: auto;
        background: rgba(46, 52, 64, 0.5);
        border-radius: 4px;
        padding: 10px;
        margin-top: 15px;
      }

      .sl-step {
        font-size: 11px;
        color: #81A1C1;
        margin-bottom: 5px;
        padding: 3px 6px;
        background: rgba(129, 161, 193, 0.1);
        border-radius: 3px;
      }

      /* Enhanced floating control panel for HTML overlay system */
      .sl-floating-controls {
        position: fixed;
        top: 20px;
        right: 20px;
        background: rgba(46, 52, 64, 0.95);
        padding: 15px;
        border-radius: 8px;
        border: 1px solid #4C566A;
        display: none;
        z-index: 999;
        backdrop-filter: blur(10px);
        box-shadow: 0 8px 16px rgba(0, 0, 0, 0.3);
        min-width: 200px;
      }

      .sl-floating-controls.show {
        display: block;
      }

      .sl-floating-controls h4 {
        margin: 0 0 10px 0;
        color: #ECEFF4;
        font-size: 14px;
        display: flex;
        align-items: center;
        gap: 8px;
      }

      .sl-floating-controls .sl-control-group {
        flex-direction: column;
        gap: 8px;
      }

      .sl-floating-controls .sl-btn {
        padding: 8px 16px;
        font-size: 12px;
        width: 100%;
      }

      .sl-overlay-counter {
        font-size: 12px;
        color: #81A1C1;
        margin-bottom: 10px;
        text-align: center;
        padding: 4px 8px;
        background: rgba(129, 161, 193, 0.1);
        border-radius: 4px;
      }

      .sl-overlay-info {
        font-size: 11px;
        color: #8FBCBB;
        margin-top: 8px;
        text-align: center;
        font-style: italic;
      }

      /* Verification Details Modal Styles */
      .sl-details-modal-content {
        max-width: 900px;
      }

      .sl-details-modal-body {
        max-height: 80vh;
      }

      .sl-details-overview {
        display: grid;
        grid-template-columns: repeat(auto-fit, minmax(200px, 1fr));
        gap: 15px;
        padding: 20px;
        background: rgba(67, 76, 94, 0.4);
        border-radius: 8px;
        margin-bottom: 25px;
      }

      .sl-details-overview-item {
        display: flex;
        flex-direction: column;
        gap: 5px;
      }

      .sl-details-overview-label {
        font-size: 12px;
        color: #81A1C1;
        font-weight: 500;
        text-transform: uppercase;
        letter-spacing: 0.5px;
      }

      .sl-details-overview-value {
        font-size: 16px;
        color: #ECEFF4;
        font-weight: 600;
      }

      .sl-details-sound {
        color: #A3BE8C;
      }

      .sl-details-unsound {
        color: #BF616A;
      }

      .sl-details-description {
        background: rgba(129, 161, 193, 0.1);
        border-left: 4px solid #81A1C1;
        padding: 20px;
        border-radius: 6px;
        margin-bottom: 25px;
      }

      .sl-details-description h3 {
        margin-top: 0;
        margin-bottom: 12px;
        color: #88C0D0;
        font-size: 18px;
      }

      .sl-details-description p {
        color: #D8DEE9;
        line-height: 1.6;
        margin-bottom: 10px;
      }

      .sl-details-description ul {
        margin: 10px 0;
        padding-left: 20px;
      }

      .sl-details-description li {
        color: #D8DEE9;
        margin-bottom: 8px;
        line-height: 1.5;
      }

      .sl-details-description strong {
        color: #88C0D0;
      }

      .sl-details-steps-container {
        margin-bottom: 25px;
      }

      .sl-details-steps-container h3 {
        color: #88C0D0;
        margin-bottom: 15px;
        font-size: 18px;
      }

      .sl-details-category {
        margin-bottom: 25px;
        border: 1px solid #4C566A;
        border-radius: 8px;
        overflow: hidden;
      }

      .sl-details-category-title {
        background: linear-gradient(135deg, #434C5E, #4C566A);
        color: #ECEFF4;
        padding: 12px 15px;
        margin: 0;
        font-size: 16px;
        display: flex;
        align-items: center;
        gap: 10px;
      }

      .sl-details-category-icon {
        font-size: 18px;
      }

      .sl-details-steps {
        padding: 10px;
        background: rgba(59, 66, 82, 0.3);
      }

      .sl-details-step {
        background: rgba(76, 86, 106, 0.3);
        border-left: 3px solid #5E81AC;
        border-radius: 4px;
        padding: 12px;
        margin-bottom: 10px;
        transition: all 0.2s ease;
      }

      .sl-details-step:hover {
        background: rgba(76, 86, 106, 0.5);
        border-left-color: #88C0D0;
        transform: translateX(2px);
      }

      .sl-details-step:last-child {
        margin-bottom: 0;
      }

      .sl-details-step-header {
        display: flex;
        justify-content: space-between;
        align-items: center;
        margin-bottom: 8px;
      }

      .sl-details-step-number {
        background: linear-gradient(135deg, #5E81AC, #81A1C1);
        color: #ECEFF4;
        padding: 2px 8px;
        border-radius: 12px;
        font-size: 11px;
        font-weight: 600;
      }

      .sl-details-step-time {
        color: #81A1C1;
        font-size: 11px;
        font-family: monospace;
      }

      .sl-details-step-content {
        color: #D8DEE9;
        font-size: 13px;
        line-height: 1.5;
      }

      .sl-details-metadata {
        margin-top: 10px;
        padding: 10px;
        background: rgba(46, 52, 64, 0.5);
        border-radius: 4px;
        border: 1px solid #434C5E;
      }

      .sl-metadata-item {
        font-size: 12px;
        color: #D8DEE9;
        margin-bottom: 5px;
        font-family: monospace;
      }

      .sl-metadata-item:last-child {
        margin-bottom: 0;
      }

      .sl-metadata-item strong {
        color: #88C0D0;
      }

      .sl-details-no-steps {
        text-align: center;
        color: #81A1C1;
        padding: 40px 20px;
        font-style: italic;
      }

      .sl-details-footer {
        display: flex;
        justify-content: flex-end;
        gap: 10px;
        padding-top: 20px;
        border-top: 1px solid #434C5E;
      }
    `;
    document.head.appendChild(style);
  }

  /**
   * Create verification section in sidebar
   */
  createVerificationSection() {
    const modelTab = document.querySelector('.sidebar-pane[data-tab="model"]');
    if (!modelTab || document.getElementById("sl-verification-section")) return;

    const section = document.createElement("div");
    section.id = "sl-verification-section";
    section.className = "sidebar-section";
    section.innerHTML = `
      <div class="section-header">
        <div class="section-title">
          <span class="section-icon">🔬</span>
          <h3>Formal Verification</h3>
        </div>
      </div>
      <div class="section-content">
        <p style="font-size: 14px; color: #D8DEE9; margin-bottom: 15px;">
          Verify soundness properties using Suvorov & Lomazova algorithms.
        </p>
        <div style="margin-bottom: 10px;">
           <!--<label style="display: block; margin-bottom: 5px; font-size: 13px;">Algorithm:</label>
          <select id="sl-algorithm-select" style="width: 100%; padding: 5px;">
            <option value="improved">Improved (Algorithm 6)</option>
            <option value="direct">Direct (Algorithm 5)</option>
          </select> -->
        </div>
        <button id="btn-sl-verify" class="button-primary" style="width: 100%; background: linear-gradient(135deg, #5E81AC, #81A1C1); border: none; padding: 12px; border-radius: 6px;">
          🔬 Run Formal Verification
        </button>
      </div>
    `;

    modelTab.appendChild(section);

    // Add event listener
    document.getElementById("btn-sl-verify").addEventListener("click", () => {
      this.startVerification();
    });
  }

  /**
   * Create verification modal dialog
   */
  createVerificationModal() {
    if (document.getElementById("sl-verification-modal")) return;

    const modal = document.createElement("div");
    modal.id = "sl-verification-modal";
    modal.className = "sl-verification-modal";
    modal.innerHTML = `
      <div class="sl-modal-content">
        <div class="sl-modal-header">
          <h2 class="sl-modal-title">
            <span>🔬</span>
            <span>Formal Soundness Verification</span>
          </h2>
          <button class="sl-close-btn" id="sl-close-modal">×</button>
        </div>
        <div class="sl-modal-body" id="sl-modal-body">
          <!-- Content will be dynamically generated -->
        </div>
      </div>
    `;

    document.body.appendChild(modal);

    // Create enhanced floating controls
    const floatingControls = document.createElement("div");
    floatingControls.id = "sl-floating-controls";
    floatingControls.className = "sl-floating-controls";
    floatingControls.innerHTML = `
      <h4>
        <span>🔬</span>
        <span>Verification Overlays</span>
      </h4>
      <div class="sl-overlay-counter" id="sl-overlay-counter">
        0 overlays active
      </div>
      <div class="sl-control-group">
        <button class="sl-btn sl-btn-secondary" id="sl-float-show-results">
          📊 Show Results
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-clear-highlights">
          🧹 Clear Visualization
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-hide-overlays">
          👁️ Hide Overlays
        </button>
        <button class="sl-btn sl-btn-secondary" id="sl-float-show-overlays" style="display: none;">
          👁️ Show Overlays
        </button>
      </div>
      <div class="sl-overlay-info">
        Drag overlays to reposition them
      </div>
    `;
    document.body.appendChild(floatingControls);

    // Event listeners
    document.getElementById("sl-close-modal").addEventListener("click", () => {
      this.closeModal();
    });

    modal.addEventListener("click", (e) => {
      if (e.target === modal) this.closeModal();
    });

    // Enhanced floating controls event listeners
    document.getElementById("sl-float-show-results")?.addEventListener("click", () => {
      this.showModal();
    });

    document.getElementById("sl-float-clear-highlights")?.addEventListener("click", () => {
      this.clearVisualization();
      this.hideFloatingControls();
    });

    document.getElementById("sl-float-hide-overlays")?.addEventListener("click", () => {
      this.hideOverlays();
    });

    document.getElementById("sl-float-show-overlays")?.addEventListener("click", () => {
      this.showOverlays();
    });
  }

  /**
   * Initialize trace visualizer
   */
  initializeTraceVisualizer() {
    if (this.app.editor && this.app.editor.renderer && !this.traceVisualizer) {
      this.traceVisualizer = new SuvorovLomazovaTraceVisualizationRenderer(this.app);
    }
  }

  /**
   * Show the verification modal
   */
  showModal() {
    const modal = document.getElementById("sl-verification-modal");
    modal.classList.add("show");
    this.hideFloatingControls();
  }

  /**
   * Close the verification modal (but keep visualization active)
   */
  closeModal() {
    const modal = document.getElementById("sl-verification-modal");
    modal.classList.remove("show");
    
    // Show floating controls if visualization is active
    if (this.isVisualizationActive) {
      this.showFloatingControls();
      this.updateOverlayCounter();
    }
  }

  /**
   * Show floating controls
   */
  showFloatingControls() {
    const controls = document.getElementById("sl-floating-controls");
    if (controls) {
      controls.classList.add("show");
    }
  }

  /**
   * Hide floating controls
   */
  hideFloatingControls() {
    const controls = document.getElementById("sl-floating-controls");
    if (controls) {
      controls.classList.remove("show");
    }
  }

  /**
   * Update overlay counter in floating controls
   */
  updateOverlayCounter() {
    const counter = document.getElementById("sl-overlay-counter");
    if (counter && this.traceVisualizer) {
      const overlayCount = this.traceVisualizer.htmlOverlays.size;
      counter.textContent = `${overlayCount} overlay${overlayCount !== 1 ? 's' : ''} active`;
    }
  }

  /**
   * Hide all overlays temporarily
   */
  hideOverlays() {
    if (this.traceVisualizer && this.traceVisualizer.overlayContainer) {
      this.traceVisualizer.overlayContainer.style.display = 'none';
      
      const hideBtn = document.getElementById("sl-float-hide-overlays");
      const showBtn = document.getElementById("sl-float-show-overlays");
      if (hideBtn) hideBtn.style.display = 'none';
      if (showBtn) showBtn.style.display = 'block';
    }
  }

  /**
   * Show all overlays
   */
  showOverlays() {
    if (this.traceVisualizer && this.traceVisualizer.overlayContainer) {
      this.traceVisualizer.overlayContainer.style.display = 'block';
      
      const hideBtn = document.getElementById("sl-float-hide-overlays");
      const showBtn = document.getElementById("sl-float-show-overlays");
      if (hideBtn) hideBtn.style.display = 'block';
      if (showBtn) showBtn.style.display = 'none';
    }
  }

  /**
   * Start the verification process
   */
  async startVerification() {
    const verifyButton = document.getElementById("btn-sl-verify");
    // const algorithmSelect = document.getElementById("sl-algorithm-select");
    const modalBody = document.getElementById("sl-modal-body");

    // Clear any existing visualization
    this.clearVisualization();

    // Disable button and show loading
    verifyButton.disabled = true;
    verifyButton.innerHTML = "⏳ Running Verification...";

    this.showModal();
    modalBody.innerHTML = this.createProgressHTML("Initializing verification...");

    try {
      // Get selected algorithm
      // const useImprovedAlgorithm = algorithmSelect.value === "improved";

      // Create verifier with options
      this.verifier = new SuvorovLomazovaVerifier(this.app.api.petriNet, {
        useImprovedAlgorithm: false,
        maxBound: 10,
        enableTauTransitions: true,
        enableCoverage: true,
      });

      // Run verification with progress updates
      this.currentResults = await this.verifier.verify((progress) => {
        modalBody.innerHTML = this.createProgressHTML(progress);
      });

      console.log("Verification completed:", this.currentResults);

      // Display results
      modalBody.innerHTML = this.createResultsHTML(this.currentResults);
      this.attachEventListeners();
    } catch (error) {
      console.error("Verification error:", error);
      modalBody.innerHTML = this.createErrorHTML(error);
    } finally {
      // Re-enable button
      verifyButton.disabled = false;
      verifyButton.innerHTML = "🔬 Run Formal Verification";
    }
  }

  createProgressHTML(message) {
    return `
      <div class="sl-progress">
        <div class="sl-spinner"></div>
        <h3>${message}</h3>
        <p>This may take a few moments...</p>
      </div>
    `;
  }

  createResultsHTML(results) {
    const algorithmUsed = results.checks?.some((c) =>
      c.name.includes("Algorithm 6")
    )
      ? "Improved (Algorithm 6)"
      : "Direct (Algorithm 5)";

    return `
      ${this.createStatusSection(results)}
      ${this.createAlgorithmInfoSection(algorithmUsed)}
      ${this.createPropertiesSection(results.checks || [])}
      ${this.createControlPanel()}
      ${this.createTimingSection(results)}
    `;
  }

  createStatusSection(results) {
    const statusClass = results.isSound ? "sound" : "unsound";
    const statusIcon = results.isSound ? "✅" : "❌";
    const statusText = results.isSound ? "Formally Sound" : "Formally Unsound";
    const statusDetails = results.isSound
      ? "All soundness properties are satisfied"
      : "One or more soundness properties are violated";

    return `
      <div class="sl-verification-status ${statusClass}">
        <div class="sl-status-icon">${statusIcon}</div>
        <div class="sl-status-details">
          <h3>${statusText}</h3>
          <p>${statusDetails}</p>
        </div>
      </div>
    `;
  }

  createAlgorithmInfoSection(algorithmUsed) {
    return `
      <div class="sl-algorithm-info">
        <strong>Algorithm Used:</strong> ${algorithmUsed}<br>
        <strong>Properties Checked:</strong> P1 (Deadlock Freedom), P2 (No Overfinal Markings), P3 (No Dead Transitions)<br>
        <strong>Visualization:</strong> Interactive HTML overlays show counterexamples directly on the Petri net (drag to reposition)
      </div>
    `;
  }

  createPropertiesSection(checks) {
    if (!checks.length) {
      return "<p>No property checks available.</p>";
    }

    const cardsHTML = checks
      .map((check, index) => this.createPropertyCard(check, index))
      .join("");

    return `
      <div class="sl-properties-grid">
        ${cardsHTML}
      </div>
    `;
  }

  createPropertyCard(check, index) {
    const statusClass = check.satisfied ? "pass" : "fail";
    const statusText = check.satisfied ? "Pass" : "Fail";
    const propertyName = this.getPropertyDisplayName(check.name);

    const hasCounterexample =
      !check.satisfied &&
      (check.trace ||
        check.deadTransitions ||
        check.overfinalNodes ||
        check.violatingNodes);

    const counterexampleSection = hasCounterexample
      ? `
      <div class="sl-counterexample-section">
        <div class="sl-counterexample-header">
          <h4 class="sl-counterexample-title">Counterexample</h4>
          <button class="sl-visualize-btn" data-check-index="${index}">
            Visualize
          </button>
        </div>
        <div class="sl-trace-info">
          ${this.getCounterexampleDescription(check)}
        </div>
      </div>
    `
      : "";

    return `
      <div class="sl-property-card" data-check-index="${index}">
        <div class="sl-property-header">
          <h3 class="sl-property-name">${propertyName}</h3>
          <span class="sl-property-status ${statusClass}">${statusText}</span>
        </div>
        <div class="sl-property-description">
          ${check.details || "No additional details available."}
        </div>
        ${this.getPropertySpecificDetails(check)}
        ${counterexampleSection}
      </div>
    `;
  }

  getPropertyDisplayName(checkName) {
    const nameMap = {
      "Deadlock freedom": "P1: Deadlock Freedom",
      "Deadlock freedom (P1)": "P1: Deadlock Freedom", 
      "Deadlock Freedom (P1)": "P1: Deadlock Freedom",
      DeadlockFreedom: "P1: Deadlock Freedom",
      "Overfinal marking (P2)": "P2: No Overfinal Markings",
      "Overfinal Marking (P2)": "P2: No Overfinal Markings",
      OverfinalMarkings: "P2: No Overfinal Markings",
      "Dead transitions (P3)": "P3: No Dead Transitions",
      "Dead Transitions (P3)": "P3: No Dead Transitions", 
      DeadTransitions: "P3: No Dead Transitions",
      "Boundedness (Alg. 3)": "Boundedness Check",
      Boundedness: "Boundedness Check",
    };
    return nameMap[checkName] || checkName;
  }

  getPropertySpecificDetails(check) {
    let details = "";

    if (check.deadTransitions && check.deadTransitions.length > 0) {
      details += `<div class="sl-property-details">Dead transitions: ${check.deadTransitions.length}</div>`;
    }

    if (check.overfinalNodes && check.overfinalNodes.length > 0) {
      details += `<div class="sl-property-details">Overfinal states: ${check.overfinalNodes.length}</div>`;
    }

    if (check.violatingNodes && check.violatingNodes.length > 0) {
      details += `<div class="sl-property-details">Violating states: ${check.violatingNodes.length}</div>`;
    }

    return details;
  }

  getCounterexampleDescription(check) {
    if (check.trace && check.trace.length > 0) {
      return `Trace with ${check.trace.length} steps showing property violation`;
    }

    if (check.deadTransitions && check.deadTransitions.length > 0) {
      const transitions = check.deadTransitions
        .map((dt) => dt.transitionLabel || dt.transitionId)
        .join(", ");
      return `Dead transitions: ${transitions}`;
    }

    if (check.overfinalNodes && check.overfinalNodes.length > 0) {
      return `${check.overfinalNodes.length} state(s) with overfinal markings`;
    }

    return "Property violation detected";
  }

  createControlPanel() {
    return `
      <div class="sl-control-panel">
        <div class="sl-control-group">
          <button class="sl-btn sl-btn-secondary" id="sl-clear-highlights">
            Clear Highlights
          </button>
          <button class="sl-btn sl-btn-secondary" id="sl-show-verification-details">
            📋 Show Verification Details
          </button>
          <button class="sl-btn sl-btn-secondary" id="sl-export-results">
            Export Results
          </button>
        </div>
        <div class="sl-control-group">
          <button class="sl-btn sl-btn-primary" id="sl-rerun-verification">
            Run Again
          </button>
          <button class="sl-btn sl-btn-secondary" id="sl-close-to-view">
            Close to View Net
          </button>
        </div>
      </div>
    `;
  }

  createTimingSection(results) {
    const steps = results.verificationSteps || [];
    const stepsHTML = steps
      .slice(-5)
      .map(
        (step) => `
      <div class="sl-step">
        [${step.name}] ${step.details} (+${step.timestamp}ms)
      </div>
    `
      )
      .join("");

    return `
      <div class="sl-timing-info">
        <strong>Verification completed in ${results.duration || 0} ms</strong>
        ${
          steps.length > 0
            ? `
          <div class="sl-verification-steps">
            <strong>Recent Steps:</strong>
            ${stepsHTML}
          </div>
        `
            : ""
        }
      </div>
    `;
  }

  createErrorHTML(error) {
    return `
      <div class="sl-verification-status unsound">
        <div class="sl-status-icon">❌</div>
        <div class="sl-status-details">
          <h3>Verification Error</h3>
          <p>${
            error?.message ||
            error ||
            "An unexpected error occurred during verification."
          }</p>
        </div>
      </div>
      <div class="sl-control-panel">
        <button class="sl-btn sl-btn-primary" id="sl-rerun-verification">
          Try Again
        </button>
      </div>
    `;
  }

  /**
   * Attach event listeners to the results
   */
  attachEventListeners() {
    // Property card clicks and visualize buttons
    document.querySelectorAll(".sl-property-card").forEach((card, index) => {
      card.addEventListener("click", (e) => {
        if (!e.target.classList.contains("sl-visualize-btn")) {
          this.selectPropertyCard(index);
        }
      });
    });

    document.querySelectorAll(".sl-visualize-btn").forEach((btn) => {
      btn.addEventListener("click", (e) => {
        e.stopPropagation();
        const index = parseInt(btn.getAttribute("data-check-index"));
        this.visualizeCheck(index);
      });
    });

    // Control panel buttons
    document.getElementById("sl-clear-highlights")?.addEventListener("click", () => {
      this.clearVisualization();
    });

    document.getElementById("sl-show-verification-details")?.addEventListener("click", () => {
      this.showVerificationDetailsModal();
    });

    document.getElementById("sl-export-results")?.addEventListener("click", () => {
      this.exportResults();
    });

    document.getElementById("sl-rerun-verification")?.addEventListener("click", () => {
      this.closeModal();
      this.startVerification();
    });

    document.getElementById("sl-close-to-view")?.addEventListener("click", () => {
      this.closeModal();
      this.showNotification("HTML overlays show counterexamples directly on the Petri net. Drag them to reposition!");
    });
  }

  /**
   * Select a property card
   */
  selectPropertyCard(index) {
    // Remove active class from all cards
    document.querySelectorAll(".sl-property-card").forEach((card) => {
      card.classList.remove("active");
    });

    // Add active class to selected card
    const selectedCard = document.querySelector(
      `.sl-property-card[data-check-index="${index}"]`
    );
    if (selectedCard) {
      selectedCard.classList.add("active");
      this.activeCheckIndex = index;
    }
  }

  /**
   * Visualize a check result
   */
  visualizeCheck(index) {
    if (
      !this.currentResults ||
      !this.currentResults.checks ||
      index >= this.currentResults.checks.length
    ) {
      return;
    }

    this.selectPropertyCard(index);

    if (this.traceVisualizer) {
      const check = this.currentResults.checks[index];
      this.traceVisualizer.visualizeCheck(check);
      
      // Mark visualization as active
      this.isVisualizationActive = true;

      // Update button state
      const btn = document.querySelector(`[data-check-index="${index}"]`);
      if (btn) {
        btn.classList.add("active");
        btn.textContent = "Visualizing...";
      }

      // Show notification with instructions
      this.showNotification(
        `Visualizing ${this.getPropertyDisplayName(check.name)}. HTML overlays show counterexamples - drag them to reposition!`
      );

      // Update overlay counter
      setTimeout(() => this.updateOverlayCounter(), 100);
    }
  }

  /**
   * Clear visualization
   */
  clearVisualization() {
    if (this.traceVisualizer) {
      this.traceVisualizer.clearHighlights();
    }

    // Mark visualization as inactive
    this.isVisualizationActive = false;

    // Remove active class from all cards
    document.querySelectorAll(".sl-property-card").forEach((card) => {
      card.classList.remove("active");
    });

    // Reset visualize buttons
    document.querySelectorAll(".sl-visualize-btn").forEach((btn) => {
      btn.classList.remove("active");
      btn.textContent = "Visualize";
    });

    this.activeCheckIndex = -1;
    this.hideFloatingControls();
    this.showNotification("Visualization cleared");
  }

  /**
   * Export verification results
   */
  exportResults() {
    if (!this.currentResults) return;

    const exportData = {
      timestamp: new Date().toISOString(),
      petriNetId: this.app.api.petriNet.id,
      petriNetName: this.app.api.petriNet.name,
      isSound: this.currentResults.isSound,
      duration: this.currentResults.duration,
      checks: this.currentResults.checks,
      verificationSteps: this.currentResults.verificationSteps,
    };

    const blob = new Blob([JSON.stringify(exportData, null, 2)], {
      type: "application/json",
    });

    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `verification-results-${new Date().getTime()}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);

    this.showNotification("Results exported successfully");
  }

  /**
   * Show a brief notification
   */
  showNotification(message) {
    // Create and show a temporary notification
    const notification = document.createElement("div");
    notification.style.cssText = `
      position: fixed;
      top: 20px;
      right: 20px;
      background: linear-gradient(135deg, #5E81AC, #81A1C1);
      color: #ECEFF4;
      padding: 12px 20px;
      border-radius: 6px;
      z-index: 10000;
      font-size: 14px;
      font-weight: 500;
      box-shadow: 0 4px 12px rgba(0, 0, 0, 0.3);
      transform: translateX(100%);
      transition: transform 0.3s ease;
      max-width: 300px;
    `;
    notification.textContent = message;

    document.body.appendChild(notification);

    // Animate in
    setTimeout(() => {
      notification.style.transform = "translateX(0)";
    }, 10);

    // Remove after delay
    setTimeout(() => {
      notification.style.transform = "translateX(100%)";
      setTimeout(() => {
        if (notification.parentNode) {
          document.body.removeChild(notification);
        }
      }, 300);
    }, 4000);
  }

  /**
   * Format log data for display in debug logs
   */
  _formatLogData(data) {
    if (typeof data === 'string') return data;
    if (typeof data === 'object') {
      try {
        return JSON.stringify(data, null, 2);
      } catch (e) {
        return String(data);
      }
    }
    return String(data);
  }

  /**
   * Show verification details modal with all steps and formulas
   */
  showVerificationDetailsModal() {
    if (!this.currentResults) return;

    // Create modal if it doesn't exist
    let detailsModal = document.getElementById("sl-details-modal");
    if (!detailsModal) {
      detailsModal = document.createElement("div");
      detailsModal.id = "sl-details-modal";
      detailsModal.className = "sl-verification-modal";
      document.body.appendChild(detailsModal);
    }

    const steps = this.currentResults.verificationSteps || [];
    const debugLogs = this.currentResults.debugLogs || [];
    const algorithmUsed = this.currentResults.checks?.some((c) =>
      c.name.includes("Algorithm 6")
    )
      ? "Algorithm 6 (Improved)"
      : "Algorithm 5 (Direct)";

    // Group steps by category
    const stepsByCategory = {};
    steps.forEach(step => {
      const category = step.name || 'General';
      if (!stepsByCategory[category]) {
        stepsByCategory[category] = [];
      }
      stepsByCategory[category].push(step);
    });

    // Group debug logs by category
    const logsByCategory = {};
    debugLogs.forEach(log => {
      const category = log.category || 'General';
      if (!logsByCategory[category]) {
        logsByCategory[category] = [];
      }
      logsByCategory[category].push(log);
    });

    // Generate step sections
    let stepsHTML = '';
    for (const [category, categorySteps] of Object.entries(stepsByCategory)) {
      stepsHTML += `
        <div class="sl-details-category">
          <h4 class="sl-details-category-title">
            <span class="sl-details-category-icon">📍</span>
            ${this.escapeHtml(category)}
          </h4>
          <div class="sl-details-steps">
            ${categorySteps.map((step, idx) => `
              <div class="sl-details-step">
                <div class="sl-details-step-header">
                  <span class="sl-details-step-number">${idx + 1}</span>
                  <span class="sl-details-step-time">+${step.timestamp}ms</span>
                </div>
                <div class="sl-details-step-content">
                  ${this.escapeHtml(step.details || 'No details available')}
                  ${step.metadata ? `
                    <div class="sl-details-metadata">
                      ${this.formatMetadata(step.metadata)}
                    </div>
                  ` : ''}
                </div>
              </div>
            `).join('')}
          </div>
        </div>
      `;
    }

    // Generate debug logs HTML with filtering
    let debugLogsHTML = `
      <div class="sl-debug-logs-controls">
        <div class="sl-debug-filter-group">
          <label>Filter by category:</label>
          <select id="sl-debug-category-filter" class="sl-debug-filter-select">
            <option value="all">All Categories</option>
            ${Object.keys(logsByCategory).map(cat => `
              <option value="${this.escapeHtml(cat)}">${this.escapeHtml(cat)} (${logsByCategory[cat].length})</option>
            `).join('')}
          </select>
        </div>
        <div class="sl-debug-filter-group">
          <label>Search:</label>
          <input type="text" id="sl-debug-search" class="sl-debug-search-input" placeholder="Search logs..." />
        </div>
      </div>
      <div class="sl-debug-logs-container" id="sl-debug-logs-list">
    `;

    for (const [category, logs] of Object.entries(logsByCategory)) {
      debugLogsHTML += `
        <div class="sl-debug-category" data-category="${this.escapeHtml(category)}">
          <h4 class="sl-debug-category-title">
            <span class="sl-debug-category-icon">🔍</span>
            ${this.escapeHtml(category)} (${logs.length} logs)
          </h4>
          <div class="sl-debug-logs-list">
            ${logs.map((log, idx) => {
              const levelClass = `sl-debug-level-${log.level || 'debug'}`;
              const dataStr = log.data ? this._formatLogData(log.data) : '';
              return `
                <div class="sl-debug-log-entry ${levelClass}" data-timestamp="${log.timestamp}">
                  <div class="sl-debug-log-header">
                    <span class="sl-debug-log-time">+${log.timestamp}ms</span>
                    <span class="sl-debug-log-level">${log.level || 'debug'}</span>
                  </div>
                  <div class="sl-debug-log-message">${this.escapeHtml(log.message)}</div>
                  ${dataStr ? `<div class="sl-debug-log-data"><pre>${this.escapeHtml(dataStr)}</pre></div>` : ''}
                </div>
              `;
            }).join('')}
          </div>
        </div>
      `;
    }

    debugLogsHTML += '</div>';

    // Create modal content with tabs
    detailsModal.innerHTML = `
      <div class="sl-modal-content sl-details-modal-content">
        <div class="sl-modal-header">
          <h2 class="sl-modal-title">
            <span>📋</span>
            <span>Verification Details</span>
          </h2>
          <button class="sl-close-btn" id="sl-close-details-modal">×</button>
        </div>
        <div class="sl-modal-body sl-details-modal-body">
          <div class="sl-details-overview">
            <div class="sl-details-overview-item">
              <span class="sl-details-overview-label">Algorithm:</span>
              <span class="sl-details-overview-value">${this.escapeHtml(algorithmUsed)}</span>
            </div>
            <div class="sl-details-overview-item">
              <span class="sl-details-overview-label">Total Duration:</span>
              <span class="sl-details-overview-value">${this.currentResults.duration}ms</span>
            </div>
            <div class="sl-details-overview-item">
              <span class="sl-details-overview-label">Total Steps:</span>
              <span class="sl-details-overview-value">${steps.length}</span>
            </div>
            <div class="sl-details-overview-item">
              <span class="sl-details-overview-label">Debug Logs:</span>
              <span class="sl-details-overview-value">${debugLogs.length}</span>
            </div>
            <div class="sl-details-overview-item">
              <span class="sl-details-overview-label">Result:</span>
              <span class="sl-details-overview-value ${this.currentResults.isSound ? 'sl-details-sound' : 'sl-details-unsound'}">
                ${this.currentResults.isSound ? '✅ Sound' : '❌ Unsound'}
              </span>
            </div>
          </div>

          <!-- Tabs -->
          <div class="sl-details-tabs">
            <button class="sl-details-tab active" data-tab="overview">📖 Overview</button>
            <button class="sl-details-tab" data-tab="steps">📍 Verification Steps</button>
            <button class="sl-details-tab" data-tab="debug">🔍 Debug Logs (${debugLogs.length})</button>
            <button class="sl-details-tab" data-tab="lts">🔀 LTS Structure</button>
          </div>

          <!-- Tab Content -->
          <div class="sl-details-tab-content active" data-tab-content="overview">
            <div class="sl-details-description">
              <h3>About the Verification Process</h3>
              <p>
                The Suvorov & Lomazova soundness verification uses symbolic state exploration with 
                SMT formulas to represent data constraints. The algorithm constructs a Labeled 
                Transition System (LTS) where each state is represented by a marking (token distribution) 
                and a formula (data constraints).
              </p>
              <p>
                Key techniques used:
              </p>
              <ul>
                <li><strong>Quantifier Elimination:</strong> Removes existentially quantified variables to keep formulas in the image-closed fragment</li>
                <li><strong>Formula Canonicalization:</strong> Simplifies formulas using Z3 SMT solver for efficient equivalence checking</li>
                <li><strong>Refinement:</strong> Adds τ-transitions to model invisible actions and refines preconditions</li>
                <li><strong>Reachability Analysis:</strong> Forward and backward reachability to check soundness properties</li>
              </ul>
            </div>
          </div>

          <div class="sl-details-tab-content" data-tab-content="steps">
            <div class="sl-details-steps-container">
              ${stepsHTML || '<p class="sl-details-no-steps">No detailed steps recorded.</p>'}
            </div>
          </div>

          <div class="sl-details-tab-content" data-tab-content="debug">
            <div class="sl-debug-logs-wrapper">
              ${debugLogs.length > 0 ? debugLogsHTML : '<p class="sl-details-no-steps">No debug logs captured.</p>'}
            </div>
          </div>

          <div class="sl-details-tab-content" data-tab-content="lts">
            <div class="sl-lts-container">
              ${this.currentResults.lts ? `
                <div class="sl-lts-info">
                  <div class="sl-lts-stats">
                    <div class="sl-lts-stat">
                      <span class="sl-lts-stat-label">Nodes:</span>
                      <span class="sl-lts-stat-value">${this.currentResults.lts.nodes.size}</span>
                    </div>
                    <div class="sl-lts-stat">
                      <span class="sl-lts-stat-label">Edges:</span>
                      <span class="sl-lts-stat-value">${this.currentResults.lts.edges.size}</span>
                    </div>
                  </div>
                  <div class="sl-lts-description">
                    <p>
                      The Labeled Transition System (LTS) represents all reachable states and transitions 
                      of the refined Petri net. Each node contains a marking (token distribution) and a 
                      formula (data constraints). Edges represent transition firings.
                    </p>
                  </div>
                </div>
                <div class="sl-lts-output">
                  <pre class="sl-lts-text">${this.escapeHtml(this.currentResults.lts.toString())}</pre>
                </div>
              ` : '<p class="sl-details-no-steps">LTS not available for this verification.</p>'}
            </div>
          </div>

          <div class="sl-details-footer">
            <button class="sl-btn sl-btn-secondary" id="sl-copy-details">
              📋 Copy to Clipboard
            </button>
            <button class="sl-btn sl-btn-secondary" id="sl-export-details">
              💾 Export as JSON
            </button>
            <button class="sl-btn sl-btn-primary" id="sl-close-details-btn">
              Close
            </button>
          </div>
        </div>
      </div>
    `;

    // Show modal
    detailsModal.classList.add("show");

    // Add tab switching functionality
    const tabs = detailsModal.querySelectorAll('.sl-details-tab');
    const tabContents = detailsModal.querySelectorAll('.sl-details-tab-content');
    
    tabs.forEach(tab => {
      tab.addEventListener('click', () => {
        const tabName = tab.dataset.tab;
        
        // Remove active class from all tabs and contents
        tabs.forEach(t => t.classList.remove('active'));
        tabContents.forEach(tc => tc.classList.remove('active'));
        
        // Add active class to clicked tab and corresponding content
        tab.classList.add('active');
        detailsModal.querySelector(`[data-tab-content="${tabName}"]`).classList.add('active');
      });
    });

    // Add debug log filtering
    const categoryFilter = document.getElementById('sl-debug-category-filter');
    const searchInput = document.getElementById('sl-debug-search');
    
    const filterLogs = () => {
      const category = categoryFilter?.value || 'all';
      const searchTerm = searchInput?.value.toLowerCase() || '';
      const logsList = document.getElementById('sl-debug-logs-list');
      
      if (!logsList) return;
      
      const categories = logsList.querySelectorAll('.sl-debug-category');
      categories.forEach(catDiv => {
        const catName = catDiv.dataset.category;
        const shouldShowCategory = category === 'all' || category === catName;
        
        if (!shouldShowCategory) {
          catDiv.style.display = 'none';
          return;
        }
        
        catDiv.style.display = 'block';
        
        if (searchTerm) {
          const logs = catDiv.querySelectorAll('.sl-debug-log-entry');
          logs.forEach(logEntry => {
            const text = logEntry.textContent.toLowerCase();
            logEntry.style.display = text.includes(searchTerm) ? 'block' : 'none';
          });
        } else {
          const logs = catDiv.querySelectorAll('.sl-debug-log-entry');
          logs.forEach(logEntry => {
            logEntry.style.display = 'block';
          });
        }
      });
    };
    
    categoryFilter?.addEventListener('change', filterLogs);
    searchInput?.addEventListener('input', filterLogs);

    // Add event listeners
    document.getElementById("sl-close-details-modal")?.addEventListener("click", () => {
      detailsModal.classList.remove("show");
    });

    document.getElementById("sl-close-details-btn")?.addEventListener("click", () => {
      detailsModal.classList.remove("show");
    });

    detailsModal.addEventListener("click", (e) => {
      if (e.target === detailsModal) {
        detailsModal.classList.remove("show");
      }
    });

    document.getElementById("sl-copy-details")?.addEventListener("click", () => {
      this.copyDetailsToClipboard();
    });

    document.getElementById("sl-export-details")?.addEventListener("click", () => {
      this.exportDetails();
    });
  }

  /**
   * Format metadata object for display
   */
  formatMetadata(metadata) {
    if (!metadata || typeof metadata !== 'object') return '';
    
    return Object.entries(metadata)
      .map(([key, value]) => {
        const displayValue = typeof value === 'object' 
          ? JSON.stringify(value, null, 2)
          : String(value);
        return `<div class="sl-metadata-item">
          <strong>${this.escapeHtml(key)}:</strong> 
          <span>${this.escapeHtml(displayValue)}</span>
        </div>`;
      })
      .join('');
  }

  /**
   * Escape HTML to prevent XSS
   */
  escapeHtml(text) {
    const div = document.createElement('div');
    div.textContent = text;
    return div.innerHTML;
  }

  /**
   * Copy verification details to clipboard
   */
  copyDetailsToClipboard() {
    if (!this.currentResults) return;

    const steps = this.currentResults.verificationSteps || [];
    const text = steps.map(step => 
      `[${step.name}] +${step.timestamp}ms: ${step.details}${
        step.metadata ? '\n  Metadata: ' + JSON.stringify(step.metadata) : ''
      }`
    ).join('\n\n');

    navigator.clipboard.writeText(text).then(() => {
      this.showNotification("Verification details copied to clipboard!");
    }).catch(err => {
      console.error('Failed to copy:', err);
      this.showNotification("Failed to copy to clipboard");
    });
  }

  /**
   * Export verification details as JSON
   */
  exportDetails() {
    if (!this.currentResults) return;

    const exportData = {
      timestamp: new Date().toISOString(),
      verificationSteps: this.currentResults.verificationSteps,
      duration: this.currentResults.duration,
      isSound: this.currentResults.isSound,
      checks: this.currentResults.checks
    };

    const blob = new Blob([JSON.stringify(exportData, null, 2)], {
      type: "application/json",
    });

    const url = URL.createObjectURL(blob);
    const a = document.createElement("a");
    a.href = url;
    a.download = `verification-details-${new Date().getTime()}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);

    this.showNotification("Details exported successfully");
  }

  /**
   * Cleanup when component is destroyed
   */
  destroy() {
    this.clearVisualization();
    
    if (this.traceVisualizer) {
      this.traceVisualizer.destroy();
    }

    // Remove modal if it exists
    const modal = document.getElementById("sl-verification-modal");
    if (modal && modal.parentNode) {
      modal.parentNode.removeChild(modal);
    }

    // Remove details modal
    const detailsModal = document.getElementById("sl-details-modal");
    if (detailsModal && detailsModal.parentNode) {
      detailsModal.parentNode.removeChild(detailsModal);
    }

    // Remove floating controls
    const controls = document.getElementById("sl-floating-controls");
    if (controls && controls.parentNode) {
      controls.parentNode.removeChild(controls);
    }

    // Remove styles
    const styles = document.getElementById("sl-verification-styles");
    if (styles && styles.parentNode) {
      styles.parentNode.removeChild(styles);
    }
  }
}

// Export classes for use in the main application
window.SuvorovLomazovaTraceVisualizationRenderer = SuvorovLomazovaTraceVisualizationRenderer;
window.SuvorovLomazovaVerificationUI = SuvorovLomazovaVerificationUI;

export { SuvorovLomazovaTraceVisualizationRenderer, SuvorovLomazovaVerificationUI };

// Enhanced initialization script for HTML overlay system
document.addEventListener('DOMContentLoaded', () => {
  // Wait for the main app to be ready
  const initTimer = setInterval(() => {
    if (window.petriApp && window.petriApp.editor && window.petriApp.editor.renderer) {
      // Initialize the verification UI with HTML overlay system
      if (!window.suvorovLomazovaUI) {
        console.log("Initializing Suvorov-Lomazova Verification UI with HTML Overlay System");
        window.suvorovLomazovaUI = new SuvorovLomazovaVerificationUI(window.petriApp);
        
      }
      clearInterval(initTimer);
    }
  }, 100);

  // Enhanced canvas resize handling for overlay system
  let resizeTimeout;
  function handleCanvasResize() {
    clearTimeout(resizeTimeout);
    resizeTimeout = setTimeout(() => {
      if (window.suvorovLomazovaUI && 
          window.suvorovLomazovaUI.traceVisualizer && 
          window.suvorovLomazovaUI.isVisualizationActive) {
        // Update overlay positions after canvas resize
        window.suvorovLomazovaUI.traceVisualizer.updateHTMLOverlays();
      }
    }, 100);
  }

  // Listen for window resize events that might affect canvas
  window.addEventListener('resize', handleCanvasResize);
  
  // Listen for fullscreen toggle events
  document.addEventListener('keydown', (e) => {
    if ((e.key === 'F' && (e.ctrlKey || e.metaKey)) || e.key === 'F11') {
      setTimeout(handleCanvasResize, 300); // Delay to allow fullscreen transition
    }
  });
});
