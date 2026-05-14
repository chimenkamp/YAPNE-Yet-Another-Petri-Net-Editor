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
  constructor(id, position, label = "", tokens = 0, capacity = null, finalMarking = null, fusionSet = "") {
    super(id, position, label);
    this.tokens = tokens;
    this.capacity = capacity;
    this.finalMarking = finalMarking;
    this.fusionSet = fusionSet;
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
    delay = 0,
    silent = false
  ) {
    super(id, position, label);
    this.width = 20;
    this.height = 50;
    this.isEnabled = false;
    this.priority = priority;
    this.delay = delay;
    this.silent = silent;
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

const MAIN_VIEW_ID = 'main';

class PetriNet {
  constructor(id, name = "New Petri Net", description = "") {
    this.id = id;
    this.name = name;
    this.places = new Map();
    this.transitions = new Map();
    this.arcs = new Map();
    this.description = description;
    this.views = new Map();
    this.activeViewId = MAIN_VIEW_ID;
    this.ensureDefaultView();
  }

  createDefaultView() {
    return {
      id: MAIN_VIEW_ID,
      name: 'Main',
      folderId: null,
      includeAll: true,
      elementIds: [],
      arcIds: [],
      layout: {},
      viewport: {
        panOffset: { x: 0, y: 0 },
        zoomFactor: 1
      }
    };
  }

  ensureDefaultView() {
    if (!this.views) this.views = new Map();
    if (!(this.views instanceof Map)) {
      this.views = new Map(Object.entries(this.views));
    }
    if (!this.views.has(MAIN_VIEW_ID)) {
      this.views.set(MAIN_VIEW_ID, this.createDefaultView());
    }
    if (!this.activeViewId || !this.views.has(this.activeViewId)) {
      this.activeViewId = MAIN_VIEW_ID;
    }
    return this.views.get(MAIN_VIEW_ID);
  }

  normalizeView(view) {
    const fallback = this.createDefaultView();
    return {
      ...fallback,
      ...view,
      id: view?.id || this.generateViewId(),
      name: String(view?.name || 'View'),
      folderId: view?.folderId || null,
      includeAll: Boolean(view?.includeAll),
      elementIds: Array.isArray(view?.elementIds) ? Array.from(new Set(view.elementIds)) : [],
      arcIds: Array.isArray(view?.arcIds) ? Array.from(new Set(view.arcIds)) : [],
      layout: view?.layout && typeof view.layout === 'object' ? { ...view.layout } : {},
      viewport: {
        panOffset: {
          x: Number(view?.viewport?.panOffset?.x) || 0,
          y: Number(view?.viewport?.panOffset?.y) || 0
        },
        zoomFactor: Number(view?.viewport?.zoomFactor) || 1
      }
    };
  }

  generateViewId() {
    return `view-${Math.random().toString(36).slice(2, 10)}-${Date.now().toString(36)}`;
  }

  importViews(views = [], activeViewId = MAIN_VIEW_ID) {
    this.views = new Map();
    this.views.set(MAIN_VIEW_ID, this.createDefaultView());

    if (Array.isArray(views)) {
      for (const viewData of views) {
        const view = this.normalizeView(viewData);
        this.views.set(view.id, view);
      }
    }

    const main = this.views.get(MAIN_VIEW_ID);
    main.includeAll = true;
    main.name = main.name || 'Main';
    this.activeViewId = this.views.has(activeViewId) ? activeViewId : MAIN_VIEW_ID;
  }

  serializeViews() {
    this.saveActiveViewLayout();
    this.ensureDefaultView();
    return Array.from(this.views.values()).map(view => ({
      id: view.id,
      name: view.name,
      folderId: view.folderId || null,
      includeAll: Boolean(view.includeAll),
      elementIds: Array.from(new Set(view.elementIds || [])),
      arcIds: Array.from(new Set(view.arcIds || [])),
      layout: { ...(view.layout || {}) },
      viewport: {
        panOffset: {
          x: Number(view.viewport?.panOffset?.x) || 0,
          y: Number(view.viewport?.panOffset?.y) || 0
        },
        zoomFactor: Number(view.viewport?.zoomFactor) || 1
      }
    }));
  }

  getActiveView() {
    this.ensureDefaultView();
    return this.views.get(this.activeViewId) || this.views.get(MAIN_VIEW_ID);
  }

  isMainViewActive() {
    return this.getActiveView()?.id === MAIN_VIEW_ID;
  }

  getView(id) {
    this.ensureDefaultView();
    return this.views.get(id);
  }

  getViews() {
    this.ensureDefaultView();
    return Array.from(this.views.values());
  }

  getNodeIdsForView(view = this.getActiveView()) {
    if (!view || view.includeAll) {
      return new Set([
        ...this.places.keys(),
        ...this.transitions.keys()
      ]);
    }
    return new Set(view.elementIds || []);
  }

  getArcIdsForView(view = this.getActiveView()) {
    if (!view || view.includeAll) {
      return new Set(this.arcs.keys());
    }
    return new Set(view.arcIds || []);
  }

  isElementVisibleInActiveView(id) {
    return this.getNodeIdsForView().has(id);
  }

  isArcVisibleInActiveView(arcOrId) {
    const arc = typeof arcOrId === 'string' ? this.arcs.get(arcOrId) : arcOrId;
    if (!arc) return false;
    const view = this.getActiveView();
    if (!view || view.includeAll) return true;
    return this.getArcIdsForView(view).has(arc.id)
      && this.isElementVisibleInActiveView(arc.source)
      && this.isElementVisibleInActiveView(arc.target);
  }

  getVisiblePlaces() {
    const ids = this.getNodeIdsForView();
    return Array.from(this.places.entries()).filter(([id]) => ids.has(id));
  }

  getVisibleTransitions() {
    const ids = this.getNodeIdsForView();
    return Array.from(this.transitions.entries()).filter(([id]) => ids.has(id));
  }

  getVisibleArcs() {
    return Array.from(this.arcs.entries()).filter(([, arc]) => this.isArcVisibleInActiveView(arc));
  }

  saveActiveViewLayout(renderer = null) {
    const view = this.getActiveView();
    if (!view) return;
    const nodeIds = this.getNodeIdsForView(view);
    view.layout = view.layout || {};

    for (const id of nodeIds) {
      const element = this.places.get(id) || this.transitions.get(id);
      if (!element?.position) continue;
      view.layout[id] = {
        x: element.position.x,
        y: element.position.y
      };
    }

    if (renderer) {
      view.viewport = {
        panOffset: { ...renderer.panOffset },
        zoomFactor: renderer.zoomFactor
      };
    }
  }

  applyActiveViewLayout(renderer = null) {
    this.applyViewLayout(this.activeViewId, renderer, { saveCurrent: false });
  }

  applyViewLayout(viewId, renderer = null, options = {}) {
    const { saveCurrent = true } = options;
    this.ensureDefaultView();
    const target = this.views.get(viewId) || this.views.get(MAIN_VIEW_ID);
    if (saveCurrent) {
      this.saveActiveViewLayout(renderer);
    }

    this.activeViewId = target.id;
    target.layout = target.layout || {};
    const nodeIds = this.getNodeIdsForView(target);
    for (const id of nodeIds) {
      const element = this.places.get(id) || this.transitions.get(id);
      if (!element) continue;
      if (!target.layout[id]) {
        target.layout[id] = { ...element.position };
      }
      element.position = { ...target.layout[id] };
    }

    if (renderer && target.viewport) {
      renderer.panOffset = { ...(target.viewport.panOffset || { x: 0, y: 0 }) };
      renderer.zoomFactor = Number(target.viewport.zoomFactor) || 1;
    }
  }

  addElementsToView(viewId, elementIds = [], arcIds = []) {
    const view = this.views.get(viewId);
    if (!view || view.includeAll) return false;

    const elements = new Set(view.elementIds || []);
    const arcs = new Set(view.arcIds || []);

    for (const id of elementIds) {
      if (this.places.has(id) || this.transitions.has(id)) {
        elements.add(id);
        const element = this.places.get(id) || this.transitions.get(id);
        if (element?.position) {
          view.layout[id] = view.layout[id] || { ...element.position };
        }
      }
    }

    for (const id of arcIds) {
      if (this.arcs.has(id)) arcs.add(id);
    }

    view.elementIds = Array.from(elements);
    view.arcIds = Array.from(arcs);
    return true;
  }

  addElementsToActiveView(elementIds = [], arcIds = []) {
    return this.addElementsToView(this.activeViewId, elementIds, arcIds);
  }

  removeElementsFromView(viewId, elementIds = [], arcIds = []) {
    const view = this.views.get(viewId);
    if (!view || view.includeAll) return false;

    const nodesToRemove = new Set(elementIds);
    const arcsToRemove = new Set(arcIds);
    for (const arc of this.arcs.values()) {
      if (nodesToRemove.has(arc.source) || nodesToRemove.has(arc.target)) {
        arcsToRemove.add(arc.id);
      }
    }

    view.elementIds = (view.elementIds || []).filter(id => !nodesToRemove.has(id));
    view.arcIds = (view.arcIds || []).filter(id => !arcsToRemove.has(id));
    for (const id of nodesToRemove) {
      delete view.layout?.[id];
    }
    return nodesToRemove.size > 0 || arcsToRemove.size > 0;
  }

  removeElementsFromActiveView(elementIds = [], arcIds = []) {
    return this.removeElementsFromView(this.activeViewId, elementIds, arcIds);
  }

  recordElementInActiveView(id) {
    const view = this.getActiveView();
    if (!view || view.includeAll) return;
    this.addElementsToView(view.id, [id], []);
  }

  recordArcInActiveView(id) {
    const view = this.getActiveView();
    if (!view || view.includeAll) return;
    this.addElementsToView(view.id, [], [id]);
  }

  getInternalArcIds(elementIds) {
    const ids = new Set(elementIds);
    return Array.from(this.arcs.values())
      .filter(arc => ids.has(arc.source) && ids.has(arc.target))
      .map(arc => arc.id);
  }

  getTransitionNeighborhood(transitionIds = []) {
    const elementIds = new Set();
    const arcIds = new Set();

    for (const transitionId of transitionIds) {
      if (!this.transitions.has(transitionId)) continue;
      elementIds.add(transitionId);
      for (const arc of this.arcs.values()) {
        if (arc.source === transitionId || arc.target === transitionId) {
          arcIds.add(arc.id);
          if (this.places.has(arc.source) || this.transitions.has(arc.source)) {
            elementIds.add(arc.source);
          }
          if (this.places.has(arc.target) || this.transitions.has(arc.target)) {
            elementIds.add(arc.target);
          }
        }
      }
    }

    return {
      elementIds: Array.from(elementIds),
      arcIds: Array.from(arcIds)
    };
  }

  createView(name, elementIds = [], arcIds = [], options = {}) {
    this.ensureDefaultView();
    const id = options.id || this.generateViewId();
    const nodeIds = Array.from(new Set(elementIds.filter(elementId =>
      this.places.has(elementId) || this.transitions.has(elementId)
    )));
    const edgeIds = Array.from(new Set([
      ...arcIds.filter(arcId => this.arcs.has(arcId)),
      ...(options.includeInternalArcs ? this.getInternalArcIds(nodeIds) : [])
    ]));
    const layout = {};
    for (const nodeId of nodeIds) {
      const element = this.places.get(nodeId) || this.transitions.get(nodeId);
      if (element?.position) {
        layout[nodeId] = { ...element.position };
      }
    }

    const view = this.normalizeView({
      id,
      name: name || `View ${this.views.size}`,
      folderId: options.folderId || null,
      includeAll: false,
      elementIds: nodeIds,
      arcIds: edgeIds,
      layout,
      viewport: options.viewport || {
        panOffset: { x: 0, y: 0 },
        zoomFactor: 1
      }
    });
    this.views.set(view.id, view);
    return view;
  }

  renameView(viewId, name) {
    const view = this.views.get(viewId);
    if (!view) return false;
    const cleanName = String(name || '').trim();
    if (!cleanName) return false;
    view.name = cleanName;
    return true;
  }

  deleteView(viewId) {
    if (viewId === MAIN_VIEW_ID || !this.views.has(viewId)) return false;
    this.views.delete(viewId);
    if (this.activeViewId === viewId) {
      this.activeViewId = MAIN_VIEW_ID;
    }
    return true;
  }

  removeIdsFromViews(ids) {
    const idSet = new Set(ids);
    for (const view of this.views.values()) {
      if (view.includeAll) continue;
      view.elementIds = (view.elementIds || []).filter(id => !idSet.has(id));
      view.arcIds = (view.arcIds || []).filter(id => !idSet.has(id));
      for (const id of idSet) {
        delete view.layout?.[id];
      }
    }
  }


  addPlace(place) {
    this.places.set(place.id, place);
  }

  getPlace(id) {
    return this.places.get(id);
  }

  removePlace(id) {
    const removedArcIds = [];

    this.arcs.forEach((arc, arcId) => {
      if (arc.source === id || arc.target === id) {
        this.arcs.delete(arcId);
        removedArcIds.push(arcId);
      }
    });
    const removed = this.places.delete(id);
    if (removed) {
      this.removeIdsFromViews([id, ...removedArcIds]);
    }
    return removed;
  }

  addTransition(transition) {
    this.transitions.set(transition.id, transition);
  }

  getTransition(id) {
    return this.transitions.get(id);
  }

  removeTransition(id) {
    const removedArcIds = [];

    this.arcs.forEach((arc, arcId) => {
      if (arc.source === id || arc.target === id) {
        this.arcs.delete(arcId);
        removedArcIds.push(arcId);
      }
    });
    const removed = this.transitions.delete(id);
    if (removed) {
      this.removeIdsFromViews([id, ...removedArcIds]);
    }
    return removed;
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
    const removed = this.arcs.delete(id);
    if (removed) {
      this.removeIdsFromViews([id]);
    }
    return removed;
  }

  normalizeFusionSetName(name) {
    return String(name || '').trim();
  }

  getFusionSetName(placeOrId) {
    const place = typeof placeOrId === 'string' ? this.places.get(placeOrId) : placeOrId;
    return this.normalizeFusionSetName(place?.fusionSet);
  }

  getPlaceMarkingKey(placeId) {
    const fusionSet = this.getFusionSetName(placeId);
    return fusionSet ? `fusion:${fusionSet}` : `place:${placeId}`;
  }

  getPlaceIdsForMarkingKey(markingKey) {
    if (!markingKey.startsWith('fusion:')) {
      return [markingKey.slice('place:'.length)];
    }

    const fusionSet = markingKey.slice('fusion:'.length);
    return Array.from(this.places.values())
      .filter(place => this.getFusionSetName(place) === fusionSet)
      .map(place => place.id);
  }

  getFusionSetMembers(fusionSet) {
    const normalized = this.normalizeFusionSetName(fusionSet);
    if (!normalized) return [];
    return Array.from(this.places.values())
      .filter(place => this.getFusionSetName(place) === normalized);
  }

  getPlaceTokens(placeId) {
    const markingKey = this.getPlaceMarkingKey(placeId);
    const ids = this.getPlaceIdsForMarkingKey(markingKey);
    const place = ids.map(id => this.places.get(id)).find(Boolean);
    return place ? Number(place.tokens) || 0 : 0;
  }

  setPlaceTokens(placeId, tokens) {
    const place = this.places.get(placeId);
    if (!place) return false;
    this.setMarkingTokens(this.getPlaceMarkingKey(placeId), Math.max(0, Number(tokens) || 0));
    return true;
  }

  setMarkingTokens(markingKey, tokens) {
    const safeTokens = Math.max(0, Number(tokens) || 0);
    for (const placeId of this.getPlaceIdsForMarkingKey(markingKey)) {
      const place = this.places.get(placeId);
      if (place) {
        place.tokens = safeTokens;
      }
    }
  }

  addMarkingTokens(markingKey, delta) {
    const ids = this.getPlaceIdsForMarkingKey(markingKey);
    const firstPlace = ids.map(id => this.places.get(id)).find(Boolean);
    if (!firstPlace) return;

    const capacity = this.getMarkingCapacity(markingKey);
    let nextTokens = (Number(firstPlace.tokens) || 0) + delta;
    if (nextTokens < 0) nextTokens = 0;
    if (capacity !== null && nextTokens > capacity) nextTokens = capacity;
    this.setMarkingTokens(markingKey, nextTokens);
  }

  getMarkingCapacity(markingKey) {
    const capacities = this.getPlaceIdsForMarkingKey(markingKey)
      .map(id => this.places.get(id)?.capacity)
      .filter(capacity => capacity !== null && capacity !== undefined);
    return capacities.length ? Math.min(...capacities) : null;
  }

  getFusionGroups() {
    const groups = new Map();
    for (const place of this.places.values()) {
      const fusionSet = this.getFusionSetName(place);
      if (!fusionSet) continue;
      if (!groups.has(fusionSet)) groups.set(fusionSet, []);
      groups.get(fusionSet).push(place);
    }
    return groups;
  }

  syncFusionSetTokens(fusionSet) {
    const members = this.getFusionSetMembers(fusionSet);
    if (members.length <= 1) return;
    const tokens = Number(members[0].tokens) || 0;
    for (const place of members) {
      place.tokens = tokens;
    }
  }

  syncAllFusionSetTokens() {
    for (const fusionSet of this.getFusionGroups().keys()) {
      this.syncFusionSetTokens(fusionSet);
    }
  }

  setPlaceFusionSet(placeId, fusionSet) {
    const place = this.places.get(placeId);
    if (!place) return false;

    const previousKey = this.getPlaceMarkingKey(placeId);
    const previousTokens = this.getPlaceTokens(placeId);
    place.fusionSet = this.normalizeFusionSetName(fusionSet);

    if (place.fusionSet) {
      const members = this.getFusionSetMembers(place.fusionSet);
      const existingMember = members.find(member => member.id !== placeId);
      const tokens = existingMember ? (Number(existingMember.tokens) || 0) : previousTokens;
      this.setMarkingTokens(this.getPlaceMarkingKey(placeId), tokens);
    } else {
      place.tokens = previousTokens;
    }

    if (previousKey.startsWith('fusion:')) {
      const previousSet = previousKey.slice('fusion:'.length);
      this.syncFusionSetTokens(previousSet);
    }

    return true;
  }

  updateEnabledTransitions() {
    for (const [id, transition] of this.transitions) {
      transition.isEnabled = this.isTransitionEnabled(id);
    }
  }

  isTransitionEnabled(transitionId) {
    const incomingArcs = Array.from(this.arcs.values())
      .filter(arc => arc.target === transitionId);
    const regularRequirements = new Map();

    for (const arc of incomingArcs) {
      const place = this.places.get(arc.source);
      if (!place) continue;
      const markingKey = this.getPlaceMarkingKey(arc.source);
      const tokens = this.getPlaceTokens(arc.source);

      if (arc.type === "inhibitor") {

        if (tokens >= arc.weight) return false;
      } else if (arc.type === "regular") {
        regularRequirements.set(markingKey, (regularRequirements.get(markingKey) || 0) + arc.weight);
      }

    }

    for (const [markingKey, requiredTokens] of regularRequirements) {
      const placeId = this.getPlaceIdsForMarkingKey(markingKey)[0];
      if (this.getPlaceTokens(placeId) < requiredTokens) return false;
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
      const markingKey = this.getPlaceMarkingKey(arc.source);

      if (arc.type === "regular") {
        this.addMarkingTokens(markingKey, -arc.weight);
      } else if (arc.type === "reset") {
        this.setMarkingTokens(markingKey, 0);
      }

    }


    for (const arc of outgoingArcs) {
      const place = this.places.get(arc.target);
      if (!place) continue;

      this.addMarkingTokens(this.getPlaceMarkingKey(arc.target), arc.weight);
    }

    return true;
  }

  /**
   * Detect if two transitions are in structural conflict (share input places)
   * @param {string} trans1Id - First transition ID
   * @param {string} trans2Id - Second transition ID
   * @returns {boolean} - True if transitions are in conflict
   */
  areTransitionsInConflict(trans1Id, trans2Id) {
    const incomingArcs1 = Array.from(this.arcs.values())
      .filter(arc => arc.target === trans1Id && arc.type === "regular");
    const incomingArcs2 = Array.from(this.arcs.values())
      .filter(arc => arc.target === trans2Id && arc.type === "regular");

    // Check if they share any input marking, including fusion sets
    const inputPlaces1 = new Set(incomingArcs1.map(arc => this.getPlaceMarkingKey(arc.source)));
    const inputPlaces2 = new Set(incomingArcs2.map(arc => this.getPlaceMarkingKey(arc.source)));

    for (const markingKey of inputPlaces1) {
      if (inputPlaces2.has(markingKey)) {
        // Check if there are enough tokens to fire both
        const placeId = this.getPlaceIdsForMarkingKey(markingKey)[0];
        const place = this.places.get(placeId);
        if (!place) continue;

        // Calculate total token requirement
        const weight1 = incomingArcs1
          .filter(arc => this.getPlaceMarkingKey(arc.source) === markingKey)
          .reduce((sum, arc) => sum + arc.weight, 0);
        const weight2 = incomingArcs2
          .filter(arc => this.getPlaceMarkingKey(arc.source) === markingKey)
          .reduce((sum, arc) => sum + arc.weight, 0);

        if (this.getPlaceTokens(placeId) < weight1 + weight2) {
          return true; // Conflict: not enough tokens for both
        }
      }
    }

    return false;
  }

  /**
   * Resolve conflicts by selecting a subset of transitions that can fire together
   * Randomly selects among transitions with equal priority and weight
   * @param {Array<string>} enabledTransitionIds - Array of enabled transition IDs
   * @returns {Array<string>} - Array of non-conflicting transition IDs to fire
   */
  resolveConflicts(enabledTransitionIds) {
    if (enabledTransitionIds.length <= 1) {
      return enabledTransitionIds;
    }

    // Group transitions by their input places to identify conflict sets
    const conflictGroups = new Map(); // placeId -> array of transition IDs

    for (const transId of enabledTransitionIds) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === transId && arc.type === "regular");

      for (const arc of incomingArcs) {
        const markingKey = this.getPlaceMarkingKey(arc.source);
        if (!conflictGroups.has(markingKey)) {
          conflictGroups.set(markingKey, []);
        }
        conflictGroups.get(markingKey).push({
          transitionId: transId,
          weight: arc.weight
        });
      }
    }

    // Find transitions that are actually in conflict
    const toFire = new Set(enabledTransitionIds);

    for (const [markingKey, transitions] of conflictGroups) {
      if (transitions.length <= 1) continue;

      const placeId = this.getPlaceIdsForMarkingKey(markingKey)[0];
      if (!placeId) continue;
      const tokens = this.getPlaceTokens(placeId);

      // Calculate total token requirement
      const totalRequired = transitions.reduce((sum, t) => sum + t.weight, 0);

      // If there's a conflict (not enough tokens for all)
      if (tokens < totalRequired) {
        // Group by priority and weight
        const transitionDetails = transitions.map(t => {
          const transition = this.transitions.get(t.transitionId);
          return {
            id: t.transitionId,
            priority: transition?.priority || 1,
            weight: t.weight
          };
        });

        // Sort by priority (higher first), then randomly shuffle within same priority
        transitionDetails.sort((a, b) => {
          if (b.priority !== a.priority) {
            return b.priority - a.priority;
          }
          // Same priority - randomize
          return Math.random() - 0.5;
        });

        // Select transitions until we run out of tokens
        let availableTokens = tokens;
        const selected = [];

        for (const trans of transitionDetails) {
          const arcWeight = transitions.find(t => t.transitionId === trans.id)?.weight || 0;
          if (availableTokens >= arcWeight && toFire.has(trans.id)) {
            selected.push(trans.id);
            availableTokens -= arcWeight;
          } else {
            toFire.delete(trans.id);
          }
        }
      }
    }

    return Array.from(toFire);
  }

  /**
   * Fire multiple transitions simultaneously in one atomic step (synchronous step semantics)
   * All transitions that are enabled at the start of the step will fire together
   * @param {Array<string>} transitionIds - Array of transition IDs to fire
   * @returns {boolean} - True if at least one transition was successfully fired
   */
  fireTransitionsSynchronously(transitionIds) {
    // Filter to only enabled transitions
    const enabledTransitions = transitionIds.filter(id => this.isTransitionEnabled(id));
    
    if (enabledTransitions.length === 0) {
      return false;
    }

    // Resolve conflicts - randomly select among transitions with same priority/weight
    const transitionsToFire = this.resolveConflicts(enabledTransitions);

    if (transitionsToFire.length === 0) {
      return false;
    }

    // Phase 1: Collect all arc operations (token consumption and production)
    const tokenDeltas = new Map(); // markingKey -> delta (positive for production, negative for consumption)

    for (const transitionId of transitionsToFire) {
      const incomingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.target === transitionId);
      const outgoingArcs = Array.from(this.arcs.values())
        .filter(arc => arc.source === transitionId);

      // Handle incoming arcs (token consumption)
      for (const arc of incomingArcs) {
        const place = this.places.get(arc.source);
        if (!place) continue;
        const markingKey = this.getPlaceMarkingKey(arc.source);

        if (arc.type === "regular") {
          const currentDelta = tokenDeltas.get(markingKey) || 0;
          tokenDeltas.set(markingKey, currentDelta - arc.weight);
        } else if (arc.type === "reset") {
          // Reset arcs set tokens to 0 (overrides any delta)
          tokenDeltas.set(markingKey, -this.getPlaceTokens(arc.source));
        }
      }

      // Handle outgoing arcs (token production)
      for (const arc of outgoingArcs) {
        const place = this.places.get(arc.target);
        if (!place) continue;

        const markingKey = this.getPlaceMarkingKey(arc.target);
        const currentDelta = tokenDeltas.get(markingKey) || 0;
        tokenDeltas.set(markingKey, currentDelta + arc.weight);
      }
    }

    // Phase 2: Apply all token changes atomically
    for (const [markingKey, delta] of tokenDeltas) {
      this.addMarkingTokens(markingKey, delta);
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
      arcs: Array.from(this.arcs.values()),
      views: this.serializeViews(),
      activeViewId: this.activeViewId
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
        placeData.capacity,
        placeData.finalMarking ?? null,
        placeData.fusionSet || ""
      );
      net.places.set(place.id, place);
    });
    net.syncAllFusionSetTokens();


    data.transitions.forEach((transitionData) => {
      // Detect silent transition: explicit silent flag or null/empty label
      const isSilent = transitionData.silent || !transitionData.label || transitionData.label.trim() === '';
      const transition = new Transition(
        transitionData.id,
        transitionData.position,
        transitionData.label || '',
        transitionData.priority,
        transitionData.delay,
        isSilent
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

    net.importViews(data.views, data.activeViewId);
    net.applyViewLayout(net.activeViewId, null, { saveCurrent: false });

    return net;
  }


  /**
   * Escapes XML special characters to prevent breaking XML structure
   * @param {string} str - The string to escape
   * @returns {string} The escaped string
   * @private
   */
  escapeXML(str) {
    if (str == null) return '';
    return String(str)
      .replace(/&/g, '&amp;')
      .replace(/</g, '&lt;')
      .replace(/>/g, '&gt;')
      .replace(/"/g, '&quot;')
      .replace(/'/g, '&apos;');
  }

  toPNML() {
    let pnml = `<?xml version="1.0" encoding="UTF-8"?>
  <pnml xmlns="http://www.pnml.org/version-2009/grammar/pnml">
    <net id="${this.escapeXML(this.id)}" type="http://www.pnml.org/version-2009/grammar/ptnet">
      <n>
        <text>${this.escapeXML(this.name)}</text>
      </n>`;


    for (const [id, place] of this.places) {
      pnml += `
      <place id="${this.escapeXML(id)}">
        <n>
          <text>${this.escapeXML(place.label)}</text>
        </n>
        <initialMarking>
          <text>${place.tokens}</text>
        </initialMarking>
        <graphics>
          <position x="${place.position.x}" y="${place.position.y}"/>
        </graphics>${place.fusionSet ? `
        <toolspecific tool="YAPNE" version="1.0">
          <fusionSet>${this.escapeXML(place.fusionSet)}</fusionSet>
        </toolspecific>` : ''}
      </place>`;
    }


    for (const [id, transition] of this.transitions) {
      pnml += `
      <transition id="${this.escapeXML(id)}">
        <n>
          <text>${this.escapeXML(transition.label)}</text>
        </n>
        <graphics>
          <position x="${transition.position.x}" y="${transition.position.y}"/>
        </graphics>`;
      
      // Add silent transition attribute in toolspecific section
      if (transition.silent) {
        pnml += `
        <toolspecific tool="YAPNE" version="1.0">
          <silent>true</silent>
        </toolspecific>`;
      }
      
      pnml += `
      </transition>`;
    }


    for (const [id, arc] of this.arcs) {
      pnml += `
      <arc id="${this.escapeXML(id)}" source="${this.escapeXML(arc.source)}" target="${this.escapeXML(arc.target)}">
        <inscription>
          <text>${this.escapeXML(arc.weight)}</text>
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



const DEFAULT_RENDERER_THEME = {
  placeColor: '#ffffff',
  placeStroke: '#000000',
  tokenColor: '#000000',
  transitionColor: '#d3d3d3',
  transitionStroke: '#000000',
  enabledTransitionColor: '#90ee90',
  silentTransitionColor: '#808080',
  arcColor: '#000000',
  selectedColor: '#4682b4',
  textColor: '#000000',
  backgroundColor: '#ffffff',
  gridColor: 'rgba(76, 86, 106, 0.25)',
  ghostColor: 'rgba(0, 0, 0, 0.3)',
  ghostFillColor: 'rgba(255, 255, 255, 0.5)',
  gridLineWidth: 1,
  elementStrokeWidth: 2,
  arcLineWidth: 1.5,
  ghostAlpha: 0.5,
  ghostStrokeWidth: 2,
  ghostArcLineWidth: 1.5,
  arcPreviewColor: 'rgba(0, 0, 0, 0.5)',
  arcPreviewLineWidth: 1.5,
  selectionFillColor: 'rgba(70, 130, 180, 0.12)',
  selectionBoundsColor: 'rgba(70, 130, 180, 0.85)',
  selectionLineWidth: 2,
  selectionBoxLineWidth: 1.5,
  selectionBoundsLineWidth: 1.5,
  selectionArcLineWidth: 3,
  structuralHighlightLineWidth: 4,
  structuralHighlightArcLineWidth: 4
};

const INVERTED_RENDERER_THEME = {
  placeColor: '#000000',
  placeStroke: '#ffffff',
  tokenColor: '#ffffff',
  transitionColor: '#2c2c2c',
  transitionStroke: '#ffffff',
  enabledTransitionColor: '#90ee90',
  silentTransitionColor: '#808080',
  arcColor: '#ffffff',
  selectedColor: '#b97d4b',
  textColor: '#ffffff',
  backgroundColor: '#000000',
  gridColor: 'rgba(205, 200, 188, 0.42)',
  ghostColor: 'rgba(255, 255, 255, 0.72)',
  ghostFillColor: 'rgba(255, 255, 255, 0.08)',
  gridLineWidth: 1.35,
  elementStrokeWidth: 2.4,
  arcLineWidth: 2,
  ghostAlpha: 0.85,
  ghostStrokeWidth: 2.6,
  ghostArcLineWidth: 2.4,
  arcPreviewColor: 'rgba(255, 255, 255, 0.78)',
  arcPreviewLineWidth: 2.2,
  selectionFillColor: 'rgba(185, 125, 75, 0.24)',
  selectionBoundsColor: 'rgba(255, 190, 125, 0.9)',
  selectionLineWidth: 2.6,
  selectionBoxLineWidth: 2.2,
  selectionBoundsLineWidth: 2.2,
  selectionArcLineWidth: 3.6,
  structuralHighlightLineWidth: 4.4,
  structuralHighlightArcLineWidth: 4.4
};

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
    this.panSensitivity = 1;
    this.showGrid = false;
    this.gridSize = 10;


    this.invertEditorColors = false;
    this.theme = { ...DEFAULT_RENDERER_THEME };
    this.structuralHighlights = { nodes: new Map(), arcs: new Map() };
  }

  clone() {
    const cloned = new PetriNetRenderer(this.canvas, this.petriNet);
    cloned.panOffset = { ...this.panOffset };
    cloned.zoomFactor = this.zoomFactor;
    cloned.theme = { ...this.theme };
    cloned.invertEditorColors = this.invertEditorColors;
    cloned.structuralHighlights = {
      nodes: new Map(this.structuralHighlights.nodes),
      arcs: new Map(this.structuralHighlights.arcs)
    };
    return cloned;
  }

  getElementPosition(element) {
    return element?.position || { x: 0, y: 0 };
  }

  setStructuralHighlights(components = []) {
    const nodes = new Map();
    const arcs = new Map();
    const addColor = (map, id, color) => {
      if (!map.has(id)) {
        map.set(id, []);
      }

      const colors = map.get(id);
      if (!colors.includes(color)) {
        colors.push(color);
      }
    };

    for (const component of components) {
      const color = component.color || '#88C0D0';
      const componentNodes = new Set([
        ...(component.placeIds || []),
        ...(component.transitionIds || [])
      ]);

      for (const id of componentNodes) {
        addColor(nodes, id, color);
      }

      for (const [arcId, arc] of this.petriNet.arcs) {
        if (componentNodes.has(arc.source) && componentNodes.has(arc.target)) {
          addColor(arcs, arcId, color);
        }
      }
    }

    this.structuralHighlights = { nodes, arcs };
  }

  clearStructuralHighlights() {
    this.structuralHighlights = { nodes: new Map(), arcs: new Map() };
  }

  getStructuralHighlight(id) {
    return this.getStructuralHighlightColors(id)[0] || null;
  }

  getStructuralHighlightColors(id) {
    const colors = this.structuralHighlights.nodes.get(id);
    if (!colors) return [];
    return Array.isArray(colors) ? colors : [colors];
  }

  getStructuralArcHighlight(id) {
    return this.getStructuralArcHighlightColors(id)[0] || null;
  }

  getStructuralArcHighlightColors(id) {
    const colors = this.structuralHighlights.arcs.get(id);
    if (!colors) return [];
    return Array.isArray(colors) ? colors : [colors];
  }

  colorWithAlpha(color, alpha) {
    const hex = String(color || '').trim();
    const shortHex = /^#([0-9a-f]{3})$/i.exec(hex);
    const fullHex = /^#([0-9a-f]{6})$/i.exec(hex);

    if (shortHex) {
      const [, value] = shortHex;
      const r = parseInt(value[0] + value[0], 16);
      const g = parseInt(value[1] + value[1], 16);
      const b = parseInt(value[2] + value[2], 16);
      return `rgba(${r}, ${g}, ${b}, ${alpha})`;
    }

    if (fullHex) {
      const [, value] = fullHex;
      const r = parseInt(value.slice(0, 2), 16);
      const g = parseInt(value.slice(2, 4), 16);
      const b = parseInt(value.slice(4, 6), 16);
      return `rgba(${r}, ${g}, ${b}, ${alpha})`;
    }

    return color;
  }

  drawSegmentedCircleStroke(x, y, radius, colors) {
    if (!colors.length) return;

    if (colors.length === 1) {
      this.ctx.beginPath();
      this.ctx.arc(x, y, radius, 0, Math.PI * 2);
      this.ctx.strokeStyle = colors[0];
      this.ctx.lineWidth = this.theme.structuralHighlightLineWidth;
      this.ctx.stroke();
      return;
    }

    const segments = Math.max(12, colors.length * 6);
    const gap = 0.035;
    this.ctx.lineWidth = this.theme.structuralHighlightLineWidth;
    this.ctx.lineCap = 'butt';

    for (let index = 0; index < segments; index += 1) {
      const start = -Math.PI / 2 + (index / segments) * Math.PI * 2 + gap;
      const end = -Math.PI / 2 + ((index + 1) / segments) * Math.PI * 2 - gap;
      this.ctx.beginPath();
      this.ctx.arc(x, y, radius, start, end);
      this.ctx.strokeStyle = colors[index % colors.length];
      this.ctx.stroke();
    }
  }

  drawSegmentedRectStroke(x, y, width, height, colors) {
    if (!colors.length) return;

    if (colors.length === 1) {
      this.ctx.strokeStyle = colors[0];
      this.ctx.lineWidth = this.theme.structuralHighlightLineWidth;
      this.ctx.strokeRect(x, y, width, height);
      return;
    }

    const perimeter = (width + height) * 2;
    const segments = Math.max(12, colors.length * 6);
    const gap = Math.min(4, perimeter / segments * 0.18);
    this.ctx.lineWidth = this.theme.structuralHighlightLineWidth;
    this.ctx.lineCap = 'butt';

    const pointAt = distance => {
      const d = ((distance % perimeter) + perimeter) % perimeter;
      if (d <= width) return { x: x + d, y };
      if (d <= width + height) return { x: x + width, y: y + d - width };
      if (d <= width * 2 + height) return { x: x + width - (d - width - height), y: y + height };
      return { x, y: y + height - (d - width * 2 - height) };
    };
    const corners = [width, width + height, width * 2 + height];

    for (let index = 0; index < segments; index += 1) {
      const start = (index / segments) * perimeter + gap;
      const end = ((index + 1) / segments) * perimeter - gap;
      const points = [
        pointAt(start),
        ...corners.filter(corner => corner > start && corner < end).map(pointAt),
        pointAt(end)
      ];

      this.ctx.beginPath();
      this.ctx.moveTo(points[0].x, points[0].y);
      for (const point of points.slice(1)) {
        this.ctx.lineTo(point.x, point.y);
      }
      this.ctx.strokeStyle = colors[index % colors.length];
      this.ctx.stroke();
    }
  }

  drawStructuralPlaceStroke(place, colors) {
    this.drawSegmentedCircleStroke(place.position.x, place.position.y, place.radius, colors);
  }

  drawStructuralTransitionStroke(transition, colors) {
    this.drawSegmentedRectStroke(
      transition.position.x - transition.width / 2,
      transition.position.y - transition.height / 2,
      transition.width,
      transition.height,
      colors
    );
  }

  drawSegmentedPolyline(points, colors, lineWidth, dash = []) {
    if (points.length < 2 || !colors.length) return;

    if (colors.length === 1) {
      this.ctx.beginPath();
      this.ctx.moveTo(points[0].x, points[0].y);
      for (const point of points.slice(1)) {
        this.ctx.lineTo(point.x, point.y);
      }
      this.ctx.strokeStyle = colors[0];
      this.ctx.lineWidth = lineWidth;
      this.ctx.setLineDash(dash);
      this.ctx.stroke();
      return;
    }

    const parts = [];
    let totalLength = 0;

    for (let index = 1; index < points.length; index += 1) {
      const from = points[index - 1];
      const to = points[index];
      const length = Math.hypot(to.x - from.x, to.y - from.y);
      if (!length) continue;
      parts.push({ from, to, length, start: totalLength, end: totalLength + length });
      totalLength += length;
    }

    if (!totalLength) return;

    const segments = Math.max(12, colors.length * 6, Math.ceil(totalLength / 28));
    const gap = Math.min(6, totalLength / segments * 0.16);

    const pointAt = distance => {
      const d = Math.max(0, Math.min(distance, totalLength));
      const part = parts.find(item => d <= item.end) || parts[parts.length - 1];
      const ratio = part.length ? (d - part.start) / part.length : 0;
      return {
        x: part.from.x + (part.to.x - part.from.x) * ratio,
        y: part.from.y + (part.to.y - part.from.y) * ratio
      };
    };

    this.ctx.lineWidth = lineWidth;
    this.ctx.lineCap = 'butt';
    this.ctx.setLineDash(dash);

    for (let index = 0; index < segments; index += 1) {
      const start = Math.min(totalLength, (index / segments) * totalLength + gap);
      const end = Math.max(start, ((index + 1) / segments) * totalLength - gap);
      const strokePoints = [
        pointAt(start),
        ...parts
          .filter(part => part.end > start && part.end < end)
          .map(part => part.to),
        pointAt(end)
      ];

      this.ctx.beginPath();
      this.ctx.moveTo(strokePoints[0].x, strokePoints[0].y);
      for (const point of strokePoints.slice(1)) {
        this.ctx.lineTo(point.x, point.y);
      }
      this.ctx.strokeStyle = colors[index % colors.length];
      this.ctx.stroke();
    }
  }

  render() {
    if (this.petriNet.saveActiveViewLayout) {
      this.petriNet.saveActiveViewLayout(this);
    }
    this.clear();
    

    this.ctx.save();
    this.ctx.translate(this.panOffset.x, this.panOffset.y);
    this.ctx.scale(this.zoomFactor, this.zoomFactor);

    if (this.showGrid) {
      this.drawGrid();
    }
    
    this.drawArcs();
    this.drawPlaces();
    this.drawTransitions();
    

    this.ctx.restore();
  }

  clear() {
    this.ctx.fillStyle = this.theme.backgroundColor;
    this.ctx.fillRect(0, 0, this.canvas.width, this.canvas.height);
  }

  drawGrid() {
    const worldTopLeft = this.screenToWorld(0, 0);
    const worldBottomRight = this.screenToWorld(this.canvas.width, this.canvas.height);
    const startX = Math.floor(worldTopLeft.x / this.gridSize) * this.gridSize;
    const endX = Math.ceil(worldBottomRight.x / this.gridSize) * this.gridSize;
    const startY = Math.floor(worldTopLeft.y / this.gridSize) * this.gridSize;
    const endY = Math.ceil(worldBottomRight.y / this.gridSize) * this.gridSize;

    this.ctx.save();
    this.ctx.strokeStyle = this.theme.gridColor;
    this.ctx.lineWidth = this.theme.gridLineWidth / this.zoomFactor;
    this.ctx.beginPath();

    for (let x = startX; x <= endX; x += this.gridSize) {
      this.ctx.moveTo(x, startY);
      this.ctx.lineTo(x, endY);
    }

    for (let y = startY; y <= endY; y += this.gridSize) {
      this.ctx.moveTo(startX, y);
      this.ctx.lineTo(endX, y);
    }

    this.ctx.stroke();
    this.ctx.restore();
  }

drawPlaces() {
  const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
  for (const [id, place] of places) {
    const highlightColors = this.getStructuralHighlightColors(id);
    const highlightColor = highlightColors[0] || null;

    // Main place circle
    this.ctx.beginPath();
    this.ctx.arc(place.position.x, place.position.y, place.radius, 0, Math.PI * 2);
    this.ctx.fillStyle = highlightColor ? this.colorWithAlpha(highlightColor, 0.24) : this.theme.placeColor;
    this.ctx.fill();
    
    // Base stroke
    if (highlightColors.length) {
      this.drawStructuralPlaceStroke(place, highlightColors);
    } else {
      this.ctx.strokeStyle = this.theme.placeStroke;
      this.ctx.lineWidth = this.theme.elementStrokeWidth;
      this.ctx.stroke();
    }

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
      this.ctx.lineWidth = this.theme.elementStrokeWidth;
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

    if (this.petriNet.getFusionSetName && this.petriNet.getFusionSetName(place)) {
      this.drawFusionTag(place, this.petriNet.getFusionSetName(place));
    }

    // Draw label (keep existing label drawing)
    this.ctx.fillStyle = this.theme.textColor;
    this.ctx.font = '12px Arial';
    this.ctx.textAlign = 'center';
    this.ctx.fillText(place.label, place.position.x, place.position.y + place.radius + 15);
  }
}

  drawFusionTag(place, fusionSet) {
    const tagText = `F:${fusionSet}`;
    const x = place.position.x + place.radius + 8;
    const y = place.position.y - place.radius - 12;

    this.ctx.save();
    this.ctx.font = '11px Arial';
    const paddingX = 6;
    const paddingY = 3;
    const width = this.ctx.measureText(tagText).width + paddingX * 2;
    const height = 18;

    this.ctx.fillStyle = this.invertEditorColors ? 'rgba(94, 129, 172, 0.88)' : 'rgba(136, 192, 208, 0.9)';
    this.ctx.strokeStyle = this.invertEditorColors ? '#D8DEE9' : '#5E81AC';
    this.ctx.lineWidth = 1;
    this.ctx.beginPath();
    this.drawRoundedRectPath(x, y, width, height, 4);
    this.ctx.fill();
    this.ctx.stroke();

    this.ctx.fillStyle = this.invertEditorColors ? '#ECEFF4' : '#2E3440';
    this.ctx.textAlign = 'left';
    this.ctx.textBaseline = 'middle';
    this.ctx.fillText(tagText, x + paddingX, y + height / 2 + paddingY - 2);
    this.ctx.restore();
  }

  drawRoundedRectPath(x, y, width, height, radius) {
    const r = Math.min(radius, width / 2, height / 2);
    this.ctx.moveTo(x + r, y);
    this.ctx.lineTo(x + width - r, y);
    this.ctx.quadraticCurveTo(x + width, y, x + width, y + r);
    this.ctx.lineTo(x + width, y + height - r);
    this.ctx.quadraticCurveTo(x + width, y + height, x + width - r, y + height);
    this.ctx.lineTo(x + r, y + height);
    this.ctx.quadraticCurveTo(x, y + height, x, y + height - r);
    this.ctx.lineTo(x, y + r);
    this.ctx.quadraticCurveTo(x, y, x + r, y);
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
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id, transition] of transitions) {
      const highlightColors = this.getStructuralHighlightColors(id);
      const highlightColor = highlightColors[0] || null;

      this.ctx.beginPath();
      const x = transition.position.x - transition.width / 2;
      const y = transition.position.y - transition.height / 2;
      this.ctx.rect(x, y, transition.width, transition.height);
      
      // Silent transitions are always grey
      if (transition.silent) {
        this.ctx.fillStyle = this.theme.silentTransitionColor;
      } else {
        this.ctx.fillStyle = highlightColor
          ? this.colorWithAlpha(highlightColor, 0.36)
          : transition.isEnabled
            ? this.theme.enabledTransitionColor
            : this.theme.transitionColor;
      }
      this.ctx.fill();
      if (highlightColors.length) {
        this.drawStructuralTransitionStroke(transition, highlightColors);
      } else {
        this.ctx.strokeStyle = this.theme.transitionStroke;
        this.ctx.lineWidth = this.theme.elementStrokeWidth;
        this.ctx.stroke();
      }

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
  }

  drawArcs() {
    const arcs = this.petriNet.getVisibleArcs ? this.petriNet.getVisibleArcs() : Array.from(this.petriNet.arcs);
    for (const [id, arc] of arcs) {
      let sourceElement;
      let targetElement;

      sourceElement = this.petriNet.places.get(arc.source) || this.petriNet.transitions.get(arc.source);
      targetElement = this.petriNet.places.get(arc.target) || this.petriNet.transitions.get(arc.target);

      if (!sourceElement || !targetElement) continue;

      const { start, end } = this.calculateArcEndpoints(sourceElement, targetElement);
      const highlightColors = this.getStructuralArcHighlightColors(id);
      const highlightColor = highlightColors[0] || null;

      // Set line style based on arc type
      this.ctx.save();
      
      // Modifier arcs use dotted lines
      if (arc.type === "modifier") {
        this.ctx.setLineDash([5, 5]);
      } else {
        this.ctx.setLineDash([]);
      }

      // Draw the arc line
      const arcPath = [start, ...(arc.points || []), end];
      if (highlightColors.length) {
        this.drawSegmentedPolyline(
          arcPath,
          highlightColors,
          this.theme.structuralHighlightArcLineWidth,
          arc.type === "modifier" ? [5, 5] : []
        );
      } else {
        this.ctx.beginPath();
        this.ctx.moveTo(start.x, start.y);

        if (arc.points.length > 0) {
          for (const point of arc.points) {
            this.ctx.lineTo(point.x, point.y);
          }
        }

        this.ctx.lineTo(end.x, end.y);
        this.ctx.strokeStyle = this.theme.arcColor;
        this.ctx.lineWidth = this.theme.arcLineWidth;
        this.ctx.stroke();
      }

      // Calculate direction for arc endings
      const direction = this.calculateArcDirection(
        arc.points.length > 0 ? arc.points[arc.points.length - 1] : start, 
        end
      );

      // Draw different endings based on arc type
      switch (arc.type) {
        case "inhibitor":
          this.drawInhibitorEnding(end, direction, highlightColor);
          break;
        case "read":
          this.drawReadArcEnding(end, direction, highlightColor);
          break;
        case "reset":
          this.drawResetArcEnding(end, direction, highlightColor);
          break;
        case "modifier":
          this.drawModifierArcEnding(end, direction, highlightColor);
          break;
        default: // regular arc
          this.drawArrowhead(end, direction, highlightColor);
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
  drawInhibitorEnding(position, angle, color = null) {
    const circleRadius = 6;
    const offset = 10;
    
    // Position the circle slightly before the endpoint
    const circleX = position.x - Math.cos(angle) * offset;
    const circleY = position.y - Math.sin(angle) * offset;
    
    this.ctx.beginPath();
    this.ctx.arc(circleX, circleY, circleRadius, 0, Math.PI * 2);
    this.ctx.fillStyle = this.theme.backgroundColor;
    this.ctx.fill();
    this.ctx.strokeStyle = color || this.theme.arcColor;
    this.ctx.lineWidth = this.theme.arcLineWidth;
    this.ctx.stroke();
  }

  /**
   * Draws read arc ending (filled dot before arrow)
   */
  drawReadArcEnding(position, angle, color = null) {
    const dotRadius = 4;
    const dotOffset = 15;
    
    // Draw the arrow first
    this.drawArrowhead(position, angle, color);
    
    // Position the dot before the arrowhead
    const dotX = position.x - Math.cos(angle) * dotOffset;
    const dotY = position.y - Math.sin(angle) * dotOffset;
    
    this.ctx.beginPath();
    this.ctx.arc(dotX, dotY, dotRadius, 0, Math.PI * 2);
    this.ctx.fillStyle = color || this.theme.arcColor;
    this.ctx.fill();
  }

  /**
   * Draws reset arc ending (double arrow or special symbol)
   */
  drawResetArcEnding(position, angle, color = null) {
    // Draw double arrowhead for reset arc
    this.drawArrowhead(position, angle, color);
    
    // Draw second arrowhead slightly behind
    const offset = 8;
    const secondPos = {
      x: position.x - Math.cos(angle) * offset,
      y: position.y - Math.sin(angle) * offset
    };
    this.drawArrowhead(secondPos, angle, color);
  }

  /**
   * Draws modifier arc ending (dotted line with arrow)
   */
  drawModifierArcEnding(position, angle, color = null) {
    // Just draw a regular arrowhead, the line is already dotted
    this.drawArrowhead(position, angle, color);
  }

  /**
   * Enhanced arrowhead drawing
   */
  drawArrowhead(position, angle, color = null) {
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
    this.ctx.fillStyle = color || this.theme.arcColor;
    this.ctx.fill();
  }

  drawGhostPlace(position, isGhost = true) {
    const radius = 20;
    const alpha = isGhost ? this.theme.ghostAlpha : 1.0;
    
    this.ctx.save();
    this.ctx.globalAlpha = alpha;
    
    this.ctx.beginPath();
    this.ctx.arc(position.x, position.y, radius, 0, Math.PI * 2);
    this.ctx.fillStyle = isGhost ? this.theme.ghostFillColor : this.theme.placeColor;
    this.ctx.fill();
    this.ctx.strokeStyle = isGhost ? this.theme.ghostColor : this.theme.placeStroke;
    this.ctx.lineWidth = isGhost ? this.theme.ghostStrokeWidth : this.theme.elementStrokeWidth;
    this.ctx.stroke();
    
    this.ctx.restore();
  }

  drawGhostTransition(position, isGhost = true) {
    const width = 20;
    const height = 50;
    const alpha = isGhost ? this.theme.ghostAlpha : 1.0;
    
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
    this.ctx.lineWidth = isGhost ? this.theme.ghostStrokeWidth : this.theme.elementStrokeWidth;
    this.ctx.stroke();
    
    this.ctx.restore();
  }

  drawGhostArc(start, end, isGhost = true, arcType = "regular") {
    const alpha = isGhost ? this.theme.ghostAlpha : 1.0;
    
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
    this.ctx.lineWidth = isGhost ? this.theme.ghostArcLineWidth : this.theme.arcLineWidth;
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
    const alpha = isGhost ? this.theme.ghostAlpha : 1.0;

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

  setPanSensitivity(sensitivity) {
    this.panSensitivity = sensitivity;
  }

  setGridVisibility(visible) {
    this.showGrid = visible;
  }

  setGridSize(gridSize) {
    this.gridSize = gridSize;
  }


  setTheme(theme) {
    this.theme = { ...this.theme, ...theme };
  }

  setColorInversion(enabled) {
    this.invertEditorColors = Boolean(enabled);
    this.theme = {
      ...this.theme,
      ...(this.invertEditorColors ? INVERTED_RENDERER_THEME : DEFAULT_RENDERER_THEME)
    };
  }
}


class PetriNetEditor {
  
  constructor(canvas, petriNet) {
    this.canvas = canvas;
    this.petriNet = petriNet;
    this.renderer = new PetriNetRenderer(canvas, petriNet);
    this.mode = 'select';
    this.selectedElement = null;
    this.selectedElements = new Map();
    this.arcDrawing = null;
    this.dragStart = null;
    this.dragOffset = null; // Add dragOffset property for absolute positioning
    this.boxSelection = null;
    this.selectionDragState = null;
    this.clipboardSelection = null;
    this.eventListeners = new Map();
    this.gridSize = 10; // Grid size for snap to grid
    this.snapToGrid = true;
    this.panSensitivity = 1;
    this.showGrid = false;
    this.autoConnectEnabled = true;
    this.autoConnectDistance = 300;
    this.callbacks = {
      onChange: null,
      onSelect: null
    };

    // Ghost element feature
    this.isShiftPressed = false;
    this.ghostElement = null;
    this.ghostPosition = null;
    this.ghostChain = null; // Array of chain links for shift+arc ghost chaining

    const isMac = navigator.userAgent.includes('Mac');
    this.PAN_KEY_BUTTON_CODE = isMac ? 'MetaLeft' : 'AltLeft';


    this.isPanning = false;
    this.lastPanPosition = null;
    this.pendingRenderFrame = null;
    this.pendingRenderUpdatesEnabled = false;
    this.pendingAfterRender = null;

    this.setupEventListeners();
  }

  requestRender(options = {}) {
    const { updateEnabled = false, afterRender = null } = options;

    this.pendingRenderUpdatesEnabled = this.pendingRenderUpdatesEnabled || updateEnabled;
    if (afterRender) {
      this.pendingAfterRender = afterRender;
    }

    if (this.pendingRenderFrame !== null) {
      return;
    }

    const scheduleFrame = window.requestAnimationFrame || ((callback) => window.setTimeout(callback, 16));
    this.pendingRenderFrame = scheduleFrame(() => {
      const shouldUpdateEnabled = this.pendingRenderUpdatesEnabled;
      const afterFrameRender = this.pendingAfterRender;

      this.pendingRenderFrame = null;
      this.pendingRenderUpdatesEnabled = false;
      this.pendingAfterRender = null;

      this.render({ updateEnabled: shouldUpdateEnabled });

      if (afterFrameRender) {
        afterFrameRender();
      }
    });
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
        this.renderer.adjustPan(dx * this.panSensitivity, dy * this.panSensitivity);
        this.lastPanPosition = { x, y };
        this.requestRender();
        return;
      }
    

      const worldPos = this.renderer.screenToWorld(x, y);

      // Handle ghost element tracking (select mode or addArc mode)
      if (this.isShiftPressed && this.selectedElement &&
          (this.mode === 'select' || (this.mode === 'addArc' && !this.arcDrawing))) {
        this.updateGhostElement(worldPos);
        this.requestRender();
        return;
      }
    
      if (this.mode === 'select' && this.boxSelection) {
        this.updateBoxSelection(worldPos.x, worldPos.y);
        this.requestRender();
      } else if (this.mode === 'select' && this.selectedElement) {
        this.handleDrag(worldPos.x, worldPos.y);
        this.requestRender();
      } else if (this.mode === 'addArc' && this.arcDrawing) {

        this.requestRender({
          afterRender: () => this.renderArcDrawing(worldPos.x, worldPos.y)
        });
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
      } else if (this.mode === 'select' && this.boxSelection) {
        this.completeBoxSelection();
      } else if (this.mode === 'select' && this.selectionDragState?.moved) {
        this.finalizeSelectionMove();
      }


      this.dragStart = null;
      this.dragOffset = null; // Reset dragOffset when done dragging
      this.selectionDragState = null;
      
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
      this.requestRender();

      if (this.app && this.app.updateZoomDisplay) {
        this.app.updateZoomDisplay();
      }
    };


    const keyDownHandler = (event) => {
      const tag = document.activeElement?.tagName;
      const isInputFocused = tag === 'INPUT' || tag === 'TEXTAREA' || tag === 'SELECT';

      if ((event.ctrlKey || event.metaKey) && !isInputFocused) {
        const key = event.key.toLowerCase();
        if (key === 'a') {
          event.preventDefault();
          this.selectAllElements();
          return;
        }
        if (key === 'c') {
          event.preventDefault();
          this.copySelection();
          return;
        }
        if (key === 'v') {
          event.preventDefault();
          this.pasteSelection();
          return;
        }
      }

      if (event.shiftKey && event.code === 'Delete' && this.selectedElement && !this.petriNet.isMainViewActive?.()) {
        event.preventDefault();
        if (this.app?.api?.removeSelectionFromActiveView) {
          this.app.api.removeSelectionFromActiveView();
          this.app._takeSnapshot?.('Remove selection from view');
          this.app.viewsPanel?.refresh();
        }
        return;
      }

      // Delete currently selected element – delegate to deleteSelected()
      if (event.code === 'Delete' && this.selectedElement) {
        this.deleteSelected();
        return;
      }

      // Add/remove tokens from selected place with arrow keys
      if (this.selectedElement && this.selectedElement.type === 'place') {
        if (event.code === 'ArrowUp') {
          event.preventDefault();
          const place = this.petriNet.places.get(this.selectedElement.id);
          if (place) {
            this.petriNet.addMarkingTokens(this.petriNet.getPlaceMarkingKey(this.selectedElement.id), 1);
            if (this.callbacks.onChange) {
              this.callbacks.onChange();
            }
            this.render();
          }
          return;
        } else if (event.code === 'ArrowDown') {
          event.preventDefault();
          const place = this.petriNet.places.get(this.selectedElement.id);
          if (place && this.petriNet.getPlaceTokens(this.selectedElement.id) > 0) {
            this.petriNet.addMarkingTokens(this.petriNet.getPlaceMarkingKey(this.selectedElement.id), -1);
            if (this.callbacks.onChange) {
              this.callbacks.onChange();
            }
            this.render();
          }
          return;
        }
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
        this.ghostChain = null;
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
        position: { ...this.ghostPosition }
      };
    } else if (this.selectedElement.type === 'transition') {
      this.ghostElement = {
        type: 'place',
        position: { ...this.ghostPosition }
      };
    }

    // Build ghost chain — find the closest fitting element and create chained ghosts
    this.ghostChain = this._buildGhostChain(this.selectedElement, this.ghostElement);
  }

  /**
   * Build a ghost chain from the first ghost element to the closest fitting
   * existing element. Returns an array of { element, arc } entries.
   * Each arc connects the previous node to the current ghost/real element.
   */
  _buildGhostChain(sourceSelection, firstGhost) {
    const chain = [];
    if (!firstGhost) return chain;

    // The first link: selected element → ghost
    const sourceObj = this._getElementObject(sourceSelection.id, sourceSelection.type);
    if (!sourceObj) return chain;

    chain.push({
      from: { id: sourceSelection.id, type: sourceSelection.type, position: { ...sourceObj.position } },
      to:   { id: null, type: firstGhost.type, position: { ...firstGhost.position }, isGhost: true },
    });

    // Now try to find the closest existing element of the opposite type to connect to
    const nextNeededType = firstGhost.type === 'place' ? 'transition' : 'place';
    // Actually we want the same type as the source (place→transition→place chain)
    // nextNeededType is the opposite of firstGhost.type
    const closestTarget = this._findClosestElement(
      firstGhost.position,
      firstGhost.type === 'place' ? 'transition' : 'place',
      sourceSelection.id // exclude the source itself
    );

    if (this.autoConnectEnabled && closestTarget && closestTarget.distance < this.autoConnectDistance) {
      chain.push({
        from: { id: null, type: firstGhost.type, position: { ...firstGhost.position }, isGhost: true },
        to:   { id: closestTarget.id, type: closestTarget.type, position: { ...closestTarget.position }, isGhost: false },
      });
    }

    return chain;
  }

  /**
   * Get the actual element object from the Petri net by id and type.
   */
  _getElementObject(id, type) {
    if (type === 'place') return this.petriNet.places.get(id);
    if (type === 'transition') return this.petriNet.transitions.get(id);
    return null;
  }

  /**
   * Find the closest existing element of a given type to a position.
   * Excludes the element with excludeId.
   */
  _findClosestElement(position, type, excludeId, excludeIds = null) {
    let closest = null;
    let minDist = Infinity;

    const collection = type === 'place'
      ? (this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places))
      : (this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions));
    for (const [id, el] of collection) {
      if (id === excludeId) continue;
      if (excludeIds && excludeIds.has(id)) continue;
      const dx = el.position.x - position.x;
      const dy = el.position.y - position.y;
      const dist = Math.sqrt(dx * dx + dy * dy);
      if (dist < minDist) {
        minDist = dist;
        closest = { id, type, position: { x: el.position.x, y: el.position.y }, distance: dist };
      }
    }

    return closest;
  }

  placeGhostElement() {
    if (!this.ghostElement || !this.ghostPosition || !this.selectedElement) return;

    const ghostPos = { ...this.ghostPosition };
    let newElementId;
    const newElementType = this.ghostElement.type;

    // Create the new element based on ghost type
    if (this.ghostElement.type === 'place') {
      newElementId = this.generateUUID();
      const newPlace = new Place(
        newElementId, 
        ghostPos, 
        `P${this.petriNet.places.size + 1}`
      );
      this.petriNet.addPlace(newPlace);
      this.petriNet.recordElementInActiveView?.(newElementId);
    } else if (this.ghostElement.type === 'transition') {
      newElementId = this.generateUUID();
      const newTransition = new Transition(
        newElementId, 
        ghostPos, 
        `T${this.petriNet.transitions.size + 1}`
      );
      this.petriNet.addTransition(newTransition);
      this.petriNet.recordElementInActiveView?.(newElementId);
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
        "" // default label
      );

      if (this.petriNet.addArc(arc)) {
        this.petriNet.recordArcInActiveView?.(arcId);
        // If ghost chain has a second link (auto-connect to closest element), materialize it
        if (this.ghostChain && this.ghostChain.length > 1) {
          const secondLink = this.ghostChain[1];
          if (secondLink.to && !secondLink.to.isGhost && secondLink.to.id) {
            const chainArcId = this.generateUUID();
            const chainArc = new Arc(
              chainArcId,
              newElementId,
              secondLink.to.id,
              1,
              "regular",
              [],
              ""
            );
            if (this.petriNet.addArc(chainArc)) {
              this.petriNet.recordArcInActiveView?.(chainArcId);
            }
          }
        }

        // Select the new element so the user can keep chaining
        this.selectedElement = { id: newElementId, type: newElementType };
        this.selectedElements.clear();
        this.selectedElements.set(this._selectionKey(newElementId, newElementType), {
          id: newElementId,
          type: newElementType
        });
        this.dragOffset = null;

        // Clear ghost state
        this.ghostElement = null;
        this.ghostPosition = null;
        this.ghostChain = null;

        // Update callbacks
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(newElementId, newElementType);
        }

        if (this.callbacks.onChange) {
          this.callbacks.onChange();
        }

        this.render();
      }
    }
  }

  handleSelection(x, y) {
    const hitElement = this._findElementAt(x, y);
    if (hitElement) {
      if (!this._selectionHas(hitElement.id, hitElement.type)) {
        this.selectElement(hitElement.id, hitElement.type, { silentRender: true, notify: false });
      }
      const element = this._getElementObject(hitElement.id, hitElement.type);
      this.dragOffset = element ? { x: x - element.position.x, y: y - element.position.y } : null;
      this.dragStart = { x, y };
      this.selectionDragState = this._createSelectionDragState();
      if (this.callbacks.onSelect) {
        if (this.selectedElements.size > 1) {
          this.callbacks.onSelect(null, 'selection');
        } else {
          this.callbacks.onSelect(hitElement.id, hitElement.type);
        }
      }
      return;
    }

    const arcs = this.petriNet.getVisibleArcs ? this.petriNet.getVisibleArcs() : Array.from(this.petriNet.arcs);
    for (const [id, arc] of arcs) {

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
        this.clearMultiSelection();
        this.selectedElement = { id, type: 'arc' };

        this.dragOffset = null;
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(id, 'arc');
        }
        return;
      }
    }

    this.clearSelection({ notify: true, render: false });
    this.startBoxSelection(x, y);
  }

  handleDrag(x, y) {
    if (!this.selectedElement) return;
    if (!this.dragStart) return;


    if (this.selectedElement.type === 'arc') {
      const dx = x - this.dragStart.x;
      const dy = y - this.dragStart.y;
      

      
      this.dragStart = { x, y };
      return;
    }

    if (this.selectionDragState && this.selectedElements.size > 1) {
      const anchor = this.selectionDragState.anchor;
      const dx = x - anchor.x;
      const dy = y - anchor.y;
      if (Math.abs(dx) > 0.5 || Math.abs(dy) > 0.5) {
        this.selectionDragState.moved = true;
      }

      for (const [key, initial] of this.selectionDragState.initialPositions) {
        const element = this._getElementObject(initial.id, initial.type);
        if (!element) continue;
        element.position.x = initial.x + dx;
        element.position.y = initial.y + dy;
        if (this.snapToGrid) {
          element.position.x = Math.round(element.position.x / this.gridSize) * this.gridSize;
          element.position.y = Math.round(element.position.y / this.gridSize) * this.gridSize;
        }
      }
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

  _selectionKey(id, type) {
    return `${type}:${id}`;
  }

  _selectionHas(id, type) {
    return this.selectedElements.has(this._selectionKey(id, type));
  }

  _syncSelectedElementFromMultiSelection() {
    if (this.selectedElements.size === 0) {
      this.selectedElement = null;
    } else if (this.selectedElements.size === 1) {
      const first = this.selectedElements.values().next().value;
      this.selectedElement = { id: first.id, type: first.type };
    } else {
      this.selectedElement = { id: null, type: 'selection' };
    }
  }

  clearMultiSelection() {
    this.selectedElements.clear();
  }

  clearSelection(options = {}) {
    const { notify = true, render = true } = options;
    this.selectedElement = null;
    this.clearMultiSelection();
    this.dragOffset = null;
    this.boxSelection = null;
    this.selectionDragState = null;
    this.ghostElement = null;
    this.ghostPosition = null;
    this.ghostChain = null;
    if (notify && this.callbacks.onSelect) {
      this.callbacks.onSelect(null, null);
    }
    if (render) {
      this.render();
    }
  }

  setMultiSelection(elements, options = {}) {
    const { notify = true, render = true } = options;
    this.selectedElements.clear();
    for (const element of elements) {
      if (!element || !element.id || !element.type || element.type === 'arc') continue;
      this.selectedElements.set(this._selectionKey(element.id, element.type), {
        id: element.id,
        type: element.type
      });
    }
    this._syncSelectedElementFromMultiSelection();
    this.dragOffset = null;
    this.ghostElement = null;
    this.ghostPosition = null;
    this.ghostChain = null;
    if (notify && this.callbacks.onSelect) {
      if (this.selectedElements.size === 1) {
        const first = this.selectedElements.values().next().value;
        this.callbacks.onSelect(first.id, first.type);
      } else if (this.selectedElements.size > 1) {
        this.callbacks.onSelect(null, 'selection');
      } else {
        this.callbacks.onSelect(null, null);
      }
    }
    if (render) {
      this.render();
    }
  }

  selectAllElements() {
    const elements = [];
    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id] of places) {
      elements.push({ id, type: 'place' });
    }
    for (const [id] of transitions) {
      elements.push({ id, type: 'transition' });
    }
    this.setMultiSelection(elements);
  }

  startBoxSelection(x, y) {
    this.boxSelection = {
      start: { x, y },
      current: { x, y }
    };
  }

  updateBoxSelection(x, y) {
    if (!this.boxSelection) return;
    this.boxSelection.current = { x, y };
  }

  completeBoxSelection() {
    if (!this.boxSelection) return;
    const bounds = this._normalizeBounds(this.boxSelection.start, this.boxSelection.current);
    this.boxSelection = null;
    const selected = [];

    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id, place] of places) {
      if (this._pointInBounds(place.position, bounds)) {
        selected.push({ id, type: 'place' });
      }
    }
    for (const [id, transition] of transitions) {
      if (this._pointInBounds(transition.position, bounds)) {
        selected.push({ id, type: 'transition' });
      }
    }

    this.setMultiSelection(selected, { render: false });
  }

  _normalizeBounds(a, b) {
    return {
      left: Math.min(a.x, b.x),
      right: Math.max(a.x, b.x),
      top: Math.min(a.y, b.y),
      bottom: Math.max(a.y, b.y)
    };
  }

  _pointInBounds(point, bounds) {
    return point.x >= bounds.left && point.x <= bounds.right &&
      point.y >= bounds.top && point.y <= bounds.bottom;
  }

  _createSelectionDragState() {
    const initialPositions = new Map();
    for (const [key, item] of this.selectedElements) {
      const element = this._getElementObject(item.id, item.type);
      if (!element) continue;
      initialPositions.set(key, {
        id: item.id,
        type: item.type,
        x: element.position.x,
        y: element.position.y
      });
    }
    return {
      anchor: { ...this.dragStart },
      initialPositions,
      moved: false,
      originalSelection: new Map(this.selectedElements)
    };
  }

  copySelection() {
    const selectedNodes = this.selectedElements.size > 0
      ? Array.from(this.selectedElements.values())
      : (this.selectedElement && this.selectedElement.type !== 'arc' && this.selectedElement.type !== 'selection'
        ? [this.selectedElement]
        : []);

    if (selectedNodes.length === 0) return false;

    const selectedIds = new Set(selectedNodes.map(item => item.id));
    const nodes = selectedNodes
      .map(item => {
        const element = this._getElementObject(item.id, item.type);
        if (!element) return null;
        return {
          id: item.id,
          type: item.type,
          data: this._cloneElementData(element)
        };
      })
      .filter(Boolean);

    const arcs = [];
    for (const arc of this.petriNet.arcs.values()) {
      if (selectedIds.has(arc.source) && selectedIds.has(arc.target)) {
        arcs.push(this._cloneArcData(arc));
      }
    }

    this.clipboardSelection = {
      nodes,
      arcs,
      boundary: this._getBoundaryNodes(new Set(nodes.map(node => node.id))),
      pasteCount: 0
    };
    return true;
  }

  pasteSelection() {
    if (!this.clipboardSelection || this.clipboardSelection.nodes.length === 0) return false;

    this.clipboardSelection.pasteCount += 1;
    const offset = 35 * this.clipboardSelection.pasteCount;
    const idMap = new Map();
    const pastedSelection = [];

    for (const node of this.clipboardSelection.nodes) {
      const newId = this.generateUUID();
      idMap.set(node.id, newId);
      const clone = this._restoreElementClone(node.data, newId, offset, node.type);
      if (node.type === 'place') {
        this.petriNet.addPlace(clone);
      } else if (node.type === 'transition') {
        this.petriNet.addTransition(clone);
      }
      this.petriNet.recordElementInActiveView?.(newId);
      pastedSelection.push({ id: newId, type: node.type });
    }

    for (const arcData of this.clipboardSelection.arcs) {
      const source = idMap.get(arcData.source);
      const target = idMap.get(arcData.target);
      if (!source || !target) continue;
      const arc = this._restoreArcClone(arcData, this.generateUUID(), source, target);
      this.petriNet.addArc(arc);
      this.petriNet.recordArcInActiveView?.(arc.id);
    }

    this.setMultiSelection(pastedSelection, { notify: true, render: false });

    if (this.autoConnectEnabled) {
      const pastedIds = new Set(pastedSelection.map(item => item.id));
      this._autoConnectBoundaryNodes(pastedIds);
    }

    this.render();
    if (this.callbacks.onChange) {
      this.callbacks.onChange();
    }
    return true;
  }

  finalizeSelectionMove() {
    if (!this.autoConnectEnabled || this.selectedElements.size <= 1) return;
    const selectedIds = new Set(Array.from(this.selectedElements.values()).map(item => item.id));
    this._autoConnectBoundaryNodes(selectedIds);
  }

  _cloneElementData(element) {
    const data = {};
    for (const key of Object.keys(element)) {
      data[key] = this._clonePlainValue(element[key]);
    }
    return {
      prototype: Object.getPrototypeOf(element),
      data
    };
  }

  _cloneArcData(arc) {
    return this._clonePlainValue(arc);
  }

  _clonePlainValue(value) {
    if (value === null || typeof value !== 'object') return value;
    if (Array.isArray(value)) {
      return value.map(item => this._clonePlainValue(item));
    }
    const clone = {};
    for (const key of Object.keys(value)) {
      clone[key] = this._clonePlainValue(value[key]);
    }
    return clone;
  }

  _restoreElementClone(snapshot, id, offset, type) {
    const clone = Object.create(snapshot.prototype || Object.prototype);
    Object.assign(clone, this._clonePlainValue(snapshot.data));
    clone.id = id;
    clone.label = this._getNextPastedLabel(snapshot.data.label, type);
    clone.position = {
      x: (snapshot.data.position?.x || 0) + offset,
      y: (snapshot.data.position?.y || 0) + offset
    };
    if (this.snapToGrid) {
      clone.position.x = Math.round(clone.position.x / this.gridSize) * this.gridSize;
      clone.position.y = Math.round(clone.position.y / this.gridSize) * this.gridSize;
    }
    return clone;
  }

  _getNextPastedLabel(label, type) {
    const original = String(label || '');
    if (!original.trim()) return original;

    const match = original.match(/^(.*?)(\d+)$/);
    const prefix = match ? match[1] : `${original} `;
    let maxNumber = match ? Number(match[2]) : 1;
    const collection = type === 'place' ? this.petriNet.places : this.petriNet.transitions;
    const labelPattern = new RegExp(`^${this._escapeRegExp(prefix)}(\\d+)$`);

    for (const element of collection.values()) {
      const existing = String(element.label || '').match(labelPattern);
      if (existing) {
        maxNumber = Math.max(maxNumber, Number(existing[1]));
      }
    }

    return `${prefix}${maxNumber + 1}`;
  }

  _escapeRegExp(value) {
    return String(value).replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
  }

  _restoreArcClone(arcData, id, source, target) {
    const arc = Object.create(Arc.prototype);
    Object.assign(arc, this._clonePlainValue(arcData));
    arc.id = id;
    arc.source = source;
    arc.target = target;
    arc.points = Array.isArray(arc.points) ? arc.points.map(point => ({ ...point })) : [];
    return arc;
  }

  _getBoundaryNodes(selectedIds) {
    const boundary = {
      starts: new Set(selectedIds),
      ends: new Set(selectedIds)
    };

    for (const arc of this.petriNet.arcs.values()) {
      if (selectedIds.has(arc.source) && selectedIds.has(arc.target)) {
        boundary.starts.delete(arc.target);
        boundary.ends.delete(arc.source);
      }
    }

    return boundary;
  }

  _autoConnectBoundaryNodes(selectedIds) {
    const boundary = this._getBoundaryNodes(selectedIds);
    const existingPairs = new Set(Array.from(this.petriNet.arcs.values()).map(arc => `${arc.source}->${arc.target}`));
    const connectedElementPairs = this._getArcElementPairKeys();

    for (const id of boundary.starts) {
      this._connectBoundaryNode(id, 'incoming', selectedIds, existingPairs, connectedElementPairs);
    }
    for (const id of boundary.ends) {
      this._connectBoundaryNode(id, 'outgoing', selectedIds, existingPairs, connectedElementPairs);
    }
  }

  _connectBoundaryNode(id, direction, selectedIds, existingPairs, connectedElementPairs) {
    const node = this.petriNet.places.get(id) || this.petriNet.transitions.get(id);
    if (!node) return;
    const nodeType = this.petriNet.places.has(id) ? 'place' : 'transition';
    const targetType = nodeType === 'place' ? 'transition' : 'place';
    const candidate = this._findClosestElement(node.position, targetType, id, selectedIds);
    if (!candidate || candidate.distance > this.autoConnectDistance) return;

    const source = direction === 'incoming' ? candidate.id : id;
    const target = direction === 'incoming' ? id : candidate.id;
    const pairKey = `${source}->${target}`;
    if (existingPairs.has(pairKey)) return;
    const elementPairKey = this._arcElementPairKey(source, target);
    if (connectedElementPairs.has(elementPairKey)) return;

    const arc = new Arc(this.generateUUID(), source, target, 1, 'regular', [], '');
    if (this.petriNet.addArc(arc)) {
      existingPairs.add(pairKey);
      connectedElementPairs.add(elementPairKey);
      this.petriNet.recordArcInActiveView?.(arc.id);
    }
  }

  _arcElementPairKey(sourceId, targetId) {
    return [sourceId, targetId].sort().join('<->');
  }

  _getArcElementPairKeys() {
    return new Set(Array.from(this.petriNet.arcs.values()).map(arc => this._arcElementPairKey(arc.source, arc.target)));
  }

  addPlace(x, y) {
    if (this.snapToGrid) {
      x = Math.round(x / this.gridSize) * this.gridSize;
      y = Math.round(y / this.gridSize) * this.gridSize;
    }

    const id = this.generateUUID();
    const place = new Place(id, { x, y }, `P${this.petriNet.places.size + 1}`);
    this.petriNet.addPlace(place);
    this.petriNet.recordElementInActiveView?.(id);
    this.selectedElement = { id, type: 'place' };
    this.selectedElements.clear();
    this.selectedElements.set(this._selectionKey(id, 'place'), { id, type: 'place' });

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
    this.petriNet.recordElementInActiveView?.(id);
    this.selectedElement = { id, type: 'transition' };
    this.selectedElements.clear();
    this.selectedElements.set(this._selectionKey(id, 'transition'), { id, type: 'transition' });

    if (this.callbacks.onSelect) {
      this.callbacks.onSelect(id, 'transition');
    }
  }

  startArcDrawing(x, y) {

    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id, place] of places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      const distance = Math.sqrt(dx * dx + dy * dy);

      if (distance <= place.radius) {
        this.arcDrawing = { sourceId: id, sourceType: 'place' };
        return;
      }
    }

    for (const [id, transition] of transitions) {
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

    // Check if the cursor is hovering over an existing compatible element
    const hoverTarget = this._findElementAt(x, y);
    const isOverCompatible = hoverTarget && (
      (this.arcDrawing.sourceType === 'place' && hoverTarget.type === 'transition') ||
      (this.arcDrawing.sourceType === 'transition' && hoverTarget.type === 'place')
    );

    this.renderer.ctx.save();
    this.renderer.ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    this.renderer.ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    this.renderer.ctx.beginPath();
    this.renderer.ctx.moveTo(sourceElement.position.x, sourceElement.position.y);
    this.renderer.ctx.lineTo(x, y);
    this.renderer.ctx.strokeStyle = this.renderer.theme.arcPreviewColor;
    this.renderer.ctx.lineWidth = this.renderer.theme.arcPreviewLineWidth;
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
    this.renderer.ctx.fillStyle = this.renderer.theme.arcPreviewColor;
    this.renderer.ctx.fill();

    // Show a ghost preview of the element that would be created when dropping in empty space
    if (!isOverCompatible) {
      const ghostPos = { x, y };
      if (this.snapToGrid) {
        ghostPos.x = Math.round(x / this.gridSize) * this.gridSize;
        ghostPos.y = Math.round(y / this.gridSize) * this.gridSize;
      }
      if (this.arcDrawing.sourceType === 'place') {
        this.renderer.drawGhostTransition(ghostPos, true);
      } else {
        this.renderer.drawGhostPlace(ghostPos, true);
      }
    }

    this.renderer.ctx.restore();
  }

  /**
   * Find an element (place or transition) at the given world coordinates.
   * Returns { id, type } or null.
   */
  _findElementAt(x, y) {
    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id, place] of places) {
      const dx = place.position.x - x;
      const dy = place.position.y - y;
      if (Math.sqrt(dx * dx + dy * dy) <= place.radius) {
        return { id, type: 'place' };
      }
    }
    for (const [id, transition] of transitions) {
      const hw = transition.width / 2;
      const hh = transition.height / 2;
      if (x >= transition.position.x - hw && x <= transition.position.x + hw &&
          y >= transition.position.y - hh && y <= transition.position.y + hh) {
        return { id, type: 'transition' };
      }
    }
    return null;
  }

  completeArcDrawing(x, y) {
    if (!this.arcDrawing) return;


    let targetId = null;
    let targetType = null;


    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [id, place] of places) {
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
      for (const [id, transition] of transitions) {
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
        this.petriNet.recordArcInActiveView?.(arcId);
        this.selectedElement = { id: arcId, type: 'arc' };
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(arcId, 'arc');
        }
      }
    } else if (!targetId) {
      // Dropped in empty space — create the opposite element type and connect
      let snappedX = x;
      let snappedY = y;
      if (this.snapToGrid) {
        snappedX = Math.round(x / this.gridSize) * this.gridSize;
        snappedY = Math.round(y / this.gridSize) * this.gridSize;
      }

      let newElementId;
      let newElementType;
      if (this.arcDrawing.sourceType === 'place') {
        newElementId = this.generateUUID();
        newElementType = 'transition';
        const newTransition = new Transition(
          newElementId,
          { x: snappedX, y: snappedY },
          `T${this.petriNet.transitions.size + 1}`
        );
        this.petriNet.addTransition(newTransition);
        this.petriNet.recordElementInActiveView?.(newElementId);
      } else {
        newElementId = this.generateUUID();
        newElementType = 'place';
        const newPlace = new Place(
          newElementId,
          { x: snappedX, y: snappedY },
          `P${this.petriNet.places.size + 1}`
        );
        this.petriNet.addPlace(newPlace);
        this.petriNet.recordElementInActiveView?.(newElementId);
      }

      const arcId = this.generateUUID();
      const arc = new Arc(
        arcId,
        this.arcDrawing.sourceId,
        newElementId,
        1,
        "regular",
        [],
        ""
      );

      if (this.petriNet.addArc(arc)) {
        this.petriNet.recordArcInActiveView?.(arcId);
        this.selectedElement = { id: newElementId, type: newElementType };
        this.selectedElements.clear();
        this.selectedElements.set(this._selectionKey(newElementId, newElementType), {
          id: newElementId,
          type: newElementType
        });
        this.dragOffset = null;
        if (this.callbacks.onSelect) {
          this.callbacks.onSelect(newElementId, newElementType);
        }
      }
    }

    this.arcDrawing = null;
  }

  render(options = {}) {
    const { updateEnabled = true } = options;
    if (this.pendingRenderFrame !== null && updateEnabled) {
      const cancelFrame = window.cancelAnimationFrame || window.clearTimeout;
      cancelFrame(this.pendingRenderFrame);
      this.pendingRenderFrame = null;
      this.pendingRenderUpdatesEnabled = false;
      this.pendingAfterRender = null;
    }

    if (updateEnabled) {
      this.petriNet.updateEnabledTransitions();
    }
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

    // Draw the first ghost element (opposite of selected)
    if (this.ghostElement.type === 'place') {
      this.renderer.drawGhostPlace(this.ghostPosition, true);
    } else if (this.ghostElement.type === 'transition') {
      this.renderer.drawGhostTransition(this.ghostPosition, true);
    }

    // Draw the primary ghost arc (selected → ghost)
    const start = { x: selectedElementObj.position.x, y: selectedElementObj.position.y };
    const end = { x: this.ghostPosition.x, y: this.ghostPosition.y };
    this.renderer.drawGhostArc(start, end, true);

    // Draw the chained ghost arc to the closest fitting element (if any)
    if (this.ghostChain && this.ghostChain.length > 1) {
      const secondLink = this.ghostChain[1];
      if (secondLink.to && secondLink.to.position) {
        const chainStart = { x: this.ghostPosition.x, y: this.ghostPosition.y };
        const chainEnd = { x: secondLink.to.position.x, y: secondLink.to.position.y };

        // Draw a dashed ghost arc for the auto-connect
        this.renderer.ctx.save();
        this.renderer.ctx.setLineDash([6, 4]);
        this.renderer.ctx.globalAlpha = 0.35;
        this.renderer.drawGhostArc(chainStart, chainEnd, true);
        this.renderer.ctx.restore();

        // Highlight the target element with a subtle ring/outline
        if (!secondLink.to.isGhost) {
          this._renderAutoConnectHighlight(secondLink.to);
        }
      }
    }

    this.renderer.ctx.restore();
  }

  /**
   * Render a subtle highlight ring around the auto-connect target element.
   */
  _renderAutoConnectHighlight(target) {
    const ctx = this.renderer.ctx;
    ctx.save();
    ctx.globalAlpha = 0.4;
    ctx.strokeStyle = '#4CAF50';
    ctx.lineWidth = 2.5;
    ctx.setLineDash([5, 3]);

    if (target.type === 'place') {
      const place = this.petriNet.places.get(target.id);
      if (place) {
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 6, 0, Math.PI * 2);
        ctx.stroke();
      }
    } else if (target.type === 'transition') {
      const transition = this.petriNet.transitions.get(target.id);
      if (transition) {
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 6,
          transition.position.y - transition.height / 2 - 6,
          transition.width + 12,
          transition.height + 12
        );
        ctx.stroke();
      }
    }

    ctx.restore();
  }

  renderSelection() {
    if (!this.selectedElement && !this.boxSelection) return;

    const ctx = this.canvas.getContext('2d');
    

    ctx.save();
    ctx.translate(this.renderer.panOffset.x, this.renderer.panOffset.y);
    ctx.scale(this.renderer.zoomFactor, this.renderer.zoomFactor);

    if (this.boxSelection) {
      const bounds = this._normalizeBounds(this.boxSelection.start, this.boxSelection.current);
      ctx.save();
      ctx.setLineDash([6, 4]);
      ctx.fillStyle = this.renderer.theme.selectionFillColor;
      ctx.strokeStyle = this.renderer.theme.selectedColor;
      ctx.lineWidth = this.renderer.theme.selectionBoxLineWidth;
      ctx.fillRect(bounds.left, bounds.top, bounds.right - bounds.left, bounds.bottom - bounds.top);
      ctx.strokeRect(bounds.left, bounds.top, bounds.right - bounds.left, bounds.bottom - bounds.top);
      ctx.restore();
      ctx.restore();
      return;
    }

    if (this.selectedElements.size > 1) {
      this._renderMultiSelection(ctx);
      this._renderSelectionAutoConnectPreview(ctx);
    } else if (this.selectedElement.type === 'place') {
      const place = this.petriNet.places.get(this.selectedElement.id);
      if (place && this.petriNet.isElementVisibleInActiveView?.(this.selectedElement.id) !== false) {
        this._renderFusionSelectionAuras(ctx, place);
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 4, 0, Math.PI * 2);
        ctx.strokeStyle = this.renderer.theme.selectedColor;
        ctx.lineWidth = this.renderer.theme.selectionLineWidth;
        ctx.stroke();
      }
    } else if (this.selectedElement.type === 'transition') {
      const transition = this.petriNet.transitions.get(this.selectedElement.id);
      if (transition && this.petriNet.isElementVisibleInActiveView?.(this.selectedElement.id) !== false) {
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 4,
          transition.position.y - transition.height / 2 - 4,
          transition.width + 8,
          transition.height + 8
        );
        ctx.strokeStyle = this.renderer.theme.selectedColor;
        ctx.lineWidth = this.renderer.theme.selectionLineWidth;
        ctx.stroke();
      }
    } else if (this.selectedElement.type === 'arc') {
      const arc = this.petriNet.arcs.get(this.selectedElement.id);
      if (arc && this.petriNet.isArcVisibleInActiveView?.(arc) !== false) {
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
          ctx.lineWidth = this.renderer.theme.selectionArcLineWidth;
          ctx.stroke();
        }
      }
    }
    
    ctx.restore();
  }

  _renderFusionSelectionAuras(ctx, selectedPlace) {
    const fusionSet = this.petriNet.getFusionSetName?.(selectedPlace);
    if (!fusionSet) return;

    ctx.save();
    ctx.setLineDash([5, 4]);
    for (const member of this.petriNet.getFusionSetMembers(fusionSet)) {
      if (member.id === selectedPlace.id) continue;
      if (this.petriNet.isElementVisibleInActiveView?.(member.id) === false) continue;
      ctx.beginPath();
      ctx.arc(member.position.x, member.position.y, member.radius + 7, 0, Math.PI * 2);
      ctx.strokeStyle = '#B48EAD';
      ctx.lineWidth = this.renderer.theme.selectionLineWidth;
      ctx.stroke();
    }
    ctx.restore();
  }

  _renderMultiSelection(ctx) {
    const bounds = this._getSelectionBounds(this.selectedElements);
    ctx.strokeStyle = this.renderer.theme.selectedColor;
    ctx.lineWidth = this.renderer.theme.selectionLineWidth;

    for (const item of this.selectedElements.values()) {
      if (this.petriNet.isElementVisibleInActiveView?.(item.id) === false) continue;
      if (item.type === 'place') {
        const place = this.petriNet.places.get(item.id);
        if (!place) continue;
        ctx.beginPath();
        ctx.arc(place.position.x, place.position.y, place.radius + 4, 0, Math.PI * 2);
        ctx.stroke();
      } else if (item.type === 'transition') {
        const transition = this.petriNet.transitions.get(item.id);
        if (!transition) continue;
        ctx.beginPath();
        ctx.rect(
          transition.position.x - transition.width / 2 - 4,
          transition.position.y - transition.height / 2 - 4,
          transition.width + 8,
          transition.height + 8
        );
        ctx.stroke();
      }
    }

    if (bounds) {
      ctx.save();
      ctx.setLineDash([8, 5]);
      ctx.strokeStyle = this.renderer.theme.selectionBoundsColor;
      ctx.lineWidth = this.renderer.theme.selectionBoundsLineWidth;
      ctx.strokeRect(
        bounds.left - 12,
        bounds.top - 12,
        bounds.right - bounds.left + 24,
        bounds.bottom - bounds.top + 24
      );
      ctx.restore();
    }
  }

  _getSelectionBounds(selection) {
    let bounds = null;
    for (const item of selection.values()) {
      if (this.petriNet.isElementVisibleInActiveView?.(item.id) === false) continue;
      const element = this._getElementObject(item.id, item.type);
      if (!element) continue;
      const paddingX = item.type === 'place' ? element.radius : element.width / 2;
      const paddingY = item.type === 'place' ? element.radius : element.height / 2;
      const next = {
        left: element.position.x - paddingX,
        right: element.position.x + paddingX,
        top: element.position.y - paddingY,
        bottom: element.position.y + paddingY
      };
      if (!bounds) {
        bounds = next;
      } else {
        bounds.left = Math.min(bounds.left, next.left);
        bounds.right = Math.max(bounds.right, next.right);
        bounds.top = Math.min(bounds.top, next.top);
        bounds.bottom = Math.max(bounds.bottom, next.bottom);
      }
    }
    return bounds;
  }

  _renderSelectionAutoConnectPreview(ctx) {
    if (!this.autoConnectEnabled || !this.selectionDragState?.moved || this.selectedElements.size <= 1) {
      return;
    }

    const selectedIds = new Set(Array.from(this.selectedElements.values()).map(item => item.id));
    const links = this._getAutoConnectPreviewLinks(selectedIds);
    if (links.length === 0) return;

    ctx.save();
    ctx.setLineDash([6, 4]);
    ctx.globalAlpha = 0.4;
    for (const link of links) {
      this.renderer.drawGhostArc(link.from.position, link.to.position, true);
      this._renderAutoConnectHighlight(link.highlight);
    }
    ctx.restore();
  }

  _getAutoConnectPreviewLinks(selectedIds) {
    const boundary = this._getBoundaryNodes(selectedIds);
    const existingPairs = new Set(Array.from(this.petriNet.arcs.values()).map(arc => `${arc.source}->${arc.target}`));
    const connectedElementPairs = this._getArcElementPairKeys();
    const links = [];

    for (const id of boundary.starts) {
      const link = this._getBoundaryAutoConnectLink(id, 'incoming', selectedIds, existingPairs, connectedElementPairs);
      if (link) {
        links.push(link);
        existingPairs.add(`${link.from.id}->${link.to.id}`);
        connectedElementPairs.add(this._arcElementPairKey(link.from.id, link.to.id));
      }
    }

    for (const id of boundary.ends) {
      const link = this._getBoundaryAutoConnectLink(id, 'outgoing', selectedIds, existingPairs, connectedElementPairs);
      if (link) {
        links.push(link);
        existingPairs.add(`${link.from.id}->${link.to.id}`);
        connectedElementPairs.add(this._arcElementPairKey(link.from.id, link.to.id));
      }
    }

    return links;
  }

  _getBoundaryAutoConnectLink(id, direction, selectedIds, existingPairs, connectedElementPairs) {
    const node = this.petriNet.places.get(id) || this.petriNet.transitions.get(id);
    if (!node) return null;
    const nodeType = this.petriNet.places.has(id) ? 'place' : 'transition';
    const targetType = nodeType === 'place' ? 'transition' : 'place';
    const candidate = this._findClosestElement(node.position, targetType, id, selectedIds);
    if (!candidate || candidate.distance > this.autoConnectDistance) return null;

    const sourceId = direction === 'incoming' ? candidate.id : id;
    const targetId = direction === 'incoming' ? id : candidate.id;
    if (existingPairs.has(`${sourceId}->${targetId}`)) return null;
    if (connectedElementPairs.has(this._arcElementPairKey(sourceId, targetId))) return null;

    const source = direction === 'incoming'
      ? { ...candidate }
      : { id, type: nodeType, position: { x: node.position.x, y: node.position.y } };
    const target = direction === 'incoming'
      ? { id, type: nodeType, position: { x: node.position.x, y: node.position.y } }
      : { ...candidate };

    return { from: source, to: target, highlight: candidate };
  }


  setMode(mode) {
    this.mode = mode;
    this.arcDrawing = null;
    this.ghostElement = null;
    this.ghostPosition = null;
    this.ghostChain = null;
  }

  selectElement(id, type, options = {}) {
    const { silentRender = false, notify = true } = options;

    if (id && type) {
      this.selectedElement = { id, type };
      this.selectedElements.clear();
      if (type === 'place' || type === 'transition') {
        this.selectedElements.set(this._selectionKey(id, type), { id, type });
      }
      

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
      this.selectedElements.clear();
      this.dragOffset = null;
    }

    // Clear ghost state when selecting programmatically
    this.ghostElement = null;
    this.ghostPosition = null;
    this.ghostChain = null;

    if (!silentRender) {
      this.render();
    }

    if (notify && this.callbacks.onSelect) {
      this.callbacks.onSelect(id, type);
    }
  }

  deleteSelected() {
    if (!this.selectedElement) return false;

    if (this.selectedElements.size > 1 || this.selectedElement.type === 'selection') {
      const selectedIds = new Set(Array.from(this.selectedElements.values()).map(item => item.id));
      let success = false;
      for (const arcId of Array.from(this.petriNet.arcs.keys())) {
        const arc = this.petriNet.arcs.get(arcId);
        if (selectedIds.has(arc.source) || selectedIds.has(arc.target)) {
          success = this.petriNet.removeArc(arcId) || success;
        }
      }
      for (const item of Array.from(this.selectedElements.values())) {
        if (item.type === 'place') {
          success = this.petriNet.removePlace(item.id) || success;
        } else if (item.type === 'transition') {
          success = this.petriNet.removeTransition(item.id) || success;
        }
      }

      if (success) {
        this.clearSelection({ notify: true, render: false });
        this.render();
        if (this.callbacks.onChange) {
          this.callbacks.onChange();
        }
      }
      return success;
    }
    
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
      this.ghostChain = null;
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
    if (!this.petriNet.setPlaceTokens(id, tokens)) return false;
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
      this.renderer.setGridSize(gridSize);
    }
    this.render();
  }

  setGridVisibility(visible) {
    this.showGrid = visible;
    this.renderer.setGridVisibility(visible);
    this.render();
  }

  setAutoConnectSettings(enabled, distance) {
    this.autoConnectEnabled = enabled;
    if (distance !== undefined) {
      this.autoConnectDistance = distance;
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

  setPanSensitivity(sensitivity) {
    if (this.renderer) {
      this.panSensitivity = sensitivity;
      this.renderer.setPanSensitivity(sensitivity);
    }
  }

  setGridVisibility(visible) {
    if (this.renderer) {
      this.showGrid = visible;
      this.renderer.setGridVisibility(visible);
      this.render();
    }
  }

  setEditorColorInversion(enabled) {
    if (this.renderer) {
      this.renderer.setColorInversion(enabled);
      this.render();
    }
  }

  setAutoConnectSettings(enabled, distance) {
    this.autoConnectEnabled = enabled;
    if (distance !== undefined) {
      this.autoConnectDistance = distance;
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
    this.petriNet.recordElementInActiveView?.(id);
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
    this.petriNet.recordElementInActiveView?.(id);
    if (this.editor) this.editor.render();
    return id;
  }

  createArc(sourceId, targetId, weight = 1, type = "regular") {
    const id = this.generateUUID();
    const arc = new Arc(id, sourceId, targetId, weight, type);

    if (this.petriNet.addArc(arc)) {
      this.petriNet.recordArcInActiveView?.(id);
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
    if (!this.petriNet.setPlaceTokens(id, tokens)) return false;
    if (this.editor) this.editor.render();
    return true;
  }

  setPlaceFusionSet(id, fusionSet) {
    if (!this.petriNet.setPlaceFusionSet(id, fusionSet)) return false;
    if (this.editor) this.editor.render();
    return true;
  }

  getViews() {
    return this.petriNet.getViews();
  }

  getActiveView() {
    return this.petriNet.getActiveView();
  }

  switchView(viewId) {
    if (!this.editor || !this.petriNet.getView(viewId)) return false;
    this.petriNet.applyViewLayout(viewId, this.editor.renderer);
    this.editor.renderer.invalidateOverlayCache?.();
    this.editor.render();
    return true;
  }

  createView(name, elementIds = [], arcIds = [], options = {}) {
    const view = this.petriNet.createView(name, elementIds, arcIds, options);
    if (this.editor) {
      this.petriNet.applyViewLayout(view.id, this.editor.renderer);
      this.editor.clearSelection({ notify: true, render: false });
      this.editor.render();
    }
    return view;
  }

  createViewFromSelection(name = '') {
    if (!this.editor) return null;
    const selected = this.editor.selectedElements.size > 0
      ? Array.from(this.editor.selectedElements.values())
      : (this.editor.selectedElement && this.editor.selectedElement.type !== 'arc' && this.editor.selectedElement.type !== 'selection'
        ? [this.editor.selectedElement]
        : []);
    const elementIds = selected.map(item => item.id);
    if (elementIds.length === 0) return null;
    const arcIds = this.petriNet.getInternalArcIds(elementIds);
    return this.createView(name || `View ${this.petriNet.views.size}`, elementIds, arcIds);
  }

  createViewFromSelectedTransitions(name = '') {
    if (!this.editor) return null;
    const transitions = this.editor.selectedElements.size > 0
      ? Array.from(this.editor.selectedElements.values()).filter(item => item.type === 'transition').map(item => item.id)
      : (this.editor.selectedElement?.type === 'transition' ? [this.editor.selectedElement.id] : []);
    if (transitions.length === 0) return null;
    const neighborhood = this.petriNet.getTransitionNeighborhood(transitions);
    return this.createView(name || `Transition View ${this.petriNet.views.size}`, neighborhood.elementIds, neighborhood.arcIds);
  }

  addSelectionToActiveView() {
    if (!this.editor) return false;
    const selected = this.editor.selectedElements.size > 0
      ? Array.from(this.editor.selectedElements.values())
      : (this.editor.selectedElement && this.editor.selectedElement.type !== 'arc' && this.editor.selectedElement.type !== 'selection'
        ? [this.editor.selectedElement]
        : []);
    const elementIds = selected.map(item => item.id);
    if (elementIds.length === 0) return false;
    const arcIds = this.petriNet.getInternalArcIds(elementIds);
    const success = this.petriNet.addElementsToActiveView(elementIds, arcIds);
    if (success) this.editor.render();
    return success;
  }

  removeSelectionFromActiveView() {
    if (!this.editor || this.petriNet.isMainViewActive()) return false;
    const elementIds = [];
    const arcIds = [];

    if (this.editor.selectedElements.size > 0) {
      for (const item of this.editor.selectedElements.values()) {
        if (item.type === 'place' || item.type === 'transition') elementIds.push(item.id);
      }
    } else if (this.editor.selectedElement) {
      if (this.editor.selectedElement.type === 'place' || this.editor.selectedElement.type === 'transition') {
        elementIds.push(this.editor.selectedElement.id);
      } else if (this.editor.selectedElement.type === 'arc') {
        arcIds.push(this.editor.selectedElement.id);
      }
    }

    if (elementIds.length === 0 && arcIds.length === 0) return false;
    const success = this.petriNet.removeElementsFromActiveView(elementIds, arcIds);
    if (success) {
      this.editor.clearSelection({ notify: true, render: false });
      this.editor.render();
    }
    return success;
  }

  renameView(viewId, name) {
    const success = this.petriNet.renameView(viewId, name);
    if (success && this.editor) this.editor.render();
    return success;
  }

  deleteView(viewId) {
    const wasActive = this.petriNet.activeViewId === viewId;
    const success = this.petriNet.deleteView(viewId);
    if (success && this.editor) {
      if (wasActive) {
        this.petriNet.applyViewLayout(MAIN_VIEW_ID, this.editor.renderer);
      }
      this.editor.clearSelection({ notify: true, render: false });
      this.editor.render();
    }
    return success;
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
    const places = this.petriNet.getVisiblePlaces ? this.petriNet.getVisiblePlaces() : Array.from(this.petriNet.places);
    const transitions = this.petriNet.getVisibleTransitions ? this.petriNet.getVisibleTransitions() : Array.from(this.petriNet.transitions);
    for (const [, place] of places) {
      hasElements = true;
      minX = Math.min(minX, place.position.x - place.radius);
      minY = Math.min(minY, place.position.y - place.radius);
      maxX = Math.max(maxX, place.position.x + place.radius);
      maxY = Math.max(maxY, place.position.y + place.radius);
    }

    // Check transitions
    for (const [, transition] of transitions) {
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

      // Update enabled transitions for the current marking
      this.petriNet.updateEnabledTransitions();
      const enabledTransitions = [];

      for (const [id, transition] of this.petriNet.transitions) {
        if (transition.isEnabled) {
          enabledTransitions.push(id);
        }
      }

      // Fire all enabled transitions simultaneously (synchronous step semantics)
      if (enabledTransitions.length > 0) {
        firedAny = this.petriNet.fireTransitionsSynchronously(enabledTransitions);
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

  setPanSensitivity(sensitivity) {

    const validSensitivity = Math.max(0.25, Math.min(3, sensitivity));

    if (this.editor) {
      this.editor.setPanSensitivity(validSensitivity);
      return true;
    }
    return false;
  }

  setGridVisibility(visible) {
    if (this.editor) {
      this.editor.setGridVisibility(Boolean(visible));
      return true;
    }
    return false;
  }

  setEditorColorInversion(enabled) {
    if (this.editor) {
      this.editor.setEditorColorInversion(Boolean(enabled));
      return true;
    }
    return false;
  }

  setAutoConnectSettings(enabled, distance) {
    const validDistance = Math.max(50, Math.min(800, distance));

    if (this.editor) {
      this.editor.setAutoConnectSettings(Boolean(enabled), validDistance);
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

export {
  PetriNetAPI,
  PetriNetEditor,
  PetriNetRenderer,
  PetriNet,
  Place,
  Transition,
  Arc
};
