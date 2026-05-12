const OMEGA = 'w';

function placeLabel(place) {
  return place.label || place.id;
}

function transitionLabel(transition) {
  return transition.label || transition.id;
}

function escapeHtml(value) {
  return String(value)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#039;');
}

function getModel(net) {
  const places = Array.from(net.places.values());
  const transitions = Array.from(net.transitions.values());
  const arcs = Array.from(net.arcs.values());
  const placeIndex = new Map(places.map((place, index) => [place.id, index]));
  const incomingByTransition = new Map(transitions.map(transition => [transition.id, []]));
  const outgoingByTransition = new Map(transitions.map(transition => [transition.id, []]));

  for (const arc of arcs) {
    if (incomingByTransition.has(arc.target)) {
      incomingByTransition.get(arc.target).push(arc);
    }
    if (outgoingByTransition.has(arc.source)) {
      outgoingByTransition.get(arc.source).push(arc);
    }
  }

  return { places, transitions, arcs, placeIndex, incomingByTransition, outgoingByTransition };
}

function formatMarking(marking, places, compact = false) {
  return marking
    .map((tokens, index) => {
      const value = tokens === OMEGA ? 'ω' : tokens;
      return compact ? value : `${placeLabel(places[index])}: ${value}`;
    })
    .join(compact ? ', ' : '  ');
}

function markingKey(marking) {
  return marking.join('|');
}

function getIncoming(arcs, transitionId) {
  return arcs.filter(arc => arc.target === transitionId);
}

function getOutgoing(arcs, transitionId) {
  return arcs.filter(arc => arc.source === transitionId);
}

function isTransitionEnabled(marking, transitionId, model) {
  const incoming = model.incomingByTransition.get(transitionId) || [];

  for (const arc of incoming) {
    const placeIdx = model.placeIndex.get(arc.source);
    if (placeIdx === undefined) continue;

    const tokens = marking[placeIdx];
    if (arc.type === 'inhibitor') {
      if (tokens === OMEGA || tokens >= arc.weight) return false;
    } else if (arc.type === 'regular') {
      if (tokens !== OMEGA && tokens < arc.weight) return false;
    }
  }

  return true;
}

function fireTransition(marking, transitionId, model, useOmega = false) {
  const next = [...marking];
  const incoming = model.incomingByTransition.get(transitionId) || getIncoming(model.arcs, transitionId);
  const outgoing = model.outgoingByTransition.get(transitionId) || getOutgoing(model.arcs, transitionId);

  for (const arc of incoming) {
    const placeIdx = model.placeIndex.get(arc.source);
    if (placeIdx === undefined) continue;

    if (arc.type === 'regular' && next[placeIdx] !== OMEGA) {
      next[placeIdx] -= arc.weight;
    } else if (arc.type === 'reset') {
      next[placeIdx] = 0;
    }
  }

  for (const arc of outgoing) {
    const placeIdx = model.placeIndex.get(arc.target);
    if (placeIdx === undefined) continue;

    if (useOmega && next[placeIdx] === OMEGA) continue;
    next[placeIdx] += arc.weight;
  }

  return next;
}

function isLessOrEqualWithStrictGrowth(ancestor, marking) {
  let grew = false;

  for (let i = 0; i < ancestor.length; i += 1) {
    const a = ancestor[i];
    const m = marking[i];

    if (a === OMEGA) {
      if (m !== OMEGA) return false;
    } else if (m === OMEGA) {
      grew = true;
    } else {
      if (a > m) return false;
      if (a < m) grew = true;
    }
  }

  return grew;
}

function accelerate(marking, ancestors) {
  const next = [...marking];

  for (const ancestor of ancestors) {
    if (!isLessOrEqualWithStrictGrowth(ancestor, next)) continue;

    for (let i = 0; i < next.length; i += 1) {
      if (ancestor[i] !== OMEGA && next[i] !== OMEGA && next[i] > ancestor[i]) {
        next[i] = OMEGA;
      }
    }
  }

  return next;
}

function layoutGraph(nodes, edges) {
  const incoming = new Map(nodes.map(node => [node.id, 0]));
  const outgoing = new Map(nodes.map(node => [node.id, []]));

  for (const edge of edges) {
    incoming.set(edge.to, (incoming.get(edge.to) || 0) + 1);
    if (outgoing.has(edge.from)) outgoing.get(edge.from).push(edge.to);
  }

  const roots = nodes.filter(node => incoming.get(node.id) === 0);
  const queue = roots.length ? roots.map(node => node.id) : [nodes[0]?.id].filter(Boolean);
  const depth = new Map(queue.map(id => [id, 0]));

  while (queue.length) {
    const id = queue.shift();
    for (const child of outgoing.get(id) || []) {
      const nextDepth = (depth.get(id) || 0) + 1;
      if (!depth.has(child) || nextDepth < depth.get(child)) {
        depth.set(child, nextDepth);
        queue.push(child);
      }
    }
  }

  const layers = new Map();
  nodes.forEach((node, index) => {
    const layer = depth.get(node.id) ?? Math.floor(index / 6);
    if (!layers.has(layer)) layers.set(layer, []);
    layers.get(layer).push(node);
  });

  const positions = new Map();
  const sortedLayers = Array.from(layers.entries()).sort((a, b) => a[0] - b[0]);
  const maxLayerSize = Math.max(1, ...sortedLayers.map(([, layerNodes]) => layerNodes.length));
  const width = Math.max(760, maxLayerSize * 210 + 160);
  const height = Math.max(420, sortedLayers.length * 150 + 100);

  sortedLayers.forEach(([layerIndex, layerNodes]) => {
    const gap = width / (layerNodes.length + 1);
    layerNodes.forEach((node, index) => {
      positions.set(node.id, {
        x: gap * (index + 1),
        y: 70 + layerIndex * 150
      });
    });
  });

  return { positions, width, height };
}

function renderStateGraphSvg(analysis, options = {}) {
  const { title = 'State Space', tree = false } = options;
  const { nodes, edges, places } = analysis;

  if (!nodes.length) {
    return `<div class="analysis-empty">No states to render yet.</div>`;
  }

  const { positions, width, height } = layoutGraph(nodes, edges);
  const nodeRadius = tree ? 42 : 46;
  const showEdgeLabels = edges.length <= 120;
  const edgeMarkup = edges.map(edge => {
    const from = positions.get(edge.from);
    const to = positions.get(edge.to);
    if (!from || !to) return '';

    const dx = to.x - from.x;
    const dy = to.y - from.y;
    const distance = Math.hypot(dx, dy) || 1;
    const sx = from.x + (dx / distance) * nodeRadius;
    const sy = from.y + (dy / distance) * nodeRadius;
    const tx = to.x - (dx / distance) * nodeRadius;
    const ty = to.y - (dy / distance) * nodeRadius;
    const midY = (sy + ty) / 2 - (tree ? 8 : 24);

    return `
      <path class="analysis-edge" d="M ${sx} ${sy} C ${sx} ${midY}, ${tx} ${midY}, ${tx} ${ty}" />
      ${showEdgeLabels ? `<text class="analysis-edge-label" x="${(sx + tx) / 2}" y="${midY - 6}">${escapeHtml(edge.label)}</text>` : ''}
    `;
  }).join('');

  const nodeMarkup = nodes.map((node, index) => {
    const pos = positions.get(node.id);
    const label = formatMarking(node.marking, places, true);
    const stateClass = [
      'analysis-node',
      node.deadlock ? 'deadlock' : '',
      node.terminal ? 'terminal' : '',
      node.covered ? 'covered' : '',
      node.marking.includes(OMEGA) ? 'unbounded' : ''
    ].filter(Boolean).join(' ');

    return `
      <g class="${stateClass}" transform="translate(${pos.x} ${pos.y})">
        <circle r="${nodeRadius}"></circle>
        <text class="analysis-node-id" y="-9">${escapeHtml(node.name || `M${index}`)}</text>
        <text class="analysis-node-marking" y="13">${escapeHtml(label)}</text>
      </g>
    `;
  }).join('');

  return `
    <div class="analysis-canvas-shell">
      <svg class="analysis-svg" viewBox="0 0 ${width} ${height}" role="img" aria-label="${escapeHtml(title)}">
        <defs>
          <marker id="analysis-arrow" markerWidth="12" markerHeight="12" refX="9" refY="3" orient="auto" markerUnits="strokeWidth">
            <path d="M0,0 L0,6 L9,3 z" fill="#8FBCBB"/>
          </marker>
        </defs>
        ${edgeMarkup}
        ${nodeMarkup}
      </svg>
    </div>
  `;
}

function emptyAnalysis(net) {
  const model = getModel(net);
  return {
    places: model.places,
    nodes: [],
    edges: [],
    truncated: false,
    stats: { states: 0, edges: 0, deadlocks: 0 }
  };
}

export function analyzeReachabilityGraph(net, options = {}) {
  const maxNodes = options.maxNodes ?? 120;
  const tokenLimit = options.tokenLimit ?? 50;
  const model = getModel(net);
  if (!model.places.length) return emptyAnalysis(net);

  const initial = model.places.map(place => Number(place.tokens) || 0);
  const nodes = [{
    id: markingKey(initial),
    name: 'M0',
    marking: initial,
    deadlock: false
  }];
  const edges = [];
  const seen = new Map([[nodes[0].id, nodes[0]]]);
  const queue = [nodes[0]];
  let truncated = false;

  while (queue.length && nodes.length < maxNodes) {
    const node = queue.shift();
    const enabled = model.transitions.filter(transition => isTransitionEnabled(node.marking, transition.id, model));
    node.deadlock = enabled.length === 0;

    for (const transition of enabled) {
      const nextMarking = fireTransition(node.marking, transition.id, model, false);
      if (nextMarking.some(tokens => tokens > tokenLimit)) {
        truncated = true;
        continue;
      }

      const key = markingKey(nextMarking);
      if (!seen.has(key)) {
        if (nodes.length >= maxNodes) {
          truncated = true;
          break;
        }

        const nextNode = {
          id: key,
          name: `M${nodes.length}`,
          marking: nextMarking,
          deadlock: false
        };
        seen.set(key, nextNode);
        nodes.push(nextNode);
        queue.push(nextNode);
      }

      edges.push({
        from: node.id,
        to: key,
        label: transitionLabel(transition)
      });
    }
  }

  if (queue.length) truncated = true;

  return {
    places: model.places,
    nodes,
    edges,
    truncated,
    stats: {
      states: nodes.length,
      edges: edges.length,
      deadlocks: nodes.filter(node => node.deadlock).length
    }
  };
}

export function analyzeCoverabilityTree(net, options = {}) {
  const maxNodes = options.maxNodes ?? 160;
  const model = getModel(net);
  if (!model.places.length) return emptyAnalysis(net);

  const initial = model.places.map(place => Number(place.tokens) || 0);
  const root = {
    id: 'c0',
    name: 'C0',
    marking: initial,
    parentId: null,
    terminal: false,
    covered: false,
    ancestors: []
  };
  const nodes = [root];
  const edges = [];
  const queue = [root];
  let truncated = false;

  while (queue.length && nodes.length < maxNodes) {
    const node = queue.shift();
    const enabled = model.transitions.filter(transition => isTransitionEnabled(node.marking, transition.id, model));

    if (!enabled.length) {
      node.terminal = true;
      continue;
    }

    for (const transition of enabled) {
      const fired = fireTransition(node.marking, transition.id, model, true);
      const accelerated = accelerate(fired, [...node.ancestors, node.marking]);
      const ancestorHit = [...node.ancestors, node.marking].some(marking => markingKey(marking) === markingKey(accelerated));

      const child = {
        id: `c${nodes.length}`,
        name: `C${nodes.length}`,
        marking: accelerated,
        parentId: node.id,
        terminal: ancestorHit,
        covered: ancestorHit,
        ancestors: [...node.ancestors, node.marking]
      };

      nodes.push(child);
      edges.push({
        from: node.id,
        to: child.id,
        label: transitionLabel(transition)
      });

      if (!ancestorHit) queue.push(child);
      if (nodes.length >= maxNodes) {
        truncated = true;
        break;
      }
    }
  }

  if (queue.length) truncated = true;

  return {
    places: model.places,
    nodes,
    edges,
    truncated,
    stats: {
      states: nodes.length,
      edges: edges.length,
      unboundedPlaces: model.places.filter((_, index) => nodes.some(node => node.marking[index] === OMEGA)).length
    }
  };
}

function unique(array) {
  return Array.from(new Set(array));
}

function preset(transitionId, arcs) {
  return unique(arcs
    .filter(arc => arc.target === transitionId && arc.type === 'regular')
    .map(arc => arc.source))
    .sort();
}

function postset(transitionId, arcs) {
  return unique(arcs
    .filter(arc => arc.source === transitionId)
    .map(arc => arc.target))
    .sort();
}

function placeAdjacentTransitions(placeId, arcs, transitionIds) {
  return unique(arcs
    .filter(arc => (
      (arc.source === placeId && transitionIds.has(arc.target)) ||
      (arc.target === placeId && transitionIds.has(arc.source))
    ))
    .map(arc => arc.source === placeId ? arc.target : arc.source))
    .sort();
}

function hasPath(startId, targetId, adjacency) {
  const queue = [startId];
  const seen = new Set(queue);

  while (queue.length) {
    const id = queue.shift();
    if (id === targetId) return true;

    for (const next of adjacency.get(id) || []) {
      if (seen.has(next)) continue;
      seen.add(next);
      queue.push(next);
    }
  }

  return false;
}

function analyzeWorkflowNet(model, net) {
  const nodeIds = [
    ...model.places.map(place => place.id),
    ...model.transitions.map(transition => transition.id)
  ];
  const adjacency = new Map(nodeIds.map(id => [id, []]));
  const reverseAdjacency = new Map(nodeIds.map(id => [id, []]));

  for (const arc of model.arcs) {
    if (!adjacency.has(arc.source) || !reverseAdjacency.has(arc.target)) continue;
    adjacency.get(arc.source).push(arc.target);
    reverseAdjacency.get(arc.target).push(arc.source);
  }

  const sourcePlaces = model.places.filter(place => (reverseAdjacency.get(place.id) || []).length === 0);
  const sinkPlaces = model.places.filter(place => (adjacency.get(place.id) || []).length === 0);
  const issues = [];

  if (sourcePlaces.length !== 1) {
    issues.push(`Expected exactly one source place, found ${sourcePlaces.length}.`);
  }

  if (sinkPlaces.length !== 1) {
    issues.push(`Expected exactly one sink place, found ${sinkPlaces.length}.`);
  }

  if (sourcePlaces.length === 1 && sinkPlaces.length === 1) {
    const sourceId = sourcePlaces[0].id;
    const sinkId = sinkPlaces[0].id;
    const missingFromSource = nodeIds.filter(id => !hasPath(sourceId, id, adjacency));
    const missingToSink = nodeIds.filter(id => !hasPath(id, sinkId, adjacency));

    if (missingFromSource.length) {
      issues.push(`${missingFromSource.length} node(s) are not reachable from the source place.`);
    }

    if (missingToSink.length) {
      issues.push(`${missingToSink.length} node(s) cannot reach the sink place.`);
    }
  }

  return {
    isWorkflowNet: issues.length === 0 && model.places.length > 0 && net.transitions.size > 0,
    sourcePlace: sourcePlaces.length === 1 ? sourcePlaces[0] : null,
    sinkPlace: sinkPlaces.length === 1 ? sinkPlaces[0] : null,
    issues
  };
}

function addShortCircuitTransition(model, workflowNet) {
  if (!workflowNet.isWorkflowNet) {
    return {
      arcs: model.arcs,
      transitionIds: model.transitions.map(transition => transition.id),
      symbolicTransitionId: null
    };
  }

  const symbolicTransitionId = '__workflow_short_circuit_transition__';
  const arcs = [
    ...model.arcs,
    {
      id: '__workflow_short_circuit_in__',
      source: workflowNet.sinkPlace.id,
      target: symbolicTransitionId,
      weight: 1,
      type: 'regular',
      symbolic: true
    },
    {
      id: '__workflow_short_circuit_out__',
      source: symbolicTransitionId,
      target: workflowNet.sourcePlace.id,
      weight: 1,
      type: 'regular',
      symbolic: true
    }
  ];

  return {
    arcs,
    transitionIds: [...model.transitions.map(transition => transition.id), symbolicTransitionId],
    symbolicTransitionId
  };
}

function componentKey(placeIds, transitionIds) {
  return `${[...placeIds].sort().join('|')}::${[...transitionIds].sort().join('|')}`;
}

function normalizeSComponent(placeIds, transitionIds, symbolicTransitionId) {
  const realTransitionIds = transitionIds.filter(id => id !== symbolicTransitionId).sort();

  return {
    placeIds: placeIds.sort(),
    transitionIds: realTransitionIds,
    usesShortCircuit: transitionIds.includes(symbolicTransitionId),
    isSComponent: realTransitionIds.length > 0 && placeIds.length > 0
  };
}

function isStronglyConnectedSubnet(placeIds, transitionIds, arcs) {
  const nodeIds = [...placeIds, ...transitionIds];
  if (!nodeIds.length) return false;

  const nodeSet = new Set(nodeIds);
  const adjacency = new Map(nodeIds.map(id => [id, []]));

  for (const arc of arcs) {
    if (!nodeSet.has(arc.source) || !nodeSet.has(arc.target)) continue;
    adjacency.get(arc.source).push(arc.target);
  }

  return nodeIds.every(from => nodeIds.every(to => hasPath(from, to, adjacency)));
}

function expandStateMachineComponents(initialPlaceIds, model, regularArcs, transitionIds, symbolicTransitionId) {
  const components = [];
  const seenStates = new Set();
  const transitionSet = new Set(transitionIds);
  const placeSet = new Set(model.places.map(place => place.id));

  function stateKey(placeIds) {
    return [...placeIds].sort().join('|');
  }

  function closePlacesOverTransitions(placeIds) {
    const closedTransitionIds = new Set();

    for (const placeId of placeIds) {
      for (const transitionId of placeAdjacentTransitions(placeId, regularArcs, transitionSet)) {
        closedTransitionIds.add(transitionId);
      }
    }

    return closedTransitionIds;
  }

  function visit(placeIds) {
    const key = stateKey(placeIds);
    if (seenStates.has(key)) return;
    seenStates.add(key);

    const closedTransitionIds = closePlacesOverTransitions(placeIds);
    const missingPlaceChoices = [];

    for (const transitionId of closedTransitionIds) {
      const inputPlaces = preset(transitionId, regularArcs).filter(id => placeSet.has(id));
      const outputPlaces = postset(transitionId, regularArcs).filter(id => placeSet.has(id));
      const selectedInputs = inputPlaces.filter(id => placeIds.has(id));
      const selectedOutputs = outputPlaces.filter(id => placeIds.has(id));

      if (selectedInputs.length > 1 || selectedOutputs.length > 1) return;
      if (!selectedInputs.length) {
        if (!inputPlaces.length) return;
        missingPlaceChoices.push(inputPlaces);
      }
      if (!selectedOutputs.length) {
        if (!outputPlaces.length) return;
        missingPlaceChoices.push(outputPlaces);
      }
    }

    if (missingPlaceChoices.length) {
      const nextChoices = missingPlaceChoices[0].filter(placeId => !placeIds.has(placeId));
      for (const placeId of nextChoices) {
        visit(new Set([...placeIds, placeId]));
      }
      return;
    }

    const placeList = [...placeIds].sort();
    const transitionList = [...closedTransitionIds].sort();
    if (!isStronglyConnectedSubnet(placeList, transitionList, regularArcs)) return;

    const component = normalizeSComponent(placeList, transitionList, symbolicTransitionId);
    if (component.isSComponent) components.push(component);
  }

  visit(new Set(initialPlaceIds));
  return components;
}

function findStateMachineCycles(model, arcs, transitionIds, symbolicTransitionId) {
  const regularArcs = arcs.filter(arc => arc.type === 'regular');
  const transitionEdges = [];

  for (const transitionId of transitionIds) {
    const inputPlaces = preset(transitionId, regularArcs);
    const outputPlaces = postset(transitionId, regularArcs);

    for (const inputPlaceId of inputPlaces) {
      for (const outputPlaceId of outputPlaces) {
        if (!model.placeIndex.has(inputPlaceId) || !model.placeIndex.has(outputPlaceId)) continue;
        transitionEdges.push({ from: inputPlaceId, to: outputPlaceId, transitionId });
      }
    }
  }

  const edgesByPlace = new Map(model.places.map(place => [place.id, []]));
  for (const edge of transitionEdges) {
    edgesByPlace.get(edge.from)?.push(edge);
  }

  const components = [];
  const seen = new Set();
  const maxDepth = Math.max(1, model.places.length);

  function addComponent(placePath) {
    const placeIds = unique(placePath);

    for (const component of expandStateMachineComponents(
      placeIds,
      model,
      regularArcs,
      transitionIds,
      symbolicTransitionId
    )) {
      const key = componentKey(component.placeIds, [
        ...component.transitionIds,
        ...(component.usesShortCircuit ? [symbolicTransitionId] : [])
      ]);
      if (seen.has(key)) continue;

      seen.add(key);
      components.push(component);
    }
  }

  function visit(startPlaceId, currentPlaceId, placePath, usedTransitions) {
    if (placePath.length > maxDepth + 1) return;

    for (const edge of edgesByPlace.get(currentPlaceId) || []) {
      if (usedTransitions.has(edge.transitionId)) continue;

      if (edge.to === startPlaceId) {
        addComponent(placePath);
        continue;
      }

      if (placePath.includes(edge.to)) continue;

      visit(
        startPlaceId,
        edge.to,
        [...placePath, edge.to],
        new Set([...usedTransitions, edge.transitionId])
      );
    }
  }

  for (const place of model.places) {
    visit(place.id, place.id, [place.id], new Set());
  }

  return components.sort((a, b) => {
    if (a.usesShortCircuit !== b.usesShortCircuit) return a.usesShortCircuit ? -1 : 1;
    if (b.placeIds.length !== a.placeIds.length) return b.placeIds.length - a.placeIds.length;
    return a.placeIds.join('|').localeCompare(b.placeIds.join('|'));
  });
}

export function analyzeStructuralProperties(net) {
  const model = getModel(net);
  const workflowNet = analyzeWorkflowNet(model, net);
  const shortCircuited = addShortCircuitTransition(model, workflowNet);
  const components = findStateMachineCycles(
    model,
    shortCircuited.arcs,
    shortCircuited.transitionIds,
    shortCircuited.symbolicTransitionId
  );

  const coveredPlaces = new Set(components.flatMap(component => component.placeIds));
  const uncoveredPlaces = model.places.filter(place => !coveredPlaces.has(place.id));

  const freeChoiceViolations = [];
  for (const place of model.places) {
    const outgoingTransitions = model.arcs
      .filter(arc => arc.source === place.id && net.transitions.has(arc.target))
      .map(arc => arc.target);

    if (outgoingTransitions.length <= 1) continue;

    const presets = outgoingTransitions.map(transitionId => ({
      transitionId,
      inputs: preset(transitionId, model.arcs)
    }));

    for (const entry of presets) {
      if (entry.inputs.length !== 1 || entry.inputs[0] !== place.id) {
        freeChoiceViolations.push({
          placeId: place.id,
          transitionId: entry.transitionId,
          inputs: entry.inputs
        });
      }
    }
  }

  return {
    places: model.places,
    transitions: model.transitions,
    arcs: model.arcs,
    sComponents: components,
    coveredPlaces: Array.from(coveredPlaces),
    uncoveredPlaces,
    isSCoverable: model.places.length > 0 && uncoveredPlaces.length === 0,
    isWorkflowNet: workflowNet.isWorkflowNet,
    workflowNetIssues: workflowNet.issues,
    workflowSourcePlace: workflowNet.sourcePlace,
    workflowSinkPlace: workflowNet.sinkPlace,
    shortCircuitTransitionId: shortCircuited.symbolicTransitionId,
    isFreeChoice: freeChoiceViolations.length === 0,
    freeChoiceViolations
  };
}

export function renderStructuralSvg(analysis) {
  const places = analysis.places;
  const transitions = analysis.transitions;
  const width = Math.max(820, Math.max(places.length, transitions.length) * 135 + 120);
  const height = 520;
  const placeY = 120;
  const transitionY = 340;
  const covered = new Set(analysis.coveredPlaces);
  const componentColors = ['#88C0D0', '#A3BE8C', '#B48EAD', '#EBCB8B', '#D08770'];
  const componentByNode = new Map();

  analysis.sComponents.forEach((component, index) => {
    const color = componentColors[index % componentColors.length];
    [...component.placeIds, ...component.transitionIds].forEach(id => componentByNode.set(id, color));
  });

  const placePositions = new Map();
  const transitionPositions = new Map();
  const placeGap = width / (places.length + 1 || 2);
  const transitionGap = width / (transitions.length + 1 || 2);

  places.forEach((place, index) => placePositions.set(place.id, { x: placeGap * (index + 1), y: placeY }));
  transitions.forEach((transition, index) => transitionPositions.set(transition.id, { x: transitionGap * (index + 1), y: transitionY }));

  const arcMarkup = analysis.arcs.map(arc => {
    const from = placePositions.get(arc.source) || transitionPositions.get(arc.source);
    const to = placePositions.get(arc.target) || transitionPositions.get(arc.target);
    if (!from || !to) return '';
    const midY = (from.y + to.y) / 2;

    return `
      <path class="analysis-edge structural-edge" d="M ${from.x} ${from.y} C ${from.x} ${midY}, ${to.x} ${midY}, ${to.x} ${to.y}" />
    `;
  }).join('');

  const placeMarkup = places.map(place => {
    const pos = placePositions.get(place.id);
    const color = componentByNode.get(place.id) || (covered.has(place.id) ? '#8FBCBB' : '#BF616A');
    const className = covered.has(place.id) ? 'structural-place covered' : 'structural-place uncovered';
    return `
      <g class="${className}" transform="translate(${pos.x} ${pos.y})">
        <circle r="38" style="--component-color:${color}"></circle>
        <text y="5">${escapeHtml(placeLabel(place))}</text>
      </g>
    `;
  }).join('');

  const transitionMarkup = transitions.map(transition => {
    const pos = transitionPositions.get(transition.id);
    const color = componentByNode.get(transition.id) || '#81A1C1';
    const violation = analysis.freeChoiceViolations.some(item => item.transitionId === transition.id);
    return `
      <g class="structural-transition ${violation ? 'violation' : ''}" transform="translate(${pos.x} ${pos.y})">
        <rect x="-24" y="-42" width="48" height="84" rx="7" style="--component-color:${color}"></rect>
        <text y="60">${escapeHtml(transitionLabel(transition))}</text>
      </g>
    `;
  }).join('');

  return `
    <div class="analysis-canvas-shell structural-shell">
      <svg class="analysis-svg structural-svg" viewBox="0 0 ${width} ${height}" role="img" aria-label="Structural Petri net analysis">
        <defs>
          <marker id="structural-arrow" markerWidth="12" markerHeight="12" refX="9" refY="3" orient="auto" markerUnits="strokeWidth">
            <path d="M0,0 L0,6 L9,3 z" fill="#8FBCBB"/>
          </marker>
        </defs>
        ${arcMarkup}
        ${placeMarkup}
        ${transitionMarkup}
      </svg>
    </div>
  `;
}

export function renderStateSpaceSvg(analysis, options = {}) {
  return renderStateGraphSvg(analysis, options);
}

export function formatAnalysisMarking(marking, places) {
  return formatMarking(marking, places);
}
