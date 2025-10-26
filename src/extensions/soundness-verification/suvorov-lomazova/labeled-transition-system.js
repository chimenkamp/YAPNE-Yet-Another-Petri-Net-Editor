/**
 * Labeled Transition System implementation for DPN analysis
 */
class LabeledTransitionSystem {
  constructor() {
    this.nodes = new Map(); // (markingId, formulaId) -> {marking, formula, id}
    this.edges = new Map(); // edgeId -> {source, target, transition}
    this.nodeCounter = 0;
    this.edgeCounter = 0;
  }

  addNode(marking, formula) {
    const nodeId = `node_${this.nodeCounter++}`;
    const node = {
      id: nodeId,
      marking: marking,
      formula: formula,
      outgoingEdges: [],
      incomingEdges: [],
    };
    this.nodes.set(nodeId, node);
    return nodeId;
  }

  addEdge(sourceId, targetId, transition) {
    const edgeId = `edge_${this.edgeCounter++}`;
    const edge = {
      id: edgeId,
      source: sourceId,
      target: targetId,
      transition: transition,
    };
    this.edges.set(edgeId, edge);

    // Update node references
    if (this.nodes.has(sourceId)) {
      this.nodes.get(sourceId).outgoingEdges.push(edgeId);
    }
    if (this.nodes.has(targetId)) {
      this.nodes.get(targetId).incomingEdges.push(edgeId);
    }

    return edgeId;
  }

  findStronglyConnectedComponents() {
    // Tarjan's algorithm for SCC detection
    const indices = new Map();
    const lowLinks = new Map();
    const onStack = new Set();
    const stack = [];
    let index = 0;
    const sccs = [];

    const strongConnect = (nodeId) => {
      indices.set(nodeId, index);
      lowLinks.set(nodeId, index);
      index++;
      stack.push(nodeId);
      onStack.add(nodeId);

      const node = this.nodes.get(nodeId);
      for (const edgeId of node.outgoingEdges) {
        const edge = this.edges.get(edgeId);
        const targetId = edge.target;

        if (!indices.has(targetId)) {
          strongConnect(targetId);
          lowLinks.set(
            nodeId,
            Math.min(lowLinks.get(nodeId), lowLinks.get(targetId))
          );
        } else if (onStack.has(targetId)) {
          lowLinks.set(
            nodeId,
            Math.min(lowLinks.get(nodeId), indices.get(targetId))
          );
        }
      }

      if (lowLinks.get(nodeId) === indices.get(nodeId)) {
        const scc = [];
        let w;
        do {
          w = stack.pop();
          onStack.delete(w);
          scc.push(w);
        } while (w !== nodeId);
        sccs.push(scc);
      }
    };

    for (const nodeId of this.nodes.keys()) {
      if (!indices.has(nodeId)) {
        strongConnect(nodeId);
      }
    }

    return sccs;
  }

  /**
   * Find a maximal set of node-disjoint elementary cycles (paper-aligned).
   * Strategy:
   * 1) Compute SCCs (only SCCs with ≥2 nodes or a self-loop can contain cycles).
   * 2) For each such SCC, enumerate elementary cycles using Johnson’s algorithm
   * restricted to the SCC’s subgraph (to avoid duplicates and reduce cost).
   * 3) From all discovered cycles, select a maximal disjoint subset by greedy
   * choice (longest-first), as required by the refinement step.
   * 4) For each selected cycle, compute:
   * - transitions: IDs of LTS edges whose source and target are both in the cycle
   * - exitTransitions: IDs of LTS edges that leave the cycle’s node set
   *
   * @returns {Array<{ nodes: string[], transitions: Set<string>, exitTransitions: Set<string> }>}
   */
  findMaximalDisjointCycles() {
    // --- Build adjacency lists once ---
    const adj = new Map(); // nodeId -> nodeId[]
    const selfLoop = new Set(); // nodes with an explicit self-loop edge

    for (const [nid, node] of this.nodes) {
      const outs = [];
      for (const eid of node.outgoingEdges || []) {
        const e = this.edges.get(eid);
        if (!e) continue;
        outs.push(e.target);
        if (e.target === nid) selfLoop.add(nid);
      }
      adj.set(nid, outs);
    }

    // --- Helper: subgraph induced by a set of nodes ---
    const inducedAdj = (nodeSet) => {
      const sub = new Map();
      for (const n of nodeSet) {
        const outs = (adj.get(n) || []).filter((t) => nodeSet.has(t));
        sub.set(n, outs);
      }
      return sub;
    };

    // --- Johnson’s algorithm for elementary cycles on a directed graph (restricted to subgraph) ---
    const elementaryCycles = (subNodesSet) => {
      const nodesArr = Array.from(subNodesSet);
      // Sort for stable iteration order
      nodesArr.sort((a, b) => String(a).localeCompare(String(b)));

      const subAdj0 = inducedAdj(subNodesSet);

      const unblock = (u, blocked, B) => {
        if (!blocked.has(u)) return;
        blocked.delete(u);
        const Bu = B.get(u) || new Set();
        B.set(u, new Set());
        for (const w of Bu) unblock(w, blocked, B);
      };

      const cycles = [];
      const stack = [];

      // We follow the original scheme: for each start index s, work on the
      // subgraph induced by nodes >= s (by position in nodesArr).
      for (let sIdx = 0; sIdx < nodesArr.length; sIdx++) {
        const start = nodesArr[sIdx];
        const allowed = new Set(nodesArr.slice(sIdx));
        const subAdj = inducedAdj(allowed);

        const blocked = new Set();
        const B = new Map();
        for (const v of allowed) B.set(v, new Set());
        stack.length = 0;

        const circuit = (v, startV) => {
          let foundCycle = false;
          stack.push(v);
          blocked.add(v);

          for (const w of subAdj.get(v) || []) {
            if (w === startV) {
              // Found an elementary cycle (copy stack)
              cycles.push([...stack]);
              foundCycle = true;
            } else if (!blocked.has(w)) {
              if (circuit(w, startV)) foundCycle = true;
            }
          }

          if (foundCycle) {
            unblock(v, blocked, B);
          } else {
            for (const w of subAdj.get(v) || []) {
              const Bw = B.get(w);
              if (Bw) Bw.add(v);
            }
          }

          stack.pop();
          return foundCycle;
        };

        circuit(start, start);
      }

      // Deduplicate cycles up to rotation (normalize by lexicographically minimal rotation)
      const normKey = (cyc) => {
        const m = cyc.length;
        let best = null;
        for (let i = 0; i < m; i++) {
          const rot = [...cyc.slice(i), ...cyc.slice(0, i)];
          const key = rot.join("->");
          if (best === null || key < best) best = key;
        }
        return best;
      };
      const seen = new Set();
      const uniq = [];
      for (const c of cycles) {
        if (c.length === 1) {
          // keep single-node cycle only if explicit self-loop exists
          if (!selfLoop.has(c[0])) continue;
        }
        const k = normKey(c);
        if (!seen.has(k)) {
          seen.add(k);
          uniq.push(c);
        }
      }
      return uniq;
    };

    // --- Find SCCs and enumerate cycles per SCC ---
    const sccs = this.findStronglyConnectedComponents();
    const allCycles = [];
    for (const comp of sccs) {
      if (comp.length > 1) {
        for (const cyc of elementaryCycles(new Set(comp))) {
          allCycles.push(cyc);
        }
      } else if (comp.length === 1 && selfLoop.has(comp[0])) {
        // Single-node SCC with a self-loop is a valid cycle
        allCycles.push([comp[0]]);
      }
    }

    if (allCycles.length === 0) return [];

    // --- Select a maximal disjoint subset (greedy, longest-first) ---
    allCycles.sort(
      (a, b) => b.length - a.length || a.join().localeCompare(b.join())
    );
    const used = new Set();
    const selected = [];

    const disjointWithUsed = (cycle) => cycle.every((n) => !used.has(n));

    for (const cyc of allCycles) {
      if (!disjointWithUsed(cyc)) continue;
      selected.push(cyc);
      for (const n of cyc) used.add(n);
    }

    // --- Build cycle descriptors with transitions and exitTransitions ---
    const result = [];
    for (const cyc of selected) {
      const nodeSet = new Set(cyc);
      const transitions = new Set();
      const exitTransitions = new Set();

      // Collect transitions on edges inside the cycle, and exits leaving it
      for (const nid of cyc) {
        const node = this.nodes.get(nid);
        if (!node) continue;
        for (const eid of node.outgoingEdges || []) {
          const e = this.edges.get(eid);
          if (!e) continue;
          if (nodeSet.has(e.target)) {
            transitions.add(String(e.transition));
          } else {
            exitTransitions.add(String(e.transition));
          }
        }
      }

      result.push({
        nodes: [...nodeSet],
        transitions,
        exitTransitions,
      });
    }

    return result;
  }

  /**
   * Performs a forward BFS/DFS to find all nodes reachable from a start node.
   * @param {string} startNodeId The ID of the node to start the search from.
   * @param {Map<string, {prev: string|null, via: string|null}>} [parentMap] Optional map to store parent pointers for trace reconstruction.
   * @returns {string[]} An array of reachable node IDs.
   */
  getReachableNodes(startNodeId, parentMap = null) {
    const visited = new Set();
    const queue = [startNodeId];

    if (!this.nodes.has(startNodeId)) return [];

    visited.add(startNodeId);
    if (parentMap) {
        parentMap.set(startNodeId, { prev: null, via: null });
    }

    let head = 0;
    while (head < queue.length) {
      const nodeId = queue[head++];
      const node = this.nodes.get(nodeId);

      for (const edgeId of node.outgoingEdges) {
        const edge = this.edges.get(edgeId);
        if (edge && !visited.has(edge.target)) {
          visited.add(edge.target);
          if (parentMap) {
              parentMap.set(edge.target, { prev: nodeId, via: edgeId });
          }
          queue.push(edge.target);
        }
      }
    }

    return Array.from(visited);
  }

  /**
   * Performs a backward BFS/DFS to find all nodes that can reach a set of target nodes.
   * @param {string[]} targetNodeIds An array of IDs for the target nodes.
   * @returns {string[]} An array of node IDs that have a path to at least one target node.
   */
  getNodesThatCanReach(targetNodeIds) {
    const canReach = new Set(targetNodeIds);
    const queue = [...targetNodeIds];

    let head = 0;
    while (head < queue.length) {
        const nodeId = queue[head++];
        if (!this.nodes.has(nodeId)) continue;

        const node = this.nodes.get(nodeId);
        for (const edgeId of node.incomingEdges) {
            const edge = this.edges.get(edgeId);
            if (edge && !canReach.has(edge.source)) {
                canReach.add(edge.source);
                queue.push(edge.source);
            }
        }
    }
    return Array.from(canReach);
  }

    /**
   * Pretty-print the labeled transition system as multiline string.
   *
   * The format is:
   *
   * LTS:
   *   Nodes:
   *     node_0:
   *       marking: <...>
   *       formula: <...>
   *       out:
   *         edge_0 --[ <transition> ]--> node_1
   *         ...
   *       in:
   *         edge_5 --[ <transition> ]-- node_2
   *         ...
   *   Edges:
   *     edge_0: node_0 --[ <transition> ]--> node_1
   *     edge_1: node_1 --[ <transition> ]--> node_2
   *     ...
   *
   * @returns {string} A human-readable string representation of the full LTS.
   */
  toString() {
    const lines = [];

    lines.push("LTS:");
    lines.push("  Nodes:");

    for (const [nodeId, node] of this.nodes.entries()) {
      lines.push(`    ${nodeId}:`);
      lines.push(`      marking: ${JSON.stringify(node.marking)}`);
      lines.push(`      formula: ${JSON.stringify(node.formula)}`);

      lines.push("      out:");
      if (node.outgoingEdges.length === 0) {
        lines.push("        <none>");
      } else {
        for (const edgeId of node.outgoingEdges) {
          const e = this.edges.get(edgeId);
          if (!e) continue;
          lines.push(
            `        ${edgeId} --[ ${JSON.stringify(
              e.transition
            )} ]--> ${e.target}`
          );
        }
      }

      lines.push("      in:");
      if (node.incomingEdges.length === 0) {
        lines.push("        <none>");
      } else {
        for (const edgeId of node.incomingEdges) {
          const e = this.edges.get(edgeId);
          if (!e) continue;
          lines.push(
            `        ${edgeId} --[ ${JSON.stringify(
              e.transition
            )} ]-- ${e.source}`
          );
        }
      }
    }

    lines.push("  Edges:");
    if (this.edges.size === 0) {
      lines.push("    <none>");
    } else {
      for (const [edgeId, e] of this.edges.entries()) {
        lines.push(
          `    ${edgeId}: ${e.source} --[ ${JSON.stringify(
            e.transition
          )} ]--> ${e.target}`
        );
      }
    }

    return lines.join("\n");
  }
}

export { LabeledTransitionSystem };