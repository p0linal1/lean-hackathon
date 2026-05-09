(() => {
  function solve(state, options = {}) {
    const nodes = state?.board?.nodes ?? [];
    const dominoes = state?.dominoes ?? [];
    const constraints = state?.constraints ?? [];

    if (!nodes.length) throw new Error("No board nodes detected");
    if (!dominoes.length) throw new Error("No dominoes detected");

    const graph = buildSolverGraph(nodes, constraints);
    const remainingDominoes = dominoes.map((domino, index) => ({ domino, index }));
    const deadline = solverDeadline(options.timeoutMs);
    const result = search(graph, remainingDominoes, new Map(), [], new Set(), deadline);
    if (!result) throw new Error("No solution found");
    return result;
  }

  function solverDeadline(timeoutMs) {
    return Number.isFinite(timeoutMs) && timeoutMs > 0 ? performance.now() + timeoutMs : null;
  }

  function checkDeadline(deadline) {
    if (deadline !== null && performance.now() > deadline) {
      throw new Error("Timed out after 10 seconds");
    }
  }

  function buildSolverGraph(nodes, constraints) {
    const nodeById = new Map(nodes.map((node) => [node.id, node]));
    const neighborsByNode = new Map();

    for (const node of nodes) {
      const neighbors = ["left", "right", "up", "down"]
        .map((direction) => node[direction])
        .filter((id) => id && nodeById.has(id));
      neighborsByNode.set(node.id, neighbors);
    }

    return {
      nodes,
      nodeById,
      neighborsByNode,
      constraints
    };
  }

  function orientations(domino) {
    const first = { top: domino.top, bottom: domino.bottom };
    const second = { top: domino.bottom, bottom: domino.top };
    return domino.top === domino.bottom ? [first] : [first, second];
  }

  function search(graph, remainingDominoes, valuesByNode, placements, usedNodes, deadline) {
    checkDeadline(deadline);

    const propagated = propagateState(
      graph,
      remainingDominoes,
      new Map(valuesByNode),
      [...placements],
      new Set(usedNodes),
      deadline
    );
    if (!propagated) return null;

    if (!propagated.remainingDominoes.length) {
      return propagated.usedNodes.size === graph.nodes.length && constraintsSatisfied(graph.constraints, propagated.valuesByNode)
        ? { placements: propagated.placements, valuesByNode: Object.fromEntries(propagated.valuesByNode) }
        : null;
    }

    const candidates = nextPlacementCandidates(
      graph,
      propagated.remainingDominoes,
      propagated.valuesByNode,
      propagated.usedNodes
    );
    if (!candidates.length) return null;

    for (const { placement, nextDominoes } of candidates) {
      applyPlacement(placement, propagated.valuesByNode, propagated.usedNodes);

      if (!hasDeadEnd(graph, propagated.usedNodes)) {
        const result = search(
          graph,
          nextDominoes,
          propagated.valuesByNode,
          [...propagated.placements, placement],
          propagated.usedNodes,
          deadline
        );
        if (result) return result;
      }

      undoPlacement(placement, propagated.valuesByNode, propagated.usedNodes);
    }

    return null;
  }

  function withoutIndex(items, index) {
    return items.slice(0, index).concat(items.slice(index + 1));
  }

  function propagateState(graph, remainingDominoes, valuesByNode, placements, usedNodes, deadline) {
    let remaining = remainingDominoes;

    while (true) {
      checkDeadline(deadline);
      const domains = candidateDomains(graph, remaining, valuesByNode, usedNodes);
      if (!domains) return null;

      const forced = firstForcedPlacement(domains);
      if (!forced) {
        return {
          remainingDominoes: remaining,
          valuesByNode,
          placements,
          usedNodes
        };
      }

      applyPlacement(forced.placement, valuesByNode, usedNodes);
      placements.push(forced.placement);
      remaining = withoutIndex(remaining, forced.dominoPosition);

      if (
        hasDeadEnd(graph, usedNodes) ||
        !constraintsStillPossible(graph.constraints, valuesByNode, remaining)
      ) {
        return null;
      }
    }
  }

  function candidateDomains(graph, remainingDominoes, valuesByNode, usedNodes) {
    const byNode = new Map(graph.nodes
      .filter((node) => !usedNodes.has(node.id))
      .map((node) => [node.id, []]));
    const byDomino = new Map(remainingDominoes.map((entry) => [entry.index, []]));
    const all = [];
    const seenEdges = new Set();

    for (const node of graph.nodes) {
      if (usedNodes.has(node.id)) continue;

      for (const neighborId of emptyNeighborIds(graph, node.id, usedNodes)) {
        const edgeKey = [node.id, neighborId].sort().join("|");
        if (seenEdges.has(edgeKey)) continue;
        seenEdges.add(edgeKey);

        for (let dominoPosition = 0; dominoPosition < remainingDominoes.length; dominoPosition += 1) {
          const entry = remainingDominoes[dominoPosition];
          const nextDominoes = withoutIndex(remainingDominoes, dominoPosition);

          for (const orientation of orientations(entry.domino)) {
            const placement = {
              domino: entry.domino,
              topNode: node.id,
              bottomNode: neighborId,
              values: {
                [node.id]: orientation.top,
                [neighborId]: orientation.bottom
              }
            };

            if (!placeIsStillPossible(graph, placement, valuesByNode, usedNodes, nextDominoes)) continue;

            const candidate = {
              placement,
              nextDominoes,
              dominoPosition,
              dominoIndex: entry.index
            };
            all.push(candidate);
            byNode.get(node.id)?.push(candidate);
            byNode.get(neighborId)?.push(candidate);
            byDomino.get(entry.index)?.push(candidate);
          }
        }
      }
    }

    for (const candidates of byNode.values()) {
      if (!candidates.length) return null;
    }

    for (const candidates of byDomino.values()) {
      if (!candidates.length) return null;
    }

    return { all, byNode, byDomino };
  }

  function firstForcedPlacement(domains) {
    for (const candidates of domains.byNode.values()) {
      if (candidates.length === 1) return candidates[0];
    }

    for (const candidates of domains.byDomino.values()) {
      if (candidates.length === 1) return candidates[0];
    }

    return null;
  }

  function nextPlacementCandidates(graph, remainingDominoes, valuesByNode, usedNodes) {
    const domains = candidateDomains(graph, remainingDominoes, valuesByNode, usedNodes);
    if (!domains) return [];
    let best = domains.all;

    for (const candidates of domains.byNode.values()) {
      if (!candidates.length) return [];
      if (!best || candidates.length < best.length) {
        best = candidates;
        if (best.length === 1) break;
      }
    }

    return best ?? [];
  }

  function emptyNeighborIds(graph, nodeId, usedNodes) {
    return (graph.neighborsByNode.get(nodeId) ?? []).filter((neighborId) => !usedNodes.has(neighborId));
  }

  function placeIsStillPossible(graph, placement, valuesByNode, usedNodes, remainingDominoes) {
    if (usedNodes.has(placement.topNode) || usedNodes.has(placement.bottomNode)) return false;

    valuesByNode.set(placement.topNode, placement.values[placement.topNode]);
    valuesByNode.set(placement.bottomNode, placement.values[placement.bottomNode]);
    const possible = constraintsStillPossible(graph.constraints, valuesByNode, remainingDominoes);
    valuesByNode.delete(placement.topNode);
    valuesByNode.delete(placement.bottomNode);

    return possible;
  }

  function applyPlacement(placement, valuesByNode, usedNodes) {
    valuesByNode.set(placement.topNode, placement.values[placement.topNode]);
    valuesByNode.set(placement.bottomNode, placement.values[placement.bottomNode]);
    usedNodes.add(placement.topNode);
    usedNodes.add(placement.bottomNode);
  }

  function undoPlacement(placement, valuesByNode, usedNodes) {
    usedNodes.delete(placement.topNode);
    usedNodes.delete(placement.bottomNode);
    valuesByNode.delete(placement.topNode);
    valuesByNode.delete(placement.bottomNode);
  }

  function hasDeadEnd(graph, usedNodes) {
    return graph.nodes.some((node) =>
      !usedNodes.has(node.id) && emptyNeighborIds(graph, node.id, usedNodes).length === 0
    );
  }

  function constraintsStillPossible(constraints, valuesByNode, remainingDominoes) {
    const remainingValues = availableHalfValues(remainingDominoes);
    return constraints.every((item) =>
      constraintStillPossible(item, valuesByNode, remainingValues)
    );
  }

  function availableHalfValues(remainingDominoes) {
    return remainingDominoes.flatMap(({ domino }) => [domino.top, domino.bottom]);
  }

  function constraintStillPossible({ nodes, constraint }, valuesByNode, remainingValues) {
    const values = (nodes ?? []).map((node) => valuesByNode.get(node));
    const assigned = values.filter((value) => value !== undefined);
    const unassignedCount = values.length - assigned.length;

    if (constraint?.type === "equal") {
      if (assigned.length && !assigned.every((value) => value === assigned[0])) return false;
      if (!unassignedCount) return true;
      if (assigned.length) {
        return countValue(remainingValues, assigned[0]) >= unassignedCount;
      }
      return uniqueValues(remainingValues).some((value) =>
        countValue(remainingValues, value) >= unassignedCount
      );
    }

    if (constraint?.type === "unequal") {
      if (new Set(assigned).size !== assigned.length) return false;
      if (!unassignedCount) return true;
      const assignedValues = new Set(assigned);
      const availableDistinct = uniqueValues(remainingValues)
        .filter((value) => !assignedValues.has(value)).length;
      return availableDistinct >= unassignedCount;
    }

    if (constraint?.type === "sum") {
      if (remainingValues.length < unassignedCount) return false;
      const assignedSum = assigned.reduce((total, value) => total + value, 0);
      const target = constraint.value;
      if (!Number.isFinite(target)) return true;

      const sorted = [...remainingValues].sort((a, b) => a - b);
      const minPossible = assignedSum + sorted.slice(0, unassignedCount)
        .reduce((total, value) => total + value, 0);
      const largestValues = unassignedCount ? sorted.slice(-unassignedCount) : [];
      const maxPossible = assignedSum + largestValues.reduce((total, value) => total + value, 0);

      if (constraint.sign === "<") return minPossible < target;
      if (constraint.sign === ">") return maxPossible > target;
      return minPossible <= target && target <= maxPossible;
    }

    return true;
  }

  function uniqueValues(values) {
    return Array.from(new Set(values));
  }

  function countValue(values, target) {
    return values.filter((value) => value === target).length;
  }

  function constraintsSatisfied(constraints, valuesByNode) {
    return constraints.every(({ nodes, constraint }) => {
      const values = (nodes ?? []).map((node) => valuesByNode.get(node));
      if (values.some((value) => value === undefined)) return false;

      if (constraint?.type === "equal") {
        return values.every((value) => value === values[0]);
      }

      if (constraint?.type === "unequal") {
        return new Set(values).size === values.length;
      }

      if (constraint?.type === "sum") {
        const sum = values.reduce((total, value) => total + value, 0);
        if (constraint.sign === "<") return sum < constraint.value;
        if (constraint.sign === ">") return sum > constraint.value;
        return sum === constraint.value;
      }

      return true;
    });
  }

  window.PipsSolver = {
    solve,
    constraintsSatisfied
  };
})();
