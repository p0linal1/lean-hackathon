(() => {
  function solve(state) {
    const nodes = state?.board?.nodes ?? [];
    const dominoes = state?.dominoes ?? [];
    const constraints = state?.constraints ?? [];

    if (!nodes.length) throw new Error("No board nodes detected");
    if (!dominoes.length) throw new Error("No dominoes detected");

    const graph = buildSolverGraph(nodes, constraints);
    const remainingDominoes = dominoes.map((domino, index) => ({ domino, index }));
    const result = search(graph, remainingDominoes, new Map(), [], new Set());
    if (!result) throw new Error("No solution found");
    return result;
  }

  function buildSolverGraph(nodes, constraints) {
    const nodeById = new Map(nodes.map((node) => [node.id, node]));
    const neighborsByNode = new Map();
    const constraintsByNode = new Map(nodes.map((node) => [node.id, []]));

    for (const node of nodes) {
      const neighbors = ["left", "right", "up", "down"]
        .map((direction) => node[direction])
        .filter((id) => id && nodeById.has(id));
      neighborsByNode.set(node.id, neighbors);
    }

    for (const constraint of constraints) {
      for (const nodeId of constraint.nodes ?? []) {
        if (constraintsByNode.has(nodeId)) {
          constraintsByNode.get(nodeId).push(constraint);
        }
      }
    }

    return {
      nodes,
      nodeById,
      neighborsByNode,
      constraints,
      constraintsByNode
    };
  }

  function orientations(domino) {
    const first = { top: domino.top, bottom: domino.bottom };
    const second = { top: domino.bottom, bottom: domino.top };
    return domino.top === domino.bottom ? [first] : [first, second];
  }

  function search(graph, remainingDominoes, valuesByNode, placements, usedNodes) {
    if (!remainingDominoes.length) {
      return usedNodes.size === graph.nodes.length && constraintsSatisfied(graph.constraints, valuesByNode)
        ? { placements, valuesByNode: Object.fromEntries(valuesByNode) }
        : null;
    }

    const nodeId = findNextEmptyNode(graph, usedNodes);
    if (!nodeId) return null;

    const emptyNeighbors = emptyNeighborIds(graph, nodeId, usedNodes)
      .sort((a, b) => emptyNeighborIds(graph, a, usedNodes).length - emptyNeighborIds(graph, b, usedNodes).length);
    if (!emptyNeighbors.length) return null;

    for (const neighborId of emptyNeighbors) {
      for (let dominoIndex = 0; dominoIndex < remainingDominoes.length; dominoIndex += 1) {
        const entry = remainingDominoes[dominoIndex];
        for (const orientation of orientations(entry.domino)) {
          const placement = {
            domino: entry.domino,
            topNode: nodeId,
            bottomNode: neighborId,
            values: {
              [nodeId]: orientation.top,
              [neighborId]: orientation.bottom
            }
          };

          if (!placeIsStillPossible(graph, placement, valuesByNode, usedNodes)) continue;

          applyPlacement(placement, valuesByNode, usedNodes);

          if (!hasDeadEnd(graph, usedNodes)) {
            const nextDominoes = withoutIndex(remainingDominoes, dominoIndex);
            const result = search(graph, nextDominoes, valuesByNode, [...placements, placement], usedNodes);
            if (result) return result;
          }

          undoPlacement(placement, valuesByNode, usedNodes);
        }
      }
    }

    return null;
  }

  function withoutIndex(items, index) {
    return items.slice(0, index).concat(items.slice(index + 1));
  }

  function findNextEmptyNode(graph, usedNodes) {
    let best = null;
    let bestEmptyNeighbors = Infinity;

    for (const node of graph.nodes) {
      if (usedNodes.has(node.id)) continue;

      const count = emptyNeighborIds(graph, node.id, usedNodes).length;
      if (count === 0) return node.id;
      if (count < bestEmptyNeighbors) {
        best = node.id;
        bestEmptyNeighbors = count;
      }
    }

    return best;
  }

  function emptyNeighborIds(graph, nodeId, usedNodes) {
    return (graph.neighborsByNode.get(nodeId) ?? []).filter((neighborId) => !usedNodes.has(neighborId));
  }

  function placeIsStillPossible(graph, placement, valuesByNode, usedNodes) {
    if (usedNodes.has(placement.topNode) || usedNodes.has(placement.bottomNode)) return false;

    valuesByNode.set(placement.topNode, placement.values[placement.topNode]);
    valuesByNode.set(placement.bottomNode, placement.values[placement.bottomNode]);
    const possible = affectedConstraints(placement, graph.constraintsByNode)
      .every((constraint) => constraintStillPossible(constraint, valuesByNode));
    valuesByNode.delete(placement.topNode);
    valuesByNode.delete(placement.bottomNode);

    return possible;
  }

  function affectedConstraints(placement, constraintsByNode) {
    return Array.from(new Set([
      ...(constraintsByNode.get(placement.topNode) ?? []),
      ...(constraintsByNode.get(placement.bottomNode) ?? [])
    ]));
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

  function constraintStillPossible({ nodes, constraint }, valuesByNode) {
    const values = (nodes ?? []).map((node) => valuesByNode.get(node));
    const assigned = values.filter((value) => value !== undefined);
    if (!assigned.length) return true;

    if (constraint?.type === "equal") {
      return assigned.every((value) => value === assigned[0]);
    }

    if (constraint?.type === "unequal") {
      return new Set(assigned).size === assigned.length;
    }

    if (constraint?.type === "sum") {
      const sum = assigned.reduce((total, value) => total + value, 0);
      const target = constraint.value;
      if (!Number.isFinite(target)) return true;
      if (constraint.sign === "<") return sum < target;
      if (constraint.sign === ">") return assigned.length === values.length ? sum > target : true;
      return assigned.length === values.length ? sum === target : sum <= target;
    }

    return true;
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
