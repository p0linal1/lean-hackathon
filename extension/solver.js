(() => {
  const LOG_PREFIX = "[NYT Pips Solver]";
  const CLASS_PARTS = {
    boardContainer: "Board-module_boardContainer",
    board: "Board-module_droppable",
    cell: "Board-module_droppableCell",
    hidden: "Board-module_hidden",
    domino: "Domino-module_domino",
    half: "Domino-module_halfDomino",
    dot: "Domino-module_dot"
  };

  let button = null;
  let status = null;
  let toolbar = null;
  let lastActivation = 0;
  let renderedSolution = null;
  let renderedState = null;
  let solutionOverlay = null;
  let hintElementsByKey = new Map();

  function hasClassPart(element, part) {
    return element.className && String(element.className).includes(part);
  }

  function hasClassTokenPrefix(element, prefix) {
    return Array.from(element.classList || []).some((className) => className.startsWith(`${prefix}__`));
  }

  function byClassTokenPrefix(prefix, root = document) {
    return Array.from(root.querySelectorAll(`[class*="${prefix}"]`))
      .filter((element) => hasClassTokenPrefix(element, prefix));
  }

  function directByClassTokenPrefix(root, prefix) {
    return Array.from(root.children).filter((child) => hasClassTokenPrefix(child, prefix));
  }

  function isVisible(element) {
    const style = getComputedStyle(element);
    const rect = element.getBoundingClientRect();
    return style.display !== "none" && style.visibility !== "hidden" && style.opacity !== "0" && rect.width > 0 && rect.height > 0;
  }

  function isEffectivelyVisible(element) {
    for (let current = element; current && current !== document.documentElement; current = current.parentElement) {
      if (!isVisible(current)) return false;
      if (current.hasAttribute("hidden") || current.getAttribute("aria-hidden") === "true") return false;
    }
    return true;
  }

  function findActiveBoardElement() {
    const boards = byClassTokenPrefix(CLASS_PARTS.board)
      .filter((element) => directByClassTokenPrefix(element, CLASS_PARTS.cell).length > 0);
    const visibleBoards = boards.filter(isEffectivelyVisible);
    return visibleBoards[0] || boards[0] || null;
  }

  function installButton() {
    const board = findActiveBoardElement();
    if (!board) return;

    if (button?.isConnected) {
      positionToolbar(board);
      return;
    }

    toolbar = document.createElement("div");
    toolbar.dataset.nytPipsSolver = "true";
    toolbar.style.display = "flex";
    toolbar.style.alignItems = "center";
    toolbar.style.gap = "8px";
    toolbar.style.position = "fixed";
    toolbar.style.zIndex = "2147483647";
    toolbar.style.pointerEvents = "auto";

    button = document.createElement("div");
    button.setAttribute("role", "button");
    button.setAttribute("tabindex", "0");
    button.textContent = "Solve with brute force";
    button.style.border = "1px solid #111";
    button.style.borderRadius = "6px";
    button.style.background = "#fff";
    button.style.color = "#111";
    button.style.font = "700 13px system-ui, sans-serif";
    button.style.padding = "7px 10px";
    button.style.cursor = "pointer";

    status = document.createElement("span");
    status.style.color = "#333";
    status.style.font = "12px system-ui, sans-serif";
    status.style.background = "rgba(255, 255, 255, 0.92)";
    status.style.borderRadius = "6px";
    status.style.padding = "4px 6px";

    for (const eventName of ["pointerdown", "mousedown", "mouseup", "click"]) {
      button.addEventListener(eventName, stopPageClickHandlers, true);
    }
    button.addEventListener("pointerup", activateSolver, true);
    button.addEventListener("keydown", (event) => {
      if (event.key !== "Enter" && event.key !== " ") return;
      activateSolver(event);
    }, true);
    toolbar.append(button, status);
    document.body.appendChild(toolbar);
    positionToolbar(board);
  }

  function positionToolbar(board) {
    if (!toolbar) return;

    const rect = board.getBoundingClientRect();
    const left = Math.min(window.innerWidth - 190, Math.max(8, rect.right + 12));
    const top = Math.min(window.innerHeight - 48, Math.max(8, rect.top));
    toolbar.style.left = `${left}px`;
    toolbar.style.top = `${top}px`;
  }

  function activateSolver(event) {
    stopPageClickHandlers(event);

    const now = Date.now();
    if (now - lastActivation < 800) return;
    lastActivation = now;

    solveAndPlace();
  }

  function stopPageClickHandlers(event) {
    event.preventDefault();
    event.stopPropagation();
    event.stopImmediatePropagation();
  }

  function setStatus(message) {
    if (status) status.textContent = message;
    console.info(LOG_PREFIX, message);
  }

  function readState() {
    if (typeof window.__nytPipsReadState !== "function") {
      throw new Error("content.js state reader is not available");
    }
    return window.__nytPipsReadState();
  }

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

  function constraintsStillPossible(constraints, valuesByNode) {
    return constraints.every(({ nodes, constraint }) => {
      return constraintStillPossible({ nodes, constraint }, valuesByNode);
    });
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

  async function solveAndPlace(event) {
    if (event) stopPageClickHandlers(event);

    try {
      button.setAttribute("aria-disabled", "true");
      button.style.pointerEvents = "none";
      setStatus("Solving...");

      const state = readState();
      const solution = solve(state);
      console.log(`${LOG_PREFIX} solution`, solution);

      renderSolutionOverlay(solution, state);
      setStatus("Solved (shown)");
    } catch (error) {
      setStatus(String(error?.message ?? error));
      console.warn(LOG_PREFIX, error);
    } finally {
      button.removeAttribute("aria-disabled");
      button.style.pointerEvents = "";
    }
  }

  function renderSolutionOverlay(solution, state) {
    renderedSolution = solution;
    renderedState = state;

    const board = findActiveBoardElement();
    if (!board) throw new Error("Could not find board");

    removeSolutionOverlay();

    const cells = directByClassTokenPrefix(board, CLASS_PARTS.cell);
    const nodeIndexes = new Map((state.board.nodes ?? []).map((node) => [node.id, node.index]));

    solutionOverlay = document.createElement("div");
    solutionOverlay.dataset.nytPipsSolverOverlay = "true";
    solutionOverlay.style.position = "fixed";
    solutionOverlay.style.inset = "0";
    solutionOverlay.style.zIndex = "2147483646";
    solutionOverlay.style.pointerEvents = "none";
    document.body.appendChild(solutionOverlay);
    hintElementsByKey = new Map();

    for (const placement of solution.placements) {
      const topCell = cells[nodeIndexes.get(placement.topNode)];
      const bottomCell = cells[nodeIndexes.get(placement.bottomNode)];
      if (!topCell || !bottomCell) continue;

      drawDominoHint(topCell, bottomCell, placement);
    }

    updateHintVisibility();
  }

  function removeSolutionOverlay() {
    solutionOverlay?.remove();
    solutionOverlay = null;
    hintElementsByKey = new Map();
  }

  function redrawSolutionOverlay() {
    if (!renderedSolution || !renderedState) return;
    renderSolutionOverlay(renderedSolution, renderedState);
  }

  function drawDominoHint(firstCell, secondCell, placement) {
    const first = firstCell.getBoundingClientRect();
    const second = secondCell.getBoundingClientRect();
    const left = Math.min(first.left, second.left);
    const top = Math.min(first.top, second.top);
    const right = Math.max(first.right, second.right);
    const bottom = Math.max(first.bottom, second.bottom);
    const horizontal = Math.abs(first.left - second.left) > Math.abs(first.top - second.top);

    const hint = document.createElement("div");
    hint.dataset.placementKey = placementKey(placement);
    hint.style.position = "absolute";
    hint.style.left = `${left + 4}px`;
    hint.style.top = `${top + 4}px`;
    hint.style.width = `${right - left - 8}px`;
    hint.style.height = `${bottom - top - 8}px`;
    hint.style.display = "grid";
    hint.style.gridTemplateColumns = horizontal ? "1fr 1fr" : "1fr";
    hint.style.gridTemplateRows = horizontal ? "1fr" : "1fr 1fr";
    hint.style.border = "2px solid rgba(15, 118, 110, 0.82)";
    hint.style.borderRadius = "12px";
    hint.style.boxSizing = "border-box";
    hint.style.background = "rgba(240, 253, 250, 0.58)";
    hint.style.backdropFilter = "saturate(1.1)";
    hint.style.boxShadow = "0 4px 14px rgba(15, 23, 42, 0.18)";
    hint.title = placement.domino.id;

    const firstNode = firstCell.getBoundingClientRect().top <= secondCell.getBoundingClientRect().top &&
      firstCell.getBoundingClientRect().left <= secondCell.getBoundingClientRect().left
      ? placement.topNode
      : placement.bottomNode;
    const secondNode = firstNode === placement.topNode ? placement.bottomNode : placement.topNode;
    hint.append(
      createDominoHalf(placement.values[firstNode], horizontal ? "right" : "bottom"),
      createDominoHalf(placement.values[secondNode], "")
    );

    solutionOverlay.appendChild(hint);
    hintElementsByKey.set(placementKey(placement), hint);
  }

  function createDominoHalf(value, dividerSide) {
    const half = document.createElement("div");
    half.style.position = "relative";
    if (dividerSide === "right") half.style.borderRight = "2px solid rgba(15, 118, 110, 0.62)";
    if (dividerSide === "bottom") half.style.borderBottom = "2px solid rgba(15, 118, 110, 0.62)";

    for (const position of pipPositions(value)) {
      const pip = document.createElement("span");
      pip.style.position = "absolute";
      pip.style.left = `${position.x}%`;
      pip.style.top = `${position.y}%`;
      pip.style.width = "8px";
      pip.style.height = "8px";
      pip.style.marginLeft = "-4px";
      pip.style.marginTop = "-4px";
      pip.style.borderRadius = "50%";
      pip.style.background = "rgba(17, 24, 39, 0.82)";
      pip.style.boxShadow = "0 1px 2px rgba(255, 255, 255, 0.55)";
      half.appendChild(pip);
    }

    return half;
  }

  function pipPositions(value) {
    const positions = {
      0: [],
      1: [{ x: 50, y: 50 }],
      2: [{ x: 30, y: 30 }, { x: 70, y: 70 }],
      3: [{ x: 30, y: 30 }, { x: 50, y: 50 }, { x: 70, y: 70 }],
      4: [{ x: 30, y: 30 }, { x: 70, y: 30 }, { x: 30, y: 70 }, { x: 70, y: 70 }],
      5: [{ x: 30, y: 30 }, { x: 70, y: 30 }, { x: 50, y: 50 }, { x: 30, y: 70 }, { x: 70, y: 70 }],
      6: [{ x: 30, y: 25 }, { x: 70, y: 25 }, { x: 30, y: 50 }, { x: 70, y: 50 }, { x: 30, y: 75 }, { x: 70, y: 75 }]
    };
    return positions[value] ?? [{ x: 50, y: 50 }];
  }

  function placementKey(placement) {
    return `${placement.domino.id}:${placement.topNode}:${placement.bottomNode}`;
  }

  function updateHintVisibility() {
    if (!renderedSolution || !renderedState || !solutionOverlay) return;

    const placed = readPlacedDominoes(renderedState);
    for (const placement of renderedSolution.placements) {
      const hint = hintElementsByKey.get(placementKey(placement));
      if (!hint) continue;
      const satisfied = placed.some((domino) => placementMatchesPlacedDomino(placement, domino));
      if (satisfied && hint.style.display !== "none") {
        console.info(`${LOG_PREFIX} hiding solved hint`, placement.domino.id, placement.topNode, placement.bottomNode);
      }
      hint.style.display = satisfied ? "none" : "grid";
    }
  }

  function readPlacedDominoes(state) {
    const board = findActiveBoardElement();
    if (!board) return [];

    const boardRect = board.getBoundingClientRect();
    const cells = directByClassTokenPrefix(board, CLASS_PARTS.cell);
    const nodeByIndex = new Map((state.board.nodes ?? []).map((node) => [node.index, node.id]));

    return byClassTokenPrefix(CLASS_PARTS.domino, document)
      .filter((domino) => isVisible(domino) && overlapRatio(domino.getBoundingClientRect(), boardRect) > 0.2)
      .map((domino) => {
        const halves = byClassTokenPrefix(CLASS_PARTS.half, domino)
          .map((half, halfIndex) => placedHalfInfo(half, halfIndex, domino, cells, nodeByIndex))
          .filter((half) => half.node);

        return halves.length === 2 ? halves : null;
      })
      .filter(Boolean);
  }

  function placedHalfInfo(half, halfIndex, domino, cells, nodeByIndex) {
    const halfRect = half.getBoundingClientRect();
    const rect = halfRect.width > 0 && halfRect.height > 0
      ? halfRect
      : inferredHalfRect(domino.getBoundingClientRect(), halfIndex);
    const cellIndex = bestOverlappingCellIndex(rect, cells);
    return {
      node: nodeByIndex.get(cellIndex),
      value: readPipCount(half)
    };
  }

  function inferredHalfRect(rect, halfIndex) {
    if (rect.width >= rect.height) {
      return {
        left: rect.left + (halfIndex === 0 ? 0 : rect.width / 2),
        right: rect.left + (halfIndex === 0 ? rect.width / 2 : rect.width),
        top: rect.top,
        bottom: rect.bottom,
        width: rect.width / 2,
        height: rect.height
      };
    }

    return {
      left: rect.left,
      right: rect.right,
      top: rect.top + (halfIndex === 0 ? 0 : rect.height / 2),
      bottom: rect.top + (halfIndex === 0 ? rect.height / 2 : rect.height),
      width: rect.width,
      height: rect.height / 2
    };
  }

  function bestOverlappingCellIndex(element, cells) {
    const rect = typeof element.getBoundingClientRect === "function"
      ? element.getBoundingClientRect()
      : element;
    let best = { index: null, ratio: 0 };
    cells.forEach((cell, index) => {
      const ratio = overlapRatio(rect, cell.getBoundingClientRect());
      if (ratio > best.ratio) best = { index, ratio };
    });
    return best.ratio > 0.12 ? best.index : null;
  }

  function overlapRatio(a, b) {
    const left = Math.max(a.left, b.left);
    const right = Math.min(a.right, b.right);
    const top = Math.max(a.top, b.top);
    const bottom = Math.min(a.bottom, b.bottom);
    const area = Math.max(0, right - left) * Math.max(0, bottom - top);
    const denominator = Math.max(1, Math.min(a.width * a.height, b.width * b.height));
    return area / denominator;
  }

  function readPipCount(half) {
    return byClassTokenPrefix(CLASS_PARTS.dot, half).length;
  }

  function placementMatchesPlacedDomino(placement, placedDomino) {
    const expected = new Map([
      [placement.topNode, placement.values[placement.topNode]],
      [placement.bottomNode, placement.values[placement.bottomNode]]
    ]);

    return placedDomino.every((half) => expected.get(half.node) === half.value);
  }

  installButton();
  window.addEventListener("resize", () => {
    installButton();
    redrawSolutionOverlay();
  }, { passive: true });
  window.addEventListener("scroll", () => {
    installButton();
    redrawSolutionOverlay();
  }, { passive: true });
  new MutationObserver(() => {
    installButton();
    updateHintVisibility();
  }).observe(document.documentElement, {
    childList: true,
    subtree: true,
    attributes: true,
    attributeFilter: ["class", "style"]
  });
})();
