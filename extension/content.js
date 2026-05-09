(() => {
  const LOG_PREFIX = "[NYT Pips]";
  const CLASS_PARTS = {
    boardContainer: "Board-module_boardContainer",
    board: "Board-module_droppable",
    cell: "Board-module_droppableCell",
    hidden: "Board-module_hidden",
    regionCell: "RegionCell-module_regionCell",
    regionHidden: "RegionCell-module_hidden",
    regionLabel: "RegionCell-module_regionLabel",
    regionLabelText: "RegionCell-module_regionLabelText",
    regionSymbol: "RegionCell-module_regionLabelSymbol",
    tray: "Tray-module_tray",
    trayWrapper: "Tray-module_trayDominoWrapper",
    domino: "Domino-module_domino",
    half: "Domino-module_halfDomino",
    dot: "Domino-module_dot",
    constraint: "Constraint-module"
  };

  let lastSnapshot = "";
  let pendingLog = 0;

  function byClassPart(part, root = document) {
    return Array.from(root.querySelectorAll(`[class*="${part}"]`));
  }

  function byClassTokenPrefix(prefix, root = document) {
    return Array.from(root.querySelectorAll(`[class*="${prefix}"]`))
      .filter((element) => hasClassTokenPrefix(element, prefix));
  }

  function directByClassPart(root, part) {
    return Array.from(root.children).filter((child) => hasClassPart(child, part));
  }

  function directByClassTokenPrefix(root, prefix) {
    return Array.from(root.children).filter((child) => hasClassTokenPrefix(child, prefix));
  }

  function hasClassPart(element, part) {
    return element.className && String(element.className).includes(part);
  }

  function hasClassTokenPrefix(element, prefix) {
    return Array.from(element.classList || []).some((className) => className.startsWith(`${prefix}__`));
  }

  function cssNumber(element, property) {
    const value = getComputedStyle(element).getPropertyValue(property).trim();
    const parsed = Number(value);
    return Number.isFinite(parsed) ? parsed : null;
  }

  function textOf(element) {
    return (element.textContent || "").replace(/\s+/g, " ").trim();
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

  function visibleArea(element) {
    const rect = element.getBoundingClientRect();
    return rect.width * rect.height;
  }

  function commonAncestor(left, right) {
    if (!left || !right) return null;
    const ancestors = new Set();
    for (let current = left; current; current = current.parentElement) ancestors.add(current);
    for (let current = right; current; current = current.parentElement) {
      if (ancestors.has(current)) return current;
    }
    return null;
  }

  function findActiveTrayElement(boardState) {
    const trays = byClassTokenPrefix(CLASS_PARTS.tray)
      .filter((tray) => byClassTokenPrefix(CLASS_PARTS.trayWrapper, tray).length > 0);
    const visibleTrays = trays.filter(isEffectivelyVisible);
    const candidates = visibleTrays.length ? visibleTrays : trays;
    if (!candidates.length) return null;

    const boardContainer = boardState?.element?.closest(`[class*="${CLASS_PARTS.boardContainer}"]`);
    const boardRect = boardState?.element?.getBoundingClientRect();
    return candidates
      .map((tray) => {
        const ancestor = commonAncestor(boardContainer || boardState?.element, tray);
        const rect = tray.getBoundingClientRect();
        const verticalDistance = boardRect
          ? Math.max(0, rect.top - boardRect.bottom, boardRect.top - rect.bottom)
          : 0;
        return {
          tray,
          ancestorDepth: ancestor ? depthOf(ancestor) : 0,
          verticalDistance,
          area: visibleArea(tray)
        };
      })
      .sort((a, b) =>
        b.ancestorDepth - a.ancestorDepth ||
        a.verticalDistance - b.verticalDistance ||
        b.area - a.area
      )[0].tray;
  }

  function depthOf(element) {
    let depth = 0;
    for (let current = element; current; current = current.parentElement) depth += 1;
    return depth;
  }

  function parseGridTrackCount(value) {
    if (!value || value === "none") return null;
    const repeatMatch = value.match(/^repeat\((\d+),/);
    if (repeatMatch) return Number(repeatMatch[1]);
    return value.split(/\s+/).filter(Boolean).length || null;
  }

  function inferColumns(board, cells) {
    const boardContainer = board.closest(`[class*="${CLASS_PARTS.boardContainer}"]`);
    const cssCols = boardContainer ? cssNumber(boardContainer, "--cols") : null;
    if (cssCols) return cssCols;

    const computed = getComputedStyle(board);
    const cssColumns = parseGridTrackCount(computed.gridTemplateColumns);
    if (cssColumns) return cssColumns;

    const visibleRects = cells
      .map((cell) => cell.getBoundingClientRect())
      .filter((rect) => rect.width > 0 && rect.height > 0);

    if (visibleRects.length) {
      const firstTop = visibleRects[0].top;
      const tolerance = Math.max(2, visibleRects[0].height * 0.25);
      const firstRowCount = visibleRects.filter((rect) => Math.abs(rect.top - firstTop) <= tolerance).length;
      if (firstRowCount > 0) return firstRowCount;
    }

    const square = Math.sqrt(cells.length);
    return Number.isInteger(square) ? square : null;
  }

  function readBoard() {
    const board = findActiveBoardElement();
    if (!board) return null;

    const boardContainer = board.closest(`[class*="${CLASS_PARTS.boardContainer}"]`);
    const cells = directByClassTokenPrefix(board, CLASS_PARTS.cell);
    const columns = inferColumns(board, cells);
    const cssRows = boardContainer ? cssNumber(boardContainer, "--rows") : null;
    const rows = cssRows || (columns ? Math.ceil(cells.length / columns) : null);
    const flatCells = cells.map((cell, index) => {
      const style = getComputedStyle(cell);
      const hidden = hasClassPart(cell, CLASS_PARTS.hidden) || style.display === "none" || style.visibility === "hidden";
      return {
        index,
        row: columns ? Math.floor(index / columns) : null,
        column: columns ? index % columns : null,
        hidden,
        active: !hidden
      };
    });

    const mask = columns
      ? Array.from({ length: rows }, (_, row) =>
          flatCells
            .slice(row * columns, row * columns + columns)
            .map((cell) => (cell.hidden ? 0 : 1))
        )
      : null;

    return {
      rows,
      columns,
      totalCells: cells.length,
      activeCells: flatCells.filter((cell) => cell.active).length,
      hiddenCells: flatCells.filter((cell) => cell.hidden).length,
      mask,
      cells: flatCells,
      boardId: board.getAttribute("data-testid") || board.parentElement?.getAttribute("data-testid") || null,
      element: board
    };
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

  function cellIndexesForElement(element, boardState) {
    if (!boardState?.element) return [];
    const elementRect = element.getBoundingClientRect();
    const cells = directByClassTokenPrefix(boardState.element, CLASS_PARTS.cell);
    return cells
      .map((cell, index) => ({ index, ratio: overlapRatio(elementRect, cell.getBoundingClientRect()) }))
      .filter((item) => item.ratio > 0.15)
      .map((item) => item.index);
  }

  function normalizeConstraintText(labelElement) {
    const text = textOf(labelElement);
    if (text) return text;

    const symbol = labelElement.querySelector(`[class*="${CLASS_PARTS.regionSymbol}"]`);
    if (!symbol) return "";
    const className = String(symbol.className || "");
    if (className.includes("equal")) return "=";
    if (className.includes("less")) return "<";
    if (className.includes("greater")) return ">";
    return "";
  }

  function colorFromClassName(className) {
    return ["blue", "pink", "orange", "teal", "purple", "green"].find((color) =>
      className.includes(`_${color}__`) || className.includes(`-${color}__`)
    ) || null;
  }

  function regionCellInfo(regionCell, index, boardState) {
    const className = String(regionCell.className || "");
    const inner = regionCell.querySelector('[class*="RegionCell-module_regionCellInner"]');
    const label = regionCell.querySelector(`[class*="${CLASS_PARTS.regionLabel}"]`);
    const hidden = hasClassPart(regionCell, CLASS_PARTS.regionHidden) || hasClassPart(regionCell, CLASS_PARTS.hidden);
    const color = colorFromClassName(`${className} ${inner?.className || ""} ${label?.className || ""}`);
    return {
      element: regionCell,
      index,
      row: boardState.columns ? Math.floor(index / boardState.columns) : null,
      column: boardState.columns ? index % boardState.columns : null,
      hidden,
      color
    };
  }

  function matchingRegionIndexes(regionCells, start, boardState) {
    const startCell = regionCells[start];
    if (!startCell?.color || startCell.hidden || !boardState.columns) {
      return startCell ? [startCell.index] : [];
    }

    const cellsByIndex = new Map(regionCells.map((cell) => [cell.index, cell]));
    const visited = new Set();
    const stack = [startCell.index];
    const result = [];

    while (stack.length) {
      const index = stack.pop();
      const cell = cellsByIndex.get(index);
      if (!cell || visited.has(index) || cell.hidden || cell.color !== startCell.color) continue;

      visited.add(index);
      result.push(index);

      const row = Math.floor(index / boardState.columns);
      const column = index % boardState.columns;
      const neighbors = [
        row > 0 ? index - boardState.columns : null,
        row < boardState.rows - 1 ? index + boardState.columns : null,
        column > 0 ? index - 1 : null,
        column < boardState.columns - 1 ? index + 1 : null
      ].filter((neighbor) => neighbor !== null);

      stack.push(...neighbors);
    }

    return result.sort((a, b) => a - b);
  }

  function readRegionConstraints(boardState) {
    const boardContainer = boardState?.element?.closest(`[class*="${CLASS_PARTS.boardContainer}"]`);
    if (!boardContainer) return [];

    const regionCells = byClassTokenPrefix(CLASS_PARTS.regionCell, boardContainer)
      .filter((cell) => cell.parentElement?.matches(`[class*="Board-module_regions"]`));
    const regionCellDetails = regionCells.map((cell, index) => regionCellInfo(cell, index, boardState));

    return regionCells.flatMap((regionCell, index) => {
      const labels = byClassTokenPrefix(CLASS_PARTS.regionLabel, regionCell);
      if (!labels.length) return [];

      const details = regionCellDetails[index];
      return labels.map((label) => {
        const labelText = label.querySelector(`[class*="${CLASS_PARTS.regionLabelText}"]`) || label;
        const text = normalizeConstraintText(labelText);
        const cellIndexes = matchingRegionIndexes(regionCellDetails, index, boardState);
        return {
          source: "region",
          text,
          color: details.color,
          index,
          row: details.row,
          column: details.column,
          hidden: details.hidden,
          cellIndexes,
          className: String(label.className || "")
        };
      });
    });
  }

  function readConstraints(boardState) {
    const labelPattern = /\b(sum|total|equal|equals|same|different|less|greater|under|over)\b|[<>=]/i;
    const textNodesInBoard = boardState?.element
      ? Array.from(boardState.element.querySelectorAll("*")).filter((element) => {
          if (hasClassPart(element, CLASS_PARTS.cell) || hasClassPart(element, CLASS_PARTS.dot)) return false;
          return textOf(element) && isVisible(element);
        })
      : [];

    const regionConstraints = readRegionConstraints(boardState);
    const candidates = new Set([
      ...Array.from((boardState?.element?.closest(`[class*="${CLASS_PARTS.boardContainer}"]`) || document)
        .querySelectorAll('[class*="Constraint"], [class*="constraint"]')),
      ...textNodesInBoard,
      ...Array.from(document.querySelectorAll("[aria-label], [title]")).filter((element) => {
        const hint = `${element.getAttribute("aria-label") || ""} ${element.getAttribute("title") || ""}`;
        return labelPattern.test(hint);
      })
    ]);

    const boardRect = boardState?.element?.getBoundingClientRect();
    const constraints = Array.from(candidates)
      .filter(isVisible)
      .map((element) => {
        const rect = element.getBoundingClientRect();
        const inBoard =
          boardRect &&
          overlapRatio(rect, boardRect) > 0.05;
        return {
          text: textOf(element),
          ariaLabel: element.getAttribute("aria-label") || null,
          title: element.getAttribute("title") || null,
          className: String(element.className || ""),
          cellIndexes: cellIndexesForElement(element, boardState),
          inBoard
        };
      })
      .filter((item) => {
        const hint = `${item.text} ${item.ariaLabel || ""} ${item.title || ""} ${item.className}`;
        return item.className.includes("Constraint") || labelPattern.test(hint);
      });

    const unique = new Map();
    for (const constraint of constraints) {
      const key = JSON.stringify([
        constraint.text,
        constraint.ariaLabel,
        constraint.title,
        constraint.className,
        constraint.cellIndexes
      ]);
      unique.set(key, constraint);
    }

    return [...regionConstraints, ...Array.from(unique.values())];
  }

  function readPipCount(half) {
    return byClassTokenPrefix(CLASS_PARTS.dot, half).length;
  }

  function readDominoes(boardState) {
    const tray = findActiveTrayElement(boardState);
    if (!tray) return [];

    return byClassTokenPrefix(CLASS_PARTS.trayWrapper, tray)
      .map((wrapper, trayIndex) => {
        const domino = wrapper.querySelector(`[class*="${CLASS_PARTS.domino}"]`);
        if (!domino) return null;

        const halves = byClassTokenPrefix(CLASS_PARTS.half, domino);
        const values = halves.map(readPipCount);
        const idMatch = halves[0]?.id?.match(/^domino-(\d+)-/);
        return {
          id: idMatch ? Number(idMatch[1]) : trayIndex + 1,
          trayIndex,
          values,
          rotation: domino.style.transform || getComputedStyle(domino).transform,
          halfIds: halves.map((half) => half.id || null),
          visible: isEffectivelyVisible(domino),
          element: domino
        };
      })
      .filter(Boolean);
  }

  function readDebugCounts() {
    const boards = byClassTokenPrefix(CLASS_PARTS.board)
      .filter((element) => directByClassTokenPrefix(element, CLASS_PARTS.cell).length > 0);
    const trays = byClassTokenPrefix(CLASS_PARTS.tray)
      .filter((tray) => byClassTokenPrefix(CLASS_PARTS.trayWrapper, tray).length > 0);
    return {
      boardCandidates: boards.length,
      visibleBoardCandidates: boards.filter(isEffectivelyVisible).length,
      trayCandidates: trays.length,
      visibleTrayCandidates: trays.filter(isEffectivelyVisible).length
    };
  }

  function readGameState() {
    const board = readBoard();
    return {
      url: location.href,
      readAt: new Date().toISOString(),
      debug: readDebugCounts(),
      board,
      constraints: readConstraints(board),
      dominoes: readDominoes(board)
    };
  }

  function serializable(state) {
    const board = state.board
      ? {
          rows: state.board.rows,
          columns: state.board.columns,
          totalCells: state.board.totalCells,
          activeCells: state.board.activeCells,
          hiddenCells: state.board.hiddenCells,
          boardId: state.board.boardId,
          mask: state.board.mask,
          cells: state.board.cells
        }
      : null;

    return {
      ...state,
      board,
      dominoes: state.dominoes.map((domino) => ({ ...domino, element: undefined }))
    };
  }

  function logState(reason) {
    const state = readGameState();
    const cleanState = serializable(state);
    const snapshot = JSON.stringify(cleanState);
    if (snapshot === lastSnapshot) return;

    lastSnapshot = snapshot;
    window.__nytPipsState = cleanState;

    console.groupCollapsed(`${LOG_PREFIX} game state (${reason})`);
    console.log("state", cleanState);
    console.log("board shape", cleanState.board);
    console.log("constraints", cleanState.constraints);
    console.log("debug", cleanState.debug);
    console.table(cleanState.dominoes.map(({ id, trayIndex, values, rotation, halfIds, visible }) => ({
      id,
      trayIndex,
      first: values[0],
      second: values[1],
      rotation,
      visible,
      halfIds: halfIds.join(", ")
    })));
    console.groupEnd();
  }

  function scheduleLog(reason) {
    clearTimeout(pendingLog);
    pendingLog = setTimeout(() => logState(reason), 250);
  }

  scheduleLog("initial load");

  const observer = new MutationObserver(() => scheduleLog("DOM changed"));
  observer.observe(document.documentElement, {
    childList: true,
    subtree: true,
    attributes: true,
    attributeFilter: ["class", "style", "aria-label", "title"]
  });

  window.__nytPipsReadState = () => {
    const state = serializable(readGameState());
    console.log(`${LOG_PREFIX} manual read`, state);
    return state;
  };
})();
