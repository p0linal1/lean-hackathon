let currentState = null;
const LEAN_SERVER_STATE_URL = "http://127.0.0.1:8765/solve";
const POPUP_STATE_KEY = "pipsHelper.popupState.v1";
const TEST_RUN_KEY = "pipsHelper.testRun.v1";
const TEST_SOLVE_TIMEOUT_MS = 10000;
const STATUS_CLASSES = [
  "reading",
  "detected",
  "solving",
  "solved",
  "error"
];

const solveButton = document.querySelector("#solveButton");
const testButton = document.querySelector("#testButton");
const statusEl = document.querySelector("#status");
const boardEl = document.querySelector("#board");
const boardSection = document.querySelector("#board-section");
const testSection = document.querySelector("#test-section");
const testProgressEl = document.querySelector("#test-progress");
const testProgressFillEl = document.querySelector("#test-progress-fill");
const testFailuresEl = document.querySelector("#test-failures");
const testResultsEl = document.querySelector("#test-results");

solveButton.addEventListener("click", solvePuzzle);
testButton.addEventListener("click", runPuzzleTests);
initializePopup();

async function initializePopup() {
  const restored = restorePopupState();
  await readPuzzle({ preserveOnError: restored });
}

async function readPuzzle(options = {}) {
  setStatus("Reading");

  try {
    const response = await readStateFromCurrentTab();

    currentState = response.state;
    solveButton.disabled = !currentState?.board?.nodes?.length;

    renderState(currentState);
    savePopupState({ currentState, solution: null, status: "Detected" });
    setStatus("Detected");
  } catch (error) {
    if (!options.preserveOnError) setStatus("Error");
    console.warn("[Pips Helper]", error);
  }
}

async function solvePuzzle() {
  if (!currentState?.board?.nodes) return;

  setStatus("Solving");

  try {
    const solution = await solveWithBackend(currentState).catch((error) => {
      console.warn("[Pips Helper] Backend solve failed, falling back to frontend solver", error);
      return window.PipsSolver.solve(currentState);
    });
    renderState(currentState, solution);
    savePopupState({
      currentState,
      solution,
      status: "Solved"
    });
    setStatus("Solved");
  } catch (error) {
    setStatus("Error");
    console.warn("[Pips Helper]", error);
  }
}

async function solveWithBackend(state) {
  const response = await fetch(LEAN_SERVER_STATE_URL, {
    method: "POST",
    headers: {
      "Content-Type": "application/json"
    },
    body: JSON.stringify(state)
  });

  if (!response.ok) {
    throw new Error(`Lean server returned HTTP ${response.status}`);
  }

  const payload = await response.json();
  if (payload?.solution?.placements?.length) return payload.solution;
  if (payload?.placements?.length) return payload;
  throw new Error("Lean server did not return a solved placement set");
}

function renderState(state, solution = null) {
  const board = state.board;

  renderBoard(board, solution);
  boardSection.classList.toggle("hidden", !Array.isArray(board?.nodes));
}

function renderBoard(board, solution) {
  boardEl.innerHTML = "";

  if (!Array.isArray(board?.nodes)) {
    boardEl.textContent = "No board detected";
    return;
  }

  const nodes = board.nodes.map((node) => normalizeBoardNode(node, board));
  const nodesByIndex = new Map(nodes.map((node) => [node.index, node]));
  const nodesById = new Map(nodes.map((node) => [node.id, node]));
  const dimensions = boardDimensions(board, nodesByIndex);

  boardEl.style.gridTemplateColumns = `repeat(${dimensions.columns}, var(--popup-board-cell-size))`;
  boardEl.style.gridTemplateRows = `repeat(${dimensions.rows}, var(--popup-board-cell-size))`;

  if (!(solution?.placements?.length)) {
    for (const node of nodes) {
      const div = document.createElement("div");
      div.className = "cell";
      div.style.gridColumn = `${node.column + 1}`;
      div.style.gridRow = `${node.row + 1}`;

      boardEl.appendChild(div);
    }
  }

  for (const placement of solution?.placements ?? []) {
    const domino = renderDominoPlacement(placement, nodesById);
    if (domino) boardEl.appendChild(domino);
  }
}

function renderDominoPlacement(placement, nodesById) {
  const firstNode = nodesById.get(placement.topNode);
  const secondNode = nodesById.get(placement.bottomNode);
  if (!firstNode || !secondNode) return null;

  const orientation = dominoOrientation(placement.topNode, placement.bottomNode);
  const orderedNodes = orderedPlacementNodes(firstNode, secondNode, orientation);
  const domino = document.createElement("div");
  domino.className = `Domino-module_domino__hSfP4 solved-domino ${orientation}`;

  if (orientation === "horizontal") {
    const column = Math.min(firstNode.column, secondNode.column) + 1;
    domino.style.gridColumn = `${column} / span 2`;
    domino.style.gridRow = `${orderedNodes[0].row + 1}`;
  } else {
    const row = Math.min(firstNode.row, secondNode.row) + 1;
    domino.style.gridColumn = `${orderedNodes[0].column + 1}`;
    domino.style.gridRow = `${row} / span 2`;
  }

  domino.append(
    renderHalfDomino(placement.values[orderedNodes[0].id], true),
    renderHalfDomino(placement.values[orderedNodes[1].id], false)
  );

  return domino;
}

function orderedPlacementNodes(firstNode, secondNode, orientation) {
  return [firstNode, secondNode].sort((left, right) => {
    if (orientation === "horizontal") return left.column - right.column;
    return left.row - right.row;
  });
}

function renderHalfDomino(value, isFirst) {
  const half = document.createElement("div");
  half.className = [
    "Domino-module_halfDomino__FWnOS",
    isFirst ? "Domino-module_isFirst__qiM7f" : ""
  ].filter(Boolean).join(" ");
  half.setAttribute("aria-label", String(value));

  const dots = document.createElement("div");
  dots.className = `Domino-module_dotsWrapper__kkdAC domino-dots domino-dots-${value}`;

  for (let i = 0; i < value; i += 1) {
    const dot = document.createElement("span");
    dot.className = `Domino-module_dot__z3BLH domino-dot ${dominoDotPositionClass(value, i)}`;
    dots.appendChild(dot);
  }

  half.appendChild(dots);
  return half;
}

function dominoDotPositionClass(value, index) {
  if (value === 1) return "Domino-module_middle__0bq7B";
  if (value === 2) return index === 0 ? "Domino-module_topLeft__6Ke73" : "Domino-module_bottomRight__d7pPA";
  if (value === 3) return ["Domino-module_topLeft__6Ke73", "Domino-module_middle__0bq7B", "Domino-module_bottomRight__d7pPA"][index];
  if (value === 4) return [
    "Domino-module_topLeft__6Ke73",
    "Domino-module_topRight__j3Pw9",
    "Domino-module_bottomLeft__qjL6t",
    "Domino-module_bottomRight__d7pPA"
  ][index];
  if (value === 5) return [
    "Domino-module_topLeft__6Ke73",
    "Domino-module_topRight__j3Pw9",
    "Domino-module_middle__0bq7B",
    "Domino-module_bottomLeft__qjL6t",
    "Domino-module_bottomRight__d7pPA"
  ][index];
  return [
    "Domino-module_topLeft__6Ke73",
    "Domino-module_topRight__j3Pw9",
    "Domino-module_middleLeft__L5amZ",
    "Domino-module_middleRight__jjcVI",
    "Domino-module_bottomLeft__qjL6t",
    "Domino-module_bottomRight__d7pPA"
  ][index] ?? "";
}

function dominoOrientation(firstNodeId, secondNodeId) {
  const first = nodeIndex(firstNodeId);
  const second = nodeIndex(secondNodeId);
  return Math.abs(first - second) === 1 ? "horizontal" : "vertical";
}

function setStatus(status) {
  statusEl.textContent = status;
  STATUS_CLASSES.forEach(cls => statusEl.classList.remove(cls));
  statusEl.classList.add(status.toLowerCase());
}

async function readStateFromCurrentTab() {
  return sendMessageToCurrentTab({ type: "READ_PIPS_STATE" });
}

async function sendMessageToCurrentTab(message) {
  const [tab] = await chrome.tabs.query({
    active: true,
    currentWindow: true
  });

  if (!tab?.id) {
    throw new Error("No active tab found");
  }

  const response = await chrome.tabs.sendMessage(tab.id, message);

  if (!response?.ok) {
    throw new Error(response?.error || "The NYT tab did not accept the request");
  }

  return response;
}

function nodeGridIndex(node, board) {
  if (Number.isFinite(node)) return node;
  if (Number.isFinite(node.index)) return node.index;
  if (Number.isFinite(node.row) && Number.isFinite(node.column) && board.columns) {
    return node.row * board.columns + node.column;
  }
  return nodeIndex(node.id);
}

function nodeIndex(id) {
  if (Number.isFinite(id)) return id;
  const match = String(id).match(/^node-(\d+)$/);
  return match ? Number(match[1]) : -1;
}

function normalizeBoardNode(node, board) {
  const index = nodeGridIndex(node, board);
  if (typeof node === "object" && node !== null) {
    return {
      ...node,
      id: node.id ?? index,
      index,
      row: Number.isFinite(node.row) ? node.row : board.columns ? Math.floor(index / board.columns) : null,
      column: Number.isFinite(node.column) ? node.column : board.columns ? index % board.columns : null
    };
  }

  return {
    id: index,
    index,
    row: board.columns ? Math.floor(index / board.columns) : null,
    column: board.columns ? index % board.columns : null
  };
}

function boardDimensions(board, nodesByIndex) {
  if (board.rows && board.columns) {
    return {
      rows: board.rows,
      columns: board.columns
    };
  }

  const maxIndex = Math.max(...nodesByIndex.keys(), 0);
  const side = Math.ceil(Math.sqrt(maxIndex + 1));

  return {
    rows: side,
    columns: side
  };
}

// ── Puzzle JSON → game state conversion ──────────────────────────────────────

function puzzleToGameState(puzzle) {
  // Collect all active [row, col] cells from all regions
  const activeSet = new Set();
  for (const region of puzzle.regions ?? []) {
    for (const [row, col] of region.indices ?? []) {
      activeSet.add(`${row},${col}`);
    }
  }

  const activeCells = Array.from(activeSet).map((key) => {
    const [row, col] = key.split(",").map(Number);
    return { row, col };
  }).sort((a, b) => a.row - b.row || a.col - b.col);

  const rows = Math.max(...activeCells.map((c) => c.row)) + 1;
  const columns = Math.max(...activeCells.map((c) => c.col)) + 1;

  const nodeId = (row, col) => row * columns + col;
  const nodes = activeCells.map(({ row, col }) => nodeId(row, col));
  const edges = [];
  for (const { row, col } of activeCells) {
    const id = nodeId(row, col);
    if (activeSet.has(`${row},${col + 1}`)) edges.push([id, nodeId(row, col + 1)]);
    if (activeSet.has(`${row + 1},${col}`)) edges.push([id, nodeId(row + 1, col)]);
  }

  const dominoes = (puzzle.dominoes ?? []).map(([top, bottom], i) => ({
    id: `domino-${i + 1}`,
    top,
    bottom
  }));

  const constraints = (puzzle.regions ?? [])
    .filter((r) => r.type !== "empty")
    .map((region) => {
      const nodes = (region.indices ?? []).map(([row, col]) => nodeId(row, col));
      let constraint = null;
      if (region.type === "equals") {
        constraint = { type: "equal" };
      } else if (region.type === "unequal") {
        constraint = { type: "unequal" };
      } else if (region.type === "sum") {
        constraint = { type: "sum", sign: "=", value: region.target };
      } else if (region.type === "less") {
        constraint = { type: "sum", sign: "<", value: region.target };
      } else if (region.type === "greater") {
        constraint = { type: "sum", sign: ">", value: region.target };
      }
      return constraint ? { nodes, constraint } : null;
    })
    .filter(Boolean);

  return { board: { rows, columns, nodes, edges }, dominoes, constraints };
}

// ── Test runner ───────────────────────────────────────────────────────────────

async function runPuzzleTests() {
  testButton.disabled = true;
  testSection.classList.remove("hidden");
  testResultsEl.innerHTML = "<em>Loading puzzles…</em>";

  let puzzles;
  try {
    const url = chrome.runtime.getURL("pips_puzzles.json");
    const res = await fetch(url);
    puzzles = await res.json();
  } catch (err) {
    testResultsEl.innerHTML = `<span class="test-error">Failed to load puzzles: ${err.message}</span>`;
    testButton.disabled = false;
    return;
  }

  testResultsEl.innerHTML = "";
  testFailuresEl.innerHTML = "";
  testFailuresEl.classList.add("hidden");

  const difficulties = ["easy_puzzle", "medium_puzzle", "hard_puzzle"];
  const testCases = puzzles.flatMap((puzzle) =>
    difficulties
      .filter((difficulty) => puzzle[difficulty])
      .map((difficulty) => ({
        puzzle,
        difficulty,
        sub: puzzle[difficulty],
        date: puzzle.print_date,
        difficultyLabel: difficulty.replace("_puzzle", ""),
        label: `${puzzle.print_date} ${difficulty.replace("_puzzle", "")} (#${puzzle.id})`
      }))
  );
  const total = testCases.length;
  const savedRun = loadTestRun();
  const shouldResume = savedRun?.total === total && savedRun.completed < total;
  const rows = shouldResume ? savedRun.rows ?? [] : [];
  let passed = rows.filter((row) => row.ok).length;
  let failed = rows.filter((row) => !row.ok).length;
  let completed = rows.length;
  const summary = document.createElement("div");
  summary.className = "test-summary";
  summary.textContent = formatTestSummary(completed, total, passed, failed);
  testResultsEl.appendChild(summary);
  updateTestProgress(completed, total);
  renderSavedTestRows(rows);
  renderFailureRows(rows);

  for (const testCase of testCases.slice(completed)) {
    const gameState = puzzleToGameState(testCase.sub);

    const result = {
      label: testCase.label,
      date: testCase.date,
      difficulty: testCase.difficultyLabel,
      ok: true,
      message: ""
    };

    try {
      window.PipsSolver.solve(gameState, { timeoutMs: TEST_SOLVE_TIMEOUT_MS });
      passed++;
    } catch (err) {
      result.ok = false;
      result.message = String(err?.message ?? err);
      failed++;
    }

    completed++;
    rows.push(result);
    testResultsEl.appendChild(createTestRow(result));
    if (!result.ok) appendFailureRow(result);
    summary.textContent = formatTestSummary(completed, total, passed, failed);
    updateTestProgress(completed, total);
    saveTestRun({ total, completed, rows });
    await nextFrame();
  }

  summary.textContent = formatTestSummary(completed, total, passed, failed);
  updateTestProgress(completed, total);
  saveTestRun({ total, completed, rows });

  testButton.disabled = false;
}

function restorePopupState() {
  let restored = false;
  const saved = loadJson(POPUP_STATE_KEY);
  if (saved?.currentState?.board?.nodes) {
    currentState = saved.currentState;
    solveButton.disabled = false;
    renderState(currentState, saved.solution ?? null);
    setStatus(saved.status ?? "Detected");
    restored = true;
  }

  const testRun = loadTestRun();
  if (testRun?.rows?.length) {
    testSection.classList.remove("hidden");
    testResultsEl.innerHTML = "";
    testFailuresEl.innerHTML = "";
    testFailuresEl.classList.add("hidden");
    const passed = testRun.rows.filter((row) => row.ok).length;
    const failed = testRun.rows.filter((row) => !row.ok).length;
    const summary = document.createElement("div");
    summary.className = "test-summary";
    summary.textContent = formatTestSummary(testRun.completed, testRun.total, passed, failed);
    testResultsEl.appendChild(summary);
    updateTestProgress(testRun.completed, testRun.total);
    renderSavedTestRows(testRun.rows);
    renderFailureRows(testRun.rows);
    restored = true;
  }

  return restored;
}

function renderSavedTestRows(rows) {
  for (const row of rows) {
    testResultsEl.appendChild(createTestRow(row));
  }
}

function renderFailureRows(rows) {
  for (const row of rows) {
    if (!row.ok) appendFailureRow(row);
  }
}

function appendFailureRow(result) {
  if (testFailuresEl.classList.contains("hidden")) {
    testFailuresEl.classList.remove("hidden");
    const heading = document.createElement("div");
    heading.className = "test-failures-label";
    heading.textContent = "Failures";
    testFailuresEl.appendChild(heading);
  }

  testFailuresEl.appendChild(createTestRow(result));
}

function createTestRow(result) {
  const row = document.createElement("div");
  row.className = "test-row";

  const badge = document.createElement("span");
  badge.className = `test-badge ${result.ok ? "pass" : "fail"}`;
  badge.textContent = result.ok ? "✓" : "✗";
  row.appendChild(badge);

  const text = document.createElement("span");
  const failureLabel = result.date && result.difficulty
    ? `${result.date} ${result.difficulty}`
    : result.label;
  text.textContent = result.ok ? result.label : `${failureLabel} — ${result.message}`;
  row.appendChild(text);

  return row;
}

function formatTestSummary(completed, total, passed, failed) {
  return `${completed}/${total} solved, ${passed} passed, ${failed} failed`;
}

function loadTestRun() {
  return loadJson(TEST_RUN_KEY);
}

function saveTestRun(testRun) {
  saveJson(TEST_RUN_KEY, testRun);
}

function savePopupState(state) {
  saveJson(POPUP_STATE_KEY, state);
}

function loadJson(key) {
  try {
    return JSON.parse(localStorage.getItem(key) || "null");
  } catch {
    return null;
  }
}

function saveJson(key, value) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
  } catch {
    // The popup still works without persistence if extension storage is unavailable.
  }
}

function updateTestProgress(completed, total) {
  const percent = total ? Math.round((completed / total) * 100) : 0;
  testProgressEl.classList.remove("hidden");
  testProgressEl.setAttribute("aria-valuenow", String(percent));
  testProgressEl.setAttribute("aria-label", `${completed} of ${total} puzzle tests complete`);
  testProgressFillEl.style.width = `${percent}%`;
}

function nextFrame() {
  return new Promise((resolve) => requestAnimationFrame(resolve));
}
