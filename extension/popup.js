let currentState = null;
const LEAN_SERVER_STATE_URL = "http://127.0.0.1:8765/solve";
const POPUP_STATE_KEY = "pipsHelper.popupState.v1";
const TEST_RUN_KEY = "pipsHelper.testRun.v1";
const TEST_SOLVE_TIMEOUT_MS = 10000;

const readButton = document.querySelector("#readButton");
const solveButton = document.querySelector("#solveButton");
const testButton = document.querySelector("#testButton");
const statusEl = document.querySelector("#status");
const summaryEl = document.querySelector("#summary");
const boardEl = document.querySelector("#board");
const boardSection = document.querySelector("#board-section");
const dominoesEl = document.querySelector("#dominoes");
const dominoesSection = document.querySelector("#dominoes-section");
const testSection = document.querySelector("#test-section");
const testProgressEl = document.querySelector("#test-progress");
const testProgressFillEl = document.querySelector("#test-progress-fill");
const testFailuresEl = document.querySelector("#test-failures");
const testResultsEl = document.querySelector("#test-results");
const debugEl = document.querySelector("#debug");

readButton.addEventListener("click", readPuzzle);
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
    const response = await readStateFromCurrentTab().catch(readStateFromLeanServer);

    currentState = response.state;
    solveButton.disabled = !currentState?.board?.nodes?.length;

    renderState(currentState);
    savePopupState({ currentState, solution: null, status: "Detected" });
    setStatus("Detected");
  } catch (error) {
    if (!options.preserveOnError) setStatus("Error");
    debugEl.textContent = String(error?.message ?? error);
  }
}

function solvePuzzle() {
  if (!currentState?.board?.nodes) return;

  setStatus("Solving");

  try {
    const solution = window.PipsSolver.solve(currentState);
    renderState(currentState, { valuesByNodeId: solution.valuesByNode });
    savePopupState({
      currentState,
      solution: { valuesByNodeId: solution.valuesByNode },
      status: "Solved"
    });
    setStatus("Solved");
  } catch (error) {
    setStatus("Error");
    debugEl.textContent = String(error?.message ?? error);
  }
}

function renderState(state, solution = null) {
  const board = state.board;
  const activeNodeCount = board?.nodes?.length ?? 0;

  const pills = [
    `Board: ${board?.rows ?? "?"} × ${board?.columns ?? "?"}`,
    `Cells: ${activeNodeCount}`,
    `Constraints: ${state.constraints?.length ?? 0}`,
    `Dominoes: ${state.dominoes?.length ?? 0}`,
  ];
  summaryEl.innerHTML = pills
    .map(text => `<span class="summary-pill">${text}</span>`)
    .join("");

  renderBoard(board, solution);
  renderDominoes(state.dominoes ?? []);

  boardSection.classList.toggle("hidden", !Array.isArray(board?.nodes));
  dominoesSection.classList.toggle("hidden", !(state.dominoes?.length));

  debugEl.textContent = JSON.stringify(state, null, 2);
}

function renderBoard(board, solution) {
  boardEl.innerHTML = "";

  if (!Array.isArray(board?.nodes)) {
    boardEl.textContent = "No board detected";
    return;
  }

  const nodesByIndex = new Map(
    board.nodes.map((node) => [nodeGridIndex(node, board), node])
  );
  const dimensions = boardDimensions(board, nodesByIndex);

  boardEl.style.gridTemplateColumns = `repeat(${dimensions.columns}, 1fr)`;

  for (let index = 0; index < dimensions.rows * dimensions.columns; index += 1) {
    const node = nodesByIndex.get(index);
    const div = document.createElement("div");
    div.className = node ? "cell" : "cell hidden";
    div.textContent = node && solution?.valuesByNodeId?.[node.id] !== undefined
      ? solution.valuesByNodeId[node.id]
      : "";

    boardEl.appendChild(div);
  }
}

function renderDominoes(dominoes) {
  dominoesEl.innerHTML = "";

  for (const domino of dominoes) {
    const tile = document.createElement("div");
    tile.className = "domino";
    tile.textContent = `${domino.top} | ${domino.bottom}`;
    dominoesEl.appendChild(tile);
  }
}

const STATUS_CLASSES = ["reading", "detected", "solving", "solved", "error"];

function setStatus(status) {
  statusEl.textContent = status;
  STATUS_CLASSES.forEach(cls => statusEl.classList.remove(cls));
  statusEl.classList.add(status.toLowerCase());
}

async function readStateFromCurrentTab() {
  const [tab] = await chrome.tabs.query({
    active: true,
    currentWindow: true
  });

  if (!tab?.id) {
    throw new Error("No active tab found");
  }

  const response = await chrome.tabs.sendMessage(tab.id, {
    type: "READ_PIPS_STATE"
  });

  if (!response?.ok) {
    throw new Error(response?.error || "Could not read state from the NYT tab");
  }

  return response;
}

async function readStateFromLeanServer() {
  const response = await fetch(LEAN_SERVER_STATE_URL);

  if (!response.ok) {
    throw new Error(`Lean server returned HTTP ${response.status}`);
  }

  const payload = await response.json();

  if (!payload?.ok || !payload.solvedState) {
    throw new Error("Lean server has no stored Pips state yet");
  }

  return {
    ok: true,
    state: payload.solvedState
  };
}

function nodeGridIndex(node, board) {
  if (Number.isFinite(node.index)) return node.index;
  if (Number.isFinite(node.row) && Number.isFinite(node.column) && board.columns) {
    return node.row * board.columns + node.column;
  }
  return nodeIndex(node.id);
}

function nodeIndex(id) {
  const match = String(id).match(/^node-(\d+)$/);
  return match ? Number(match[1]) : -1;
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

  const nodeId = (row, col) => `node-${row * columns + col}`;

  const nodes = activeCells.map(({ row, col }) => ({
    id: nodeId(row, col),
    index: row * columns + col,
    row,
    column: col,
    left: activeSet.has(`${row},${col - 1}`) ? nodeId(row, col - 1) : null,
    right: activeSet.has(`${row},${col + 1}`) ? nodeId(row, col + 1) : null,
    up: activeSet.has(`${row - 1},${col}`) ? nodeId(row - 1, col) : null,
    down: activeSet.has(`${row + 1},${col}`) ? nodeId(row + 1, col) : null
  }));

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

  return { board: { rows, columns, nodes }, dominoes, constraints };
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
