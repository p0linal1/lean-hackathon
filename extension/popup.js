let currentState = null;
const LEAN_SERVER_STATE_URL = "http://127.0.0.1:8765/game-state";

const readButton = document.querySelector("#readButton");
const solveButton = document.querySelector("#solveButton");
const statusEl = document.querySelector("#status");
const summaryEl = document.querySelector("#summary");
const boardEl = document.querySelector("#board");
const boardSection = document.querySelector("#board-section");
const dominoesEl = document.querySelector("#dominoes");
const dominoesSection = document.querySelector("#dominoes-section");
const debugEl = document.querySelector("#debug");

readButton.addEventListener("click", readPuzzle);
solveButton.addEventListener("click", solvePuzzle);

async function readPuzzle() {
  setStatus("Reading");

  try {
    const response = await readStateFromCurrentTab().catch(readStateFromLeanServer);

    currentState = response.state;
    solveButton.disabled = !currentState?.board?.nodes?.length;

    renderState(currentState);
    setStatus("Detected");
  } catch (error) {
    setStatus("Error");
    debugEl.textContent = String(error?.message ?? error);
  }
}

function solvePuzzle() {
  if (!currentState?.board?.nodes) return;

  setStatus("Solving");

  // Temporary mock solution until solver is ready.
  const mockSolution = {
    valuesByNodeId: Object.fromEntries(
      currentState.board.nodes.map((node, index) => [
        node.id,
        index % 7
      ])
    )
  };

  renderState(currentState, mockSolution);
  setStatus("Solved");
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

  if (!payload?.ok || !payload.state) {
    throw new Error("Lean server has no stored Pips state yet");
  }

  return {
    ok: true,
    state: payload.state
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
