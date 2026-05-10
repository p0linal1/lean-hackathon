# Genuinely Goated Lean Pips Solver

A formally verified puzzle solver for the New York Times **Pips** game, built with Lean 4 and delivered as a Chrome extension.

## What is this?

Pips is a NYT puzzle where you place dominoes on a grid subject to constraints (sums, equalities, inequalities). This project solves any Pips puzzle instantly using a backtracking solver written in Lean 4 — with mathematical proofs that the solver produces correct solutions.

## Architecture

The project has two parts:

1. **Lean 4 Backend** — An HTTP server that accepts puzzle state as JSON and returns a verified solution using constraint-propagation backtracking with parallelization.

2. **Chrome Extension** — Reads the puzzle state directly from the NYT Pips page DOM, sends it to the Lean server, and displays the solution with animated domino placements.

## How the Solver Works

- Parses the puzzle into a formal graph structure (nodes, edges, dominoes, constraints)
- Uses a **backtracking search** with:
  - Most-constrained-first node ordering
  - Early pruning via partial constraint checking
  - Dead-end detection (nodes with no viable placements)
  - Domino multiset grouping to avoid redundant permutations
- **Parallelizes** first-move exploration across multiple tasks
- Returns a valid assignment mapping each domino to a pair of adjacent nodes

### Constraint Types

| Type | Description |
|------|-------------|
| `sum` | Sum of node values equals / is less than / is greater than a target |
| `equiv` | All nodes in a group must have the same value |
| `not_equiv` | All nodes in a group must have distinct values |

### Formal Verification

The solver includes a two-layer formalization in Lean 4:
- **Spec layer** — Prop-based definitions for theorem proving (`ValidAssignment`, `SatisfiesConstraint`, `Solvable`)
- **Implementation layer** — Bool-returning decision procedures for execution
- **Bridge layer** — Proofs that the implementation correctly decides the spec predicates

#### What's Proven

| Property | Branch | Description |
|----------|--------|-------------|
| **Correctness** | `main` | Any solution returned by the solver is valid — placements satisfy all constraints |
| **Completeness** | `completeness-proof` | If a valid solution exists, the (less optimized) solver will find it — it never incorrectly reports "no solution" |

#### Tags

| Tag | Description |
|-----|-------------|
| `completeness-proof-done` | Completeness proof achieved for the unoptimized solver |

## Installation

### Prerequisites

- [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) (v4.30.0-rc2)
- Google Chrome or Chromium-based browser

### 1. Build and run the Lean server

```bash
cd lean/Untitled
lake build lean_http_server
lake exe lean_http_server
```

The server starts on `http://127.0.0.1:8765` with these routes:
- `GET /health` — health check
- `POST /solve` — solve a puzzle (accepts JSON body)
- `GET /lean/version` — Lean version info

### 2. Install the Chrome extension

1. Open `chrome://extensions` in Chrome
2. Enable **Developer mode** (toggle in top-right)
3. Click **Load unpacked**
4. Select the `extension/` folder from this repo

### 3. Use it

1. Navigate to a [NYT Pips puzzle](https://www.nytimes.com/games/pips)
2. Click the extension icon to open the side panel
3. The puzzle state is detected automatically
4. Click **Solve** — the solution appears with a rolling ball animation

## Project Structure

```
├── extension/           # Chrome extension
│   ├─�� manifest.json    # Extension manifest (MV3)
│   ├── content.js       # Reads puzzle state from NYT DOM
│   ���── popup.js         # Extension UI + solver communication
│   ��── popup.html       # Side panel interface
│   ├─��� popup.css        # Styling + animations
│   └── background.js    # Service worker
│
├── lean/Untitled/       # Lean 4 project
│   ├── lakefile.toml    # Build configuration
│   ├── lean-toolchain   # Lean version pin
│   ├── LeanHttpServer.lean  # HTTP server + JSON parsing
│   └── Untitled/
│       ├── Pips.lean    # Core types, predicates, proofs
│       └── Solver.lean  # Backtracking solver implementation
│
└── pips_puzzles.json    # Test puzzle database
```

## API

### `POST /solve`

**Request:**
```json
{
  "board": {
    "nodes": [5, 6, 7, 8],
    "edges": [[5, 6], [7, 8]]
  },
  "dominoes": [
    {"id": "domino-1", "top": 4, "bottom": 0}
  ],
  "constraints": [
    {"nodes": [5, 6], "constraint": {"type": "equal"}}
  ]
}
```

**Response:**
```json
{
  "ok": true,
  "solved": true,
  "assignment": [
    {"domino": {"left": 4, "right": 0}, "fst": 5, "snd": 6}
  ]
}
```

## Testing

The extension includes a batch test mode that runs the solver against a database of known puzzles (`pips_puzzles.json`). Open the extension and click **Test puzzles** to run.
