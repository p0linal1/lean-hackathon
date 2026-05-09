# NYT Pips State Logger

Minimal unpacked Chrome extension that logs NYT Pips state from the page DOM and submits it to the local Lean HTTP server.

## Install

1. Open `chrome://extensions`.
2. Enable **Developer mode**.
3. Click **Load unpacked**.
4. Select this `extension` folder.
5. Start the Lean server from `../lean/Untitled`:

```bash
lake exe lean_http_server
```

6. Open NYT Pips and check DevTools Console.

## Console helpers

- `window.__nytPipsState` contains the latest logged snapshot.
- `window.__nytPipsReadState()` reads and logs the current snapshot on demand.
- `window.__nytPipsSubmitState()` reads and submits the current snapshot to `http://127.0.0.1:8765/solve`.

The popup asks `content.js` for the current state, so it uses the same board detection path as the page logger. `solver.js` adds an in-page **Solve with brute force** button next to the puzzle, calls the local Lean `/solve` endpoint, and renders the returned solved state.

The logged snapshot includes:

- `board`: active node ids with `left`, `right`, `up`, and `down` links
- `dominoes`: `{ id, top, bottom }`
- `dominoNodeMap`: domino id to `{ Top: topNode, Bottom: bottomNode }`
- `constraints`: `{ nodes, constraint }`, where constraint is either `{ type: "equal" }` or `{ type: "sum", sign, value }`
