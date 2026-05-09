# NYT Pips State Logger

Minimal unpacked Chrome extension that logs NYT Pips state from the page DOM.

## Install

1. Open `chrome://extensions`.
2. Enable **Developer mode**.
3. Click **Load unpacked**.
4. Select this `extension` folder.
5. Open NYT Pips and check DevTools Console.

## Console helpers

- `window.__nytPipsState` contains the latest logged snapshot.
- `window.__nytPipsReadState()` reads and logs the current snapshot on demand.

The logged snapshot includes:

- `board`: active node ids with `left`, `right`, `up`, and `down` links
- `dominoes`: `{ id, top, bottom }`
- `dominoNodeMap`: domino id to `[topNode, bottomNode]`
- `constraints`: `{ nodes, constraint }`, where constraint is either `{ type: "equal" }` or `{ type: "sum", sign, value }`
