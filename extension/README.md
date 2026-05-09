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

- board shape: rows, columns, hidden/active cell mask, and indexed cells
- constraints: visible constraint-like DOM nodes with text, labels, classes, and overlapping cell indexes when detectable
- dominoes: tray domino ids, pip values, rotation, and half element ids
