# Untitled

## Bare-bones Lean HTTP server

Run from this directory:

```bash
lake build lean_http_server
lake exe lean_http_server
```

Server listens on `http://127.0.0.1:8765`.

Routes:

- `GET /health` -> `{"ok":true}`
- `GET /lean/version` -> `{"leanVersion":"..."}`
- `POST /game-state` -> stores posted JSON in memory and returns `{"ok":true,"storedState":<your-json>}`
- `GET /game-state` -> returns `{"ok":true,"state":<latest-json-or-null>}`
- `OPTIONS *` for CORS preflight

Quick test:

```bash
curl http://127.0.0.1:8765/health
curl http://127.0.0.1:8765/lean/version
curl -X POST http://127.0.0.1:8765/game-state \
  -H "Content-Type: application/json" \
  --data '{"board":{"nodes":[{"id":"node-0"}]},"dominoes":[],"dominoNodeMap":{},"constraints":[]}'
curl http://127.0.0.1:8765/game-state
```
