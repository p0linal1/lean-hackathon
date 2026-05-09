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
- `OPTIONS *` for CORS preflight

Quick test:

```bash
curl http://127.0.0.1:8765/health
curl http://127.0.0.1:8765/lean/version
```
