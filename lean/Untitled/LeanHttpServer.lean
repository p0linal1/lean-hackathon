import Lean
import Lean.Data.Json
import Std
import Std.Internal.Async.TCP

open Std
open Std.Net
open Std.Internal.IO.Async
open Std.Internal.IO.Async.TCP

namespace LeanHttpServer

def defaultPort : UInt16 := UInt16.ofNat 8765

def localhost (port : UInt16) : SocketAddress :=
  .v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := port }

def buildResponse (status : String) (body : String) (contentType : String := "application/json") : String :=
  let contentLength := body.toUTF8.size
  String.intercalate "\r\n"
    [ s!"HTTP/1.1 {status}"
    , s!"Content-Type: {contentType}"
    , s!"Content-Length: {contentLength}"
    , "Access-Control-Allow-Origin: *"
    , "Access-Control-Allow-Methods: GET, POST, OPTIONS"
    , "Access-Control-Allow-Headers: Content-Type"
    , "Connection: close"
    , ""
    , body
    ]

def parseRequestLine (raw : String) : String × String :=
  let firstLine := (raw.splitOn "\r\n").headD ""
  let parts := firstLine.splitOn " "
  (parts.getD 0 "", parts.getD 1 "/")

def parseRequestBody (raw : String) : String :=
  let parts := raw.splitOn "\r\n\r\n"
  String.intercalate "\r\n\r\n" (parts.drop 1)

def jsonResponse (status : String) (json : Lean.Json) : String :=
  buildResponse status json.compress

def errorResponse (status : String) (message : String) : String :=
  jsonResponse status <| .mkObj [("error", message)]

def handleRequest (stateRef : IO.Ref (Option Lean.Json)) (method path body : String) : IO String := do
  if method = "OPTIONS" then
    pure <| buildResponse "204 No Content" "" "text/plain"
  else if method = "GET" && path = "/health" then
    pure <| jsonResponse "200 OK" <| .mkObj [("ok", true)]
  else if method = "GET" && path = "/lean/version" then
    pure <| jsonResponse "200 OK" <| .mkObj [("leanVersion", Lean.versionString)]
  else if method = "POST" && path = "/solve" then
    match Lean.Json.parse body with
    | .error err =>
      pure <| errorResponse "400 Bad Request" s!"Invalid JSON body: {err}"
    | .ok json =>
      stateRef.set (some json)
      pure <| jsonResponse "200 OK" <| .mkObj
        [ ("ok", true)
        , ("solverImplemented", false)
        , ("solvedState", json)
        ]
  else if method = "GET" && path = "/solve" then
    match ← stateRef.get with
    | some json =>
      pure <| jsonResponse "200 OK" <| .mkObj
        [ ("ok", true)
        , ("solverImplemented", false)
        , ("solvedState", json)
        ]
    | none =>
      pure <| jsonResponse "200 OK" <| .mkObj
        [ ("ok", true)
        , ("solverImplemented", false)
        , ("solvedState", Lean.Json.null)
        ]
  else
    pure <| errorResponse "404 Not Found" s!"No route for {method} {path}"

def readRequest (client : Socket.Client) : IO String := do
  let chunk? ← Async.block (Socket.Client.recv? client 65536)
  match chunk? with
  | none => pure ""
  | some chunk => pure <| (String.fromUTF8? chunk).getD ""

def respond (client : Socket.Client) (message : String) : IO Unit := do
  Async.block (Socket.Client.send client message.toUTF8)
  try
    Async.block (Socket.Client.shutdown client)
  catch _ =>
    pure ()

def handleClient (stateRef : IO.Ref (Option Lean.Json)) (client : Socket.Client) : IO Unit := do
  try
    let raw ← readRequest client
    let body := parseRequestBody raw
    let (method, path) := parseRequestLine raw
    let response ← handleRequest stateRef method path body
    respond client response
  catch err =>
    IO.eprintln s!"[lean-http-server] client error: {err}"

partial def serveLoop (stateRef : IO.Ref (Option Lean.Json)) (server : Socket.Server) : IO Unit := do
  try
    let client ← Async.block (Socket.Server.accept server)
    handleClient stateRef client
  catch err =>
    IO.eprintln s!"[lean-http-server] accept error: {err}"
  serveLoop stateRef server

def run : IO Unit := do
  let stateRef ← IO.mkRef (none : Option Lean.Json)
  let server ← Socket.Server.mk
  server.bind (localhost defaultPort)
  server.listen 128
  IO.println s!"lean-http-server listening on http://127.0.0.1:{defaultPort}/"
  IO.println "routes: GET /health, GET /lean/version, POST /solve, GET /solve, OPTIONS *"
  serveLoop stateRef server

end LeanHttpServer

def main : IO Unit :=
  LeanHttpServer.run
