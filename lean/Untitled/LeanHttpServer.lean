import Lean
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

def handleRequest (method path : String) : String :=
  if method = "OPTIONS" then
    buildResponse "204 No Content" "" "text/plain"
  else if method = "GET" && path = "/health" then
    buildResponse "200 OK" "{\"ok\":true}"
  else if method = "GET" && path = "/lean/version" then
    buildResponse "200 OK" ("{\"leanVersion\":\"" ++ Lean.versionString ++ "\"}")
  else
    buildResponse "404 Not Found" ("{\"error\":\"No route for " ++ method ++ " " ++ path ++ "\"}")

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

def handleClient (client : Socket.Client) : IO Unit := do
  try
    let raw ← readRequest client
    let (method, path) := parseRequestLine raw
    let response := handleRequest method path
    respond client response
  catch err =>
    IO.eprintln s!"[lean-http-server] client error: {err}"

partial def serveLoop (server : Socket.Server) : IO Unit := do
  try
    let client ← Async.block (Socket.Server.accept server)
    handleClient client
  catch err =>
    IO.eprintln s!"[lean-http-server] accept error: {err}"
  serveLoop server

def run : IO Unit := do
  let server ← Socket.Server.mk
  server.bind (localhost defaultPort)
  server.listen 128
  IO.println s!"lean-http-server listening on http://127.0.0.1:{defaultPort}/"
  IO.println "routes: GET /health, GET /lean/version, OPTIONS *"
  serveLoop server

end LeanHttpServer

def main : IO Unit :=
  LeanHttpServer.run
