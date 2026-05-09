import Lean
import Lean.Data.Json
import Std
import Std.Internal.Async.TCP
import pips

open Std
open Std.Net
open Std.Internal.IO.Async
open Std.Internal.IO.Async.TCP

-- ── Frontend JSON → Lean-Pips conversion ─────────────────────────────────────
--
-- The frontend sends game states with this shape:
--   board.nodes[]: Nat[]   (flat grid indices)
--   board.edges[]: [Nat, Nat][]  (normalized pairs, a ≤ b)
--   dominoes[]:    { id, top: Nat, bottom: Nat }
--   constraints[]: { nodes: Nat[],
--                    constraint: { type: "equal"|"unequal"|"sum", sign?, value? } }
--
-- We convert to:
--   Pip        { nodes : List Node, edges : List (Node × Node) }
--   List Domino  { left right : Nat }   (top→left, bottom→right)
--   List Constraint (equiv | allNeq | sum)

namespace PipsConvert

private def intToNat? : Int → Option Nat
  | .ofNat n => some n
  | _        => none

private def jsonNat? (j : Lean.Json) : Option Nat :=
  match j with
  | .num jn => if jn.exponent == 0 then intToNat? jn.mantissa else none
  | _       => none

-- ── Pip (nodes + edges) ──────────────────────────────────────────────────────

def parsePip (json : Lean.Json) : Except String Pip := do
  let boardJ ← json.getObjVal? "board"

  let nodesArr ← match ← boardJ.getObjVal? "nodes" with
    | .arr a => pure a
    | _      => throw "board.nodes is not an array"
  let nodes ← nodesArr.toList.mapM fun n => do
    match jsonNat? n with
    | some id => pure (Node.mk id)
    | none    => throw s!"board.nodes element is not a nat: {n}"

  let edgesArr ← match ← boardJ.getObjVal? "edges" with
    | .arr a => pure a
    | _      => throw "board.edges is not an array"
  let edges ← edgesArr.toList.mapM fun e => do
    let pair ← match e with
      | .arr a => pure a
      | _      => throw "edge is not an array"
    let a ← match pair[0]? with
      | some j => match jsonNat? j with
        | some n => pure n | none => throw "edge[0] is not a nat"
      | none => throw "edge has no element 0"
    let b ← match pair[1]? with
      | some j => match jsonNat? j with
        | some n => pure n | none => throw "edge[1] is not a nat"
      | none => throw "edge has no element 1"
    return normalizeEdge (Node.mk a) (Node.mk b)

  return { nodes, edges }

-- ── Dominoes ─────────────────────────────────────────────────────────────────

def parseDominoes (json : Lean.Json) : Except String (List Domino) := do
  let arr ← match ← json.getObjVal? "dominoes" with
    | .arr a => pure a
    | _      => throw "dominoes is not an array"
  arr.toList.mapM fun d => do
    let top    ← match jsonNat? (← d.getObjVal? "top") with
      | some n => pure n | none => throw "domino top is not a nat"
    let bottom ← match jsonNat? (← d.getObjVal? "bottom") with
      | some n => pure n | none => throw "domino bottom is not a nat"
    return { left := top, right := bottom }

-- ── Constraints ──────────────────────────────────────────────────────────────

def parseConstraints (json : Lean.Json) : Except String (List Constraint) := do
  let arr ← match ← json.getObjVal? "constraints" with
    | .arr a => pure a
    | _      => throw "constraints is not an array"
  let maybes ← arr.toList.mapM fun c => do
    let nodesArr ← match ← c.getObjVal? "nodes" with
      | .arr a => pure a
      | _      => throw "constraint nodes is not an array"
    let nodes ← nodesArr.toList.mapM fun n => do
      match jsonNat? n with
      | some id => pure (Node.mk id)
      | none    => throw s!"constraint node is not a nat: {n}"
    let cJ  ← c.getObjVal? "constraint"
    let ty  ← match ← cJ.getObjVal? "type" with
      | .str s => pure s | _ => throw "constraint type not a string"
    match ty with
    | "equal"   => return some (Constraint.equiv nodes)
    | "unequal" => return some (Constraint.allNeq nodes)
    | "sum"     =>
        let value ← match jsonNat? (← cJ.getObjVal? "value") with
          | some n => pure n | none => throw "sum value is not a nat"
        let sign : String := match cJ.getObjVal? "sign" with
          | .ok (.str s) => s | _ => "="
        let cmpTy := match sign with
          | "<" => SumConstraintType.lt
          | ">" => SumConstraintType.gt
          | _   => SumConstraintType.eq
        return some (Constraint.sum nodes value cmpTy)
    | _ => return none   -- unknown type → skip
  return maybes.filterMap id

-- ── Top-level parser ─────────────────────────────────────────────────────────

def parseFrontendState (json : Lean.Json) :
    Except String (Pip × List Domino × List Constraint) := do
  let pip         ← parsePip json
  let dominoes    ← parseDominoes json
  let constraints ← parseConstraints json
  return (pip, dominoes, constraints)

-- ── JSON serialisation of parsed structures (for response) ───────────────────

private def natJ (n : Nat) : Lean.Json :=
  .num { mantissa := n, exponent := 0 }

private def nodeJ (n : Node) : Lean.Json := natJ n.id

private def edgeJ (e : Node × Node) : Lean.Json :=
  .arr #[nodeJ e.1, nodeJ e.2]

private def dominoJ (d : Domino) : Lean.Json :=
  .mkObj [("left", natJ d.left), ("right", natJ d.right)]

private def constraintJ (c : Constraint) : Lean.Json :=
  match c with
  | .sum ns target ty =>
      .mkObj [ ("type",   .str "sum")
             , ("nodes",  .arr (ns.map nodeJ).toArray)
             , ("target", natJ target)
             , ("cmp",    .str (match ty with | .eq => "eq" | .lt => "lt" | .gt => "gt"))
             ]
  | .equiv ns =>
      .mkObj [("type", .str "equiv"), ("nodes", .arr (ns.map nodeJ).toArray)]
  | .allNeq ns =>
      .mkObj [("type", .str "allNeq"), ("nodes", .arr (ns.map nodeJ).toArray)]

def toResponseJson (pip : Pip) (dominoes : List Domino) (constraints : List Constraint) :
    Lean.Json :=
  .mkObj
    [ ("nodeCount",       natJ pip.nodes.length)
    , ("edgeCount",       natJ pip.edges.length)
    , ("dominoCount",     natJ dominoes.length)
    , ("constraintCount", natJ constraints.length)
    , ("nodes",       .arr (pip.nodes.map nodeJ).toArray)
    , ("edges",       .arr (pip.edges.map edgeJ).toArray)
    , ("dominoes",    .arr (dominoes.map dominoJ).toArray)
    , ("constraints", .arr (constraints.map constraintJ).toArray)
    ]

end PipsConvert

-- ── HTTP server ───────────────────────────────────────────────────────────────

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
      match json with
      | .obj _ =>
        stateRef.set (some json)
        match PipsConvert.parseFrontendState json with
        | .error parseErr =>
          pure <| errorResponse "400 Bad Request" parseErr
        | .ok (pip, dominoes, constraints) =>
          IO.println s!"[lean-http-server] parsed: {pip.nodes.length} nodes, \
            {pip.edges.length} edges, {dominoes.length} dominoes, \
            {constraints.length} constraints"
          pure <| jsonResponse "200 OK" <| .mkObj
            [ ("ok",          true)
            , ("leanState",   PipsConvert.toResponseJson pip dominoes constraints)
            , ("solvedState", json)
            ]
      | _ =>
        pure <| errorResponse "400 Bad Request" "JSON body must be an object"
  else if method = "GET" && path = "/solve" then
    match ← stateRef.get with
    | some json =>
      pure <| jsonResponse "200 OK" <| .mkObj
        [ ("ok", true), ("solvedState", json) ]
    | none =>
      pure <| jsonResponse "200 OK" <| .mkObj
        [ ("ok", true), ("solvedState", Lean.Json.null) ]
  else
    pure <| errorResponse "404 Not Found" s!"No route for {method} {path}"

def readRequest (client : Socket.Client) : IO String := do
  let chunk? ← Async.block (Socket.Client.recv? client 65536)
  match chunk? with
  | none       => pure ""
  | some chunk => pure <| (String.fromUTF8? chunk).getD ""

def respond (client : Socket.Client) (message : String) : IO Unit := do
  Async.block (Socket.Client.send client message.toUTF8)
  try
    Async.block (Socket.Client.shutdown client)
  catch _ =>
    pure ()

def handleClient (stateRef : IO.Ref (Option Lean.Json)) (client : Socket.Client) : IO Unit := do
  try
    let raw  ← readRequest client
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
  let server   ← Socket.Server.mk
  server.bind (localhost defaultPort)
  server.listen 128
  IO.println s!"lean-http-server listening on http://127.0.0.1:{defaultPort}/"
  IO.println "routes: GET /health, GET /lean/version, POST /solve, GET /solve, OPTIONS *"
  serveLoop stateRef server

end LeanHttpServer

def main : IO Unit :=
  LeanHttpServer.run
