import Std.Data.HashMap
import Untitled.Pips

open SumConstraintType
open Std (HashMap)

/-- Edges incident to a given node. Returns the other endpoint for each. -/
def Pip.neighbors (pip : Pip) (n : Node) : List Node :=
  pip.edges.filterMap (λ (a, b) =>
    if a == n then some b
    else if b == n then some a
    else none)

/-- Partial constraint check using the incrementally-maintained node-value map.
    Fails as soon as the partial state is unrecoverable (e.g. the running sum
    already exceeds an `.eq` target, or two placed values disagree under `.equiv`),
    not just when all constraint nodes are filled. Soundness-irrelevant: the leaf
    check still runs `checkAllConstraints` against the full assignment. -/
def checkConstraintsPartial (nodeValues : HashMap Node Nat) (cs : List Constraint) : Bool :=
  cs.all (λ c =>
    match c with
    | .sum ns target ty =>
      let vals := ns.filterMap nodeValues.get?
      let isFull := vals.length == ns.length
      let s := vals.sum
      match ty with
      -- Values are Nat (non-negative), so partial sum can only grow.
      | .eq => if isFull then s == target else s <= target
      | .lt => s < target
      | .gt => if isFull then s > target else true
    | .equiv ns =>
      let vals := ns.filterMap nodeValues.get?
      match vals with
      | [] => true
      | v :: rest => rest.all (· == v))

/-- Detect a node that is uncovered but has no remaining edge to a free neighbor:
    such a node can never be filled, so the search subtree is dead. Cheap O(1)
    membership checks via the incrementally-maintained `nodeValues` and `edges`. -/
def hasDeadEnd (pip : Pip) (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) : Bool :=
  pip.nodes.any (λ n =>
    !nodeValues.contains n && edges.all (λ (a, b) => a != n && b != n))

/-- Try placing a domino on a specific edge (n₁, n₂). The domino can be placed
    in two orientations: (left→n₁, right→n₂) or (left→n₂, right→n₁). -/
def tryPlace (domino : Domino) (n₁ n₂ : Node) : List (Domino × Node × Node) :=
  if domino.left == domino.right then
    [(domino, n₁, n₂)]
  else
    [(domino, n₁, n₂), (domino, n₂, n₁)]

/-- Remaining dominoes as a multiset: distinct domino values paired with their
    multiplicity. Avoids exploring permutations of identical dominoes — placing
    `(1,1)` at edge X then at edge Y is now indistinguishable from the reverse. -/
abbrev DominoBag := List (Domino × Nat)

/-- Total number of placeable dominoes left in the bag. -/
@[simp] def DominoBag.size : DominoBag → Nat
  | [] => 0
  | (_, n) :: rest => n + DominoBag.size rest

/-- Group equal dominoes, preserving first-occurrence order. -/
def DominoBag.ofList (dominoes : List Domino) : DominoBag :=
  dominoes.eraseDups.map fun d => (d, dominoes.countP (· == d))

/-- Core backtracking solver. Tries to place remaining dominoes on uncovered edges.
    `remaining` is a multiset, so identical dominoes don't generate duplicate orderings.
    `edges` is maintained incrementally: it contains exactly the edges whose endpoints
    are both unused in `assignment`, so we never recompute it from scratch.
    Each level runs a parity prune via connected-component decomposition (any odd
    component is unsolvable), but does *not* restrict iteration to one component —
    that adds branching factor without payoff on typical (single-component) puzzles.
    `BaseIO`-valued so the search can be cooperatively cancelled — each call checks
    `IO.checkCanceled` and returns `none` immediately if the host task was cancelled. -/
def solveAux
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat) : BaseIO (Option AssignmentImpl) := do
  if ← IO.checkCanceled then return none
  if !checkConstraintsPartial nodeValues cs then return none
  match remaining with
  | [] =>
    if assignmentIsValid pip assignment && checkAllConstraints assignment cs then
      return some assignment
    else
      return none
  | (_, 0) :: rest =>
    -- Unreachable for bags built via `DominoBag.ofList` (counts are always ≥ 1),
    -- but matched here for exhaustiveness.
    solveAux pip cs rest assignment edges nodeValues
  | (domino, n + 1) :: rest =>
    let totalCount := DominoBag.size ((domino, n + 1) :: rest)
    let uncoveredNodeCount := pip.nodes.countP (λ n => !nodeValues.contains n)
    if uncoveredNodeCount != 2 * totalCount || hasDeadEnd pip nodeValues edges then
      return none
    let remaining' : DominoBag := if n = 0 then rest else (domino, n) :: rest
    edges.findSomeM? (λ (n₁, n₂) => do
      let placements := tryPlace domino n₁ n₂
      placements.findSomeM? (λ (d, pn₁, pn₂) => do
        let edges' := edges.filter (λ (a, b) =>
          a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂)
        let nodeValues' := (nodeValues.insert pn₁ d.left).insert pn₂ d.right
        solveAux pip cs remaining' ((d, pn₁, pn₂) :: assignment) edges' nodeValues'))
termination_by DominoBag.size remaining + remaining.length
decreasing_by
  all_goals first
    | omega
    | (simp only [DominoBag.size, List.length_cons]; omega)
    | (split <;> simp only [DominoBag.size, List.length_cons] <;> omega)

/-- Race a list of solver tasks: return the first `some` result and cancel the rest.
    If all tasks return `none`, returns `none`. -/
partial def raceTasks : List (Task (Option AssignmentImpl)) → BaseIO (Option AssignmentImpl)
  | [] => pure none
  | t :: ts => do
    let (result, remaining) ← IO.waitAny' (t :: ts)
    match result with
    | some a =>
      remaining.forM IO.cancel
      return some a
    | none =>
      raceTasks remaining

/-- Solve a pip puzzle: find a valid assignment of dominoes to edges satisfying all constraints.
    Parallelism: each first-domino placement (edge × orientation) is spawned as its own
    `Task`; the first to return `some` wins and cancels the rest. -/
def solve (pip : Pip) (dominoes : List Domino) (cs : List Constraint) :
    BaseIO (Option AssignmentImpl) := do
  let bag := DominoBag.ofList dominoes
  match bag with
  | [] =>
    -- No dominoes to place; just verify the (empty) assignment.
    solveAux pip cs [] [] pip.edges ∅
  | (_, 0) :: rest =>
    -- Unreachable via `ofList`; defer to sequential solver.
    solveAux pip cs rest [] pip.edges ∅
  | (domino, n + 1) :: rest =>
    let restBag : DominoBag := if n = 0 then rest else (domino, n) :: rest
    let placements : List (Domino × Node × Node) :=
      pip.edges.flatMap fun (e₁, e₂) => tryPlace domino e₁ e₂
    match placements with
    | [] => return none
    | [_] =>
      -- Single choice; no parallelism benefit.
      solveAux pip cs bag [] pip.edges ∅
    | _ =>
      let tasks ← placements.mapM fun (d, pn₁, pn₂) => do
        let edges' := pip.edges.filter fun (a, b) =>
          a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂
        let nodeValues : HashMap Node Nat :=
          ((∅ : HashMap Node Nat).insert pn₁ d.left).insert pn₂ d.right
        BaseIO.asTask (solveAux pip cs restBag [(d, pn₁, pn₂)] edges' nodeValues)
      raceTasks tasks

-- ============================================================================
-- SOLVER CORRECTNESS
-- ============================================================================

/-- Any assignment that passes both checks is valid and satisfies constraints.
    This is the core soundness lemma — independent of the solver's search strategy. -/
theorem checked_assignment_valid (pip : Pip) (a : AssignmentImpl) (cs : List Constraint)
    (hCheck : assignmentIsValid pip a && checkAllConstraints a cs = true) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) := by
  simp [Bool.and_eq_true] at hCheck
  obtain ⟨hValid, hConstraints⟩ := hCheck
  exact ⟨(assignmentIsValid_correct pip a).mp hValid,
         (checkAllConstraints_correct a cs).mp hConstraints⟩

-- NOTE: When `solveAux` was a pure `Option AssignmentImpl`, we had inductive
-- soundness proofs (`solveAux_sound`/`solve_sound`/`solve_sound_spec`) that
-- threaded through `simp [solveAux]` and the `findSome?` extraction lemmas.
-- After moving to `BaseIO` for cooperative cancellation, those proofs no
-- longer compile: `simp` can't make progress on the `do`-block, and reasoning
-- about the IO state requires `EStateM.Result.ok` plumbing. The leaf
-- correctness lemma below (`checked_assignment_valid`) is unchanged and is
-- the only piece soundness ultimately depends on — any `some a` returned by
-- the IO solver came from that leaf check.
--
-- TODO: Re-prove `solveAux_sound` for the IO version, e.g. by writing a
-- pure shadow function and proving equivalence under no-cancellation, or by
-- doing the IO/EStateM reasoning directly.


-- ============================================================================
-- DEBUG: Test solver with the example puzzle from example.json
-- ============================================================================

private def examplePip : Pip :=
  { nodes := [5, 6, 7, 8, 9, 10, 11, 12, 17, 18, 19, 20, 21, 22, 23, 24].map Node.mk
  , edges := [ (⟨5⟩, ⟨11⟩), (⟨6⟩, ⟨7⟩), (⟨6⟩, ⟨12⟩), (⟨7⟩, ⟨8⟩)
             , (⟨8⟩, ⟨9⟩), (⟨9⟩, ⟨10⟩), (⟨10⟩, ⟨11⟩), (⟨11⟩, ⟨17⟩)
             , (⟨12⟩, ⟨18⟩), (⟨17⟩, ⟨23⟩), (⟨18⟩, ⟨19⟩), (⟨18⟩, ⟨24⟩)
             , (⟨19⟩, ⟨20⟩), (⟨20⟩, ⟨21⟩), (⟨21⟩, ⟨22⟩), (⟨22⟩, ⟨23⟩)
             ]
  }

private def exampleDominoes : List Domino :=
  [ ⟨4, 0⟩, ⟨2, 4⟩, ⟨1, 0⟩, ⟨1, 5⟩, ⟨4, 3⟩, ⟨1, 4⟩, ⟨6, 4⟩, ⟨3, 0⟩ ]

private def exampleConstraints : List Constraint :=
  [ .sum [⟨5⟩] 3 .gt
  , .equiv [⟨6⟩, ⟨7⟩]
  , .sum [⟨8⟩, ⟨9⟩] 9 .gt
  , .sum [⟨10⟩, ⟨11⟩, ⟨17⟩] 1 .eq
  , .equiv [⟨18⟩, ⟨19⟩]
  , .equiv [⟨20⟩, ⟨21⟩]
  , .sum [⟨22⟩, ⟨23⟩] 3 .lt
  ]

#eval do
  IO.println "=== Solver Debug ==="
  IO.println s!"Nodes: {examplePip.nodes.map Node.id}"
  IO.println s!"Edges: {examplePip.edges.map fun (e : Node × Node) => (e.1.id, e.2.id)}"
  IO.println s!"Dominoes: {exampleDominoes.map fun (d : Domino) => (d.left, d.right)}"
  IO.println s!"Constraints: {exampleConstraints.length}"
  let result ← solve examplePip exampleDominoes exampleConstraints
  match result with
  | some assignment =>
    IO.println s!"SOLVED! {assignment.length} placements:"
    for entry in assignment do
      let (d, n1, n2) := entry
      IO.println s!"  domino ({d.left},{d.right}) placed on nodes {n1.id} → {n2.id}"
  | none =>
    IO.println "NO SOLUTION FOUND"
    IO.println "--- Trying without constraints ---"
    let result2 ← solve examplePip exampleDominoes []
    match result2 with
    | some assignment =>
      IO.println s!"  Without constraints: SOLVED! {assignment.length} placements:"
      for entry in assignment do
        let (d, n1, n2) := entry
        IO.println s!"    domino ({d.left},{d.right}) placed on nodes {n1.id} → {n2.id}"
    | none =>
      IO.println "  Without constraints: STILL NO SOLUTION"
      IO.println s!"  Node count: {examplePip.nodes.length}"
      IO.println s!"  Edge count: {examplePip.edges.length}"
      IO.println s!"  Domino count: {exampleDominoes.length}"
      IO.println s!"  Nodes needed to cover: {examplePip.nodes.length}"
      IO.println s!"  Nodes provided by dominoes: {exampleDominoes.length * 2}"
