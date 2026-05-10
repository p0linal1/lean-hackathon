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

def DominoBag.choices : DominoBag → List (Domino × DominoBag)
  | [] => []
  | (_, 0) :: rest => DominoBag.choices rest
  | (domino, n + 1) :: rest =>
    let decremented := if n = 0 then rest else (domino, n) :: rest
    (domino, decremented) ::
      (DominoBag.choices rest).map
        (λ (choice, withoutChoice) => (choice, (domino, n + 1) :: withoutChoice))

def DominoBag.values (bag : DominoBag) : List Nat :=
  bag.flatMap fun (d, n) => List.replicate n d.left ++ List.replicate n d.right

def minPossibleSum (values : List Nat) (count : Nat) : Nat :=
  (values.mergeSort (· <= ·)).take count |>.sum

def maxPossibleSum (values : List Nat) (count : Nat) : Nat :=
  (values.mergeSort (λ a b => b <= a)).take count |>.sum

/-- Partial constraint check using the incrementally-maintained node-value map.
    Fails as soon as the partial state is unrecoverable (e.g. the running sum
    already exceeds an `.eq` target, or two placed values disagree under `.equiv`),
    not just when all constraint nodes are filled. Soundness-irrelevant: the leaf
    check still runs `checkAllConstraints` against the full assignment. -/
def checkConstraintsPartial (nodeValues : HashMap Node Nat) (remaining : DominoBag)
    (cs : List Constraint) : Bool :=
  let remainingValues := remaining.values
  cs.all (λ c =>
    match c with
    | .sum ns target ty =>
      let vals := ns.filterMap nodeValues.get?
      let isFull := vals.length == ns.length
      let missing := ns.length - vals.length
      let s := vals.sum
      match ty with
      | .eq =>
          if isFull then
            s == target
          else
            s + minPossibleSum remainingValues missing <= target &&
            target <= s + maxPossibleSum remainingValues missing
      | .lt => s + minPossibleSum remainingValues missing < target
      | .gt =>
          if isFull then
            s > target
          else
            target < s + maxPossibleSum remainingValues missing
    | .equiv ns =>
      let vals := ns.filterMap nodeValues.get?
      match vals with
      | [] => true
      | v :: rest => rest.all (· == v)
    | .not_equiv ns =>
      let vals := ns.filterMap nodeValues.get?
      vals.Nodup)

/-- Detect a node that is uncovered but has no remaining edge to a free neighbor:
    such a node can never be filled, so the search subtree is dead. Cheap O(1)
    membership checks via the incrementally-maintained `nodeValues` and `edges`. -/
def hasDeadEnd (pip : Pip) (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) : Bool :=
  pip.nodes.any (λ n =>
    !nodeValues.contains n && edges.all (λ (a, b) => a != n && b != n))

def emptyNeighborCount (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) (n : Node) : Nat :=
  if nodeValues.contains n then
    0
  else
    edges.countP (λ (a, b) => a == n || b == n)

def orderedUnusedNodes (pip : Pip) (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) : List Node :=
  (pip.nodes.filter (λ n => !nodeValues.contains n)).mergeSort
    (λ a b => emptyNeighborCount nodeValues edges a <= emptyNeighborCount nodeValues edges b)

def incidentEdges (edges : List (Node × Node)) (n : Node) : List (Node × Node) :=
  edges.filter (λ (a, b) => a == n || b == n)

def otherEndpoint (edge : Node × Node) (n : Node) : Node :=
  if edge.1 == n then edge.2 else edge.1

/-- Try placing a domino on a specific edge (n₁, n₂). The domino can be placed
    in two orientations: (left→n₁, right→n₂) or (left→n₂, right→n₁). -/
def tryPlace (domino : Domino) (n₁ n₂ : Node) : List (Domino × Node × Node) :=
  if domino.left == domino.right then
    [(domino, n₁, n₂)]
  else
    [(domino, n₁, n₂), (domino, n₂, n₁)]

def viablePlacementCount (pip : Pip) (cs : List Constraint)
    (remaining : DominoBag) (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) (n₁ : Node) : Nat :=
  (incidentEdges edges n₁).foldl (init := 0) fun acc edge =>
    let n₂ := otherEndpoint edge n₁
    acc + (DominoBag.choices remaining).foldl (init := 0) (fun acc (domino, rest) =>
      acc + (tryPlace domino n₁ n₂).countP (fun (d, pn₁, pn₂) =>
        let edges' := edges.filter (λ (a, b) =>
          a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂)
        let nodeValues' := (nodeValues.insert pn₁ d.left).insert pn₂ d.right
        checkConstraintsPartial nodeValues' rest cs &&
        !hasDeadEnd pip nodeValues' edges'))

def findNextEmptyNode (pip : Pip) (cs : List Constraint)
    (remaining : DominoBag) (nodeValues : HashMap Node Nat)
    (edges : List (Node × Node)) : Option Node :=
  let nodes := orderedUnusedNodes pip nodeValues edges
  nodes.mergeSort
    (λ a b =>
      let ac := viablePlacementCount pip cs remaining nodeValues edges a
      let bc := viablePlacementCount pip cs remaining nodeValues edges b
      ac < bc || (ac == bc && emptyNeighborCount nodeValues edges a <= emptyNeighborCount nodeValues edges b))
    |>.head?

/-- Pure core backtracking solver. Picks the most constrained empty node first, then
    tries its remaining incident edges and every remaining domino value.
    `remaining` is a multiset, so identical dominoes don't generate duplicate orderings.
    `edges` is maintained incrementally: it contains exactly the edges whose endpoints
    are both unused in `assignment`, so we never recompute it from scratch. -/
def solveAuxFuelCore
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat) : Option AssignmentImpl :=
  if !checkConstraintsPartial nodeValues remaining cs then none
  else
    match remaining, fuel with
    | [], _ =>
      if assignmentIsValid pip assignment && checkAllConstraints assignment cs then
        some assignment
      else
        none
    | _ :: _, 0 => none
    | _ :: _, fuel' + 1 =>
      let totalCount := DominoBag.size remaining
      let uncoveredNodeCount := pip.nodes.countP (λ n => !nodeValues.contains n)
      if uncoveredNodeCount != 2 * totalCount || hasDeadEnd pip nodeValues edges then
        none
      else
        match findNextEmptyNode pip cs remaining nodeValues edges with
        | none => none
        | some n₁ =>
          (incidentEdges edges n₁).findSome? (λ edge =>
            let n₂ := otherEndpoint edge n₁
            (DominoBag.choices remaining).findSome? (λ (domino, rest) =>
              let placements := tryPlace domino n₁ n₂
              placements.findSome? (λ (d, pn₁, pn₂) =>
                let edges' := edges.filter (λ (a, b) =>
                  a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂)
                let nodeValues' := (nodeValues.insert pn₁ d.left).insert pn₂ d.right
                solveAuxFuelCore fuel' pip cs rest ((d, pn₁, pn₂) :: assignment) edges' nodeValues')))

/-- Core backtracking solver.
    `BaseIO`-valued so the search can be cooperatively cancelled — each call checks
    `IO.checkCanceled` and returns `none` immediately if the host task was cancelled. -/
def solveAuxFuel
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat) : BaseIO (Option AssignmentImpl) := do
  if ← IO.checkCanceled then return none
  return solveAuxFuelCore fuel pip cs remaining assignment edges nodeValues

def solveAux
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat) : BaseIO (Option AssignmentImpl) :=
  solveAuxFuel remaining.size pip cs remaining assignment edges nodeValues

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
  match findNextEmptyNode pip cs bag (∅ : HashMap Node Nat) pip.edges with
  | none => solveAux pip cs bag [] pip.edges ∅
  | some n₁ =>
    let placements : List (Domino × Node × Node × DominoBag) :=
      (incidentEdges pip.edges n₁).flatMap fun edge =>
        let n₂ := otherEndpoint edge n₁
        (DominoBag.choices bag).flatMap fun (domino, restBag) =>
          (tryPlace domino n₁ n₂).map fun (d, pn₁, pn₂) => (d, pn₁, pn₂, restBag)
    match placements with
    | [] => return none
    | [_] =>
      -- Single choice; no parallelism benefit.
      solveAux pip cs bag [] pip.edges ∅
    | _ =>
      let tasks ← placements.mapM fun (d, pn₁, pn₂, restBag) => do
        let edges' := pip.edges.filter fun (a, b) =>
          a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂
        let nodeValues : HashMap Node Nat :=
          ((∅ : HashMap Node Nat).insert pn₁ d.left).insert pn₂ d.right
        BaseIO.asTask (solveAuxFuel restBag.size pip cs restBag [(d, pn₁, pn₂)] edges' nodeValues)
      raceTasks tasks

-- ============================================================================
-- SOLVER CORRECTNESS
-- ============================================================================

/-- Any assignment that passes both checks is valid and satisfies constraints.
    This is the core soundness lemma — independent of the solver's search strategy. -/
theorem checked_assignment_valid (pip : Pip) (a : AssignmentImpl) (cs : List Constraint)
    (hNodup : ∀ c ∈ cs, match c with | .not_equiv ns => ns.Nodup | _ => True)
    (hCheck : assignmentIsValid pip a && checkAllConstraints a cs = true) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) := by
  simp [Bool.and_eq_true] at hCheck
  obtain ⟨hValid, hConstraints⟩ := hCheck
  exact ⟨(assignmentIsValid_correct pip a).mp hValid,
         (checkAllConstraints_correct a cs hNodup).mp hConstraints⟩

private theorem findSome?_sound {α β : Type} (f : α → Option β) :
    ∀ (xs : List α) {b : β},
      xs.findSome? f = some b →
      ∃ x ∈ xs, f x = some b := by
  intro xs
  induction xs with
  | nil =>
      intro b h
      rw [List.findSome?_nil] at h
      contradiction
  | cons x xs ih =>
      intro b h
      rw [List.findSome?_cons] at h
      cases hfx : f x with
      | none =>
          simp [hfx] at h
          obtain ⟨y, hy, hfy⟩ := ih h
          exact ⟨y, by simp [hy], hfy⟩
      | some b' =>
          simp [hfx] at h
          subst b'
          exact ⟨x, by simp, hfx⟩

private theorem checked_leaf_sound
    (pip : Pip) (assignment : AssignmentImpl) (cs : List Constraint) {a : AssignmentImpl}
    (hRun :
      (if assignmentIsValid pip assignment && checkAllConstraints assignment cs then
        some assignment
      else
        none) = some a) :
    assignmentIsValid pip a && checkAllConstraints a cs = true := by
  cases hCheck : assignmentIsValid pip assignment && checkAllConstraints assignment cs <;>
    simp [hCheck] at hRun
  cases hRun
  simpa using hCheck

private theorem solveAuxFuelCore_sound_checked
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat)
    {a : AssignmentImpl}
    (hRun : solveAuxFuelCore fuel pip cs remaining assignment edges nodeValues = some a) :
    assignmentIsValid pip a && checkAllConstraints a cs = true := by
  induction fuel generalizing remaining assignment edges nodeValues with
  | zero =>
      unfold solveAuxFuelCore at hRun
      split at hRun
      · contradiction
      · cases remaining with
        | nil =>
            exact checked_leaf_sound pip assignment cs hRun
        | cons _ _ =>
            contradiction
  | succ fuel ih =>
      unfold solveAuxFuelCore at hRun
      cases remaining with
      | nil =>
          simp at hRun
          rcases hRun with ⟨_, ⟨⟨hValid, hConstraints⟩, hEq⟩⟩
          subst a
          simp [hValid, hConstraints]
      | cons head tail =>
        simp at hRun
        rcases hRun with ⟨_, hRun⟩
        split at hRun
        · rcases hRun with ⟨_, hnone⟩
          contradiction
        · rcases hRun with ⟨_, hRun⟩
          obtain ⟨edge, _hedge, hedge⟩ := findSome?_sound _ _ hRun
          obtain ⟨choice, _hchoice, hchoice⟩ := findSome?_sound _ _ hedge
          rcases choice with ⟨domino, rest⟩
          obtain ⟨placement, _hplacement, hplacement⟩ := findSome?_sound _ _ hchoice
          rcases placement with ⟨d, pn₁, pn₂⟩
          exact ih rest ((d, pn₁, pn₂) :: assignment)
            (edges.filter fun (a, b) =>
              a != pn₁ && a != pn₂ && b != pn₁ && b != pn₂)
            ((nodeValues.insert pn₁ d.left).insert pn₂ d.right)
            hplacement

private theorem solveAuxFuel_sound_checked
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat)
    (s : Void IO.RealWorld)
    {a : AssignmentImpl}
    (hRun : (solveAuxFuel fuel pip cs remaining assignment edges nodeValues s).val = some a) :
    assignmentIsValid pip a && checkAllConstraints a cs = true := by
  unfold solveAuxFuel at hRun
  cases hCanceled : IO.checkCanceled s with
  | mk canceled s₁ =>
      simp [Bind.bind, Pure.pure, instMonadBaseIO._aux_5, instMonadBaseIO._aux_13,
        ST.bind, hCanceled] at hRun
      split at hRun
      · contradiction
      · exact solveAuxFuelCore_sound_checked fuel pip cs remaining assignment edges nodeValues hRun

theorem solveAuxFuel_sound
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat)
    (s : Void IO.RealWorld)
    {a : AssignmentImpl}
    (hNodup : ∀ c ∈ cs, match c with | .not_equiv ns => ns.Nodup | _ => True)
    (hRun : (solveAuxFuel fuel pip cs remaining assignment edges nodeValues s).val = some a) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) :=
  checked_assignment_valid pip a cs hNodup
    (solveAuxFuel_sound_checked fuel pip cs remaining assignment edges nodeValues s hRun)

theorem solveAux_sound
    (pip : Pip)
    (cs : List Constraint)
    (remaining : DominoBag)
    (assignment : AssignmentImpl)
    (edges : List (Node × Node))
    (nodeValues : HashMap Node Nat)
    (s : Void IO.RealWorld)
    {a : AssignmentImpl}
    (hNodup : ∀ c ∈ cs, match c with | .not_equiv ns => ns.Nodup | _ => True)
    (hRun : (solveAux pip cs remaining assignment edges nodeValues s).val = some a) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) :=
  solveAuxFuel_sound remaining.size pip cs remaining assignment edges nodeValues s hNodup hRun

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
