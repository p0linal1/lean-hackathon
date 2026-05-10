import Untitled.Pips

open SumConstraintType

/-- Edges incident to a given node. Returns the other endpoint for each. -/
def Pip.neighbors (pip : Pip) (n : Node) : List Node :=
  pip.edges.filterMap (λ (a, b) =>
    if a == n then some b
    else if b == n then some a
    else none)

/-- Check if a node is already used in the current partial assignment. -/
def isNodeUsed (assignment : AssignmentImpl) (n : Node) : Bool :=
  assignment.any (λ (_, n₁, n₂) => n₁ == n || n₂ == n)

/-- Check whether a single constraint can still be satisfied by a partial
    assignment. Fully assigned constraints are evaluated exactly; partially
    assigned constraints are pruned when the current values already make them
    impossible. -/
def checkConstraintPartial (assignment : AssignmentImpl) : Constraint → Bool
  | .sum ns target ty =>
    let vals := ns.filterMap (nodeValueImpl assignment)
    let sum := vals.sum
    if vals.length == ns.length then
      match ty with
      | .eq => sum == target
      | .lt => sum < target
      | .gt => sum > target
    else
      match ty with
      | .eq => sum <= target
      | .lt => sum < target
      | .gt => true
  | .equiv ns =>
    let vals := ns.filterMap (nodeValueImpl assignment)
    match vals with
    | [] => true
    | v :: rest => rest.all (· == v)

/-- Check constraints against the current partial assignment. -/
def checkConstraintsPartial (assignment : AssignmentImpl) (cs : List Constraint) : Bool :=
  cs.all (checkConstraintPartial assignment)

/-- Find uncovered edges: edges where neither endpoint pair is assigned by a single domino. -/
def uncoveredEdges (pip : Pip) (assignment : AssignmentImpl) : List (Node × Node) :=
  pip.edges.filter (λ (a, b) =>
    !isNodeUsed assignment a && !isNodeUsed assignment b)

def emptyNeighbors (pip : Pip) (assignment : AssignmentImpl) (n : Node) : List Node :=
  (pip.neighbors n).filter (λ neighbor => !isNodeUsed assignment neighbor)

def emptyNeighborCount (pip : Pip) (assignment : AssignmentImpl) (n : Node) : Nat :=
  (emptyNeighbors pip assignment n).length

def unusedNodes (pip : Pip) (assignment : AssignmentImpl) : List Node :=
  pip.nodes.filter (λ n => !isNodeUsed assignment n)

def hasDeadEnd (pip : Pip) (assignment : AssignmentImpl) : Bool :=
  (unusedNodes pip assignment).any (λ n => emptyNeighborCount pip assignment n == 0)

def orderedUnusedNodes (pip : Pip) (assignment : AssignmentImpl) : List Node :=
  (unusedNodes pip assignment).mergeSort
    (λ a b => emptyNeighborCount pip assignment a <= emptyNeighborCount pip assignment b)

def findNextEmptyNode (pip : Pip) (assignment : AssignmentImpl) : Option Node :=
  (orderedUnusedNodes pip assignment).head?

def dominoChoices : List Domino → List (Domino × List Domino)
  | [] => []
  | domino :: rest =>
    (domino, rest) ::
      (dominoChoices rest).map (λ (choice, withoutChoice) => (choice, domino :: withoutChoice))

/-- Try placing a domino on a specific edge (n₁, n₂). The domino can be placed
    in two orientations: (left→n₁, right→n₂) or (left→n₂, right→n₁). -/
def tryPlace (domino : Domino) (n₁ n₂ : Node) : List (Domino × Node × Node) :=
  if domino.left == domino.right then
    [(domino, n₁, n₂)]
  else
    [(domino, n₁, n₂), (domino, n₂, n₁)]

/-- Core backtracking solver. Picks the most constrained empty node, tries its
    empty neighbors, then tries every remaining domino on that edge. `fuel`
    decreases whenever a domino is removed. -/
def solveAuxFuel
    (fuel : Nat)
    (pip : Pip)
    (cs : List Constraint)
    (remaining : List Domino)
    (assignment : AssignmentImpl) : Option AssignmentImpl :=
  if !checkConstraintsPartial assignment cs then
    none
  else
    match remaining with
    | [] =>
      if assignmentIsValid pip assignment && checkAllConstraints assignment cs then
        some assignment
      else
        none
    | _ =>
      match fuel with
      | 0 => none
      | fuel' + 1 =>
        match findNextEmptyNode pip assignment with
        | none => none
        | some n₁ =>
          (emptyNeighbors pip assignment n₁).findSome? (λ n₂ =>
            (dominoChoices remaining).findSome? (λ (domino, rest) =>
              let placements := tryPlace domino n₁ n₂
              placements.findSome? (λ placement =>
                let nextAssignment := placement :: assignment
                if hasDeadEnd pip nextAssignment then
                  none
                else
                  solveAuxFuel fuel' pip cs rest nextAssignment)))

def solveAux
    (pip : Pip)
    (cs : List Constraint)
    (remaining : List Domino)
    (assignment : AssignmentImpl) : Option AssignmentImpl :=
  solveAuxFuel remaining.length pip cs remaining assignment

/-- Solve a pip puzzle: find a valid assignment of dominoes to edges satisfying all constraints. -/
def solve (pip : Pip) (dominoes : List Domino) (cs : List Constraint) : Option AssignmentImpl :=
  solveAux pip cs dominoes []

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

/-- solveAuxFuel only returns assignments that pass both checks. -/
theorem solveAuxFuel_sound (fuel : Nat) (pip : Pip) (cs : List Constraint)
    (remaining : List Domino) (assignment : AssignmentImpl)
    (a : AssignmentImpl)
    (h : solveAuxFuel fuel pip cs remaining assignment = some a) :
    assignmentIsValid pip a = true ∧ checkAllConstraints a cs = true := by
  induction fuel generalizing remaining assignment with
  | zero =>
    cases hRemaining : remaining with
    | nil =>
      simp [solveAuxFuel, hRemaining] at h
      obtain ⟨_, ⟨hValid, hConstraints⟩, heq⟩ := h
      subst heq
      exact ⟨hValid, hConstraints⟩
    | cons domino rest =>
      simp [solveAuxFuel, hRemaining] at h
  | succ fuel' ih =>
    cases hRemaining : remaining with
    | nil =>
      simp [solveAuxFuel, hRemaining] at h
      obtain ⟨_, ⟨hValid, hConstraints⟩, heq⟩ := h
      subst heq
      exact ⟨hValid, hConstraints⟩
    | cons domino rest =>
      simp [solveAuxFuel, hRemaining] at h
      obtain ⟨_, hnext⟩ := h
      cases hNext : findNextEmptyNode pip assignment with
      | none =>
        simp [hNext] at hnext
      | some n₁ =>
        simp [hNext] at hnext
        have ⟨_, _, _, _, hfindDominoes, _⟩ := List.findSome?_eq_some_iff.mp hnext
        have ⟨_, choice, _, _, hfindPlacements, _⟩ := List.findSome?_eq_some_iff.mp hfindDominoes
        obtain ⟨_, withoutChosen⟩ := choice
        have ⟨_, placement, _, _, hsolve, _⟩ := List.findSome?_eq_some_iff.mp hfindPlacements
        simp at hsolve
        exact ih withoutChosen (placement :: assignment) hsolve.2

/-- solveAux only returns assignments that pass both checks. -/
theorem solveAux_sound (pip : Pip) (cs : List Constraint)
    (remaining : List Domino) (assignment : AssignmentImpl)
    (a : AssignmentImpl)
    (h : solveAux pip cs remaining assignment = some a) :
    assignmentIsValid pip a = true ∧ checkAllConstraints a cs = true := by
  exact solveAuxFuel_sound remaining.length pip cs remaining assignment a h

/-- The solver is sound: if it returns an assignment, that assignment is valid
    and satisfies all constraints. -/
theorem solve_sound (pip : Pip) (dominoes : List Domino) (cs : List Constraint)
    (a : AssignmentImpl)
    (hSolve : solve pip dominoes cs = some a) :
    assignmentIsValid pip a = true ∧ checkAllConstraints a cs = true := by
  exact solveAux_sound pip cs dominoes [] a hSolve

/-- Lift solve_sound to the spec level using the bridge theorems. -/
theorem solve_sound_spec (pip : Pip) (dominoes : List Domino) (cs : List Constraint)
    (a : AssignmentImpl)
    (hSolve : solve pip dominoes cs = some a) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) := by
  have ⟨hValid, hConstraints⟩ := solve_sound pip dominoes cs a hSolve
  exact ⟨(assignmentIsValid_correct pip a).mp hValid,
         (checkAllConstraints_correct a cs).mp hConstraints⟩

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
  let result := solve examplePip exampleDominoes exampleConstraints
  match result with
  | some assignment =>
    IO.println s!"SOLVED! {assignment.length} placements:"
    for entry in assignment do
      let (d, n1, n2) := entry
      IO.println s!"  domino ({d.left},{d.right}) placed on nodes {n1.id} → {n2.id}"
  | none =>
    IO.println "NO SOLUTION FOUND"
    IO.println "--- Trying without constraints ---"
    let result2 := solve examplePip exampleDominoes []
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
