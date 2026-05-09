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

/-- Check constraints that can be evaluated given the current partial assignment.
    A constraint is checked only if all its nodes have been assigned values. -/
def checkConstraintsPartial (assignment : AssignmentImpl) (cs : List Constraint) : Bool :=
  cs.all (λ c =>
    match c with
    | .sum ns target ty =>
      let vals := ns.filterMap (nodeValueImpl assignment)
      if vals.length == ns.length then
        match ty with
        | .eq => vals.sum == target
        | .lt => vals.sum < target
        | .gt => vals.sum > target
      else true
    | .equiv ns =>
      let vals := ns.filterMap (nodeValueImpl assignment)
      if vals.length == ns.length then
        match vals with
        | [] => true
        | v :: rest => rest.all (· == v)
      else true)

/-- Find uncovered edges: edges where neither endpoint pair is assigned by a single domino. -/
def uncoveredEdges (pip : Pip) (assignment : AssignmentImpl) : List (Node × Node) :=
  pip.edges.filter (λ (a, b) =>
    !isNodeUsed assignment a && !isNodeUsed assignment b)

/-- Try placing a domino on a specific edge (n₁, n₂). The domino can be placed
    in two orientations: (left→n₁, right→n₂) or (left→n₂, right→n₁). -/
def tryPlace (domino : Domino) (n₁ n₂ : Node) : List (Domino × Node × Node) :=
  if domino.left == domino.right then
    [(domino, n₁, n₂)]
  else
    [(domino, n₁, n₂), (domino, n₂, n₁)]

/-- Core backtracking solver. Tries to place remaining dominoes on uncovered edges. -/
partial def solveAux
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
    | domino :: rest =>
      let edges := uncoveredEdges pip assignment
      edges.findSome? (λ (n₁, n₂) =>
        let placements := tryPlace domino n₁ n₂
        placements.findSome? (λ placement =>
          solveAux pip cs rest (placement :: assignment)))

/-- Solve a pip puzzle: find a valid assignment of dominoes to edges satisfying all constraints. -/
def solve (pip : Pip) (dominoes : List Domino) (cs : List Constraint) : Option AssignmentImpl :=
  solveAux pip cs dominoes []
