import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Pip Puzzle Formalization

Two-layer architecture:
1. **Spec layer** — Prop-based definitions using ∀/∃ over simple types.
   Theorems are proved against this layer.
2. **Implementation layer** — Bool-returning functions with HashMaps.
   This is what actually executes.
3. **Bridge** — proves the implementation decides the spec.
-/

-- ============================================================================
-- Core types (shared by both layers)
-- ============================================================================

structure Node where
  id : Nat
deriving Repr, DecidableEq, Hashable, BEq

structure Domino where
  left : Nat
  right : Nat
deriving Repr, DecidableEq, BEq, Hashable

-- ============================================================================
-- SPEC LAYER — Prop-based, for proving theorems
-- ============================================================================

section Spec

/-- Abstract puzzle board: a set of nodes and a symmetric adjacency relation. -/
structure PuzzleSpec where
  nodes : List Node
  adj : Node → Node → Prop

/-- An assignment in the spec is a list of placements (domino, node, node). -/
structure Placement where
  domino : Domino
  fst : Node
  snd : Node
deriving DecidableEq

abbrev AssignmentSpec := List Placement

/-- Two placed nodes are adjacent on the board. -/
def DominoesPlacedAdjacently (spec : PuzzleSpec) (a : AssignmentSpec) : Prop :=
  ∀ p ∈ a, spec.adj p.fst p.snd

/-- Every node in the board appears in exactly one placement. -/
def CoversAllNodes (spec : PuzzleSpec) (a : AssignmentSpec) : Prop :=
  ∀ n ∈ spec.nodes, ∃! p, p ∈ a ∧ (p.fst = n ∨ p.snd = n)

/-- No node is used by more than one placement. -/
def NoOverlap (a : AssignmentSpec) : Prop :=
  ∀ p₁ ∈ a, ∀ p₂ ∈ a, p₁ ≠ p₂ →
    p₁.fst ≠ p₂.fst ∧ p₁.fst ≠ p₂.snd ∧
    p₁.snd ≠ p₂.fst ∧ p₁.snd ≠ p₂.snd

/-- A domino's pip values match the node values given by a valuation. -/
def DominoMatchesNodes (val : Node → Nat) (p : Placement) : Prop :=
  (val p.fst = p.domino.left ∧ val p.snd = p.domino.right) ∨
  (val p.fst = p.domino.right ∧ val p.snd = p.domino.left)

def DominoValuesMatch (val : Node → Nat) (a : AssignmentSpec) : Prop :=
  ∀ p ∈ a, DominoMatchesNodes val p

/-- Top-level validity: the assignment is a correct solution. -/
def ValidAssignment (spec : PuzzleSpec) (val : Node → Nat) (a : AssignmentSpec) : Prop :=
  DominoesPlacedAdjacently spec a ∧
  CoversAllNodes spec a ∧
  NoOverlap a ∧
  DominoValuesMatch val a

-- Constraints (spec level)

inductive SumConstraintType where
  | eq
  | lt
  | gt
deriving Repr, DecidableEq, BEq, Hashable

inductive ConstraintSpec where
  | sum   (ns : List Node) (target : Nat) (ty : SumConstraintType)
  | equiv (ns : List Node) (target : Nat)

def SatisfiesConstraint (val : Node → Nat) : ConstraintSpec → Prop
  | .sum ns target .eq  => (ns.map val).sum = target
  | .sum ns target .lt  => (ns.map val).sum < target
  | .sum ns target .gt  => (ns.map val).sum > target
  | .equiv ns target    => ∀ n ∈ ns, val n = target

def SatisfiesAllConstraints (val : Node → Nat) (cs : List ConstraintSpec) : Prop :=
  ∀ c ∈ cs, SatisfiesConstraint val c

/-- A puzzle is solvable if there exists a valid assignment satisfying all constraints. -/
def Solvable (spec : PuzzleSpec) (val : Node → Nat) (cs : List ConstraintSpec) : Prop :=
  ∃ a : AssignmentSpec, ValidAssignment spec val a ∧ SatisfiesAllConstraints val cs

end Spec

-- ============================================================================
-- IMPLEMENTATION LAYER — Bool-returning, for execution
-- ============================================================================

section Impl

structure Pip where
  board : Std.HashMap Node (Std.HashSet Node)
deriving Repr

def Pip.empty : Pip :=
  { board := Std.HashMap.emptyWithCapacity 64 }

def Pip.nodes (pip : Pip) : List Node :=
  pip.board.keys

def adjacent (pip : Pip) (n₁ n₂ : Node) : Bool :=
  match pip.board.get? n₁ with
  | some neighbors => neighbors.contains n₂
  | none => false

abbrev AssignmentImpl := List (Domino × Node × Node)

def allPlacedAdjacently (pip : Pip) (a : AssignmentImpl) : Bool :=
  a.all (λ (_, n₁, n₂) => adjacent pip n₁ n₂)

def assignedNodes (a : AssignmentImpl) : List Node :=
  a.flatMap (λ (_, n₁, n₂) => [n₁, n₂])

def coversAllNodesImpl (pip : Pip) (a : AssignmentImpl) : Bool :=
  let nodes := assignedNodes a
  let boardNodes := pip.nodes
  boardNodes.all (λ n => nodes.contains n) &&
  nodes.length == boardNodes.length

def noOverlapImpl (a : AssignmentImpl) : Bool :=
  let nodes := assignedNodes a
  nodes.eraseDups.length == nodes.length

def assignmentIsValid (pip : Pip) (a : AssignmentImpl) : Bool :=
  allPlacedAdjacently pip a &&
  coversAllNodesImpl pip a &&
  noOverlapImpl a

-- Constraint checking (implementation)

inductive Constraint where
  | sum   (ns : List Node) (c : Nat) (t : SumConstraintType)
  | equiv (ns : List Node) (c : Nat)
deriving Repr, BEq, Hashable

def checkConstraint (val : Node → Nat) : Constraint → Bool
  | .sum ns target .eq  => (ns.map val).sum == target
  | .sum ns target .lt  => (ns.map val).sum < target
  | .sum ns target .gt  => (ns.map val).sum > target
  | .equiv ns target    => ns.all (λ n => val n == target)

def checkAllConstraints (val : Node → Nat) (cs : List Constraint) : Bool :=
  cs.all (checkConstraint val)

end Impl

-- ============================================================================
-- BRIDGE — connecting implementation to spec
-- ============================================================================

section Bridge

/-- Convert implementation board to spec adjacency relation. -/
def Pip.toSpec (pip : Pip) : PuzzleSpec where
  nodes := pip.nodes
  adj n₁ n₂ := adjacent pip n₁ n₂ = true

/-- Convert implementation assignment to spec assignment. -/
def toAssignmentSpec (a : AssignmentImpl) : AssignmentSpec :=
  a.map (λ (d, n₁, n₂) => { domino := d, fst := n₁, snd := n₂ })

/--
The key bridge theorem to prove:
the Bool implementation decides the Prop-based spec.

theorem assignmentIsValid_correct (pip : Pip) (a : AssignmentImpl) :
    assignmentIsValid pip a = true ↔
    (DominoesPlacedAdjacently (pip.toSpec) (toAssignmentSpec a) ∧
     CoversAllNodes (pip.toSpec) (toAssignmentSpec a) ∧
     NoOverlap (toAssignmentSpec a)) := by
  sorry
-/

end Bridge
