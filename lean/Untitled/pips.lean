/-!
# Pip Puzzle Formalization

Two-layer architecture:
1. **Spec layer** — Prop-based definitions using ∀/∃ over simple types.
   Theorems are proved against this layer.
2. **Implementation layer** — Bool-returning functions with edge lists.
   This is what actually executes.
3. **Bridge** — proves the implementation decides the spec.

Edges are stored in normalized form: (min id, max id). Queries normalize
before lookup, so adjacency is symmetric by construction.
-/

-- ============================================================================
-- Core types (shared by both layers)
-- ============================================================================

structure Node where
  id : Nat
deriving Repr, DecidableEq, Hashable

instance : Ord Node where
  compare n₁ n₂ := compare n₁.id n₂.id

structure Domino where
  left : Nat
  right : Nat
deriving Repr, DecidableEq, BEq, Hashable

/-- Normalize an edge so the smaller node id comes first. -/
def normalizeEdge (n₁ n₂ : Node) : Node × Node :=
  if n₁.id ≤ n₂.id then (n₁, n₂) else (n₂, n₁)

-- ============================================================================
-- SPEC LAYER — Prop-based, for proving theorems
-- ============================================================================

section Spec

/-- Abstract puzzle board: nodes and edges (normalized: fst.id ≤ snd.id). -/
structure PuzzleSpec where
  nodes : List Node
  edges : List (Node × Node)

/-- Two nodes are adjacent if their normalized edge is in the edge list. -/
def Adjacent (spec : PuzzleSpec) (n₁ n₂ : Node) : Prop :=
  normalizeEdge n₁ n₂ ∈ spec.edges

/-- An assignment in the spec is a list of placements (domino, node, node). -/
structure Placement where
  domino : Domino
  fst : Node
  snd : Node
deriving DecidableEq

abbrev AssignmentSpec := List Placement

/-- Every placed domino sits on an edge. -/
def DominoesPlacedAdjacently (spec : PuzzleSpec) (a : AssignmentSpec) : Prop :=
  ∀ p ∈ a, Adjacent spec p.fst p.snd

/-- Every node in the board appears in some placement. -/
def CoversAllNodes (spec : PuzzleSpec) (a : AssignmentSpec) : Prop :=
  ∀ n ∈ spec.nodes, ∃ p ∈ a, (p.fst = n ∨ p.snd = n)

/-- Flatten all nodes from an assignment. -/
def assignmentNodes (a : AssignmentSpec) : List Node :=
  a.flatMap (λ p => [p.fst, p.snd])

/-- All assigned nodes are globally unique (no node appears twice). -/
def AllNodesDistinct (a : AssignmentSpec) : Prop :=
  a.flatMap (λ p => [p.fst, p.snd]) |>.Nodup

/-- Each domino's two nodes are distinct. -/
def InternallyDisjoint (a : AssignmentSpec) : Prop :=
  ∀ p ∈ a, p.fst ≠ p.snd

/-- No node is used by more than one placement. -/
def NoOverlap (a : AssignmentSpec) : Prop :=
  ∀ p₁ ∈ a, ∀ p₂ ∈ a, p₁ ≠ p₂ →
    p₁.fst ≠ p₂.fst ∧ p₁.fst ≠ p₂.snd ∧
    p₁.snd ≠ p₂.fst ∧ p₁.snd ≠ p₂.snd

/-- Derive the value at a node from the assignment: which domino half covers it. -/
def nodeValue (a : AssignmentSpec) (n : Node) : Option Nat :=
  match a.find? (λ p => p.fst == n) with
  | some p => some p.domino.left
  | none =>
    match a.find? (λ p => p.snd == n) with
    | some p => some p.domino.right
    | none => none

/-- Top-level validity: the assignment is a correct solution. -/
def ValidAssignment (spec : PuzzleSpec) (a : AssignmentSpec) : Prop :=
  DominoesPlacedAdjacently spec a ∧
  CoversAllNodes spec a ∧
  AllNodesDistinct a

-- Constraints (spec level)

inductive SumConstraintType where
  | eq
  | lt
  | gt
deriving Repr, DecidableEq, BEq, Hashable

inductive ConstraintSpec where
  | sum   (ns : List Node) (target : Nat) (ty : SumConstraintType)
  | equiv (ns : List Node)

def SatisfiesConstraint (a : AssignmentSpec) : ConstraintSpec → Prop
  | .sum ns target .eq  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum = target
  | .sum ns target .lt  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum < target
  | .sum ns target .gt  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum > target
  | .equiv ns           => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            ∃ v, ∀ n ∈ ns, nodeValue a n = some v

def SatisfiesAllConstraints (a : AssignmentSpec) (cs : List ConstraintSpec) : Prop :=
  ∀ c ∈ cs, SatisfiesConstraint a c

/-- A puzzle is solvable if there exists a valid assignment satisfying all constraints. -/
def Solvable (spec : PuzzleSpec) (cs : List ConstraintSpec) : Prop :=
  ∃ a : AssignmentSpec, ValidAssignment spec a ∧ SatisfiesAllConstraints a cs

end Spec

-- ============================================================================
-- IMPLEMENTATION LAYER — Bool-returning, for execution
-- ============================================================================

section Impl

/-- Puzzle board as a list of nodes and a list of normalized edges. -/
structure Pip where
  nodes : List Node
  edges : List (Node × Node)
deriving Repr

def Pip.empty : Pip :=
  { nodes := [], edges := [] }

/-- Check adjacency by normalizing and scanning the edge list. -/
def adjacent (pip : Pip) (n₁ n₂ : Node) : Bool :=
  let (a, b) := normalizeEdge n₁ n₂
  pip.edges.any (λ (x, y) => x == a && y == b)

abbrev AssignmentImpl := List (Domino × Node × Node)

def allPlacedAdjacently (pip : Pip) (a : AssignmentImpl) : Bool :=
  a.all (λ (_, n₁, n₂) => adjacent pip n₁ n₂)

def assignedNodes (a : AssignmentImpl) : List Node :=
  a.flatMap (λ (_, n₁, n₂) => [n₁, n₂])

def coversAllNodesImpl (pip : Pip) (a : AssignmentImpl) : Bool :=
  let nodes := assignedNodes a
  pip.nodes.all (λ n => nodes.contains n)

def noOverlapImpl (a : AssignmentImpl) : Bool :=
  let nodes := assignedNodes a
  nodes.Pairwise (· != ·)

def assignmentIsValid (pip : Pip) (a : AssignmentImpl) : Bool :=
  allPlacedAdjacently pip a &&
  coversAllNodesImpl pip a &&
  noOverlapImpl a

-- Constraint checking (implementation)

inductive Constraint where
  | sum   (ns : List Node) (c : Nat) (t : SumConstraintType)
  | equiv (ns : List Node)
deriving Repr, BEq, Hashable

def nodeValueImpl (a : AssignmentImpl) (n : Node) : Option Nat :=
  match a.find? (λ (_, n₁, _) => n₁ == n) with
  | some (d, _, _) => some d.left
  | none =>
    match a.find? (λ (_, _, n₂) => n₂ == n) with
    | some (d, _, _) => some d.right
    | none => none

def checkConstraint (a : AssignmentImpl) : Constraint → Bool
  | .sum ns target .eq  =>
    let vals := ns.filterMap (nodeValueImpl a)
    vals.length == ns.length && vals.sum == target
  | .sum ns target .lt  =>
    let vals := ns.filterMap (nodeValueImpl a)
    vals.length == ns.length && vals.sum < target
  | .sum ns target .gt  =>
    let vals := ns.filterMap (nodeValueImpl a)
    vals.length == ns.length && vals.sum > target
  | .equiv ns           =>
    let vals := ns.filterMap (nodeValueImpl a)
    vals.length == ns.length &&
    match vals with
    | [] => true
    | v :: rest => rest.all (· == v)

def checkAllConstraints (a : AssignmentImpl) (cs : List Constraint) : Bool :=
  cs.all (checkConstraint a)

end Impl

-- ============================================================================
-- BRIDGE — connecting implementation to spec
-- ============================================================================

section Bridge

/-- Convert implementation board to spec. Trivial — same structure. -/
def Pip.toSpec (pip : Pip) : PuzzleSpec where
  nodes := pip.nodes
  edges := pip.edges

/-- Convert implementation assignment to spec assignment. -/
def toAssignmentSpec (a : AssignmentImpl) : AssignmentSpec :=
  a.map (λ (d, n₁, n₂) => { domino := d, fst := n₁, snd := n₂ })

-- The key bridge theorem: the Bool check decides the Prop-based spec.
private theorem adjacent_iff_mem (pip : Pip) (n₁ n₂ : Node) :
    adjacent pip n₁ n₂ = true ↔ normalizeEdge n₁ n₂ ∈ pip.edges := by
  simp [adjacent, normalizeEdge]

-- Sub-lemma: allPlacedAdjacently decides DominoesPlacedAdjacently
theorem allPlacedAdjacently_correct (pip : Pip) (a : AssignmentImpl) :
    allPlacedAdjacently pip a = true ↔
    DominoesPlacedAdjacently (pip.toSpec) (toAssignmentSpec a) := by
  unfold allPlacedAdjacently DominoesPlacedAdjacently toAssignmentSpec Pip.toSpec Adjacent
  simp [List.all_eq_true, List.mem_map]
  constructor
  · intro h p d n₁ n₂ hmem heq
    subst heq; simp
    exact (adjacent_iff_mem pip n₁ n₂).mp (h d n₁ n₂ hmem)
  · intro h d n₁ n₂ hmem
    exact (adjacent_iff_mem pip n₁ n₂).mpr (h _ d n₁ n₂ hmem rfl)

-- DAG of sub-lemmas:
-- 1. noOverlapImpl_correct (no preconditions — the root)
-- 2. coversAllNodesImpl_correct (assumes AllNodesDistinct)


-- Level 1: noOverlapImpl decides AllNodesDistinct (no deps)
-- Both sides are Pairwise (· ≠ ·) on the same flattened node list
theorem noOverlapImpl_correct (a : AssignmentImpl) :
    noOverlapImpl a = true ↔
    AllNodesDistinct (toAssignmentSpec a) := by
  unfold noOverlapImpl AllNodesDistinct toAssignmentSpec assignedNodes
  simp [List.Nodup, List.flatMap_map, decide_eq_true_eq]

-- Level 2: coversAllNodesImpl decides CoversAllNodes (assumes AllNodesDistinct)
-- With distinctness, the length check becomes: exactly the right number of nodes
-- and the all-contains check becomes: every board node is assigned
theorem coversAllNodesImpl_correct (pip : Pip) (a : AssignmentImpl)
    (_h_distinct : AllNodesDistinct (toAssignmentSpec a)) :
    coversAllNodesImpl pip a = true ↔
    CoversAllNodes (pip.toSpec) (toAssignmentSpec a) := by
  unfold coversAllNodesImpl CoversAllNodes toAssignmentSpec Pip.toSpec assignedNodes
  simp [List.all_eq_true, List.mem_map]
  constructor
  · intro hcovers n hmem
    obtain ⟨d, n₁, n₂, hin, hor⟩ := hcovers n hmem
    exact ⟨{ domino := d, fst := n₁, snd := n₂ }, ⟨d, n₁, n₂, hin, rfl⟩,
           hor.imp Eq.symm Eq.symm⟩
  · intro h n hmem
    obtain ⟨p, ⟨d, n₁, n₂, hin, heq⟩, hor⟩ := h n hmem
    subst heq; simp at hor
    exact ⟨d, n₁, n₂, hin, hor.imp Eq.symm Eq.symm⟩

-- Main bridge theorem
theorem assignmentIsValid_correct (pip : Pip) (a : AssignmentImpl) :
    assignmentIsValid pip a = true ↔
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) := by
  unfold assignmentIsValid ValidAssignment
  simp [Bool.and_eq_true]
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩
    have hDistinct := (noOverlapImpl_correct a).mp h3
    exact ⟨(allPlacedAdjacently_correct pip a).mp h1,
           (coversAllNodesImpl_correct pip a hDistinct).mp h2,
           hDistinct⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨⟨(allPlacedAdjacently_correct pip a).mpr h1,
            (coversAllNodesImpl_correct pip a h3).mpr h2⟩,
           (noOverlapImpl_correct a).mpr h3⟩

end Bridge
