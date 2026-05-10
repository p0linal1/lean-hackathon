import Mathlib.Data.List.Nodup

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
  | not_equiv (ns : List Node)

def SatisfiesConstraint (a : AssignmentSpec) : ConstraintSpec → Prop
  | .sum ns target .eq  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum = target
  | .sum ns target .lt  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum < target
  | .sum ns target .gt  => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            (ns.filterMap (nodeValue a)).sum > target
  | .equiv ns           => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            ∃ v, ∀ n ∈ ns, nodeValue a n = some v
  | .not_equiv ns           => (∀ n ∈ ns, (nodeValue a n).isSome) ∧
                            ∀ n1 ∈ ns, ∀ n2 ∈ ns, n1 ≠ n2 → nodeValue a n1 ≠ nodeValue a n2

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
  nodes.Nodup

def assignmentIsValid (pip : Pip) (a : AssignmentImpl) : Bool :=
  allPlacedAdjacently pip a &&
  coversAllNodesImpl pip a &&
  noOverlapImpl a

-- Constraint checking (implementation)

inductive Constraint where
  | sum   (ns : List Node) (c : Nat) (t : SumConstraintType)
  | equiv (ns : List Node)
  | not_equiv (ns : List Node)
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
  | .not_equiv ns       =>
    let vals := ns.filterMap (nodeValueImpl a)
    vals.length == ns.length &&
    vals.Nodup

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
    exact ⟨d, n₁, n₂, hin, hor.imp Eq.symm Eq.symm⟩
  · intro h n hmem
    obtain ⟨d, n₁, n₂, hin, hor⟩ := h n hmem
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

/-- Convert an implementation constraint to a spec constraint. -/
def toConstraintSpec : Constraint → ConstraintSpec
  | .sum ns target ty => .sum ns target ty
  | .equiv ns => .equiv ns
  | .not_equiv ns => .not_equiv ns

/-- Convert a list of implementation constraints to spec constraints. -/
def toConstraintSpecs (cs : List Constraint) : List ConstraintSpec :=
  cs.map toConstraintSpec

private theorem find_map_comm {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).find? p = (l.find? (p ∘ f)).map f := by
  induction l with
  | nil => simp [List.find?, List.map]
  | cons a as ih =>
    simp only [List.map, List.find?, Function.comp]
    cases hp : p (f a)
    · simp [ih]
    · simp

private theorem find_fst_comp (a : AssignmentImpl) (n : Node) :
    List.find? ((fun p : Placement => p.fst == n) ∘
      fun x : Domino × Node × Node => { domino := x.fst, fst := x.2.fst, snd := x.2.snd }) a =
    List.find? (fun x : Domino × Node × Node => x.2.fst == n) a := by
  congr 1

private theorem find_snd_comp (a : AssignmentImpl) (n : Node) :
    List.find? ((fun p : Placement => p.snd == n) ∘
      fun x : Domino × Node × Node => { domino := x.fst, fst := x.2.fst, snd := x.2.snd }) a =
    List.find? (fun x : Domino × Node × Node => x.2.snd == n) a := by
  congr 1

/-- nodeValueImpl on impl assignment agrees with nodeValue on spec assignment. -/
theorem nodeValue_correct (a : AssignmentImpl) (n : Node) :
    nodeValueImpl a n = nodeValue (toAssignmentSpec a) n := by
  simp only [nodeValueImpl, nodeValue, toAssignmentSpec, find_map_comm, Option.map,
             find_fst_comp, find_snd_comp]
  cases hfst : List.find? (fun x => x.2.fst == n) a with
  | none =>
    simp
    cases hsnd : List.find? (fun x => x.2.snd == n) a with
    | none => simp
    | some val => obtain ⟨d, n₁, n₂⟩ := val; simp
  | some val => obtain ⟨d, n₁, n₂⟩ := val; simp

/-- nodeValueImpl and nodeValue produce the same filterMap results. -/
theorem filterMap_nodeValue_correct (a : AssignmentImpl) (ns : List Node) :
    ns.filterMap (nodeValueImpl a) = ns.filterMap (nodeValue (toAssignmentSpec a)) := by
  congr 1; funext n; exact nodeValue_correct a n

/-- nodeValueImpl isSome ↔ nodeValue isSome. -/
theorem nodeValue_isSome_correct (a : AssignmentImpl) (n : Node) :
    (nodeValueImpl a n).isSome = (nodeValue (toAssignmentSpec a) n).isSome := by
  rw [nodeValue_correct]

private theorem all_eq_first_iff_exists {α : Type} [BEq α] [LawfulBEq α]
    (l : List α) (hl : l ≠ []) :
    (match l with | [] => true | v :: rest => rest.all (· == v)) = true ↔
    ∃ v, ∀ x ∈ l, x = v := by
  match l, hl with
  | v :: rest, _ => simp [List.all_eq_true]

private theorem filterMap_all_some {α β : Type} (f : α → Option β) (l : List α)
    (h : ∀ x ∈ l, (f x).isSome = true) :
    (l.filterMap f).length = l.length := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    rw [Option.isSome_iff_exists] at ha
    obtain ⟨v, hv⟩ := ha
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp [List.filterMap, hv, ih']

private theorem filterMap_ne_nil_of_ne_nil {α β : Type} (f : α → Option β) (l : List α)
    (hl : l ≠ []) (h : ∀ x ∈ l, (f x).isSome = true) :
    l.filterMap f ≠ [] := by
  intro heq
  have hlen := filterMap_all_some f l h
  rw [heq] at hlen; simp at hlen
  exact hl (List.eq_nil_of_length_eq_zero hlen.symm)

private theorem filterMap_all_eq_iff
    (f : Node → Option Nat) (l : List Node)
    (hSome : ∀ n ∈ l, (f n).isSome = true) :
    (match l.filterMap f with | [] => true | v :: rest => rest.all (· == v)) = true ↔
    ∃ v, ∀ n ∈ l, f n = some v := by
  match l with
  | [] => simp [List.filterMap]
  | a :: as =>
    have hne : (a :: as).filterMap f ≠ [] :=
      filterMap_ne_nil_of_ne_nil f (a :: as) (by simp) hSome
    match hfm : (a :: as).filterMap f, hne with
    | v :: rest, _ =>
      simp only [List.all_eq_true]
      constructor
      · intro hAllEq
        refine ⟨v, fun n hn => ?_⟩
        have hnSome := hSome n hn
        rw [Option.isSome_iff_exists] at hnSome
        obtain ⟨w, hw⟩ := hnSome
        have hmem : w ∈ v :: rest := by
          rw [← hfm, List.mem_filterMap]; exact ⟨n, hn, by rw [hw]⟩
        cases hmem with
        | head => rw [← hw]
        | tail _ hm =>
          have heq := LawfulBEq.eq_of_beq (hAllEq w hm)
          rw [heq] at hw; rw [← hw]
      · intro ⟨val, hval⟩
        intro x hx
        have hv_mem : v ∈ v :: rest := .head ..
        rw [← hfm, List.mem_filterMap] at hv_mem
        obtain ⟨nv, hnv, hfnv⟩ := hv_mem
        have hval_nv := hval nv hnv
        rw [hval_nv] at hfnv; simp at hfnv
        have hmem : x ∈ v :: rest := List.mem_cons_of_mem v hx
        rw [← hfm, List.mem_filterMap] at hmem
        obtain ⟨nx, hnx, hfnx⟩ := hmem
        have hval_nx := hval nx hnx
        rw [hval_nx] at hfnx; simp at hfnx
        rw [← hfnv, ← hfnx]
        simp [BEq.beq]

private theorem filterMap_nodup_iff
    (f : Node → Option Nat) (l : List Node)
    (hSome : ∀ n ∈ l, (f n).isSome = true) :
    (l.filterMap f).Nodup ↔
    ∀ n1 ∈ l, ∀ n2 ∈ l, n1 ≠ n2 → f n1 ≠ f n2 := by
  sorry

/-- checkConstraint decides SatisfiesConstraint. -/
theorem checkConstraint_correct (a : AssignmentImpl) (c : Constraint) :
    checkConstraint a c = true ↔
    SatisfiesConstraint (toAssignmentSpec a) (toConstraintSpec c) := by
  cases c with
  | sum ns target ty =>
    cases ty <;> simp [checkConstraint, SatisfiesConstraint, toConstraintSpec,
                        filterMap_nodeValue_correct, Bool.and_eq_true]
  | equiv ns =>
    simp [checkConstraint, SatisfiesConstraint, toConstraintSpec,
          filterMap_nodeValue_correct, Bool.and_eq_true]
    intro hSome
    exact filterMap_all_eq_iff (nodeValue (toAssignmentSpec a)) ns hSome
  | not_equiv ns =>
    simp [checkConstraint, SatisfiesConstraint, toConstraintSpec,
          filterMap_nodeValue_correct, Bool.and_eq_true, List.Nodup]
    intro hSome
    exact filterMap_nodup_iff (nodeValue (toAssignmentSpec a)) ns hSome


/-- checkAllConstraints decides SatisfiesAllConstraints. -/
theorem checkAllConstraints_correct (a : AssignmentImpl) (cs : List Constraint) :
    checkAllConstraints a cs = true ↔
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) := by
  unfold checkAllConstraints SatisfiesAllConstraints toConstraintSpecs
  simp [List.all_eq_true, List.mem_map]
  constructor
  · intro h c hmem
    exact (checkConstraint_correct a c).mp (h c hmem)
  · intro h c hmem
    exact (checkConstraint_correct a c).mpr (h c hmem)

end Bridge
