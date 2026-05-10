import Untitled.Pips

open SumConstraintType

/-- Check if a node is already used in the current partial assignment. -/
def isNodeUsed (assignment : AssignmentImpl) (n : Node) : Bool :=
  assignment.any (λ (_, n₁, n₂) => n₁ == n || n₂ == n)

/-- Find uncovered edges: edges where both endpoints are free. -/
def uncoveredEdges (pip : Pip) (assignment : AssignmentImpl) : List (Node × Node) :=
  pip.edges.filter (λ (a, b) =>
    !isNodeUsed assignment a && !isNodeUsed assignment b)

/-- Try placing a domino on a specific edge (n₁, n₂). Both orientations always. -/
def tryPlace (domino : Domino) (n₁ n₂ : Node) : List (Domino × Node × Node) :=
  [(domino, n₁, n₂), (domino, n₂, n₁)]

/-- All ways to pick one domino from a list, returning (chosen, remaining). -/
def dominoChoices : List Domino → List (Domino × List Domino)
  | [] => []
  | domino :: rest =>
    (domino, rest) ::
      (dominoChoices rest).map (λ (choice, withoutChoice) => (choice, domino :: withoutChoice))

/-- Brute-force backtracking solver. Structurally recursive on `remaining`.
    For each remaining domino choice, tries every uncovered edge in both orientations. -/
def solveAux
    (pip : Pip)
    (cs : List Constraint)
    (remaining : List Domino)
    (assignment : AssignmentImpl) : Option AssignmentImpl :=
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

/-- Solve a pip puzzle. -/
def solve (pip : Pip) (dominoes : List Domino) (cs : List Constraint) : Option AssignmentImpl :=
  solveAux pip cs dominoes []

-- ============================================================================
-- SOLVER SOUNDNESS
-- ============================================================================

/-- solveAux only returns assignments that pass both checks. -/
theorem solveAux_sound (pip : Pip) (cs : List Constraint)
    (remaining : List Domino) (assignment : AssignmentImpl)
    (a : AssignmentImpl)
    (h : solveAux pip cs remaining assignment = some a) :
    assignmentIsValid pip a = true ∧ checkAllConstraints a cs = true := by
  induction remaining generalizing assignment with
  | nil =>
    simp [solveAux] at h
    obtain ⟨⟨hValid, hConstraints⟩, heq⟩ := h
    subst heq
    exact ⟨hValid, hConstraints⟩
  | cons domino rest ih =>
    simp [solveAux] at h
    have ⟨_, edge, _, _, hinner, _⟩ := List.findSome?_eq_some_iff.mp h
    have ⟨_, placement, _, _, hsolve, _⟩ := List.findSome?_eq_some_iff.mp hinner
    exact ih (placement :: assignment) hsolve

/-- The solver is sound. -/
theorem solve_sound (pip : Pip) (dominoes : List Domino) (cs : List Constraint)
    (a : AssignmentImpl)
    (hSolve : solve pip dominoes cs = some a) :
    assignmentIsValid pip a = true ∧ checkAllConstraints a cs = true := by
  exact solveAux_sound pip cs dominoes [] a hSolve

/-- Lift solve_sound to the spec level. -/
theorem solve_sound_spec (pip : Pip) (dominoes : List Domino) (cs : List Constraint)
    (hNodup : ∀ c ∈ cs, match c with | .not_equiv ns => ns.Nodup | _ => True)
    (a : AssignmentImpl)
    (hSolve : solve pip dominoes cs = some a) :
    ValidAssignment (pip.toSpec) (toAssignmentSpec a) ∧
    SatisfiesAllConstraints (toAssignmentSpec a) (toConstraintSpecs cs) := by
  have ⟨hValid, hConstraints⟩ := solve_sound pip dominoes cs a hSolve
  exact ⟨(assignmentIsValid_correct pip a).mp hValid,
         (checkAllConstraints_correct a cs hNodup).mp hConstraints⟩

-- ============================================================================
-- SOLVER COMPLETENESS
-- ============================================================================

/-- assignmentIsValid is invariant under permutation. -/
theorem assignmentIsValid_perm (pip : Pip) (a b : AssignmentImpl)
    (h : a.Perm b) : assignmentIsValid pip a = assignmentIsValid pip b := by
  sorry

/-- checkAllConstraints is invariant under permutation.
    nodeValueImpl depends only on membership in the list. -/
theorem checkAllConstraints_perm (a b : AssignmentImpl) (cs : List Constraint)
    (h : a.Perm b) : checkAllConstraints a cs = checkAllConstraints b cs := by
  sorry

/-- A valid extension of an assignment: a list of placements that, when prepended,
    makes the whole thing valid and constraint-satisfying. Each placement uses
    one of the remaining dominoes on an adjacent pair of board nodes. -/
def IsValidExtension (pip : Pip) (cs : List Constraint)
    (remaining : List Domino) (assignment extension : AssignmentImpl) : Prop :=
  extension.map (·.1) = remaining ∧
  assignmentIsValid pip (extension ++ assignment) = true ∧
  checkAllConstraints (extension ++ assignment) cs = true

/-- If findSome? returns none, f returns none for every element. -/
private theorem findSome_none {α β : Type} {f : α → Option β} {l : List α}
    (h : l.findSome? f = none) (x : α) (hx : x ∈ l) : f x = none := by
  induction l with
  | nil => simp at hx
  | cons a as ih =>
    cases hfa : f a with
    | none =>
      simp [List.findSome?, hfa] at h
      cases hx with
      | head => rw [hfa]
      | tail _ hx' => exact h _ hx'
    | some val =>
      have : (a :: as).findSome? f = some val := by simp [List.findSome?, hfa]
      rw [this] at h; exact absurd h (by simp)

/-- If a valid assignment places (d, n₁, n₂), there exists an edge (a,b) in
    uncoveredEdges such that (d, n₁, n₂) ∈ tryPlace domino a b. -/
private theorem valid_placement_in_some_tryPlace (pip : Pip) (assignment : AssignmentImpl)
    (d : Domino) (n₁ n₂ : Node) (extRest : AssignmentImpl)
    (hvalid : assignmentIsValid pip ((d, n₁, n₂) :: extRest ++ assignment) = true)
    (hdom : d = domino) :
    ∃ (a b : Node), (a, b) ∈ uncoveredEdges pip assignment ∧
      (d, n₁, n₂) ∈ tryPlace domino a b := by
  subst hdom
  -- From hvalid, extract adjacency and node-freeness
  -- adjacent pip n₁ n₂ = true → normalizeEdge n₁ n₂ ∈ pip.edges
  -- noOverlapImpl → n₁, n₂ not used in assignment
  -- Therefore normalizeEdge n₁ n₂ ∈ uncoveredEdges pip assignment
  -- And (d, n₁, n₂) ∈ tryPlace d (normalizeEdge n₁ n₂).1 (normalizeEdge n₁ n₂).2
  --   because tryPlace always generates both orientations
  refine ⟨(normalizeEdge n₁ n₂).1, (normalizeEdge n₁ n₂).2, ?_, ?_⟩
  · -- edge ∈ uncoveredEdges
    simp [uncoveredEdges, List.mem_filter, assignmentIsValid, Bool.and_eq_true,
          allPlacedAdjacently, List.all_eq_true, noOverlapImpl, assignedNodes,
          isNodeUsed] at hvalid ⊢
    obtain ⟨⟨⟨hadj, _, _⟩, _⟩, ⟨_, _, hn1_assign⟩, ⟨_, hn2_assign⟩, _⟩ := hvalid
    refine ⟨?_, ?_, ?_⟩
    · -- normalizeEdge n₁ n₂ ∈ pip.edges
      simp [adjacent, normalizeEdge] at hadj
      exact hadj
    · -- (normalizeEdge n₁ n₂).fst not used in assignment
      intro a a₁ b hmem
      simp [normalizeEdge]
      split
      · have ⟨h1, h2⟩ := hn1_assign a a₁ b hmem
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
      · have ⟨h1, h2⟩ := hn2_assign a a₁ b hmem
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
    · -- (normalizeEdge n₁ n₂).snd not used in assignment
      intro a a₁ b hmem
      simp [normalizeEdge]
      split
      · have ⟨h1, h2⟩ := hn2_assign a a₁ b hmem
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
      · have ⟨h1, h2⟩ := hn1_assign a a₁ b hmem
        exact ⟨fun h => h1 h.symm, fun h => h2 h.symm⟩
  · -- (d, n₁, n₂) ∈ tryPlace d edge.1 edge.2
    simp [tryPlace, normalizeEdge]
    split <;> simp

/-- solveAux is complete: if it returns none, no valid extension exists. -/
theorem solveAux_complete (pip : Pip) (cs : List Constraint)
    (remaining : List Domino) (assignment : AssignmentImpl) :
    solveAux pip cs remaining assignment = none →
    ¬∃ ext, IsValidExtension pip cs remaining assignment ext := by
  induction remaining generalizing assignment with
  | nil =>
    intro h ⟨ext, hmap, hvalid, hconst⟩
    have hnil : ext = [] := by
      cases ext with | nil => rfl | cons _ _ => simp at hmap
    subst hnil; simp at hvalid hconst
    simp [solveAux, Bool.and_eq_true] at h
    rw [h hvalid] at hconst; exact absurd hconst (by simp)
  | cons domino rest ih =>
    intro h ⟨ext, hmap, hvalid, hconst⟩
    match ext, hmap with
    | placement :: extRest, hmap =>
      simp at hmap
      obtain ⟨hdom, hrestMap⟩ := hmap
      -- Step 1+2: find the edge and show recursive call returned none
      have hRecNone : solveAux pip cs rest (placement :: assignment) = none := by
        simp [solveAux] at h
        obtain ⟨d, n₁, n₂⟩ := placement
        simp at hdom ⊢
        have ⟨a, b, hedge, hmemTP⟩ :=
          valid_placement_in_some_tryPlace pip assignment d n₁ n₂ extRest hvalid hdom
        exact h a b hedge d n₁ n₂ hmemTP
      -- Step 3: Apply ih — extRest is a valid extension of (placement :: assignment)
      -- (placement :: extRest) ++ assignment is a perm of extRest ++ (placement :: assignment)
      have hperm : (placement :: extRest ++ assignment).Perm
                   (extRest ++ (placement :: assignment)) := by
        exact List.perm_middle.symm
      have hvalidRest : assignmentIsValid pip (extRest ++ (placement :: assignment)) = true := by
        rw [← assignmentIsValid_perm pip _ _ hperm]; exact hvalid
      have hconstRest : checkAllConstraints (extRest ++ (placement :: assignment)) cs = true := by
        rw [← checkAllConstraints_perm _ _ cs hperm]; exact hconst
      exact ih (placement :: assignment) hRecNone
        ⟨extRest, hrestMap, hvalidRest, hconstRest⟩

/-- Top-level completeness: if solve returns none, the puzzle has no solution
    using the given dominoes (in that order). -/
theorem solve_complete (pip : Pip) (dominoes : List Domino) (cs : List Constraint) :
    solve pip dominoes cs = none →
    ¬∃ ext, IsValidExtension pip cs dominoes [] ext := by
  intro h
  exact solveAux_complete pip cs dominoes [] h
