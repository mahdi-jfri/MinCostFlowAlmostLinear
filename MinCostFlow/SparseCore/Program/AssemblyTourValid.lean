module

public import MinCostFlow.SparseCore.Program.AssemblyStatement
public import MinCostFlow.SparseCore.Program.AssemblyUnique
public import MinCostFlow.SparseCore.Program.ContractOrder
public import MinCostFlow.Basic.Forest

/-!
# Tour edit validity from the contract precondition and forest changes (`AssemblyTourValid`)

Piece P2 (`TourContract.lean`) requires each edit sent to its `applyEdits` operation
(`op 0`) to satisfy `TourEditValid`, which asks for forest-level invariants that go beyond the
order-store condition `OrdEditsValidFor`:
* `.dropEdge e` requires `e ∉ s.rf.F.E` (forest edges must be cut first);
* `.insertBefore v x y` requires `v ∈ s.rf.F.V` and `x.1 ∉ s.rf.F.E`;
* `.moveEnds v v' sel c` requires `v ∈ s.rf.F.V`, `v' ∉ s.rf.F.V`, and `s.ord v' = []`.

This file proves when the tour edits are valid:
1. It proves that `TourEditsValid` does **not** follow from `sparseCoreOrdMachineContractKF.pre 0`
   together with P4's postcondition (`not_tourEditsValid_insertBefore`, `not_tourEditsValid_dropEdge`,
   `not_tourEditsValid_moveEnds`), because `OrderedBatch` constrains only the final order
   `applyOrdEdits ord edits`, not intermediate edits on vertices outside `G.V` or on forest edges.
2. It defines the minimal step-by-step compatibility predicate `EditsTourCompat` on `(V, F_E, ord,
   edits)` and proves `asmTourEditsValid_of_compat`: `OrdEditsValidFor` together with
   `EditsTourCompat` (on the post-cut forest edges `F_E`) implies the full `AsmTourEditsValid`
   required by P2.
3. It defines the minimal contract strengthening `OrdEditsTourValidFor` and proves that level-`0`
   delete/insert edit lists (no splits) satisfy `EditsTourCompat` once deleted forest edges are cut.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.LSF

/-! ## Mirrored P2 tour edit state and validity (from `TourContract.lean`) -/

/-- Mirrored abstract state of P2 (`TourAbs` in `TourContract.lean`): an order of ends, a rooted
forest, and a set of marked open ends. -/
structure AsmTourAbs where
  ord : ℕ → List End
  rf : RootedForest
  marked : Finset End

/-- Effect of one `OrdEdit` on `AsmTourAbs` (mirroring `tourApplyEdit` in `TourContract.lean`). -/
noncomputable def asmTourApplyEdit (s : AsmTourAbs) : OrdEdit → AsmTourAbs
  | .dropEdge e =>
    { ord := applyOrdEdit s.ord (.dropEdge e)
      rf := s.rf
      marked := s.marked.filter fun x => x.1 != e }
  | .insertBefore v x y =>
    { ord := applyOrdEdit s.ord (.insertBefore v x y)
      rf := s.rf
      marked := s.marked }
  | .rotateTo v y =>
    { ord := applyOrdEdit s.ord (.rotateTo v y)
      rf := s.rf
      marked := s.marked }
  | .moveEnds v v' sel c =>
    open Classical in
    let moved := ((s.ord v).filter (movedBy sel c)).toFinset
    let St := (moved.filter fun x => x.2).image Prod.fst
    let Sh := (moved.filter fun x => !x.2).image Prod.fst
    let F' := s.rf.F.applyUpdate (.split v v' St Sh)
    let r := s.rf.root v
    let newRoot := if F'.Connected v r then v' else v
    { ord := applyOrdEdit s.ord (.moveEnds v v' sel c)
      rf := ⟨F', insert newRoot s.rf.R⟩
      marked := s.marked }

/-- Effect of a list of `OrdEdit`s on `AsmTourAbs`. -/
noncomputable def asmTourApplyEdits (s : AsmTourAbs) (edits : List OrdEdit) : AsmTourAbs :=
  edits.foldl asmTourApplyEdit s

/-- Precondition for a single `OrdEdit` on `AsmTourAbs` (mirroring `TourEditValid` in
`TourContract.lean`). -/
def AsmTourEditValid (vCap eCap : ℕ) (s : AsmTourAbs) : OrdEdit → Prop
  | .dropEdge e => e < eCap ∧ e ∉ s.rf.F.E
  | .insertBefore v x y =>
    v < vCap ∧ v ∈ s.rf.F.V ∧ x.1 < eCap ∧ x.1 ∉ s.rf.F.E ∧ (∀ u, x ∉ s.ord u) ∧
      ∀ y' ∈ y, y'.1 < eCap
  | .rotateTo v y => v < vCap ∧ y.1 < eCap
  | .moveEnds v v' sel _ =>
    v < vCap ∧ v' < vCap ∧ v ≠ v' ∧ v ∈ s.rf.F.V ∧ v' ∉ s.rf.F.V ∧ s.ord v' = [] ∧
      ∀ x ∈ sel, x.1 < eCap

/-- Step-by-step validity of a list of `OrdEdit`s on `AsmTourAbs` (mirroring `TourEditsValid`). -/
def AsmTourEditsValid (vCap eCap : ℕ) : AsmTourAbs → List OrdEdit → Prop
  | _, [] => True
  | s, e :: es => AsmTourEditValid vCap eCap s e ∧ AsmTourEditsValid vCap eCap (asmTourApplyEdit s e) es

/-! ## Counterexamples: `TourEditsValid` does not follow from `KF.pre 0` + P4's post -/

/-- Edits inserting an end at vertex `1 ∉ {0}` and then dropping edge `0`. -/
def ghostVertexEdits : List OrdEdit :=
  [.insertBefore 1 (0, true) none, .dropEdge 0]

/-- On `oneVertexGraph` (`V = {0}, E = ∅`), `ghostVertexEdits` satisfies `OrderedBatch` for `U = []`
and `OrdEditsValidFor 2 1`, yet fails `AsmTourEditsValid 2 1` because `1 ∉ {0}`. -/
theorem not_tourEditsValid_insertBefore :
    let s : AsmTourAbs := ⟨fun _ => [], ⟨oneVertexGraph, {0}⟩, ∅⟩
    OrderedBatch oneVertexGraph [] s.ord (applyOrdEdits s.ord ghostVertexEdits) ∧
      OrdEditsValidFor 2 1 s.ord ghostVertexEdits ∧
      ¬ AsmTourEditsValid 2 1 s ghostVertexEdits := by
  intro s
  have hres : applyOrdEdits (fun _ => []) ghostVertexEdits = fun _ => [] := by
    funext u
    by_cases hu : u = 1
    · subst hu; simp [applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList]
    · simp [applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
        Function.update_of_ne hu]
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hres]
    exact ⟨oneVertexRotation, oneVertexRotation, rfl, rfl, RotationBatch.refl _⟩
  · intro e he
    simp only [ghostVertexEdits, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> simp
  · intro k hk
    have hlen : ghostVertexEdits.length = 2 := rfl
    rcases k with _ | _ | k
    · refine ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by cases h⟩,
        fun _ _ _ h => by cases h⟩
    · refine ⟨⟨fun u => ?_, fun u hu => ?_, fun u x hx => ?_⟩, fun u v x hu hv => ?_⟩
      · by_cases h1 : u = 1
        · subst h1; simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList]
        · simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
            Function.update_of_ne h1]
      · have hne : u ≠ 1 := by omega
        simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
          Function.update_of_ne hne]
      · by_cases h1 : u = 1
        · subst h1
          simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList] at hx
          subst hx; decide
        · simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
            Function.update_of_ne h1] at hx
      · by_cases h1 : u = 1 <;> by_cases h2 : v = 1
        · omega
        · simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
            Function.update_of_ne h2] at hv
        · simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
            Function.update_of_ne h1] at hu
        · simp [s, applyOrdEdits, ghostVertexEdits, applyOrdEdit, insertBeforeList,
            Function.update_of_ne h1] at hu
    · have hk2 : ghostVertexEdits.take (k + 2) = ghostVertexEdits := List.take_of_length_le (by omega)
      rw [hk2, hres]
      exact ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by cases h⟩,
        fun _ _ _ h => by cases h⟩
  · intro h
    have hv : (1 : ℕ) ∈ oneVertexGraph.V := h.1.2.1
    simp [oneVertexGraph] at hv

/-- Two-vertex graph `{0, 1}` with a single edge `0` from `0` to `1`. -/
def twoVertexEdgeGraph : MGraph where
  V := {0, 1}
  E := {0}
  tail _ := 0
  head _ := 1

/-- Rotation of `twoVertexEdgeGraph`. -/
def twoVertexEdgeRotation : Rotation twoVertexEdgeGraph where
  order v := if v = 0 then [(0, true)] else if v = 1 then [(0, false)] else []
  nodup v := by split_ifs <;> simp
  mem_order v x := by
    rcases x with ⟨e, b⟩
    cases b <;> simp only [twoVertexEdgeGraph, MGraph.src, Finset.mem_singleton, ↓reduceIte,
      Bool.false_eq_true]
    · by_cases hv : v = 1
      · subst hv; simp
      · by_cases h0 : v = 0
        · subst h0; simp
        · simp [hv, h0, Ne.symm hv]
    · by_cases h0 : v = 0
      · subst h0; simp
      · by_cases hv : v = 1
        · subst hv; simp
        · simp [hv, h0, Ne.symm h0]

/-- Dropping forest edge `0` and immediately re-inserting both of its ends. -/
def dropReinsertEdits : List OrdEdit :=
  [.dropEdge 0, .insertBefore 0 (0, true) none, .insertBefore 1 (0, false) none]

/-- On `twoVertexEdgeGraph` with forest edge `0 ∈ F.E`, `dropReinsertEdits` satisfies `OrderedBatch`
for `U = []` and `OrdEditsValidFor 2 1`, yet fails `AsmTourEditsValid 2 1` because `0 ∈ F.E`. -/
theorem not_tourEditsValid_dropEdge :
    let s : AsmTourAbs := ⟨twoVertexEdgeRotation.order, ⟨twoVertexEdgeGraph, {0}⟩, ∅⟩
    OrderedBatch twoVertexEdgeGraph [] s.ord (applyOrdEdits s.ord dropReinsertEdits) ∧
      OrdEditsValidFor 2 1 s.ord dropReinsertEdits ∧
      ¬ AsmTourEditsValid 2 1 s dropReinsertEdits := by
  intro s
  have h1 : applyOrdEdit s.ord (.dropEdge 0) = fun _ => [] := by
    funext u
    by_cases h0 : u = 0
    · subst h0; simp [s, twoVertexEdgeRotation, applyOrdEdit]
    · by_cases h1 : u = 1
      · subst h1; simp [s, twoVertexEdgeRotation, applyOrdEdit]
      · simp [s, twoVertexEdgeRotation, applyOrdEdit, h0, h1]
  have hres : applyOrdEdits s.ord dropReinsertEdits = s.ord := by
    funext u
    simp only [applyOrdEdits, dropReinsertEdits, List.foldl_cons, List.foldl_nil, h1]
    by_cases h0 : u = 0
    · subst h0; simp [s, twoVertexEdgeRotation, applyOrdEdit, insertBeforeList]
    · by_cases h1' : u = 1
      · subst h1'; simp [s, twoVertexEdgeRotation, applyOrdEdit, insertBeforeList]
      · simp [s, twoVertexEdgeRotation, applyOrdEdit, insertBeforeList, h0, h1']
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hres]
    exact ⟨twoVertexEdgeRotation, twoVertexEdgeRotation, rfl, rfl, RotationBatch.refl _⟩
  · intro e he
    simp only [dropReinsertEdits, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp
  · intro k hk
    have hlen : dropReinsertEdits.length = 3 := rfl
    have huniq0 : OrdUniqueWithin 2 1 s.ord :=
      ordUniqueWithin_of_rotation (G := twoVertexEdgeGraph)
        (fun e he => by simp [twoVertexEdgeGraph] at he ⊢)
        (fun v hv => by simp [twoVertexEdgeGraph] at hv; rcases hv with rfl | rfl <;> omega)
        (fun e he => by simp [twoVertexEdgeGraph] at he; omega)
        ⟨twoVertexEdgeRotation, rfl⟩
    rcases k with _ | _ | _ | k
    · exact huniq0
    · simp only [dropReinsertEdits, List.take_succ_cons, List.take_zero, applyOrdEdits,
        List.foldl_cons, List.foldl_nil, h1]
      exact ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by cases h⟩,
        fun _ _ _ h => by cases h⟩
    · simp only [dropReinsertEdits, List.take_succ_cons, List.take_zero, applyOrdEdits,
        List.foldl_cons, List.foldl_nil, h1]
      refine ⟨⟨fun u => ?_, fun u hu => ?_, fun u x hx => ?_⟩, fun u v x hu hv => ?_⟩
      · by_cases h0 : u = 0
        · subst h0; simp [applyOrdEdit, insertBeforeList]
        · simp [applyOrdEdit, insertBeforeList, Function.update_of_ne h0]
      · have hne : u ≠ 0 := by omega
        simp [applyOrdEdit, insertBeforeList, Function.update_of_ne hne]
      · by_cases h0 : u = 0
        · subst h0; simp [applyOrdEdit, insertBeforeList] at hx; subst hx; decide
        · simp [applyOrdEdit, insertBeforeList, Function.update_of_ne h0] at hx
      · by_cases h0 : u = 0 <;> by_cases h0' : v = 0
        · omega
        · simp [applyOrdEdit, insertBeforeList, Function.update_of_ne h0'] at hv
        · simp [applyOrdEdit, insertBeforeList, Function.update_of_ne h0] at hu
        · simp [applyOrdEdit, insertBeforeList, Function.update_of_ne h0] at hu
    · have hk3 : dropReinsertEdits.take (k + 3) = dropReinsertEdits := List.take_of_length_le (by omega)
      rw [hk3, hres]; exact huniq0
  · intro h
    exact h.1.2 (by simp [s, twoVertexEdgeGraph])

/-- Two-vertex edgeless graph `{0, 1}`. -/
def twoVertexEmptyGraph : MGraph where
  V := {0, 1}
  E := ∅
  tail _ := 0
  head _ := 0

/-- Empty rotation of `twoVertexEmptyGraph`. -/
def twoVertexEmptyRotation : Rotation twoVertexEmptyGraph where
  order _ := []
  nodup _ := List.nodup_nil
  mem_order _ _ := by simp [twoVertexEmptyGraph]

/-- On `twoVertexEmptyGraph` (`V = {0, 1}, E = ∅`), `[.moveEnds 0 1 ∅ false]` satisfies
`OrderedBatch` for `U = []` and `OrdEditsValidFor 2 1`, yet fails `AsmTourEditsValid 2 1` because
`1 ∈ F.V`. -/
theorem not_tourEditsValid_moveEnds :
    let s : AsmTourAbs := ⟨fun _ => [], ⟨twoVertexEmptyGraph, {0, 1}⟩, ∅⟩
    let edits : List OrdEdit := [.moveEnds 0 1 ∅ false]
    OrderedBatch twoVertexEmptyGraph [] s.ord (applyOrdEdits s.ord edits) ∧
      OrdEditsValidFor 2 1 s.ord edits ∧
      ¬ AsmTourEditsValid 2 1 s edits := by
  intro s edits
  have hres : applyOrdEdits (fun _ => []) edits = fun _ => [] := by
    funext u
    simp only [applyOrdEdits, edits, List.foldl_cons, List.foldl_nil, applyOrdEdit]
    split_ifs <;> rfl
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hres]
    exact ⟨twoVertexEmptyRotation, twoVertexEmptyRotation, rfl, rfl, RotationBatch.refl _⟩
  · intro e he
    simp only [edits, List.mem_cons, List.not_mem_nil, or_false] at he
    subst he; simp
  · intro k hk
    rcases k with _ | k
    · exact ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by cases h⟩,
        fun _ _ _ h => by cases h⟩
    · have hk1 : edits.take (k + 1) = edits := List.take_of_length_le (by simp [edits])
      rw [hk1, hres]
      exact ⟨⟨fun _ => List.nodup_nil, fun _ _ => rfl, fun _ _ h => by cases h⟩,
        fun _ _ _ h => by cases h⟩
  · intro h
    exact h.1.2.2.2.2.1 (by simp [s, twoVertexEmptyGraph])

/-! ## Minimal compatibility condition implying `AsmTourEditsValid` -/

/-- Step-by-step compatibility of an edit list with a current vertex set `V`, surviving forest edge
set `F_E` (after cutting deleted forest edges), and order `ord`. This is the exact minimal extra
condition beyond `OrdEditsValidFor` needed by P2's `applyEdits`. -/
def EditsTourCompat : Finset ℕ → Finset ℕ → (ℕ → List End) → List OrdEdit → Prop
  | _, _, _, [] => True
  | V, F_E, ord, e :: es =>
    match e with
    | .dropEdge eid =>
      eid ∉ F_E ∧ EditsTourCompat V F_E (applyOrdEdit ord (.dropEdge eid)) es
    | .insertBefore v x y =>
      v ∈ V ∧ x.1 ∉ F_E ∧ EditsTourCompat V F_E (applyOrdEdit ord (.insertBefore v x y)) es
    | .rotateTo v y =>
      EditsTourCompat V F_E (applyOrdEdit ord (.rotateTo v y)) es
    | .moveEnds v v' sel c =>
      v ∈ V ∧ v' ∉ V ∧ ord v' = [] ∧
      EditsTourCompat (insert v' V) F_E (applyOrdEdit ord (.moveEnds v v' sel c)) es

/-- Exact vertex-set and edge-set effect of `asmTourApplyEdit` on `s.rf.F`. -/
theorem asmTourApplyEdit_V_E (s : AsmTourAbs) (e : OrdEdit) :
    (asmTourApplyEdit s e).ord = applyOrdEdit s.ord e ∧
    (asmTourApplyEdit s e).rf.F.E = s.rf.F.E ∧
    (asmTourApplyEdit s e).rf.F.V =
      match e with
      | .moveEnds _ v' _ _ => insert v' s.rf.F.V
      | _ => s.rf.F.V := by
  cases e <;> simp [asmTourApplyEdit, MGraph.applyUpdate]

/-- **Derivation of `AsmTourEditsValid`.** Given `OrdEditsValidFor vCap eCap s.ord edits` (from
`sparseCoreOrdMachineContractKF.pre 0`) and `EditsTourCompat s.rf.F.V s.rf.F.E s.ord edits` (on the
post-cut forest), every edit in `edits` satisfies P2's `AsmTourEditValid` step-by-step. -/
theorem asmTourEditsValid_of_compat {vCap eCap : ℕ} :
    ∀ (edits : List OrdEdit) (s : AsmTourAbs),
      OrdEditsValidFor vCap eCap s.ord edits →
      EditsTourCompat s.rf.F.V s.rf.F.E s.ord edits →
      AsmTourEditsValid vCap eCap s edits
  | [], _, _, _ => trivial
  | e :: es, s, ⟨hW, hU⟩, hC => by
    have hWe := hW e List.mem_cons_self
    have hWes : OrdEditsWithin vCap eCap es := fun x hx => hW x (List.mem_cons_of_mem e hx)
    have hUhd := hU.head
    have hUtl := hU.tail
    have hVE := asmTourApplyEdit_V_E s e
    cases e with
    | dropEdge eid =>
      simp only at hWe
      refine ⟨⟨hWe, hC.1⟩, ?_⟩
      apply asmTourEditsValid_of_compat es (asmTourApplyEdit s (.dropEdge eid))
      · rw [hVE.1]; exact ⟨hWes, hUtl⟩
      · rw [hVE.1, hVE.2.1, hVE.2.2]; exact hC.2
    | insertBefore v x y =>
      simp only at hWe
      have hnotmem : ∀ u, x ∉ s.ord u := insertBefore_not_mem_of_unique hUhd.2
      refine ⟨⟨hWe.1, hC.1, hWe.2.1, hC.2.1, hnotmem, hWe.2.2⟩, ?_⟩
      apply asmTourEditsValid_of_compat es (asmTourApplyEdit s (.insertBefore v x y))
      · rw [hVE.1]; exact ⟨hWes, hUtl⟩
      · rw [hVE.1, hVE.2.1, hVE.2.2]; exact hC.2.2
    | rotateTo v y =>
      simp only at hWe
      refine ⟨hWe, ?_⟩
      apply asmTourEditsValid_of_compat es (asmTourApplyEdit s (.rotateTo v y))
      · rw [hVE.1]; exact ⟨hWes, hUtl⟩
      · rw [hVE.1, hVE.2.1, hVE.2.2]; exact hC
    | moveEnds v v' sel c =>
      simp only at hWe
      have hne : v ≠ v' := fun h => hC.2.1 (h ▸ hC.1)
      refine ⟨⟨hWe.1, hWe.2.1, hne, hC.1, hC.2.1, hC.2.2.1, hWe.2.2⟩, ?_⟩
      apply asmTourEditsValid_of_compat es (asmTourApplyEdit s (.moveEnds v v' sel c))
      · rw [hVE.1]; exact ⟨hWes, hUtl⟩
      · rw [hVE.1, hVE.2.1, hVE.2.2]; exact hC.2.2.2

/-- Level-`0` edit lists (containing only `dropEdge`, `insertBefore`, and `rotateTo`, with no
`moveEnds`) satisfy `EditsTourCompat V F_E ord edits` whenever every dropped edge and every inserted
edge lies outside `F_E` and every insertion vertex lies in `V`. -/
theorem editsTourCompat_of_noSplit {V F_E : Finset ℕ} :
    ∀ (edits : List OrdEdit) (ord : ℕ → List End),
      (∀ e ∈ edits, match e with
        | .dropEdge eid => eid ∉ F_E
        | .insertBefore v x _ => v ∈ V ∧ x.1 ∉ F_E
        | .rotateTo _ _ => True
        | .moveEnds _ _ _ _ => False) →
      EditsTourCompat V F_E ord edits
  | [], _, _ => trivial
  | e :: es, ord, h => by
    have he := h e List.mem_cons_self
    have hes : ∀ x ∈ es, _ := fun x hx => h x (List.mem_cons_of_mem e hx)
    cases e with
    | dropEdge eid => exact ⟨he, editsTourCompat_of_noSplit es _ hes⟩
    | insertBefore v x y => exact ⟨he.1, he.2, editsTourCompat_of_noSplit es _ hes⟩
    | rotateTo v y => exact editsTourCompat_of_noSplit es _ hes
    | moveEnds _ _ _ _ => exact False.elim he

end MinCostFlow.SparseCore.Program
