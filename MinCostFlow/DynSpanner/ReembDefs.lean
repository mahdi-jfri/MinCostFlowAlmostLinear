module

public import MinCostFlow.DynSpanner.Correctness

import Mathlib.Tactic.Linarith

/-!
# Edges re-embedded by `DynSpanner.step` and `DynSpanner.update`

During one step of Algorithm 6 (`DynSpanner.step`, Theorem 8.2, page 39), the maintained
embedding `piTotal` can change on a surviving edge `e ∈ (st.G.applyUpdate u).E` only if:
* the step is a level-`0` full restart (`chooseLevel L st.q (st.t + 1) = 0`), in which case every
  edge of `G' = st.G.applyUpdate u` gets a fresh embedding from `initCore`; or
* the step is a partial rebuild at level `j > 0`, in which case `e ∈ E_aff`, the affected edge
  set `affectedEdges G' H_lt piLt_mid S_prev`. Any surviving edge `e ∉ E_aff` keeps its exact
  embedding `piTotal st' e = piTotal st e`, because its level-`< j` walk avoids every vertex
  touched since the last rebuild of level `j - 1`, so no intermediate step at level `≥ j` affected
  it either.

This file defines:
* `stepReembSet` and `reembList` (its sorted duplicate-free list) for a single step `step`;
* `updateReembGo`, `updateReembSet`, and `updateReembList` for a batch `update` (the union of
  per-step sets intersected with the surviving edges `G_final.E`).

Main theorems:
* `reembList_length_le_cost` and `updateReembList_length_le_cost`: the list length is at most the
  model step / batch cost.
* `piTotal_eq_of_not_mem_stepReembSet` / `mem_reembList_of_piTotal_ne`: every surviving edge
  whose `piTotal` embedding changed in one step belongs to `reembList`.
* `piTotal_eq_of_not_mem_updateReembSet` / `mem_updateReembList_of_piTotal_ne`: every surviving
  edge whose `piTotal` embedding changed across a batch belongs to `updateReembList`.
-/

namespace MinCostFlow.DynSpanner

@[expose] public section

/-! ## Single-step re-embedded edge set and list -/

/-- Set of edges of `G' = st.G.applyUpdate u` whose embedding `step st u sparsify` can change:
all of `G'.E` on a level-`0` restart, and `E_aff` on a partial rebuild at level `j > 0`. -/
def stepReembSet {L : ℕ} (st : DynSpannerState L) (u : Update) : Finset ℕ :=
  let G' := st.G.applyUpdate u
  let touched := touchedVertices st.G u
  let H_mid : Fin (L + 1) → MGraph := fun i =>
    (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
  let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
  let S_mid : Fin (L + 1) → Finset ℕ := fun i => st.S_level i ∪ touched
  let t' := st.t + 1
  let j := chooseLevel L st.q t'
  if j = 0 then
    G'.E
  else
    let H_lt := unionGraphLt G' H_mid j
    let S_prev := S_mid ⟨j - 1, by
      have hjle : j ≤ L := chooseLevel_le L st.q t'
      omega⟩
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    affectedEdges G' H_lt piLt_mid S_prev

/-- Sorted duplicate-free list of `stepReembSet st u`: the edges whose embedding `DynSpanner.step`
can change. -/
def reembList {L : ℕ} (st : DynSpannerState L) (u : Update) : List ℕ :=
  (stepReembSet st u).sort (· ≤ ·)

theorem stepReembSet_eq_zero {L : ℕ} (st : DynSpannerState L) (u : Update)
    (hj0 : chooseLevel L st.q (st.t + 1) = 0) :
    stepReembSet st u = (st.G.applyUpdate u).E := by
  unfold stepReembSet
  simp [hj0]

theorem stepReembSet_eq_pos {L : ℕ} (st : DynSpannerState L) (u : Update)
    (hj0 : chooseLevel L st.q (st.t + 1) ≠ 0) :
    let G' := st.G.applyUpdate u
    let H_mid : Fin (L + 1) → MGraph := fun i =>
      (st.H_level i).applyBatch (restrictUpdate u (st.H_level i))
    let inDom_mid : Fin (L + 1) → Finset ℕ := fun i => st.inDom i ∩ G'.E
    let j := chooseLevel L st.q (st.t + 1)
    let H_lt := unionGraphLt G' H_mid j
    let S_prev := st.S_level ⟨j - 1, by have := chooseLevel_le L st.q (st.t + 1); omega⟩ ∪
      touchedVertices st.G u
    let piLt_mid := piLtFrom st.Pi_level inDom_mid j
    stepReembSet st u = affectedEdges G' H_lt piLt_mid S_prev := by
  unfold stepReembSet
  simp [hj0]

theorem stepReembSet_subset_G' {L : ℕ} (st : DynSpannerState L) (u : Update) :
    stepReembSet st u ⊆ (st.G.applyUpdate u).E := by
  unfold stepReembSet
  dsimp only
  split_ifs
  · exact Finset.Subset.rfl
  · exact Finset.filter_subset _ _

theorem reembList_nodup {L : ℕ} (st : DynSpannerState L) (u : Update) :
    (reembList st u).Nodup :=
  (stepReembSet st u).sort_nodup (· ≤ ·)

theorem mem_reembList {L : ℕ} (st : DynSpannerState L) (u : Update) (e : ℕ) :
    e ∈ reembList st u ↔ e ∈ stepReembSet st u :=
  Finset.mem_sort (· ≤ ·)

theorem reembList_toFinset {L : ℕ} (st : DynSpannerState L) (u : Update) :
    (reembList st u).toFinset = stepReembSet st u := by
  ext e
  simp [mem_reembList]

theorem reembList_length {L : ℕ} (st : DynSpannerState L) (u : Update) :
    (reembList st u).length = (stepReembSet st u).card :=
  Finset.length_sort (· ≤ ·)

/-- `initCore` pays at least `G.m` in its cost. -/
theorem m_le_initCore_cost (G : MGraph)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    G.m ≤ (initCore G sparsify).2.2 := by
  unfold initCore
  split_ifs with hE
  · dsimp only
    omega
  · have hm : G.m = 0 := by
      rw [MGraph.m, Finset.card_eq_zero, Finset.not_nonempty_iff_eq_empty.mp hE]
    omega

/-- `initAt` pays at least `G₀.m` in its cost. -/
theorem m_le_initAt_cost (G₀ : MGraph) (L q t : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    G₀.m ≤ (initAt G₀ L q t sparsify).cost := by
  unfold initAt
  have h := m_le_initCore_cost G₀ sparsify
  dsimp only
  omega

/-- `init` pays at least `G₀.m` in its cost. -/
theorem m_le_init_cost (G₀ : MGraph) (L q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    G₀.m ≤ (init G₀ L q sparsify).cost :=
  m_le_initAt_cost G₀ L q 0 sparsify

/-- The cardinality of `stepReembSet st u` is at most the step cost `(step st u sparsify).cost`. -/
theorem card_stepReembSet_le_cost {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (stepReembSet st u).card ≤ (step st u sparsify).cost := by
  by_cases hj0 : chooseLevel L st.q (st.t + 1) = 0
  · rw [stepReembSet_eq_zero st u hj0]
    unfold step
    simp only [hj0, ↓reduceDIte]
    have h := m_le_initAt_cost (st.G.applyUpdate u) L st.q (st.t + 1) sparsify
    change (st.G.applyUpdate u).m ≤ _
    omega
  · have hsr := stepReembSet_eq_pos st u hj0
    dsimp only at hsr
    rw [hsr]
    unfold step
    simp only [hj0, ↓reduceDIte]
    omega

/-- The length of `reembList st u` is at most `(step st u sparsify).cost`. -/
theorem reembList_length_le_cost {L : ℕ} (st : DynSpannerState L) (u : Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (reembList st u).length ≤ (step st u sparsify).cost := by
  rw [reembList_length]
  exact card_stepReembSet_le_cost st u sparsify

/-! ## Batch re-embedded edge set and list -/

/-- Accumulator loop collecting the union of `stepReembSet` over a batch `us`, intersected with the
surviving edges `cur.G.E` at the end of the batch. -/
def updateReembGo {L : ℕ} (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (cur : DynSpannerState L) (us : List Update) (rAcc : Finset ℕ) : Finset ℕ :=
  match us with
  | [] => rAcc ∩ cur.G.E
  | u :: rest =>
    let r := stepReembSet cur u
    let res := step cur u sparsify
    updateReembGo sparsify res.state rest (rAcc ∪ r)

/-- Surviving edges of `(update st U sparsify).state.G` whose embedding can change during
`update st U sparsify`. -/
def updateReembSet {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : Finset ℕ :=
  updateReembGo sparsify st U ∅

/-- Sorted duplicate-free list of `updateReembSet st U sparsify`. -/
def updateReembList {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) : List ℕ :=
  (updateReembSet st U sparsify).sort (· ≤ ·)

theorem updateReembSet_nil {L : ℕ} (st : DynSpannerState L)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    updateReembSet st [] sparsify = ∅ := by
  simp [updateReembSet, updateReembGo]

theorem updateReembGo_subset_G {L : ℕ}
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    ∀ (cur : DynSpannerState L) (U : List Update) (rAcc : Finset ℕ)
      (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      updateReembGo sparsify cur U rAcc ⊆ (updateGo sparsify cur U uhAcc dAcc cAcc).state.G.E
  | cur, [], rAcc, _, _, _ => by
    simp [updateReembGo, updateGo]
  | cur, u :: rest, rAcc, uhAcc, dAcc, cAcc =>
    updateReembGo_subset_G sparsify (step cur u sparsify).state rest (rAcc ∪ stepReembSet cur u)
      (uhAcc ++ (step cur u sparsify).UH) (dAcc ∪ (step cur u sparsify).D)
      (cAcc + (step cur u sparsify).cost)

theorem updateReembSet_subset_G {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    updateReembSet st U sparsify ⊆ (update st U sparsify).state.G.E :=
  updateReembGo_subset_G sparsify st U ∅ [] ∅ 0

private theorem card_updateReembGo_le_cost {L : ℕ}
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    ∀ (cur : DynSpannerState L) (U : List Update) (rAcc : Finset ℕ)
      (uhAcc : List Update) (dAcc : Finset ℕ) (cAcc : ℕ),
      (updateReembGo sparsify cur U rAcc).card + cAcc ≤
        rAcc.card + (updateGo sparsify cur U uhAcc dAcc cAcc).cost
  | cur, [], rAcc, _, _, cAcc => by
    simp only [updateReembGo, updateGo]
    have h := Finset.card_le_card (Finset.inter_subset_left (s₁ := rAcc) (s₂ := cur.G.E))
    omega
  | cur, u :: rest, rAcc, uhAcc, dAcc, cAcc => by
    simp only [updateReembGo, updateGo]
    have ih := card_updateReembGo_le_cost sparsify (step cur u sparsify).state rest
      (rAcc ∪ stepReembSet cur u) (uhAcc ++ (step cur u sparsify).UH)
      (dAcc ∪ (step cur u sparsify).D) (cAcc + (step cur u sparsify).cost)
    have hun := Finset.card_union_le rAcc (stepReembSet cur u)
    have hstep := card_stepReembSet_le_cost cur u sparsify
    omega

/-- The cardinality of `updateReembSet st U sparsify` is at most `(update st U sparsify).cost`. -/
theorem card_updateReembSet_le_cost {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (updateReembSet st U sparsify).card ≤ (update st U sparsify).cost := by
  have h := card_updateReembGo_le_cost sparsify st U ∅ [] ∅ 0
  simpa [updateReembSet, update] using h

theorem updateReembList_nodup {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (updateReembList st U sparsify).Nodup :=
  (updateReembSet st U sparsify).sort_nodup (· ≤ ·)

theorem mem_updateReembList {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (e : ℕ) :
    e ∈ updateReembList st U sparsify ↔ e ∈ updateReembSet st U sparsify :=
  Finset.mem_sort (· ≤ ·)

theorem updateReembList_toFinset {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (updateReembList st U sparsify).toFinset = updateReembSet st U sparsify := by
  ext e
  simp [mem_updateReembList]

theorem updateReembList_length {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (updateReembList st U sparsify).length = (updateReembSet st U sparsify).card :=
  Finset.length_sort (· ≤ ·)

/-- The length of `updateReembList st U sparsify` is at most `(update st U sparsify).cost`. -/
theorem updateReembList_length_le_cost {L : ℕ} (st : DynSpannerState L) (U : List Update)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) :
    (updateReembList st U sparsify).length ≤ (update st U sparsify).cost := by
  rw [updateReembList_length]
  exact card_updateReembSet_le_cost st U sparsify

/-- Per-step `stepReembSet` along a flat trace `us` at step `k`. -/
def runStepReembSet {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (us : List Update) (k : ℕ) : Finset ℕ :=
  match us[k]? with
  | some u => stepReembSet (runState (L := L) G₀ q sparsify us k) u
  | none => ∅

/-- Characterization of `updateReembGo` along a slice `U` matching `us[k₀ .. k₀ + U.length)`. -/
theorem updateReembGo_run_eq {L q : ℕ} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (G₀ : MGraph) (us : List Update) :
    ∀ (U : List Update) (k₀ : ℕ) (rAcc : Finset ℕ),
      (∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) →
      updateReembGo sparsify (runState (L := L) G₀ q sparsify us k₀) U rAcc =
        (rAcc ∪ (Finset.range U.length).biUnion fun i =>
          runStepReembSet (L := L) G₀ q sparsify us (k₀ + i)) ∩
          (runState (L := L) G₀ q sparsify us (k₀ + U.length)).G.E
  | [], k₀, rAcc, _ => by
    simp [updateReembGo]
  | u :: rest, k₀, rAcc, hmatch => by
    have hu_some : us[k₀]? = some u := by simpa using hmatch 0 (Nat.zero_lt_succ rest.length)
    have hst1 : runState (L := L) G₀ q sparsify us (k₀ + 1) =
        (step (runState (L := L) G₀ q sparsify us k₀) u sparsify).state := by
      simp [runState, hu_some]
    have hr0 : runStepReembSet (L := L) G₀ q sparsify us k₀ =
        stepReembSet (runState (L := L) G₀ q sparsify us k₀) u := by
      simp [runStepReembSet, hu_some]
    have ih := updateReembGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us rest (k₀ + 1)
      (rAcc ∪ stepReembSet (runState (L := L) G₀ q sparsify us k₀) u)
      fun i hi => by
        have h1 := hmatch (i + 1) (Nat.succ_lt_succ hi)
        rw [show k₀ + 1 + i = k₀ + (i + 1) by omega]
        exact h1
    dsimp only [updateReembGo]
    rw [← hst1, ih, ← hr0]
    have hidx : k₀ + 1 + rest.length = k₀ + (u :: rest).length := by
      simp only [List.length_cons]; omega
    rw [hidx]
    congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_range, List.length_cons]
    constructor
    · rintro ((hx | hx) | ⟨i, hi, hxi⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨0, Nat.zero_lt_succ _, by simpa using hx⟩
      · exact Or.inr ⟨i + 1, Nat.succ_lt_succ hi, by
          rwa [show k₀ + (i + 1) = k₀ + 1 + i by omega]⟩
    · rintro (hx | ⟨i, hi, hxi⟩)
      · exact Or.inl (Or.inl hx)
      · cases i with
        | zero => exact Or.inl (Or.inr (by simpa using hxi))
        | succ i' =>
          exact Or.inr ⟨i', Nat.lt_of_succ_lt_succ hi, by
            rwa [show k₀ + 1 + i' = k₀ + (i' + 1) by omega]⟩

/-- Characterization of `updateReembSet` along a slice `U` matching `us[k₀ .. k₀ + U.length)`. -/
theorem updateReembSet_run_eq {L q : ℕ} {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (G₀ : MGraph) (us U : List Update) (k₀ : ℕ)
    (hmatch : ∀ (i : ℕ) (hi : i < U.length), us[k₀ + i]? = some (U[i]'hi)) :
    updateReembSet (runState (L := L) G₀ q sparsify us k₀) U sparsify =
      ((Finset.range U.length).biUnion fun i =>
        runStepReembSet (L := L) G₀ q sparsify us (k₀ + i)) ∩
        (runState (L := L) G₀ q sparsify us (k₀ + U.length)).G.E := by
  simpa [updateReembSet] using
    updateReembGo_run_eq (L := L) (q := q) (sparsify := sparsify) G₀ us U k₀ ∅ hmatch

end

end MinCostFlow.DynSpanner
