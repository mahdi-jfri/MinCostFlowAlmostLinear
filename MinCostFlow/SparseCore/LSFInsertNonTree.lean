module

public import MinCostFlow.SparseCore.CompLSFBridge
public import MinCostFlow.SparseCore.Program.ReadWalk
public import MinCostFlow.SparseCore.Program.AssemblyModel

/-!
# Tree edge names and P10's sequential non-tree insert condition

This file proves the two facts that P10's update condition needs (`ReadBranchAt.step` in
`SparseCore/Program/ReadSpec.lean`):

1. **No bridge-edge name clash (`encTEdge`).** On every `CompLSFInv` state, each component
   `compGraph cs.G₀ C` is connected, so its spanning tree `T₀` has no bridge edges
   (`lsfInv_T_E_subset_G₀_of_connected`, `compLSF_encTEdge_eq_self` in `CompLSFBridge.lean`).
   Hence `encTEdge cs.G₀ C f = f` for every tree edge, `cs.T.E ⊆ cs.G₀.E`
   (`compLSF_T_E_subset_G₀`), and `∀ e ∈ cs.T.E, e < eCap` whenever `∀ e ∈ cs.G₀.E, e < eCap`
   (`compLSF_T_E_lt_cap`). Bridge names above `cs.G₀.E.sup id` never occur on reached states.

2. **Re-inserted edges and P10's sequential update condition.** `CompLSFState.T` keeps only the
   surviving original tree edges (`cs.T.E ⊆ cs.G.E \ cs.insertedGlobal`), so `cs.T.E ⊆ cs.G.E`
   (`compLSF_T_E_subset_G`), `cs.G.IsSubgraph cs.T` (`compLSF_G_isSubgraph_T`), and each valid
   update transforms `cs.T` by `Read.tViewUpdate` up to `Read.SameGraph`
   (`compLSFStepSingle_T_sameGraph`, `compLSFBatch_T_sameGraph`). Consequently, whenever `U` is a
   valid batch on `cs.G` (including batches from `buildUSOrd` that delete and re-insert edges of
   `D_reins` in the same batch), every inserted edge `U[k] = .insert e x z` is absent from
   `((U.take k).foldl Read.tViewUpdate cs.lsf.T).E` at the moment the walk inserts it
   (`compLSF_batch_insert_not_mem_T_at`) and from `(compLSFBatch cs U).lsf.T.E` after the batch
   (`compLSF_batch_insert_not_mem_T_after`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.Bundle MinCostFlow.DynSpanner
open MinCostFlow.SparseCore.Program MinCostFlow.SparseCore.Program.Read

/-! ## 1. No bridge-edge names in `CompLSFState.T` -/

/-- On any `CompLSFInv` state, every edge of `cs.T.E` is an original edge of `cs.G₀.E` (no bridge
edge names from the `else` branch of `encTEdge` ever appear). -/
theorem compLSF_T_E_subset_G₀ {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) : cs.T.E ⊆ cs.G₀.E := by
  intro e he
  have he1 : e ∈ (components cs.G₀).biUnion fun C =>
      (cs.compSt C).T_cur.E.image (encTEdge cs.G₀ C) := (Finset.mem_inter.mp he).1
  rw [Finset.mem_biUnion] at he1
  rcases he1 with ⟨C, hC, him⟩
  rcases Finset.mem_image.mp him with ⟨f, hfT, rfl⟩
  have hself := compLSF_encTEdge_eq_self hI hC hfT
  rw [hself.2]
  exact Finset.filter_subset _ _ hself.1

/-- On any `CompLSFInv` state, every edge of `cs.T.E` is at most `cs.G₀.E.sup id`. -/
theorem compLSF_T_E_le_sup {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.T.E) :
    e ≤ cs.G₀.E.sup id :=
  Finset.le_sup (f := id) (compLSF_T_E_subset_G₀ hI he)

/-- On any `CompLSFInv` state, if every initial edge of `cs.G₀` is below `eCap`, then every edge of
`cs.T` is below `eCap` (so `tCap = eCap` suffices for P10). -/
theorem compLSF_T_E_lt_cap {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {eCap : ℕ} (hCap : ∀ e ∈ cs.G₀.E, e < eCap) :
    ∀ e ∈ cs.T.E, e < eCap :=
  fun e he => hCap e (compLSF_T_E_subset_G₀ hI he)

/-- At initialization, `cs₀.T.E` is the union of the component spanning trees `(cs₀.compSt C).T_cur.E`
with no bridge-edge relabeling. -/
theorem compLSF_init_T_E_eq {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k) :
    let cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j
    cs₀.T.E = (components G₀).biUnion fun C => (cs₀.compSt C).T_cur.E := by
  intro cs₀
  have hI₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  ext e
  constructor
  · intro he
    have he1 : e ∈ (components G₀).biUnion fun C =>
        (cs₀.compSt C).T_cur.E.image (encTEdge G₀ C) := (Finset.mem_inter.mp he).1
    rw [Finset.mem_biUnion] at he1 ⊢
    rcases he1 with ⟨C, hC, him⟩
    rcases Finset.mem_image.mp him with ⟨f, hfT, rfl⟩
    have hEq : encTEdge G₀ C f = f := (compLSF_encTEdge_eq_self hI₀ hC hfT).2
    rw [hEq]
    exact ⟨C, hC, hfT⟩
  · intro he
    rw [Finset.mem_biUnion] at he
    rcases he with ⟨C, hC, hfT⟩
    have hself := compLSF_encTEdge_eq_self hI₀ hC hfT
    have heG₀ : e ∈ G₀.E := Finset.filter_subset _ _ hself.1
    refine Finset.mem_inter.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨heG₀, Finset.notMem_empty e⟩⟩
    exact Finset.mem_biUnion.mpr ⟨C, hC, Finset.mem_image.mpr ⟨e, hfT, hself.2⟩⟩

/-! ## 2. Subgraph property and `tViewUpdate` tracking of `CompLSFState.T` -/

/-- Every edge of `cs.T` is currently an edge of `cs.G`. -/
theorem compLSF_T_E_subset_G (cs : CompLSFState) : cs.T.E ⊆ cs.G.E :=
  fun _ he => (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1

/-- `cs.T.E` is disjoint from `cs.insertedGlobal`. -/
theorem compLSF_T_disjoint_insertedGlobal (cs : CompLSFState) :
    Disjoint cs.T.E cs.insertedGlobal :=
  Finset.disjoint_left.mpr fun _ he => (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).2

/-- `cs.T` is a subgraph of `cs.G` with the same vertex set and endpoints (`ReadView.Inv` agreement). -/
theorem compLSF_G_isSubgraph_T (cs : CompLSFState) : cs.G.IsSubgraph cs.T :=
  ⟨Finset.Subset.rfl, compLSF_T_E_subset_G cs, fun _ _ => ⟨rfl, rfl⟩⟩

private theorem compLSFStepSingle_T_base_eq (cs : CompLSFState) (u : Update) :
    ((components (compLSFStepSingle cs u).G₀).biUnion fun C =>
        (((compLSFStepSingle cs u).compSt C).T_cur.E.image (encTEdge (compLSFStepSingle cs u).G₀ C))) =
      ((components cs.G₀).biUnion fun C =>
        ((cs.compSt C).T_cur.E.image (encTEdge cs.G₀ C))) := by
  have hE : ∀ C, ((compLSFStepSingle cs u).compSt C).T_cur.E = (cs.compSt C).T_cur.E := by
    intro C
    change (applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u)).T_cur.E = _
    have hfold : ∀ (U : List Update) (S : LSFState), (applyLSFBatch S U).T_cur.E = S.T_cur.E := by
      intro U
      induction U with
      | nil => intro _; rfl
      | cons a rest ih =>
        intro S
        change (applyLSFBatch (applyLSFUpdate S a) rest).T_cur.E = S.T_cur.E
        rw [ih]
        cases a <;> rfl
    exact hfold _ _
  refine Finset.biUnion_congr rfl fun C _ => ?_
  rw [hE C]
  rfl

/-- One valid update transforms `cs.T` by `Read.tViewUpdate` up to `Read.SameGraph`. -/
theorem compLSFStepSingle_T_sameGraph {cs : CompLSFState} {u : Update}
    (hu : cs.G.UpdateIsValid u) :
    SameGraph (compLSFStepSingle cs u).T (tViewUpdate cs.T u) := by
  have hbase := compLSFStepSingle_T_base_eq cs u
  cases u with
  | delete e =>
    refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    change ((components (compLSFStepSingle cs (.delete e)).G₀).biUnion fun C =>
        (((compLSFStepSingle cs (.delete e)).compSt C).T_cur.E.image
          (encTEdge (compLSFStepSingle cs (.delete e)).G₀ C))) ∩
        ((compLSFStepSingle cs (.delete e)).G.E \ (compLSFStepSingle cs (.delete e)).insertedGlobal) =
      cs.T.E.erase e
    rw [hbase]
    ext f
    simp only [CompLSFState.T, compLSFStepSingle, updateInserted, MGraph.applyUpdate,
      Finset.mem_inter, Finset.mem_sdiff, Finset.mem_erase]
    tauto
  | insert e a b =>
    refine ⟨rfl, ?_, fun f hf => ?_⟩
    · change ((components (compLSFStepSingle cs (.insert e a b)).G₀).biUnion fun C =>
          (((compLSFStepSingle cs (.insert e a b)).compSt C).T_cur.E.image
            (encTEdge (compLSFStepSingle cs (.insert e a b)).G₀ C))) ∩
          ((compLSFStepSingle cs (.insert e a b)).G.E \
            (compLSFStepSingle cs (.insert e a b)).insertedGlobal) = cs.T.E
      rw [hbase]
      ext f
      have heG : e ∉ cs.G.E := hu.1
      simp only [CompLSFState.T, compLSFStepSingle, updateInserted, MGraph.applyUpdate,
        Finset.mem_inter, Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1, rfl | hfG, hni⟩
        · exact absurd (Or.inl rfl) hni
        · exact ⟨h1, hfG, fun h => hni (Or.inr h)⟩
      · rintro ⟨h1, hfG, hni⟩
        have hne : f ≠ e := fun h => heG (h ▸ hfG)
        exact ⟨h1, Or.inr hfG, fun h => h.elim hne hni⟩
    · have hfG : f ∈ cs.G.E := by
        have h1 : f ∈ (compLSFStepSingle cs (.insert e a b)).G.E \
            (compLSFStepSingle cs (.insert e a b)).insertedGlobal := (Finset.mem_inter.mp hf).2
        simp only [compLSFStepSingle, updateInserted, MGraph.applyUpdate, Finset.mem_sdiff,
          Finset.mem_insert] at h1
        exact h1.1.resolve_left fun h => h1.2 (Or.inl h)
      have hne : f ≠ e := fun h => hu.1 (h ▸ hfG)
      simp only [CompLSFState.T, compLSFStepSingle, tViewUpdate, MGraph.applyUpdate,
        Function.update_of_ne hne, and_self]
  | split v v' St Sh =>
    refine ⟨rfl, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    change ((components (compLSFStepSingle cs (.split v v' St Sh)).G₀).biUnion fun C =>
        (((compLSFStepSingle cs (.split v v' St Sh)).compSt C).T_cur.E.image
          (encTEdge (compLSFStepSingle cs (.split v v' St Sh)).G₀ C))) ∩
        ((compLSFStepSingle cs (.split v v' St Sh)).G.E \
          (compLSFStepSingle cs (.split v v' St Sh)).insertedGlobal) = cs.T.E
    rw [hbase]
    rfl

private theorem sameGraph_tViewUpdate {T₁ T₂ : MGraph} (h : SameGraph T₁ T₂) (u : Update) :
    SameGraph (tViewUpdate T₁ u) (tViewUpdate T₂ u) := by
  cases u with
  | insert _ _ _ => exact h
  | delete e =>
    refine ⟨h.1, ?_, fun f hf => h.2.2 f (Finset.mem_of_mem_erase hf)⟩
    dsimp only [tViewUpdate, MGraph.applyUpdate]
    rw [h.2.1]
  | split v v' St Sh =>
    refine ⟨?_, h.2.1, fun f hf => ?_⟩
    · dsimp only [tViewUpdate, MGraph.applyUpdate]
      rw [h.1]
    · obtain ⟨ht, hh⟩ := h.2.2 f hf
      dsimp only [tViewUpdate, MGraph.applyUpdate]
      rw [ht, hh]
      exact ⟨rfl, rfl⟩

/-- A valid batch transforms `cs.T` by `U.foldl Read.tViewUpdate` up to `Read.SameGraph`. -/
theorem compLSFBatch_T_sameGraph {cs : CompLSFState} :
    ∀ {U : List Update}, cs.G.BatchIsValid U →
      SameGraph (compLSFBatch cs U).T (U.foldl tViewUpdate cs.T)
  | [], _ => SameGraph.refl _
  | u :: rest, ⟨hu, hrest⟩ => by
    change SameGraph (compLSFBatch (compLSFStepSingle cs u) rest).T
      (rest.foldl tViewUpdate (tViewUpdate cs.T u))
    have h1 := compLSFStepSingle_T_sameGraph hu
    have h2 := compLSFBatch_T_sameGraph (cs := compLSFStepSingle cs u) hrest
    have h3 : ∀ (V : List Update) (T₁ T₂ : MGraph), SameGraph T₁ T₂ →
        SameGraph (V.foldl tViewUpdate T₁) (V.foldl tViewUpdate T₂) := by
      intro V
      induction V with
      | nil => intro _ _ h; exact h
      | cons a bs ih => intro _ _ h; exact ih _ _ (sameGraph_tViewUpdate h a)
    exact h2.trans (h3 rest _ _ h1)

/-- For any valid batch `U` on `cs.G`, `(compLSFBatch cs U).T.E = (U.foldl tViewUpdate cs.T).E`. -/
theorem compLSFBatch_T_E_eq_foldl {cs : CompLSFState} {U : List Update} (hU : cs.G.BatchIsValid U) :
    (compLSFBatch cs U).T.E = (U.foldl tViewUpdate cs.T).E :=
  (compLSFBatch_T_sameGraph hU).2.1

/-! ## 3. P10's sequential non-tree insert condition -/

/-- `tViewUpdate` preserves the edge-subset relation `T.E ⊆ G.E` across any batch. -/
theorem tViewUpdate_foldl_E_subset :
    ∀ (U : List Update) {G T : MGraph}, T.E ⊆ G.E →
      (U.foldl tViewUpdate T).E ⊆ (G.applyBatch U).E
  | [], _, _, hsub => hsub
  | u :: rest, G, T, hsub => by
    apply tViewUpdate_foldl_E_subset rest
    cases u with
    | insert e _ _ => exact hsub.trans (Finset.subset_insert e G.E)
    | delete e => exact Finset.erase_subset_erase e hsub
    | split _ _ _ _ => exact hsub

/-- `tViewUpdate` is monotone-decreasing on edge sets across any batch. -/
theorem tViewUpdate_foldl_E_sub_self :
    ∀ (U : List Update) (T : MGraph), (U.foldl tViewUpdate T).E ⊆ T.E
  | [], _ => Finset.Subset.rfl
  | u :: rest, T => (tViewUpdate_foldl_E_sub_self rest (tViewUpdate T u)).trans
      (tViewUpdate_E_subset T u)

/-- **Sequential non-tree insert condition for P10.** If `T.E ⊆ G.E` and `U` is a valid batch on `G`,
then every insertion `U[k] = .insert e x z` inserts an edge that is not in the tree at step `k`. -/
theorem tViewUpdate_insert_not_mem_T_at {G T : MGraph} {U : List Update}
    (hsub : T.E ⊆ G.E) (hU : G.BatchIsValid U) :
    ∀ k (hk : k < U.length), ∀ e x z, U[k] = Update.insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate T).E := by
  intro k hk e x z heq heT
  have hdrop := batchIsValid_drop k G U hU
  rw [(List.cons_getElem_drop_succ (h := hk)).symm, heq] at hdrop
  exact hdrop.1.1 (tViewUpdate_foldl_E_subset (U.take k) hsub heT)

/-- **Post-batch non-tree insert condition.** If `T.E ⊆ G.E` and `U` is a valid batch on `G`, then
no edge inserted anywhere in `U` belongs to the tree after `U`. -/
theorem tViewUpdate_insert_not_mem_T_after {G T : MGraph} {U : List Update}
    (hsub : T.E ⊆ G.E) (hU : G.BatchIsValid U) :
    ∀ e x z, Update.insert e x z ∈ U → e ∉ (U.foldl tViewUpdate T).E := by
  intro e x z hmem heT
  obtain ⟨k, hk, heq⟩ := List.mem_iff_getElem.mp hmem
  have hsplit : U.foldl tViewUpdate T = (U.drop k).foldl tViewUpdate ((U.take k).foldl tViewUpdate T) := by
    rw [← List.foldl_append, List.take_append_drop]
  rw [hsplit] at heT
  exact tViewUpdate_insert_not_mem_T_at hsub hU k hk e x z heq
    (tViewUpdate_foldl_E_sub_self (U.drop k) _ heT)

/-- P10's sequential update condition holds unconditionally for every `CompLSFState` and every valid
batch `U` on `cs.G`. -/
theorem compLSF_batch_insert_not_mem_T_at (cs : CompLSFState) {U : List Update}
    (hU : cs.G.BatchIsValid U) :
    ∀ k (hk : k < U.length), ∀ e x z, U[k] = Update.insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate cs.lsf.T).E :=
  tViewUpdate_insert_not_mem_T_at (compLSF_T_E_subset_G cs) hU

/-- No edge inserted by a valid batch `U` on `cs.G` belongs to `(compLSFBatch cs U).lsf.T.E`. -/
theorem compLSF_batch_insert_not_mem_T_after (cs : CompLSFState) {U : List Update}
    (hU : cs.G.BatchIsValid U) :
    ∀ e x z, Update.insert e x z ∈ U → e ∉ (compLSFBatch cs U).lsf.T.E := by
  intro e x z hmem
  rw [show (compLSFBatch cs U).lsf.T.E = (U.foldl tViewUpdate cs.lsf.T).E from
    compLSFBatch_T_E_eq_foldl hU]
  exact tViewUpdate_insert_not_mem_T_after (compLSF_T_E_subset_G cs) hU e x z hmem

/-- Specialization to a `BundleTreeState` branch for the sparse-core assembly. -/
theorem bundleTree_insert_not_mem_T_at {depth : ℕ} (tr : BundleTreeState depth) {U : List Update}
    (hU : tr.cs.G.BatchIsValid U) :
    ∀ k (hk : k < U.length), ∀ e x z, U[k] = Update.insert e x z →
      e ∉ ((U.take k).foldl tViewUpdate tr.cs.lsf.T).E :=
  compLSF_batch_insert_not_mem_T_at tr.cs hU

private theorem compLSFBatch_G_eq (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).G = cs.G.applyBatch U := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih => exact ih (compLSFStepSingle cs u)

/-- On every nonempty state reached by `SparseCoreOrdInput`, every branch tracks the current graph
`G`. -/
theorem sparseCoreOrdInput_cs_G_eq {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N st G ord n) :
    SparseCoreBundleState.isNonempty (L := L) st = true →
      ∀ j, (SparseCoreBundleState.trees (L := L) st j).cs.G = G := by
  induction hIn with
  | init G₀ ℓ₀ g₀ ord₀ _ _ _ _ _ =>
    intro _ j
    exact rfl
  | @update s₀ G₀ ord₀ n₀ _ U ℓ g ord' _ _ _ _ ih =>
    intro hne j
    by_cases hs : s₀.isNonempty = true
    · rw [asm_updateOrd_of_nonempty lsfInit C_lsst L sparsify params spanConst s₀ hs]
      change (compLSFBatch (s₀.trees j).cs U).G = G₀.applyBatch U
      rw [compLSFBatch_G_eq, ih hs j]
    · have hsF : s₀.isNonempty = false := Bool.eq_false_iff.mpr hs
      rw [asm_updateOrd_of_empty lsfInit C_lsst L sparsify params spanConst s₀ hsF] at hne
      exact absurd hne hs
  | @restart s₀ G₀ ord₀ n₀ _ j₀ _ ih =>
    have hR := sparseCoreBundleRestartTool_restart_eq lsfInit C_lsst L sparsify s₀ j₀
    have key : ∀ x : SparseCoreBundleState L, x =
        (if s₀.isNonempty = true then
          { isNonempty := s₀.isNonempty, k := s₀.k, ord := s₀.ord,
            trees := Function.update s₀.trees j₀
              (restartBundleTree L sparsify (s₀.trees j₀) s₀.ord) }
        else s₀) →
        x.isNonempty = true → ∀ j, (x.trees j).cs.G = G₀ := by
      intro x hx hne j
      subst hx
      by_cases hs : s₀.isNonempty = true
      · simp only [hs, ↓reduceIte]
        by_cases hjj : j = j₀
        · subst hjj
          simp only [Function.update_self]
          exact ih hs j
        · simp only [Function.update_of_ne hjj]
          exact ih hs j
      · simp only [hs] at hne
        exact absurd hne hs
    exact key _ hR

/-- On every state reached by the ordered sparse-core contract (`SparseCoreOrdInput`), the tree of
every branch `j` satisfies `T.E ⊆ G.E`. -/
theorem sparseCoreOrdInput_T_E_subset_G {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N st G ord n) (j : ℕ) :
    ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).lsfs st j).T.E ⊆
      G.E := by
  by_cases hne : SparseCoreBundleState.isNonempty (L := L) st = true
  · have hGeq : (SparseCoreBundleState.trees (L := L) st j).cs.G = G :=
      sparseCoreOrdInput_cs_G_eq hIn hne j
    change (if SparseCoreBundleState.isNonempty (L := L) st then
      (SparseCoreBundleState.trees (L := L) st j).cs.lsf else emptyLSF).T.E ⊆ G.E
    simp only [hne, ↓reduceIte, ← hGeq]
    exact compLSF_T_E_subset_G (SparseCoreBundleState.trees (L := L) st j).cs
  · have hneF : SparseCoreBundleState.isNonempty (L := L) st = false := Bool.eq_false_iff.mpr hne
    change (if SparseCoreBundleState.isNonempty (L := L) st then
      (SparseCoreBundleState.trees (L := L) st j).cs.lsf else emptyLSF).T.E ⊆ G.E
    simp only [hneF, Bool.false_eq_true, ↓reduceIte]
    exact Finset.empty_subset _

/-- P10's sequential update condition on every state reached by `SparseCoreOrdInput`. -/
theorem sparseCoreOrdInput_insert_not_mem_T_at {lsfInit : LSFInit} {C_lsst : ℝ} {L : ℕ}
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {params : ℕ → SparsifyParams} {spanConst : ℕ} {k M N : ℕ}
    {st : (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).State}
    {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (hIn : SparseCoreOrdInput
      (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst)
      k M N st G ord n) (j : ℕ) {U : List Update} (hU : G.BatchIsValid U) :
    ∀ idx (hidx : idx < U.length), ∀ e x z, U[idx] = Update.insert e x z →
      e ∉ ((U.take idx).foldl tViewUpdate
        ((sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params spanConst).lsfs st j).T).E :=
  tViewUpdate_insert_not_mem_T_at (sparseCoreOrdInput_T_E_subset_G hIn j) hU

end MinCostFlow.SparseCore
