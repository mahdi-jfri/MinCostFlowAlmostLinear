module

public import MinCostFlow.SparseCore.BundleStepLocal
public import MinCostFlow.SparseCore.BundleRunInvBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bundle stage of one component: the step lemma

The bundles of a component `C` and a bucket move by `bundleCompStep` along each input batch. This
file proves what one such step keeps, in the form that the run invariant `bundleRunSeq_stage_inv`
(`BundleStage.lean`) uses at every stage and that the restart of an epoch can use again:
`bundleCompStep_stage`.

Before the step the bundles of `C` form a partition for the core rotation of every rotation with
the given order, their parents are roots of `C`, and their edges are edges of the component
graph of `C`. After the step the same holds for the new order and the new component graph. The
bundles lose exactly the edges that the input batch deletes. They split at most twice per new
root of `C` (`bundleCompStep_local`). A component that the batch does not touch keeps its
bundles.

The file also has the facts about the projection of a batch onto a component that this needs,
and the facts about the initial bundles: their parents are roots of their component, and their
edges are edges of the component graph.
-/

public section

namespace MinCostFlow.SparseCore

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.Bundle MinCostFlow.DynSpanner

/-! ### Rotations and the initial bundles -/

/-- Two rotations with the same order give the same core rotation. -/
theorem coreRotation_eq_of_order {G : MGraph} {L : LSF} {ρ ρ' : Rotation G}
    (h : ρ.order = ρ'.order) (hG hG' : G.IsValid) (hF hF' : L.F.IsRootedSpanningForestOf G) :
    coreRotation ρ hG hF = coreRotation ρ' hG' hF' := by
  obtain rfl := Rotation.ext_order h
  rfl

/-- When the order is the order of a rotation and the component-wise LSF meets its invariant,
the initial bundle state is `initBundleState` for the core rotation of that rotation. -/
theorem initBundleFor_eq {cs : CompLSFState} {ord : ℕ → List End} {C_lsst : ℝ}
    {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ cs) {ρ : Rotation cs.G} (hρ : ρ.order = ord)
    (E : Finset ℕ) (k : ℕ) :
    initBundleFor cs ord E k =
      initBundleState (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) E k := by
  have h : ∃ (C_lsst : ℝ) (ℓ₀ : ℕ → ℝ) (_ : CompLSFInv C_lsst ℓ₀ cs) (ρ : Rotation cs.G),
      ρ.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
  unfold initBundleFor
  rw [dite_eq_left h]
  exact congrArg (fun σ => initBundleState σ E k)
    (coreRotation_eq_of_order (h.choose_spec.choose_spec.choose_spec.choose_spec.trans hρ.symm)
      _ _ _ _)

/-- Every initial bundle has an end of an admitted edge at its parent: a vertex without admitted
ends gets no chunk. -/
theorem initBundleState_parent_src {C : MGraph} (ρ : Rotation C) {E : Finset ℕ} (hE : E ⊆ C.E)
    (k : ℕ) : ∀ b ∈ (initBundleState ρ E k).vertices,
      ∃ x : End, x.1 ∈ E ∧ C.src x = (initBundleState ρ E k).parent b := by
  intro b hb
  have hi : b < (initialSlots ρ E k).length := Finset.mem_range.mp hb
  have hp : (initBundleState ρ E k).parent b = ((initialSlots ρ E k)[b]).1 := by
    simp [initBundleState, List.getElem?_eq_getElem hi]
  have hmem := List.getElem_mem hi
  generalize (initialSlots ρ E k)[b] = s at hp hmem
  obtain ⟨v, ys⟩ := s
  simp only [initialSlots, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨w, -, zs, hz, rfl, rfl⟩ := hmem
  have hne : restrictedEnds ρ E w ≠ [] := by
    intro h0
    rw [h0] at hz
    have hl := initialChunks_length k ([] : List End)
    have h00 : (0 : ℕ) ⌈/⌉ k = 0 := by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; rfl
      · exact Nat.le_zero.mp ((ceilDiv_le_iff_le_mul hk).2 (by simp))
    rw [List.length_nil, h00, List.length_eq_zero_iff] at hl
    rw [hl] at hz
    exact List.not_mem_nil hz
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  obtain ⟨hxE, hxv⟩ := (mem_restrictedEnds ρ hE w x).mp hx
  exact ⟨x, hxE, hxv.trans hp.symm⟩

/-- The source of an end in the core graph is the root of its source. -/
theorem coreGraph_src (G : MGraph) (L : LSF) (x : End) :
    (coreGraph G L).src x = L.F.root (G.src x) := by
  obtain ⟨e, b⟩ := x
  cases b <;> rfl

/-- A vertex whose root lies in the vertex set of the component state of `C` lies there too. -/
theorem compLSF_mem_V_of_root {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) {v : ℕ}
    (hv : v ∈ cs.G.V) (hr : cs.RF.root v ∈ (cs.compSt C).G.V) : v ∈ (cs.compSt C).G.V := by
  rw [← hI.hV_eq] at hv
  obtain ⟨D, hD, hvD⟩ := Finset.mem_biUnion.mp hv
  have hrD : cs.RF.root v ∈ (cs.compSt D).G.V := by
    have hID := (hI.hCompLSF D hD).1
    rw [compLSF_RF_root_eq hI hD hvD]
    exact lsfInv_R_sub_V hID (rootedForest_root_spec (lsfInv_to_RS hID) hvD).1
  by_cases hDC : D = C
  · exact hDC ▸ hvD
  · exact absurd hr (Finset.disjoint_left.mp (hI.hV_disj D hD C hC hDC) hrD)

/-- The root of a vertex of the component state of `C` is a root of `C`. -/
theorem compLSF_root_mem_R {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀) {v : ℕ}
    (hv : v ∈ (cs.compSt C).G.V) : cs.RF.root v ∈ (cs.compSt C).R := by
  rw [compLSF_RF_root_eq hI hC hv]
  exact (rootedForest_root_spec (lsfInv_to_RS (hI.hCompLSF C hC).1) hv).1

/-- If the edges `E` are core edges of the component graph of `C`, then the initial bundles on
`E` have their parents among the roots of `C`. -/
theorem initBundleState_parent_mem {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    (ρ : Rotation (coreGraph cs.G cs.lsf)) {E : Finset ℕ} (hE : E ⊆ (coreGraph cs.G cs.lsf).E)
    (hEC : E ⊆ (cs.compSt C).G.E) (hX : ∀ e ∈ E, e ∉ cs.crossEdges) (k : ℕ) :
    ∀ b ∈ (initBundleState ρ E k).vertices,
      (initBundleState ρ E k).parent b ∈ (cs.compSt C).R := by
  intro b hb
  obtain ⟨x, hxE, hxp⟩ := initBundleState_parent_src ρ hE k b hb
  rw [← hxp, coreGraph_src]
  obtain ⟨e, side⟩ := x
  have heC := hEC hxE
  have hends := hI.hNonCross_ends C hC e heC (hX e hxE)
  have hval := (hI.hCompLSF C hC).1.hG_val e heC
  apply compLSF_root_mem_R hI hC
  cases side
  · change cs.G.head e ∈ _
    rw [← hends.2]
    exact hval.2
  · change cs.G.tail e ∈ _
    rw [← hends.1]
    exact hval.1

/-! ### The projection of a batch onto a component -/

/-- The projection of one valid update deletes an existing edge of `G_C` only if the update deletes
it. -/
theorem projCompUpdateG_delete (G G_C : MGraph) (u : Update)
    (hsub : G_C.E ⊆ G.E) (hu : G.UpdateIsValid u) :
    ∀ op ∈ projCompUpdateG G G_C u, ∀ e ∈ G_C.E, op = .delete e → u = .delete e := by
  intro op hop e he hdel
  subst hdel
  cases u with
  | insert f a b =>
    simp only [projCompUpdateG] at hop
    split_ifs at hop <;> simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      Update.delete.injEq, false_or] at hop
    · exact absurd (hop ▸ hsub he) hu.1
    · exact absurd (hop ▸ hsub he) hu.1
  | delete f =>
    simp only [projCompUpdateG] at hop
    split_ifs at hop
    · rw [List.mem_singleton.mp hop]
    · simp at hop
  | split v v' St Sh =>
    simp only [projCompUpdateG] at hop
    split_ifs at hop <;> simp at hop

/-- The edge subset invariant `G_C.E ⊆ G.E` is preserved by one projected update step. -/
private theorem projCompUpdateG_E_sub (G G_C : MGraph) (u : Update) (hsub : G_C.E ⊆ G.E) :
    (G_C.applyBatch (projCompUpdateG G G_C u)).E ⊆ (G.applyUpdate u).E := by
  classical
  intro f hf
  cases u with
  | delete e₀ =>
    dsimp only [projCompUpdateG] at hf
    split_ifs at hf with he₀
    · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Finset.mem_erase] at hf ⊢
      exact ⟨hf.1, hsub hf.2⟩
    · exact Finset.mem_erase.mpr ⟨fun h => he₀ (h ▸ hf), hsub hf⟩
  | insert e₀ a b =>
    dsimp only [projCompUpdateG] at hf
    split_ifs at hf
    · rcases Finset.mem_insert.mp hf with rfl | hfC
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (hsub hfC)
    · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Finset.mem_erase, Finset.mem_insert] at hf
      exact Finset.mem_insert_of_mem (hsub (hf.2.resolve_left hf.1))
    · simp only [MGraph.applyBatch, List.foldl_cons, List.foldl_nil, MGraph.applyUpdate,
        Finset.mem_erase, Finset.mem_insert] at hf
      exact Finset.mem_insert_of_mem (hsub (hf.2.resolve_left hf.1))
    · exact Finset.mem_insert_of_mem (hsub hf)
  | split v v' St Sh =>
    dsimp only [projCompUpdateG] at hf
    split_ifs at hf <;> exact hsub hf

/-- An edge of a graph stays when no update of the batch deletes it. -/
theorem mem_applyBatch_E_of_not_delete (G : MGraph) (V : List Update) {e : ℕ} (he : e ∈ G.E)
    (hd : Update.delete e ∉ V) : e ∈ (G.applyBatch V).E := by
  by_contra hn
  exact hd (exists_delete_of_mem_sdiff_applyBatch G V he hn)

/-- A deletion of an existing edge `e ∈ G_C.E` in the projection of a valid batch is a deletion of
the batch. -/
theorem mem_batchDeletes_of_proj :
    ∀ (U : List Update) (G G_C : MGraph) {e : ℕ},
      G_C.E ⊆ G.E → G.BatchIsValid U → e ∈ G_C.E →
      Update.delete e ∈ projCompBatchG G G_C U → e ∈ batchDeletes U
  | [], _, _, _, _, _, _, h => by simp [projCompBatchG] at h
  | u :: rest, G, G_C, e, hsub, ⟨hu, hrest⟩, he, h => by
    rw [mem_batchDeletes_iff]
    change Update.delete e ∈ projCompUpdateG G G_C u ++
      projCompBatchG (G.applyUpdate u) (G_C.applyBatch (projCompUpdateG G G_C u)) rest at h
    rcases List.mem_append.mp h with h | h
    · exact ⟨u, List.mem_cons_self, projCompUpdateG_delete G G_C u hsub hu _ h e he rfl⟩
    · by_cases hue : u = .delete e
      · exact ⟨u, List.mem_cons_self, hue⟩
      · have he' : e ∈ (G_C.applyBatch (projCompUpdateG G G_C u)).E :=
          mem_applyBatch_E_of_not_delete _ _ he fun hdel =>
            hue (projCompUpdateG_delete G G_C u hsub hu _ hdel e he rfl)
        obtain ⟨w, hw, hwe⟩ := (mem_batchDeletes_iff _ _).mp
          (mem_batchDeletes_of_proj rest _ _ (projCompUpdateG_E_sub G G_C u hsub) hrest he' h)
        exact ⟨w, List.mem_cons_of_mem _ hw, hwe⟩

/-- The projection of a valid batch deletes every edge of the component graph that the batch
deletes. -/
theorem delete_mem_projCompBatchG :
    ∀ (U : List Update) (G G_C : MGraph) {e : ℕ},
      G_C.E ⊆ G.E → G.BatchIsValid U → e ∈ G_C.E → e ∈ batchDeletes U →
      Update.delete e ∈ projCompBatchG G G_C U
  | [], _, _, _, _, _, _, h => by simp [mem_batchDeletes_iff] at h
  | u :: rest, G, G_C, e, hsub, ⟨hu, hrest⟩, he, hd => by
    change Update.delete e ∈ projCompUpdateG G G_C u ++
      projCompBatchG (G.applyUpdate u) (G_C.applyBatch (projCompUpdateG G G_C u)) rest
    by_cases hu_eq : u = .delete e
    · subst hu_eq
      refine List.mem_append_left _ ?_
      simp [projCompUpdateG, he]
    · have hrest_d : e ∈ batchDeletes rest := by
        obtain ⟨w, hw, rfl⟩ := (mem_batchDeletes_iff _ _).mp hd
        rcases List.mem_cons.mp hw with hw | hw
        · exact absurd hw.symm hu_eq
        · exact (mem_batchDeletes_iff _ _).mpr ⟨_, hw, rfl⟩
      have he' : e ∈ (G_C.applyBatch (projCompUpdateG G G_C u)).E :=
        mem_applyBatch_E_of_not_delete _ _ he fun h =>
          hu_eq (projCompUpdateG_delete G G_C u hsub hu _ h e he rfl)
      exact List.mem_append_right _ (delete_mem_projCompBatchG rest _ _
        (projCompUpdateG_E_sub G G_C u hsub) hrest he' hrest_d)

/-- An edge of the component graph that a valid batch does not delete stays in the component
graph. -/
theorem mem_proj_E_of_not_deleted (U : List Update) (G G_C : MGraph) {e : ℕ}
    (hsub : G_C.E ⊆ G.E) (hU : G.BatchIsValid U) (he : e ∈ G_C.E)
    (hd : e ∉ batchDeletes U) : e ∈ (G_C.applyBatch (projCompBatchG G G_C U)).E :=
  mem_applyBatch_E_of_not_delete _ _ he fun h => hd (mem_batchDeletes_of_proj U G G_C hsub hU he h)

/-- A valid batch with an empty projection onto a component deletes no edge of the component
graph. -/
theorem not_deleted_of_proj_nil {U : List Update} {G G_C : MGraph}
    (hsub : G_C.E ⊆ G.E) (hU : G.BatchIsValid U)
    (h : projCompBatchG G G_C U = []) {e : ℕ} (he : e ∈ G_C.E) : e ∉ batchDeletes U := by
  intro hd
  have hm := delete_mem_projCompBatchG U G G_C hsub hU he hd
  rw [h] at hm
  exact List.not_mem_nil hm

/-! ### The component states along a batch -/

/-- An LSF batch keeps the lineage of an LSF state. -/
theorem lsfDerivedFrom_batch {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ S : LSFState} {V : List Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hV : S.G.BatchIsValid V) (hD : LSFDerivedFrom S₀ S) :
    LSFDerivedFrom S₀ (applyLSFBatch S V) := by
  have h := applyLSFBatch_inv_with V hI hV
  exact ⟨h.2.2.1.trans hD.hG₀_eq, hD.hS₀_G, h.2.2.2.1.trans hD.hT₀_eq,
    h.2.2.2.2.2.2.2.1.trans hD.hW_eq, hD.hS₀_iso, hD.hR_sub.trans h.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.1.trans hD.hFE_sub⟩

/-- A batch adds at most `56 |U| log² (n + 2)` roots to a component, where `n` is the number of
vertices of the initial graph (paper Lemma 5.4, page 18). -/
theorem compLSFBatch_compSt_R_card_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) {C : Finset ℕ}
    (hC : C ∈ components cs.G₀) :
    ((((compLSFBatch cs U).compSt C).R.card : ℕ) : ℝ) ≤ ((cs.compSt C).R.card : ℝ) +
      56 * (U.length : ℝ) * (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 := by
  have hb := compLSFBatch_compSt_R_le_compN hI hU hC
  have hsq : (Real.log (((compGraph cs.G₀ C).n : ℝ) + 2)) ^ 2 ≤
      (Real.log ((cs.G₀.n : ℝ) + 2)) ^ 2 :=
    pow_le_pow_left₀ (by linarith [half_lt_log_add_two (compGraph cs.G₀ C).n])
      (Real.log_le_log (by positivity)
        (by linarith [show ((compGraph cs.G₀ C).n : ℝ) ≤ cs.G₀.n from
          by exact_mod_cast compGraph_n_le hC])) 2
  have hnn : (0 : ℝ) ≤ 56 * (U.length : ℝ) := by positivity
  linarith [mul_le_mul_of_nonneg_left hsq hnn]

/-! ### One step of the bundles of a component -/

/-- The bundles of a component `C` before a step: a partition for the core rotation of every
rotation with order `ord`, with parents among the roots of `C` and edges in the component graph
of `C`. -/
@[expose] def BundleCompReady (cs : CompLSFState) (C : Finset ℕ) (B : BundleState) (k : ℕ)
    (ord : ℕ → List End) : Prop :=
  (∀ (ρ : Rotation cs.G) (hG : cs.G.IsValid) (hF : cs.RF.IsRootedSpanningForestOf cs.G),
    ρ.order = ord → B.IsPartition (coreRotation (L := cs.lsf) ρ hG hF) k) ∧
  (∀ b ∈ B.vertices, B.parent b ∈ (cs.compSt C).R) ∧
  B.edges ⊆ (cs.compSt C).G.E

/-- One step of the bundles of a component. On an ordered
valid batch, the bundles of a component `C` that are ready before the step are ready after it
for the new order. The bundle batch is valid, has only deletions and splits, at most two splits
per new root of `C`, and at most one deletion per bundle edge that the input deletes. The
bundles lose exactly the edges that the input deletes, and a component that the batch does not
touch keeps its bundles. -/
theorem bundleCompStep_stage {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState} {B : BundleState}
    {k : ℕ} {ord ord' : ℕ → List End} {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs)
    (hU : cs.G.BatchIsValid U) {ρ : Rotation cs.G} {σ : Rotation (cs.G.applyBatch U)}
    (hρ : ρ.order = ord) (hσ : σ.order = ord') (hrot : RotationBatch 2 U ρ σ)
    {C : Finset ℕ} (hC : C ∈ components cs.G₀) (hB : BundleCompReady cs C B k ord) :
    let out := bundleCompStep cs B k ord ord' U
    BundleCompReady (compLSFBatch cs U) C out.2 k ord' ∧
    out.2.edges = B.edges \ batchDeletes U ∧
    B.graph.BatchIsValid out.1 ∧ out.2.graph = B.graph.applyBatch out.1 ∧
    (∀ op ∈ out.1, isDelOrSplit op) ∧
    batchSplitCount out.1 ≤ 2 * (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card ∧
    out.1.countP deleteTag ≤ (B.edges ∩ batchDeletes U).card ∧
    out.2.vertices.card = B.vertices.card + batchSplitCount out.1 ∧
    (C ∉ touchedCompsBatch cs U → out = ([], B)) := by
  intro out
  obtain ⟨hP, hpar, hE⟩ := hB
  have hR : BundleStepReady cs B k ord ord' U :=
    ⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hrot, hU, hP ρ _ _ hρ⟩
  have hspec := bundleCompStep_spec hR
  obtain ⟨hpar', -⟩ := bundleCompStep_local_state hR C hC hpar
  have hloc := bundleCompStep_local hR C hC hpar
  have hEq := bundleCompStep_edges_eq hR
  have hcomp := compLSFBatch_compSt hI hU hC
  refine ⟨⟨hspec.1, hpar', ?_⟩, hEq, hspec.2.1, hspec.2.2.1, hspec.2.2.2.1, hloc.1,
    bundleCompStep_deletes_le hR, hspec.2.2.2.2.2.2, fun hnt => ?_⟩
  · rw [hEq, hcomp.2.1]
    intro e he
    obtain ⟨heB, hnd⟩ := Finset.mem_sdiff.mp he
    exact mem_proj_E_of_not_deleted U cs.G (cs.compSt C).G (hI.hCE_sub C hC) hU (hE heB) hnd
  · have hunt := compLSFBatch_untouched hI hU hC hnt
    refine bundleCompStep_unchanged hR C hC hpar (by rw [hunt.2]) ?_
    exact Finset.disjoint_left.mpr fun e he =>
      not_deleted_of_proj_nil (hI.hCE_sub C hC) hU hunt.1 (hE he)

end MinCostFlow.SparseCore
