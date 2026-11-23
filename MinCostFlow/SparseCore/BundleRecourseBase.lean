module

public import MinCostFlow.SparseCore.BundleRun
public import MinCostFlow.SparseCore.BundleConstants

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Base helpers for bundle-graph sparse-core recourse

Provides the reusable bounds and counting lemmas for `BundleEpochRecourse.lean` and
`BundleRecourse.lean`:

1. Positivity, monotonicity, and split-budget bounds for the degree-free constants of
   `BundleConstants.lean` (`bundleSplitBudget`, `bundleUCRatio`, `bundleLambdaS`,
   `bundleBucketRecUH`, `bundleBucketRecD`, `bundleRecoursePerQ`).
2. Initial bundle-graph size bounds (`n ≤ 2 m`, `m ≤ G₀.m`) and pairwise disjointness of
   `bucketCoreEdges` across `(component, bucket)` pairs.
3. Exact deletion-and-split counting for valid `isDelOrSplit` batches, component-wise root-growth
   summation, `bundleBatchList` length alignment, and `bundleRunSeq` root-growth bounds.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Constant positivity, monotonicity, and split-budget bounds -/

lemma bundleRec_splitBudget_le {k M : ℕ} (hk : 1 ≤ k) :
    bundleSplitBudget k M ≤ 2 * (56 * M + 1) := by
  unfold bundleSplitBudget
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M := by
    refine Nat.ceil_le.mpr ?_
    exact (div_le_self (by positivity) hk1).trans (by norm_cast)
  omega

lemma bundleRec_UCRatio_nonneg (n₀ : ℕ) : 0 ≤ bundleUCRatio n₀ := by
  unfold bundleUCRatio
  positivity

lemma bundleRec_UCRatio_mono {n₁ n₂ : ℕ} (h : n₁ ≤ n₂) :
    bundleUCRatio n₁ ≤ bundleUCRatio n₂ := by
  unfold bundleUCRatio
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  linarith

lemma bundleRec_LambdaS_ge_one (P_b : SparsifyParams) (m₀ : ℕ) :
    1 ≤ bundleLambdaS P_b m₀ := by
  unfold bundleLambdaS
  refine one_le_pow₀ ?_
  have : (1 : ℝ) ≤ (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg this]

lemma bundleRec_LambdaS_nonneg (P_b : SparsifyParams) (m₀ : ℕ) :
    0 ≤ bundleLambdaS P_b m₀ :=
  le_trans zero_le_one (bundleRec_LambdaS_ge_one P_b m₀)

lemma bundleRec_BucketRec_nonneg (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) :
    0 ≤ bundleBucketRecUH L P_b m₀ ∧ 0 ≤ bundleBucketRecD L P_b m₀ ∧
      0 ≤ coreE82Len L P_b := by
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hnr : 0 ≤ bundleNRoot L m₀ := by unfold bundleNRoot; positivity
  have hlam : 0 ≤ bundleLambdaS P_b m₀ := bundleRec_LambdaS_nonneg P_b m₀
  refine ⟨?_, ?_, ?_⟩
  · unfold bundleBucketRecUH; positivity
  · unfold bundleBucketRecD; positivity
  · unfold coreE82Len; positivity

lemma bundleRec_PerQ_mono_n (L : ℕ) (P_b : SparsifyParams) (m₀ : ℕ) {n₁ n₂ : ℕ} (h : n₁ ≤ n₂)
    (B : ℕ) :
    bundleRecoursePerQ L P_b m₀ n₁ B ≤ bundleRecoursePerQ L P_b m₀ n₂ B := by
  unfold bundleRecoursePerQ
  have huc := bundleRec_UCRatio_mono h
  have h1 : 0 ≤ Real.log ((n₁ : ℝ) + 2) := (half_lt_log_add_two n₁).le.trans' (by norm_num)
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((n₁ : ℝ) + 2) ≤ Real.log ((n₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  have hcp := bundleRec_BucketRec_nonneg L P_b m₀
  have hc : 0 ≤ (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b m₀ +
      2 * bundleBucketRecD L P_b m₀) := by
    have h1' := hcp.1; have h2' := hcp.2.1; have h3' := hcp.2.2; positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show 2 * bundleUCRatio n₁ ≤ 2 * bundleUCRatio n₂ by linarith) hc
  linarith

/-! ## 2. Initial bundle-graph sizes and bucket disjointness -/

private lemma flatMap_initialSlots_len_le {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    {k : ℕ} (hk : 1 ≤ k) (vs : List ℕ) :
    (vs.flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)).length ≤
      (vs.flatMap (restrictedEnds ρ E)).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, initialChunks_length]
    have hceil : (restrictedEnds ρ E v).length ⌈/⌉ k ≤ (restrictedEnds ρ E v).length :=
      (ceilDiv_le_iff_le_mul hk).2 (Nat.le_mul_of_pos_left _ hk)
    omega

/-- Every initial bundle state on an edge subset `E` has at most `2 |E|` bundle vertices. -/
lemma bundleRec_initBundleState_n_le_two_m {C : MGraph} (ρ : Rotation C)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 1 ≤ k) :
    (initBundleState ρ E k).graph.n ≤ 2 * (initBundleState ρ E k).graph.m := by
  change (Finset.range (initialSlots ρ E k).length).card ≤ 2 * E.card
  rw [Finset.card_range]
  let zs := (C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)
  have hnodup : zs.Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun v _ => (ρ.nodup v).filter _, ?_⟩
    apply List.Pairwise.imp_of_mem _ (Finset.sort_nodup C.V (· ≤ ·))
    intro v w _ _ hne
    apply List.disjoint_left.mpr
    intro x hv hw
    exact hne (((mem_restrictedEnds ρ hE v x).mp hv).2.symm.trans
      ((mem_restrictedEnds ρ hE w x).mp hw).2)
  have hsub : zs.toFinset ⊆ edgeEnds E := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨v, _, hv⟩ := List.mem_flatMap.mp hx
    exact (mem_edgeEnds E x).mpr ((mem_restrictedEnds ρ hE v x).mp hv).1
  have hzs_len : zs.length ≤ 2 * E.card := by
    rw [← List.toFinset_card_of_nodup hnodup, ← card_edgeEnds]
    exact Finset.card_le_card hsub
  exact le_trans (flatMap_initialSlots_len_le ρ E hk (C.V.sort (· ≤ ·))) hzs_len

/-- Initial bundle state bounds for `initBundleFor`: edges lie in `E`, `m ≤ |E|`, and `n ≤ 2 m`. -/
lemma bundleRec_initBundleFor_bounds (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ)
    {k : ℕ} (hk : 1 ≤ k) (hE : E ⊆ (coreGraph cs.G cs.lsf).E) :
    (initBundleFor cs ord E k).edges ⊆ E ∧
    (initBundleFor cs ord E k).graph.m ≤ E.card ∧
    (initBundleFor cs ord E k).graph.n ≤ 2 * (initBundleFor cs ord E k).graph.m := by
  classical
  unfold initBundleFor
  split_ifs with h
  · refine ⟨Finset.Subset.refl _, le_rfl,
      bundleRec_initBundleState_n_le_two_m _ hE hk⟩
  · exact ⟨Finset.empty_subset _, Nat.zero_le _, by simp [BundleState.graph, MGraph.n, MGraph.m]⟩

lemma bundleRec_bucketCoreEdges_sub (G₀ : MGraph) (L : LSF) (origB : ℕ → ℤ)
    (C : Finset ℕ) (b : ℤ) :
    bucketCoreEdges (coreGraph G₀ L) origB C b ⊆ (coreGraph G₀ L).E ∧
    (bucketCoreEdges (coreGraph G₀ L) origB C b).card ≤ G₀.m := by
  have h1 : bucketCoreEdges (coreGraph G₀ L) origB C b ⊆ (coreGraph G₀ L).E :=
    Finset.filter_subset _ _
  have h2 : (coreGraph G₀ L).E ⊆ G₀.E := Finset.sdiff_subset
  exact ⟨h1, Finset.card_le_card (Finset.Subset.trans h1 h2)⟩

lemma bundleRec_bucketCoreEdges_disjoint (G₀ : MGraph) (C₀ : MGraph) (origB : ℕ → ℤ)
    {C₁ C₂ : Finset ℕ} (hC₁ : C₁ ∈ components G₀) (hC₂ : C₂ ∈ components G₀)
    {b₁ b₂ : ℤ} (hne : (C₁, b₁) ≠ (C₂, b₂)) :
    Disjoint (bucketCoreEdges C₀ origB C₁ b₁) (bucketCoreEdges C₀ origB C₂ b₂) := by
  classical
  rw [Finset.disjoint_left]
  intro e he₁ he₂
  simp only [bucketCoreEdges, Finset.mem_filter] at he₁ he₂
  by_cases hCeq : C₁ = C₂
  · apply hne
    exact Prod.ext hCeq (he₁.2.2.symm.trans he₂.2.2)
  · exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hCeq) he₁.2.1 he₂.2.1

/-! ## 3. Del-or-split batch counting and component root growth -/

lemma bundleRec_isDelOrSplit_length {U : List Update} (h : ∀ op ∈ U, isDelOrSplit op) :
    U.length = U.countP deleteTag + batchSplitCount U := by
  induction U with
  | nil => rfl
  | cons u rest ih =>
    have hu := h u List.mem_cons_self
    have hrest : ∀ op ∈ rest, isDelOrSplit op := fun op hop => h op (List.mem_cons_of_mem _ hop)
    cases u with
    | insert _ _ _ => exact hu.elim
    | delete _ =>
      simp only [List.length_cons, List.countP_cons, deleteTag, batchSplitCount, isSplit,
        Bool.false_eq_true, ↓reduceIte, ih hrest]
      omega
    | split _ _ _ _ =>
      simp only [List.length_cons, List.countP_cons, deleteTag, batchSplitCount, isSplit,
        Bool.false_eq_true, ↓reduceIte, ih hrest]
      omega

private lemma not_mem_batchDeletes_of_delOrSplit {G : MGraph} {U : List Update} {e : ℕ}
    (hV : G.BatchIsValid U) (hDS : ∀ op ∈ U, isDelOrSplit op) (he : e ∉ G.E) :
    e ∉ batchDeletes U := by
  induction U generalizing G with
  | nil => simp [batchDeletes]
  | cons u rest ih =>
    have hu := hDS u List.mem_cons_self
    have hrest : ∀ op ∈ rest, isDelOrSplit op := fun op hop => hDS op (List.mem_cons_of_mem _ hop)
    intro hmem
    rw [mem_batchDeletes_iff] at hmem
    obtain ⟨u', hu', hEq⟩ := hmem
    rcases List.mem_cons.mp hu' with rfl | hmem_rest
    · cases hEq; exact he hV.1
    · have hne_next : e ∉ (G.applyUpdate u).E := by
        cases u with
        | insert _ _ _ => exact hu.elim
        | delete e' =>
          simp only [MGraph.applyUpdate, Finset.mem_erase, not_and]
          intro _; exact he
        | split _ _ _ _ => exact he
      exact ih hV.2 hrest hne_next ((mem_batchDeletes_iff rest e).mpr ⟨u', hmem_rest, hEq⟩)

/-- In a valid batch with only deletions and vertex splits, each deleted edge is deleted at most
once, so `U.countP deleteTag = (batchDeletes U).card`. -/
lemma bundleRec_countP_deleteTag_eq_card_batchDeletes {G : MGraph} {U : List Update}
    (hV : G.BatchIsValid U) (hDS : ∀ op ∈ U, isDelOrSplit op) :
    U.countP deleteTag = (batchDeletes U).card := by
  induction U generalizing G with
  | nil => simp [batchDeletes]
  | cons u rest ih =>
    have hu := hDS u List.mem_cons_self
    have hrest : ∀ op ∈ rest, isDelOrSplit op := fun op hop => hDS op (List.mem_cons_of_mem _ hop)
    cases u with
    | insert _ _ _ => exact hu.elim
    | delete e =>
      have he_not : e ∉ (G.applyUpdate (.delete e)).E := by
        simp [MGraph.applyUpdate]
      have hnot_rest : e ∉ batchDeletes rest :=
        not_mem_batchDeletes_of_delOrSplit hV.2 hrest he_not
      have hbd : batchDeletes (.delete e :: rest) = insert e (batchDeletes rest) := by
        ext x
        simp only [mem_batchDeletes_iff, Finset.mem_insert, List.mem_cons, exists_eq_or_imp,
          Update.delete.injEq]
        tauto
      simp only [hbd, Finset.card_insert_of_notMem hnot_rest, List.countP_cons, deleteTag,
        ↓reduceIte, ih hV.2 hrest]
    | split v v' St Sh =>
      have hbd : batchDeletes (.split v v' St Sh :: rest) = batchDeletes rest := by
        ext x
        simp only [mem_batchDeletes_iff, List.mem_cons, exists_eq_or_imp, reduceCtorEq, false_or]
      simp only [hbd, List.countP_cons, deleteTag, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
        ih hV.2 hrest]

lemma bundleRec_batchDeletes_sub_of_local {U UB : List Update} {E : Finset ℕ}
    (hloc : ∀ op ∈ UB, deleteTag op = true → ∃ e ∈ E, op = .delete e ∧ e ∈ batchDeletes U) :
    batchDeletes UB ⊆ E ∩ batchDeletes U := by
  intro e he
  obtain ⟨u, hu, rfl⟩ := (mem_batchDeletes_iff UB e).mp he
  obtain ⟨e', he'E, hEq, he'U⟩ := hloc (.delete e) hu rfl
  cases hEq
  exact Finset.mem_inter.mpr ⟨he'E, he'U⟩

/-- The sum of component-wise new roots equals the global count of new roots. -/
lemma bundleRec_sum_comp_R_sdiff_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {U : List Update} (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U) :
    ((components cs.G₀).sum fun C => (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card) =
      ((compLSFBatch cs U).RF.R \ cs.RF.R).card := by
  have hdisj_R : ∀ (st : CompLSFState), CompLSFInv C_lsst ℓ₀ st →
      st.RF.R.card = (components st.G₀).sum fun C => (st.compSt C).R.card := by
    intro st hIst
    change ((components st.G₀).biUnion fun C => (st.compSt C).R).card = _
    rw [Finset.card_biUnion]
    intro C₁ hC₁ C₂ hC₂ hne
    exact (hIst.hV_disj C₁ hC₁ C₂ hC₂ hne).mono
      (lsfInv_R_sub_V (hIst.hCompLSF C₁ hC₁).1) (lsfInv_R_sub_V (hIst.hCompLSF C₂ hC₂).1)
  have hI' := compLSFBatch_inv hI hU
  have hR_sub : cs.RF.R ⊆ (compLSFBatch cs U).RF.R := (compLSFBatch_decremental hI hU).2
  have hcomp_sub : ∀ C ∈ components cs.G₀, (cs.compSt C).R ⊆ ((compLSFBatch cs U).compSt C).R := by
    intro C hC
    have hsp := compLSFBatch_compSt hI hU hC
    rw [hsp.1]
    exact (applyLSFBatch_inv_with (projCompBatchG cs.G (cs.compSt C).G U)
      (hI.hCompLSF C hC).1 hsp.2.2.1).2.2.2.2.2.2.2.2.1
  have hsum_add :
      ((components cs.G₀).sum fun C => (((compLSFBatch cs U).compSt C).R \ (cs.compSt C).R).card) +
      ((components cs.G₀).sum fun C => (cs.compSt C).R.card) =
      (components cs.G₀).sum fun C => ((compLSFBatch cs U).compSt C).R.card := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun C hC => ?_
    have hc := Finset.card_sdiff_add_card_inter ((compLSFBatch cs U).compSt C).R (cs.compSt C).R
    rwa [Finset.inter_eq_right.mpr (hcomp_sub C hC)] at hc
  have hglob := Finset.card_sdiff_add_card_inter (compLSFBatch cs U).RF.R cs.RF.R
  rw [Finset.inter_eq_right.mpr hR_sub] at hglob
  have h1 := hdisj_R cs hI
  have h2 := hdisj_R (compLSFBatch cs U) hI'
  rw [compLSFBatch_G₀] at h2
  omega

/-! ## 4. `bundleBatchList` and `bundleRunSeq` alignment lemmas -/

lemma bundleBatchList_take_flatten_length
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ)
    (C : Finset ℕ) (b : ℤ) {t : ℕ} (ht : t ≤ τ) :
    ((bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b).take t).flatten.length =
      ∑ s ∈ Finset.range t,
        ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length := by
  induction t with
  | zero => simp
  | succ s ih =>
    have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b
      (lt_of_lt_of_le (Nat.lt_succ_self s) ht)
    rw [take_succ_of_getElem? hget, List.flatten_append, List.length_append,
      ih (Nat.le_of_succ_le ht), Finset.sum_range_succ]
    simp

lemma bundleRunBatchStepOut_eq_stepOut
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ)
    (C : Finset ℕ) (b : ℤ) {s : ℕ} (hs : s < τ)
    (hDyn : ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.dyn (C, b)) =
      DynSpanner.runBatchState (normGraph ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).graph)
        (phaseBase (((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).graph.n +
          bundleSplitBudget k M) L)
        (sparsify M) (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) s)
    (hStepOut : (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b) =
      DynSpanner.update ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.dyn (C, b))
        ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) (sparsify M)) :
    let st₀ := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1
    let Hb₀ := normGraph (st₀.bun (C, b)).graph
    let splitB := bundleSplitBudget k M
    let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
    DynSpanner.runBatchStepOut Hb₀ (phaseBase (Hb₀.n + splitB) L) (sparsify M) Us_b s =
      (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b) := by
  intro st₀ Hb₀ splitB Us_b
  have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs
  dsimp only [DynSpanner.runBatchStepOut]
  rw [hget]
  change DynSpanner.update
      (DynSpanner.runBatchState Hb₀ (phaseBase (((st₀.bun (C, b)).graph).n + splitB) L) (sparsify M) Us_b s)
      ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) (sparsify M) = _
  rw [← hDyn]
  exact hStepOut.symm

/-- `D_total` of `stepBundleTree` splits into `D_sp` (spanner re-embedded sets) and `D_left`
(walks of edges that left a spanner). -/
lemma bundleRec_stepBundleTree_D_total_eq {L : ℕ}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (st : BundleTreeState L) (U : List Update) (ord ord' : ℕ → List End) :
    let info := stepBundleTree sparsify st U ord ord'
    info.D_total =
      (info.state.activeComps.biUnion fun C =>
        (st.activeBuckets C).biUnion fun b => (info.stepOut (C, b)).D) ∪
      (info.state.activeComps.biUnion fun C =>
        (st.activeBuckets C).biUnion fun b =>
          (((st.dyn (C, b)).H.E ∩ (info.stepOut (C, b)).state.G.E) \
            (info.stepOut (C, b)).state.H.E).biUnion
            fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)) :=
  rfl

lemma bundleRec_initBundleTree_M_of_actB
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} {G₀ : MGraph} (hM : G₀.m ≤ M) {ℓ₀ : ℕ → ℝ} (ord : ℕ → List End) (j : ℕ)
    {C : Finset ℕ}
    (hne : ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).Nonempty) :
    1 ≤ M := by
  obtain ⟨b, hb⟩ := hne
  let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
  have hact_def : b ∈ ((coreGraph G₀ cs₀.lsf).E.filter fun e => (coreGraph G₀ cs₀.lsf).tail e ∈ C).image
      (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)) := hb
  obtain ⟨e₀, he₀, _⟩ := Finset.mem_image.mp hact_def
  have he₀_core : e₀ ∈ (coreGraph G₀ cs₀.lsf).E := (Finset.mem_filter.mp he₀).1
  have he₀_G : e₀ ∈ G₀.E := (Finset.mem_sdiff.mp he₀_core).1
  have hm₀_pos : 1 ≤ G₀.m := Finset.card_pos.mpr ⟨e₀, he₀_G⟩
  omega

lemma bundleRec_initBundleTree_bun_bounds
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hM : G₀.m ≤ M) {ℓ₀ : ℕ → ℝ}
    (ord : ℕ → List End) (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    (st₀.bun (C, b)).graph.m ≤ M ∧
    (st₀.bun (C, b)).graph.n ≤ 2 * (st₀.bun (C, b)).graph.m := by
  intro st₀
  let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
  let C₀ := coreGraph G₀ cs₀.lsf
  let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)
  have hcs0_G : cs₀.G = G₀ := rfl
  have hsub := bundleRec_bucketCoreEdges_sub G₀ cs₀.lsf origB C b
  have hbf := bundleRec_initBundleFor_bounds cs₀ ord (bucketCoreEdges C₀ origB C b) hk
    (by rw [hcs0_G]; exact hsub.1)
  exact ⟨le_trans (le_trans hbf.2.1 hsub.2) hM, hbf.2.2⟩

end

end MinCostFlow.SparseCore
