module

public import MinCostFlow.SparseCore.BundleConstants
public import MinCostFlow.SparseCore.BundleRun
import MinCostFlow.Bundle.Initialize
import MinCostFlow.SparseCore.CompLSFBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positivity, monotonicity, and population bounds for bundle-graph constants

Establishes the basic inequalities for the degree-free constants in `BundleConstants.lean`
and bounds the initial bundle-graph vertex and edge counts (`initBundleTree_nMax_le_bundleNMax`),
replacing the quotient-graph population bounds of `SparseCoreRunBounds.lean` for the bundle-graph
sparse core.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Population and split-budget bounds -/

lemma bundleNMax_ge_two (M : ℕ) : 2 ≤ bundleNMax M := by
  unfold bundleNMax; omega

lemma bundleNMax_pos (M : ℕ) : 0 < bundleNMax M := by
  unfold bundleNMax; omega

lemma bundleNMax_mono {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) : bundleNMax M₁ ≤ bundleNMax M₂ := by
  unfold bundleNMax; omega

lemma bundleSplitBudget_le {k M : ℕ} (hk : 1 ≤ k) :
    bundleSplitBudget k M ≤ 2 * (56 * M) := by
  unfold bundleSplitBudget
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M := by
    refine Nat.ceil_le.mpr ?_
    exact (div_le_self (by positivity) hk1).trans (by norm_cast)
  omega

lemma bundleSplitBudget_le_add_one {k M : ℕ} (hk : 1 ≤ k) :
    bundleSplitBudget k M ≤ 2 * (56 * M + 1) :=
  le_trans (bundleSplitBudget_le hk) (by omega)

/-! ## 2. Initial bundle-state vertex and edge bounds -/

private lemma ceilDiv_le_self_of_pos (n : ℕ) {k : ℕ} (hk : 0 < k) : n ⌈/⌉ k ≤ n := by
  rw [ceilDiv_le_iff_le_mul hk]
  exact Nat.le_mul_of_pos_left n hk

private lemma ceil_capacity_le' (n : ℕ) {k : ℕ} (hk : 0 < k) :
    k * (n ⌈/⌉ k) ≤ k + n := by
  have hmod := Nat.mod_lt n hk
  have hdiv := Nat.div_add_mod n k
  have h₁ : n ≤ k * (n / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have h₂ : n ⌈/⌉ k ≤ n / k + 1 := (ceilDiv_le_iff_le_mul hk).2 h₁
  apply (Nat.mul_le_mul_left k h₂).trans
  rw [Nat.mul_add, Nat.mul_one]
  omega

private lemma initialSlots_length_le_ends {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    {k : ℕ} (hk : 0 < k) (vs : List ℕ) :
    (vs.flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)).length ≤
      (vs.flatMap (restrictedEnds ρ E)).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, initialChunks_length]
    exact Nat.add_le_add (ceilDiv_le_self_of_pos _ hk) ih

private lemma initialSlots_count_on {C : MGraph} (ρ : Rotation C) {E : Finset ℕ}
    (hE : E ⊆ C.E) {S : Finset ℕ} (hS : ∀ e ∈ E, C.tail e ∈ S ∧ C.head e ∈ S)
    {k : ℕ} (hk : 0 < k) (vs : List ℕ) :
    k * (vs.flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)).length ≤
      k * (vs.filter fun v => decide (v ∈ S)).length +
        (vs.flatMap (restrictedEnds ρ E)).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, initialChunks_length,
      List.filter_cons, Nat.mul_add]
    by_cases hv : v ∈ S
    · simp only [hv, decide_true, ↓reduceIte, List.length_cons, Nat.mul_add, Nat.mul_one]
      have h := ceil_capacity_le' (restrictedEnds ρ E v).length hk
      omega
    · have hempty : restrictedEnds ρ E v = [] := by
        rw [List.eq_nil_iff_forall_not_mem]
        intro x hx
        have hm := (mem_restrictedEnds ρ hE v x).mp hx
        have hEnd := hS x.1 hm.1
        rcases x with ⟨e, side⟩
        cases side
        · exact hv (hm.2 ▸ hEnd.2)
        · exact hv (hm.2 ▸ hEnd.1)
      have h0 : (0 : ℕ) ⌈/⌉ k = 0 :=
        Nat.le_zero.mp ((ceilDiv_le_iff_le_mul hk).2 (by simp))
      simp only [hv, decide_false, Bool.false_eq_true, ↓reduceIte, hempty, List.length_nil, h0,
        Nat.mul_zero, Nat.zero_add]
      exact ih

private lemma flatMap_restrictedEnds_length {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) :
    ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).length = 2 * E.card := by
  have hnodup : ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun v _ => (ρ.nodup v).filter _, ?_⟩
    apply List.Pairwise.imp_of_mem _ (Finset.sort_nodup C.V (· ≤ ·))
    intro v w _ _ hne
    apply List.disjoint_left.mpr
    intro x hv hw
    exact hne (((mem_restrictedEnds ρ hE v x).mp hv).2.symm.trans
      ((mem_restrictedEnds ρ hE w x).mp hw).2)
  have hset : ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).toFinset = edgeEnds E := by
    ext x
    rw [List.mem_toFinset, List.mem_flatMap, mem_edgeEnds]
    constructor
    · rintro ⟨v, _, hv⟩
      exact ((mem_restrictedEnds ρ hE v x).mp hv).1
    · intro hx
      have hEnd := hC x.1 (hE hx)
      have hv : C.src x ∈ C.V := by
        rcases x with ⟨e, side⟩
        cases side
        · exact hEnd.2
        · exact hEnd.1
      exact ⟨C.src x, (Finset.mem_sort (· ≤ ·)).mpr hv, (mem_restrictedEnds ρ hE _ _).mpr ⟨hx, rfl⟩⟩
  rw [← List.toFinset_card_of_nodup hnodup, hset, card_edgeEnds]

/-- Every initial bundle holds at least one end of an admitted edge, so the initial bundle
vertex count is at most `2 * |E|`. -/
theorem initBundleState_vertices_le_two_card {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) :
    (initBundleState ρ E k).vertices.card ≤ 2 * E.card := by
  have hlen := initialSlots_length_le_ends ρ E hk (C.V.sort (· ≤ ·))
  rw [flatMap_restrictedEnds_length ρ hC hE] at hlen
  simpa only [initBundleState, initialSlots, Finset.card_range] using hlen

/-- Localized initial bundle vertex bound: if every edge of `E` has both endpoints in `S`,
then only vertices of `S` contribute non-empty restricted tours, so
`k * |V(B)| ≤ k * |S| + 2 * |E|`. -/
theorem initBundleState_vertex_bound_on {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {S : Finset ℕ}
    (hS : ∀ e ∈ E, C.tail e ∈ S ∧ C.head e ∈ S) {k : ℕ} (hk : 0 < k) :
    k * (initBundleState ρ E k).vertices.card ≤ k * S.card + 2 * E.card := by
  have hl := initialSlots_count_on ρ hE hS hk (C.V.sort (· ≤ ·))
  rw [flatMap_restrictedEnds_length ρ hC hE] at hl
  have hfilt_le : ((C.V.sort (· ≤ ·)).filter fun v => decide (v ∈ S)).length ≤ S.card := by
    have hnd : ((C.V.sort (· ≤ ·)).filter fun v => decide (v ∈ S)).Nodup :=
      (Finset.sort_nodup C.V (· ≤ ·)).filter _
    rw [← List.toFinset_card_of_nodup hnd]
    refine Finset.card_le_card fun v hv => ?_
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hv
    exact hv.2
  have hmul : k * ((C.V.sort (· ≤ ·)).filter fun v => decide (v ∈ S)).length ≤ k * S.card :=
    Nat.mul_le_mul_left k hfilt_le
  simpa only [initBundleState, initialSlots, Finset.card_range] using
    le_trans hl (Nat.add_le_add_right hmul _)

lemma initBundleFor_edges_subset (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ) (k : ℕ) :
    (initBundleFor cs ord E k).edges ⊆ E := by
  classical
  unfold initBundleFor
  split_ifs
  · exact Finset.Subset.rfl
  · exact Finset.empty_subset E

lemma initBundleFor_vertices_le_two_card {cs : CompLSFState} {ord : ℕ → List End}
    {E : Finset ℕ} (hE : E ⊆ (coreGraph cs.G cs.lsf).E) {k : ℕ} (hk : 0 < k) :
    (initBundleFor cs ord E k).vertices.card ≤ 2 * E.card := by
  classical
  unfold initBundleFor
  split_ifs with h
  · let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    have hC : (coreGraph cs.G cs.lsf).IsValid :=
      coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
    exact initBundleState_vertices_le_two_card
      (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) hC hE hk
  · simp

lemma initBundleFor_vertex_bound_on {cs : CompLSFState} {ord : ℕ → List End}
    {E : Finset ℕ} (hE : E ⊆ (coreGraph cs.G cs.lsf).E) {S : Finset ℕ}
    (hS : ∀ e ∈ E, (coreGraph cs.G cs.lsf).tail e ∈ S ∧ (coreGraph cs.G cs.lsf).head e ∈ S)
    {k : ℕ} (hk : 0 < k) :
    k * (initBundleFor cs ord E k).vertices.card ≤ k * S.card + 2 * E.card := by
  classical
  unfold initBundleFor
  split_ifs with h
  · let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    have hC : (coreGraph cs.G cs.lsf).IsValid :=
      coreGraph_isValid hI.hG_val (compLSF_RF_isRSF hI)
    exact initBundleState_vertex_bound_on
      (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) hC hE hS hk
  · simp

lemma bucketCoreEdges_sub_coreE (C₀ : MGraph) (origB : ℕ → ℤ) (C : Finset ℕ) (b : ℤ) :
    bucketCoreEdges C₀ origB C b ⊆ C₀.E :=
  Finset.filter_subset _ _

lemma initBundleTreeWith_bun_m_le (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.m ≤ M := by
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
  have hsub1 : (st₀.bun (C, b)).edges ⊆
      bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b :=
    initBundleFor_edges_subset _ _ _ _
  have hsub2 : bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b ⊆ G₀.E :=
    Finset.Subset.trans (bucketCoreEdges_sub_coreE _ _ _ _) Finset.sdiff_subset
  exact le_trans (Finset.card_le_card (Finset.Subset.trans hsub1 hsub2)) hM

lemma initBundleTree_bun_m_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.m ≤ M :=
  initBundleTreeWith_bun_m_le (initLSFOnline oracle C_lsst) L sparsify hM ℓ₀ ord j C b

lemma initBundleTreeWith_bun_n_le (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.n ≤ 2 * M := by
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
  have hE : bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b ⊆
      (coreGraph st₀.cs.G st₀.cs.lsf).E :=
    bucketCoreEdges_sub_coreE _ _ _ _
  have hcard : (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card ≤ M :=
    le_trans (Finset.card_le_card (Finset.Subset.trans hE Finset.sdiff_subset)) hM
  have hv := initBundleFor_vertices_le_two_card (cs := st₀.cs) (ord := ord) hE hk
  exact le_trans hv (Nat.mul_le_mul_left 2 hcard)

lemma initBundleTree_bun_n_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.n ≤ 2 * M :=
  initBundleTreeWith_bun_n_le (initLSFOnline oracle C_lsst) L sparsify hk hM ℓ₀ ord j C b

/-- Every bucket spanner's vertex population `Hb₀.n + bundleSplitBudget k M` is bounded by
`bundleNMax M` (independent of degrees and of `k`). -/
theorem initBundleTreeWith_nMax_le_bundleNMax (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.n +
      bundleSplitBudget k M ≤ bundleNMax M := by
  unfold bundleNMax
  exact Nat.add_le_add
    (initBundleTreeWith_bun_n_le lsfInit L sparsify hk hM ℓ₀ ord j C b)
    (bundleSplitBudget_le_add_one hk)

/-- Every bucket spanner's vertex population `Hb₀.n + bundleSplitBudget k M` is bounded by
`bundleNMax M` (independent of degrees and of `k`). -/
theorem initBundleTree_nMax_le_bundleNMax
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hM : G₀.m ≤ M) (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End)
    (j : ℕ) (C : Finset ℕ) (b : ℤ) :
    ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).graph.n +
      bundleSplitBudget k M ≤ bundleNMax M :=
  initBundleTreeWith_nMax_le_bundleNMax (initLSFOnline oracle C_lsst) L sparsify hk hM ℓ₀ ord j C b

/-! ## 3. Positivity, lower bounds, and monotonicity of bundle constants -/

lemma bundleNRoot_ge_one (L M : ℕ) : 1 ≤ bundleNRoot L M := by
  unfold bundleNRoot
  have h1 : (1 : ℝ) ≤ ((max (bundleNMax M) 1 : ℕ) : ℝ) := by
    exact_mod_cast le_max_right (bundleNMax M) 1
  exact Real.one_le_rpow h1 (by positivity)

lemma bundleNRoot_pos (L M : ℕ) : 0 < bundleNRoot L M :=
  lt_of_lt_of_le zero_lt_one (bundleNRoot_ge_one L M)

lemma bundleNRoot_mono (L : ℕ) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    bundleNRoot L M₁ ≤ bundleNRoot L M₂ := by
  unfold bundleNRoot
  have hle : ((max (bundleNMax M₁) 1 : ℕ) : ℝ) ≤ ((max (bundleNMax M₂) 1 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max_right 1 (bundleNMax_mono h)
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity)

lemma bundleNRoot_of_le (L : ℕ) {n M : ℕ} (h : n ≤ bundleNMax M) :
    ((max n 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤ bundleNRoot L M := by
  unfold bundleNRoot
  have hle : ((max n 1 : ℕ) : ℝ) ≤ ((max (bundleNMax M) 1 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max_right 1 h
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hle (by positivity)

lemma bundleLambdaS_ge_one (P_b : SparsifyParams) (M : ℕ) :
    1 ≤ bundleLambdaS P_b M := by
  unfold bundleLambdaS
  refine one_le_pow₀ ?_
  have h1 : (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg h1]

lemma bundleLambdaS_pos (P_b : SparsifyParams) (M : ℕ) :
    0 < bundleLambdaS P_b M :=
  lt_of_lt_of_le zero_lt_one (bundleLambdaS_ge_one P_b M)

lemma bundleLambdaS_mono (P_b : SparsifyParams) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    bundleLambdaS P_b M₁ ≤ bundleLambdaS P_b M₂ := by
  unfold bundleLambdaS
  have h1 : (1 : ℝ) ≤ (bundleNMax M₁ : ℝ) + (M₁ : ℝ) + 2 := by linarith
  have hnn : 0 ≤ 1 + Real.log ((bundleNMax M₁ : ℝ) + (M₁ : ℝ) + 2) := by
    linarith [Real.log_nonneg h1]
  have hN : (bundleNMax M₁ : ℝ) ≤ (bundleNMax M₂ : ℝ) := by
    exact_mod_cast bundleNMax_mono h
  have hM : (M₁ : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast h
  exact pow_le_pow_left₀ hnn
    (add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))) _

lemma bundleLambdaS_of_le (P_b : SparsifyParams) {n m M : ℕ}
    (hn : n ≤ bundleNMax M) (hm : m ≤ M) :
    (1 + Real.log ((n : ℝ) + (m : ℝ) + 2)) ^ P_b.p_s ≤ bundleLambdaS P_b M := by
  unfold bundleLambdaS
  have h1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) + 2 := by linarith
  have hnn : 0 ≤ 1 + Real.log ((n : ℝ) + (m : ℝ) + 2) := by
    linarith [Real.log_nonneg h1]
  have hnR : (n : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  exact pow_le_pow_left₀ hnn
    (add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))) _

lemma bundleLambda_ge_one (P_b : SparsifyParams) (M : ℕ) :
    1 ≤ bundleLambda P_b M := by
  unfold bundleLambda
  refine one_le_pow₀ ?_
  have h1 : (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 := by linarith
  linarith [Real.log_nonneg h1]

lemma bundleLambda_pos (P_b : SparsifyParams) (M : ℕ) :
    0 < bundleLambda P_b M :=
  lt_of_lt_of_le zero_lt_one (bundleLambda_ge_one P_b M)

lemma bundleLambda_mono (P_b : SparsifyParams) {M₁ M₂ : ℕ} (h : M₁ ≤ M₂) :
    bundleLambda P_b M₁ ≤ bundleLambda P_b M₂ := by
  unfold bundleLambda
  have h1 : (1 : ℝ) ≤ (bundleNMax M₁ : ℝ) + (M₁ : ℝ) + 2 := by linarith
  have hnn : 0 ≤ 1 + Real.log ((bundleNMax M₁ : ℝ) + (M₁ : ℝ) + 2) := by
    linarith [Real.log_nonneg h1]
  have hN : (bundleNMax M₁ : ℝ) ≤ (bundleNMax M₂ : ℝ) := by
    exact_mod_cast bundleNMax_mono h
  have hM : (M₁ : ℝ) ≤ (M₂ : ℝ) := by exact_mod_cast h
  exact pow_le_pow_left₀ hnn
    (add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))) _

lemma bundleLambda_of_le (P_b : SparsifyParams) {n m M : ℕ}
    (hn : n ≤ bundleNMax M) (hm : m ≤ M) :
    (1 + Real.log ((n : ℝ) + (m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t) ≤ bundleLambda P_b M := by
  unfold bundleLambda
  have h1 : (1 : ℝ) ≤ (n : ℝ) + (m : ℝ) + 2 := by linarith
  have hnn : 0 ≤ 1 + Real.log ((n : ℝ) + (m : ℝ) + 2) := by
    linarith [Real.log_nonneg h1]
  have hnR : (n : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hn
  have hmR : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  exact pow_le_pow_left₀ hnn
    (add_le_add le_rfl (Real.log_le_log (by linarith) (by linarith))) _

lemma bundleLambdaS_le_bundleLambda (P_b : SparsifyParams) (M : ℕ) :
    bundleLambdaS P_b M ≤ bundleLambda P_b M := by
  unfold bundleLambdaS bundleLambda
  have h1 : (1 : ℝ) ≤ 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) := by
    have : (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 := by linarith
    linarith [Real.log_nonneg this]
  exact pow_le_pow_right₀ h1 (le_max_left _ _)

lemma bundleUCRatio_ge_one (N : ℕ) : 1 ≤ bundleUCRatio N := by
  unfold bundleUCRatio
  have : 0 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := sq_nonneg _
  linarith

lemma bundleUCRatio_pos (N : ℕ) : 0 < bundleUCRatio N :=
  lt_of_lt_of_le zero_lt_one (bundleUCRatio_ge_one N)

lemma bundleUCRatio_mono {N₁ N₂ : ℕ} (h : N₁ ≤ N₂) :
    bundleUCRatio N₁ ≤ bundleUCRatio N₂ := by
  unfold bundleUCRatio
  have h1 : 0 ≤ Real.log ((N₁ : ℝ) + 2) := (half_lt_log_add_two N₁).le.trans' (by norm_num)
  have hcast : (N₁ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((N₁ : ℝ) + 2) ≤ Real.log ((N₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  linarith

lemma bundleBucketRec_pos (L : ℕ) (P_b : SparsifyParams) (M : ℕ) :
    0 ≤ bundleBucketRecUH L P_b M ∧ 0 ≤ bundleBucketRecD L P_b M ∧
      0 ≤ coreE82Len L P_b := by
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hnr := (bundleNRoot_pos L M).le
  have hlam := (bundleLambdaS_pos P_b M).le
  refine ⟨?_, ?_, ?_⟩
  · unfold bundleBucketRecUH; positivity
  · unfold bundleBucketRecD; positivity
  · unfold coreE82Len; positivity

lemma bundleRecoursePerQ_pos (L : ℕ) (P_b : SparsifyParams) (M N B : ℕ) :
    0 < bundleRecoursePerQ L P_b M N B := by
  unfold bundleRecoursePerQ
  have ⟨hUH, hD, hLen⟩ := bundleBucketRec_pos L P_b M
  have huc := (bundleUCRatio_pos N).le
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlam := (bundleLambdaS_pos P_b M).le
  have hsq : 0 ≤ (Real.log ((N : ℝ) + 2)) ^ 2 := sq_nonneg _
  positivity

lemma bundleRecoursePerQ_mono_N (L : ℕ) (P_b : SparsifyParams) (M : ℕ) {N₁ N₂ : ℕ}
    (h : N₁ ≤ N₂) (B : ℕ) :
    bundleRecoursePerQ L P_b M N₁ B ≤ bundleRecoursePerQ L P_b M N₂ B := by
  unfold bundleRecoursePerQ
  have huc := bundleUCRatio_mono h
  have h1 : 0 ≤ Real.log ((N₁ : ℝ) + 2) := (half_lt_log_add_two N₁).le.trans' (by norm_num)
  have hcast : (N₁ : ℝ) ≤ (N₂ : ℝ) := by exact_mod_cast h
  have hlog : Real.log ((N₁ : ℝ) + 2) ≤ Real.log ((N₂ : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hsq := pow_le_pow_left₀ h1 hlog 2
  have ⟨hUH, hD, hLen⟩ := bundleBucketRec_pos L P_b M
  have hc : 0 ≤ (B : ℝ) * ((3 + 2 * coreE82Len L P_b) * bundleBucketRecUH L P_b M +
      2 * bundleBucketRecD L P_b M) := by positivity
  have hmul := mul_le_mul_of_nonneg_left
    (show 2 * bundleUCRatio N₁ ≤ 2 * bundleUCRatio N₂ by linarith) hc
  linarith

lemma bundleSizeFactor_ge_115 (L : ℕ) (P_b : SparsifyParams) (M B : ℕ) :
    115 ≤ bundleSizeFactor L P_b M B := by
  unfold bundleSizeFactor
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlam := (bundleLambdaS_pos P_b M).le
  have hterm : 0 ≤ ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M * (B : ℝ) * 1000 := by
    positivity
  linarith

lemma bundleSizeFactor_pos (L : ℕ) (P_b : SparsifyParams) (M B : ℕ) :
    0 < bundleSizeFactor L P_b M B := by
  linarith [bundleSizeFactor_ge_115 L P_b M B]

lemma bundleSizeFactor_mono (L : ℕ) (P_b : SparsifyParams) {M₁ M₂ B₁ B₂ : ℕ}
    (hM : M₁ ≤ M₂) (hB : B₁ ≤ B₂) :
    bundleSizeFactor L P_b M₁ B₁ ≤ bundleSizeFactor L P_b M₂ B₂ := by
  unfold bundleSizeFactor
  have hK := P_b.hK_s
  have hγ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hlam_nn := (bundleLambdaS_pos P_b M₁).le
  have hlam := bundleLambdaS_mono P_b hM
  have hBR : (B₁ : ℝ) ≤ (B₂ : ℝ) := by exact_mod_cast hB
  have hpre : 0 ≤ ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ := by positivity
  have h1 : ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M₁ * (B₁ : ℝ) ≤
      ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * bundleLambdaS P_b M₂ * (B₂ : ℝ) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hlam hpre) hBR (Nat.cast_nonneg _)
      (mul_nonneg hpre (bundleLambdaS_pos P_b M₂).le)
  linarith

end

end MinCostFlow.SparseCore
