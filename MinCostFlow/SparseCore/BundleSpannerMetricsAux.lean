module

public import MinCostFlow.SparseCore.BundleConstantsLemmas
public import MinCostFlow.SparseCore.BundleMetrics
public import MinCostFlow.SparseCore.BundleRunInvBase
import all MinCostFlow.SparseCore.BundleCompStep
import MinCostFlow.SparseCore.SplitSpannerBase
import MinCostFlow.SparseCore.SparseCoreRunBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Auxiliary lemmas for the sparsified core theorem on bundle graphs

Provides the structural and counting helpers used by `BundleSpannerSize.lean` and
`BundleSpannerMetrics.lean`:
1. Component membership and endpoint localization of `bucketCoreEdges`, plus localized initial
   bundle vertex bounds for large and small components.
2. Transporting `OrderedUpTo` to `BundleStepReady` and rotation order casting.
3. Bundle edge survival (`(st.bun (C, b)).edges = (st₀.bun (C, b)).edges \ ⋃ batchDeletes`),
   disjointness from `st.cs.insertedGlobal`, and the `extraEdges` subset characterization.
4. Spanner input vertex count bounds (`(st.dyn (C, b)).G.n ≤ bundleNMax M` and per-component
   growth in terms of `((st.cs.compSt C).R \ (cs₀.compSt C).R).card`).
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Component localization of `bucketCoreEdges` and initial bundle vertices -/

lemma bucketCoreEdges_props {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs₀ : CompLSFState}
    (hI₀ : CompLSFInv C_lsst ℓ₀ cs₀)
    (hCross₀ : cs₀.crossEdges = ∅)
    (hCompG : ∀ C ∈ components cs₀.G₀, (cs₀.compSt C).G = compGraph cs₀.G₀ C)
    (origB : ℕ → ℤ)
    {C : Finset ℕ} (hC : C ∈ components cs₀.G₀) (b : ℤ)
    {e : ℕ} (he : e ∈ bucketCoreEdges (coreGraph cs₀.G cs₀.lsf) origB C b) :
    e ∈ compEdgeSet cs₀.G₀ C ∧
    e ∈ (cs₀.compSt C).G.E ∧
    (coreGraph cs₀.G cs₀.lsf).tail e ∈ (cs₀.compSt C).R ∧
    (coreGraph cs₀.G cs₀.lsf).head e ∈ (cs₀.compSt C).R ∧
    origB e = b := by
  classical
  have hf := Finset.mem_filter.mp he
  have heCore : e ∈ (coreGraph cs₀.G cs₀.lsf).E := hf.1
  have htailC : (coreGraph cs₀.G cs₀.lsf).tail e ∈ C := hf.2.1
  have hb : origB e = b := hf.2.2
  have heG : e ∈ cs₀.G.E := (Finset.mem_sdiff.mp heCore).1
  have hnc : e ∉ cs₀.crossEdges := by rw [hCross₀]; simp
  obtain ⟨C', hC', heC'⟩ := hI₀.hEdge_cover e heG hnc
  have hEnds' := hI₀.hNonCross_ends C' hC' e heC' hnc
  have hCI' := (hI₀.hCompLSF C' hC').1
  have htV' : (cs₀.compSt C').G.tail e ∈ (cs₀.compSt C').G.V := (hCI'.hG_val e heC').1
  have hhV' : (cs₀.compSt C').G.head e ∈ (cs₀.compSt C').G.V := (hCI'.hG_val e heC').2
  have hroot_t' : (coreGraph cs₀.G cs₀.lsf).tail e =
      (cs₀.compSt C').RF.root ((cs₀.compSt C').G.tail e) := by
    change cs₀.RF.root (cs₀.G.tail e) = _
    rw [← hEnds'.1]
    exact compLSF_RF_root_eq hI₀ hC' htV'
  have hrt_mem_R' : (coreGraph cs₀.G cs₀.lsf).tail e ∈ (cs₀.compSt C').R := by
    rw [hroot_t']
    exact (rootedForest_root_spec (lsfInv_to_RS hCI') htV').1
  have hrt_mem_V' : (coreGraph cs₀.G cs₀.lsf).tail e ∈ (cs₀.compSt C').G.V :=
    lsfInv_R_sub_V hCI' hrt_mem_R'
  have hV'_eq : (cs₀.compSt C').G.V = C' := by rw [hCompG C' hC']; rfl
  have htailC' : (coreGraph cs₀.G cs₀.lsf).tail e ∈ C' := hV'_eq ▸ hrt_mem_V'
  have hCeq : C' = C := by
    by_contra hne
    exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint cs₀.G₀ hC' hC hne) htailC' htailC
  subst hCeq
  have hroot_h : (coreGraph cs₀.G cs₀.lsf).head e =
      (cs₀.compSt C').RF.root ((cs₀.compSt C').G.head e) := by
    change cs₀.RF.root (cs₀.G.head e) = _
    rw [← hEnds'.2]
    exact compLSF_RF_root_eq hI₀ hC' hhV'
  have hrh_mem_R : (coreGraph cs₀.G cs₀.lsf).head e ∈ (cs₀.compSt C').R := by
    rw [hroot_h]
    exact (rootedForest_root_spec (lsfInv_to_RS hCI') hhV').1
  have he_ce : e ∈ compEdgeSet cs₀.G₀ C' := by
    have hE' : (cs₀.compSt C').G.E = compEdgeSet cs₀.G₀ C' := by rw [hCompG C' hC']; rfl
    exact hE' ▸ heC'
  exact ⟨he_ce, heC', hrt_mem_R', hrh_mem_R, hb⟩

lemma comp_sdiff_mem_bucketCoreEdges {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs₀ : CompLSFState}
    (hI₀ : CompLSFInv C_lsst ℓ₀ cs₀)
    (hCross₀ : cs₀.crossEdges = ∅)
    (hCompG : ∀ C ∈ components cs₀.G₀, (cs₀.compSt C).G = compGraph cs₀.G₀ C)
    (origB : ℕ → ℤ)
    {C : Finset ℕ} (hC : C ∈ components cs₀.G₀)
    {e : ℕ} (he : e ∈ (cs₀.compSt C).G.E \ (cs₀.compSt C).RF.F.E) :
    origB e ∈ ((coreGraph cs₀.G cs₀.lsf).E.filter fun x =>
        (coreGraph cs₀.G cs₀.lsf).tail x ∈ C).image origB ∧
    e ∈ bucketCoreEdges (coreGraph cs₀.G cs₀.lsf) origB C (origB e) := by
  classical
  have heCore : e ∈ (coreGraph cs₀.G cs₀.lsf).E := compLSF_comp_sdiff_sub hI₀ hC he
  have heC : e ∈ (cs₀.compSt C).G.E := (Finset.mem_sdiff.mp he).1
  have hnc : e ∉ cs₀.crossEdges := by rw [hCross₀]; simp
  have hEnds := hI₀.hNonCross_ends C hC e heC hnc
  have hCI := (hI₀.hCompLSF C hC).1
  have htV : (cs₀.compSt C).G.tail e ∈ (cs₀.compSt C).G.V := (hCI.hG_val e heC).1
  have hroot_t : (coreGraph cs₀.G cs₀.lsf).tail e =
      (cs₀.compSt C).RF.root ((cs₀.compSt C).G.tail e) := by
    change cs₀.RF.root (cs₀.G.tail e) = _
    rw [← hEnds.1]
    exact compLSF_RF_root_eq hI₀ hC htV
  have hrt_V : (coreGraph cs₀.G cs₀.lsf).tail e ∈ (cs₀.compSt C).G.V := by
    rw [hroot_t]
    exact lsfInv_R_sub_V hCI (rootedForest_root_spec (lsfInv_to_RS hCI) htV).1
  have hrt_C : (coreGraph cs₀.G cs₀.lsf).tail e ∈ C := by
    have hV : (cs₀.compSt C).G.V = C := by rw [hCompG C hC]; rfl
    exact hV ▸ hrt_V
  refine ⟨Finset.mem_image_of_mem origB (Finset.mem_filter.mpr ⟨heCore, hrt_C⟩),
    Finset.mem_filter.mpr ⟨heCore, hrt_C, rfl⟩⟩

lemma initBundleTreeWith_bun_vertex_bound_on
    (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) {j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {C : Finset ℕ} (hC : C ∈ components G₀) (b : ℤ) :
    k * ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).vertices.card ≤
      k * ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).cs.compSt C).R.card +
        2 * (bucketCoreEdges
          (coreGraph G₀ (initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).cs.lsf)
          (initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).origBucket C b).card := by
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
  let C₀ := coreGraph G₀ st₀.cs.lsf
  have hI₀ : CompLSFInv C_lsst ℓ₀ st₀.cs := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCompG : ∀ C' ∈ components G₀, (st₀.cs.compSt C').G = compGraph G₀ C' :=
    fun C' hC' => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC').2.1
  have hE : bucketCoreEdges C₀ st₀.origBucket C b ⊆ (coreGraph st₀.cs.G st₀.cs.lsf).E :=
    bucketCoreEdges_sub_coreE _ _ _ _
  have hS : ∀ e ∈ bucketCoreEdges C₀ st₀.origBucket C b,
      (coreGraph st₀.cs.G st₀.cs.lsf).tail e ∈ (st₀.cs.compSt C).R ∧
      (coreGraph st₀.cs.G st₀.cs.lsf).head e ∈ (st₀.cs.compSt C).R := by
    intro e he
    have hp := bucketCoreEdges_props hI₀ rfl hCompG st₀.origBucket hC b he
    exact ⟨hp.2.2.1, hp.2.2.2.1⟩
  exact initBundleFor_vertex_bound_on (cs := st₀.cs) (ord := ord) hE hS hk

/-- For an initial bundle tree, the initial bundle vertex count of `(C, b)` satisfies the localized
bound `k * |V| ≤ k * |(cs₀.compSt C).R| + 2 * |bucketCoreEdges|`. -/
lemma initBundleTree_bun_vertex_bound_on
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ)
    {C : Finset ℕ} (hC : C ∈ components G₀) (b : ℤ) :
    k * ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).vertices.card ≤
      k * ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).cs.compSt C).R.card +
        2 * (bucketCoreEdges
          (coreGraph G₀ (initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).cs.lsf)
          (initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).origBucket C b).card :=
  initBundleTreeWith_bun_vertex_bound_on (initLSFOnline oracle C_lsst) L sparsify k M N hk hG₀ hV₀
    hℓ₀ ord (initLSFOnline_isValidLSFInitFor hLSST k j) hC b

lemma initBundleTreeWith_small_bun_card_le_one
    (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) {j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {C : Finset ℕ} (hC : C ∈ components G₀) (hNL : C ∉ largeComps k G₀) (b : ℤ) :
    ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).vertices.card ≤ 1 := by
  let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
  have hI₀ : CompLSFInv C_lsst ℓ₀ st₀.cs := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCompG : ∀ C' ∈ components G₀, (st₀.cs.compSt C').G = compGraph G₀ C' :=
    fun C' hC' => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC').2.1
  have hlt : 4 * (compGraph G₀ C).m < k := by
    by_contra hge
    push Not at hge
    have hm1 : 1 ≤ (compGraph G₀ C).m := by
      have : 0 < 4 * (compGraph G₀ C).m := lt_of_lt_of_le hk hge
      omega
    exact hNL (Finset.mem_filter.mpr ⟨hC, hm1, hge⟩)
  have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
    rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
  have hsm := initLSF_small_props_with hInit hG₀ hℓs hk hC hlt
  have hR1 : (st₀.cs.compSt C).R.card = 1 := hsm.1
  have hbnd := initBundleTreeWith_bun_vertex_bound_on lsfInit L sparsify k M N hk hG₀ hV₀ hℓ₀ ord hInit hC b
  have hE_le : (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card ≤
      (compGraph G₀ C).m := by
    refine Finset.card_le_card fun e he => ?_
    exact (bucketCoreEdges_props hI₀ rfl hCompG st₀.origBucket hC b he).1
  change k * (st₀.bun (C, b)).vertices.card ≤
    k * (st₀.cs.compSt C).R.card +
      2 * (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card at hbnd
  rw [hR1, Nat.mul_one] at hbnd
  have hlt2 : k * (st₀.bun (C, b)).vertices.card < k * 2 := by omega
  have hlt_v : (st₀.bun (C, b)).vertices.card < 2 := Nat.lt_of_mul_lt_mul_left hlt2
  exact Nat.le_of_lt_succ hlt_v

/-- For a small component `C ∉ largeComps k G₀`, every bucket starts with at most `1` bundle
vertex. -/
lemma initBundleTree_small_bun_card_le_one
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ)
    {C : Finset ℕ} (hC : C ∈ components G₀) (hNL : C ∉ largeComps k G₀) (b : ℤ) :
    ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).bun (C, b)).vertices.card ≤ 1 :=
  initBundleTreeWith_small_bun_card_le_one (initLSFOnline oracle C_lsst) L sparsify k M N hk hG₀ hV₀
    hℓ₀ ord (initLSFOnline_isValidLSFInitFor hLSST k j) hC hNL b

lemma initBundleTreeWith_large_bun_sum_le
    (lsfInit : LSFInit) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) {j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {C : Finset ℕ} (hC : C ∈ largeComps k G₀) {B_bound : ℕ}
    (hB : ((initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤ B_bound) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
    ((st₀.activeBuckets C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
      10 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) / (k : ℝ) := by
  intro st₀
  have hC_mem : C ∈ components G₀ := largeComps_sub hC
  have hI₀ : CompLSFInv C_lsst ℓ₀ st₀.cs := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
  have hCompG : ∀ C' ∈ components G₀, (st₀.cs.compSt C').G = compGraph G₀ C' :=
    fun C' hC' => (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk hC').2.1
  by_cases hB0 : B_bound = 0
  · subst hB0
    have hempty : st₀.activeBuckets C = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hB)
    simp [hempty]
  · have hB1 : (1 : ℝ) ≤ (B_bound : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hB0
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hdisj : Set.PairwiseDisjoint (↑(st₀.activeBuckets C) : Set ℤ)
        (fun b => bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b) := by
      intro b₁ _ b₂ _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro e he1 he2
      have h1 := (Finset.mem_filter.mp he1).2.2
      have h2 := (Finset.mem_filter.mp he2).2.2
      exact hne (h1.symm.trans h2)
    have hE_sum : ((st₀.activeBuckets C).sum fun b =>
        (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card) ≤
        (compGraph G₀ C).m := by
      rw [← Finset.card_biUnion hdisj]
      refine Finset.card_le_card (Finset.biUnion_subset.mpr fun b _ e he => ?_)
      exact (bucketCoreEdges_props hI₀ rfl hCompG st₀.origBucket hC_mem b he).1
    have hnat : k * ((st₀.activeBuckets C).sum fun b => (st₀.bun (C, b)).vertices.card) ≤
        k * B_bound * (st₀.cs.compSt C).R.card + 2 * (compGraph G₀ C).m := by
      calc k * ((st₀.activeBuckets C).sum fun b => (st₀.bun (C, b)).vertices.card)
          = (st₀.activeBuckets C).sum fun b => k * (st₀.bun (C, b)).vertices.card := by
              rw [Finset.mul_sum]
        _ ≤ (st₀.activeBuckets C).sum fun b =>
              k * (st₀.cs.compSt C).R.card +
                2 * (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card :=
              Finset.sum_le_sum fun b _ =>
                initBundleTreeWith_bun_vertex_bound_on lsfInit L sparsify k M N hk hG₀ hV₀ hℓ₀ ord hInit hC_mem b
        _ = (st₀.activeBuckets C).card * (k * (st₀.cs.compSt C).R.card) +
              2 * ((st₀.activeBuckets C).sum fun b =>
                (bucketCoreEdges (coreGraph G₀ st₀.cs.lsf) st₀.origBucket C b).card) := by
              rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
        _ ≤ B_bound * (k * (st₀.cs.compSt C).R.card) + 2 * (compGraph G₀ C).m :=
              Nat.add_le_add (Nat.mul_le_mul_right _ hB) (Nat.mul_le_mul_left 2 hE_sum)
        _ = k * B_bound * (st₀.cs.compSt C).R.card + 2 * (compGraph G₀ C).m := by ring
    have hreal : (k : ℝ) * ((st₀.activeBuckets C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
        (k : ℝ) * (B_bound : ℝ) * ((st₀.cs.compSt C).R.card : ℝ) +
          2 * ((compGraph G₀ C).m : ℝ) := by
      have hr : ((k * ((st₀.activeBuckets C).sum fun b => (st₀.bun (C, b)).vertices.card) : ℕ) : ℝ) ≤
          ((k * B_bound * (st₀.cs.compSt C).R.card + 2 * (compGraph G₀ C).m : ℕ) : ℝ) := by
        exact_mod_cast hnat
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] using hr
    have hℓs : ∀ e ∈ G₀.E, 0 < safeLen G₀ ℓ₀ e := fun e he => by
      rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓ₀ e he
    have hR_le : ((st₀.cs.compSt C).R.card : ℝ) ≤ 8 * ((compGraph G₀ C).m : ℝ) / (k : ℝ) :=
      initLSF_large_R_card_le_with hInit hG₀ hℓs hk hC
    have hterm1 : (k : ℝ) * (B_bound : ℝ) * ((st₀.cs.compSt C).R.card : ℝ) ≤
        8 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hR_le (by positivity : 0 ≤ (k : ℝ) * (B_bound : ℝ))
      have heq : (k : ℝ) * (B_bound : ℝ) * (8 * ((compGraph G₀ C).m : ℝ) / (k : ℝ)) =
          8 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) := by
        field_simp [hk_pos.ne']
      linarith
    have hterm2 : 2 * ((compGraph G₀ C).m : ℝ) ≤ 2 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) := by
      have hm_nn : (0 : ℝ) ≤ ((compGraph G₀ C).m : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [le_div_iff₀ hk_pos]
    linarith

/-- For a large component `C ∈ largeComps k G₀` with at most `B_bound` active buckets, the sum of
initial bundle vertex counts across its active buckets is at most `10 * B_bound * m_C / k`. -/
lemma initBundleTree_large_bun_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ} (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N : ℕ) (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (ord : ℕ → List End) (j : ℕ)
    {C : Finset ℕ} (hC : C ∈ largeComps k G₀) {B_bound : ℕ}
    (hB : ((initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j).activeBuckets C).card ≤ B_bound) :
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    ((st₀.activeBuckets C).sum fun b => ((st₀.bun (C, b)).vertices.card : ℝ)) ≤
      10 * (B_bound : ℝ) * ((compGraph G₀ C).m : ℝ) / (k : ℝ) :=
  initBundleTreeWith_large_bun_sum_le (initLSFOnline oracle C_lsst) L sparsify k M N hk hG₀ hV₀
    hℓ₀ ord (initLSFOnline_isValidLSFInitFor hLSST k j) hC hB

/-! ## 2. Transporting `OrderedUpTo` to `BundleStepReady` -/

lemma bundleStepReady_of_ordered {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {B : BundleState} {k : ℕ} {G₁ G₂ : MGraph} {U : List Update}
    {ord ord' : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hG1 : cs.G = G₁) (hG2 : G₂ = G₁.applyBatch U)
    (hBU : cs.G.BatchIsValid U)
    (ρ₁ : Rotation G₁) (ρ₂ : Rotation G₂)
    (hρ₁ : ρ₁.order = ord) (hρ₂ : ρ₂.order = ord')
    (hrot : RotationBatch 2 U ρ₁ (hG2 ▸ ρ₂))
    (hPart : ∀ (ρ : Rotation cs.G) (hG : cs.G.IsValid)
        (hF : cs.RF.IsRootedSpanningForestOf cs.G),
        ρ.order = ord → B.IsPartition (coreRotation (L := cs.lsf) ρ hG hF) k) :
    BundleStepReady cs B k ord ord' U := by
  subst hG1
  subst hG2
  exact ⟨C_lsst, ℓ₀, hI, ρ₁, ρ₂, hρ₁, hρ₂, hrot, hBU,
    hPart ρ₁ hI.hG_val (compLSF_RF_isRSF hI) hρ₁⟩

/-! ## 3. Bundle edge survival, disjointness from `insertedGlobal`, and `extraEdges` -/

lemma mem_dynBatches_flatten_of_Icc (D : DynamicInstance) {s t : ℕ}
    (hs1 : 1 ≤ s) (hst : s ≤ t) {u : Update} (hu : u ∈ D.U s) :
    u ∈ (dynBatches D t).flatten := by
  induction t with
  | zero => omega
  | succ m ih =>
    have hsucc : dynBatches D (m + 1) = dynBatches D m ++ [D.U (m + 1)] := by
      simp [dynBatches, List.range_succ]
    rw [hsucc, List.flatten_append, List.mem_append]
    rcases Nat.eq_or_lt_of_le hst with rfl | hlt
    · exact Or.inr (by simpa using hu)
    · exact Or.inl (ih (Nat.lt_succ_iff.mp hlt))

/-- Along `bundleRunSeq`, the surviving edges of `(st.bun (C, b))` are exactly the initial edges
minus all input deletions up to stage `t`, and they stay disjoint from `st.cs.insertedGlobal`. -/
lemma bundleRunSeq_bun_edges_spec
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N τ : ℕ} {D : DynamicInstance} {ord : ℕ → ℕ → List End}
    (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    {C : Finset ℕ} (_hC : C ∈ components (D.G 0)) (b : ℤ)
    (hLocal : ∀ {cs : CompLSFState} {B : BundleState} {k' : ℕ}
        {o₁ o₂ : ℕ → List End} {U : List Update} (_ : BundleStepReady cs B k' o₁ o₂ U)
        (C' : Finset ℕ) (_ : ∀ x ∈ B.vertices, B.parent x ∈ (cs.compSt C').R),
        (bundleCompStep cs B k' o₁ o₂ U).2.edges = B.edges \ batchDeletes U)
    (hBase : ∀ t ≤ τ,
        let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
        st.k = k ∧ CompLSFInv C_lsst (D.ℓ 0) st.cs ∧ st.cs.G = D.G t ∧
        (∀ (ρ : Rotation st.cs.G) (hG : st.cs.G.IsValid)
            (hF : st.cs.RF.IsRootedSpanningForestOf st.cs.G), ρ.order = ord t →
          (st.bun (C, b)).IsPartition (coreRotation (L := st.cs.lsf) ρ hG hF) k) ∧
        (∀ x ∈ (st.bun (C, b)).vertices, (st.bun (C, b)).parent x ∈ (st.cs.compSt C).R))
    (hStep : ∀ s < τ,
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.cs.G.BatchIsValid (D.U (s + 1))) :
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let st₀ := (run 0).1
    ∀ t ≤ τ,
      let st := (run t).1
      (st.bun (C, b)).edges =
        (st₀.bun (C, b)).edges \ (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)) ∧
      Disjoint (st.bun (C, b)).edges st.cs.insertedGlobal := by
  intro run st₀ t ht
  obtain ⟨ρ_all, hρ_ord, hρ_batch⟩ := hOrd
  induction t with
  | zero =>
    refine ⟨by simp [st₀], ?_⟩
    change Disjoint (st₀.bun (C, b)).edges ∅
    exact Finset.disjoint_empty_right _
  | succ s ih =>
    have hs_le : s ≤ τ := Nat.le_of_succ_le ht
    have hs_lt : s < τ := ht
    obtain ⟨ih_eq, ih_disj⟩ := ih hs_le
    obtain ⟨hk_s, hI_s, hG_s, hPart_s, hPar_s⟩ := hBase s hs_le
    obtain ⟨hG_step, hrot_s⟩ := hρ_batch s hs_lt
    have hBU_s := hStep s hs_lt
    have hReady : BundleStepReady (run s).1.cs ((run s).1.bun (C, b)) k
        (ord s) (ord (s + 1)) (D.U (s + 1)) :=
      bundleStepReady_of_ordered hI_s hG_s hG_step hBU_s (ρ_all s) (ρ_all (s + 1))
        (hρ_ord s hs_le) (hρ_ord (s + 1) ht) hrot_s hPart_s
    have hstep_edges : ((run (s + 1)).1.bun (C, b)).edges =
        ((run s).1.bun (C, b)).edges \ batchDeletes (D.U (s + 1)) := by
      have hdef : (run (s + 1)).1.bun (C, b) =
          (bundleCompStep (run s).1.cs ((run s).1.bun (C, b)) (run s).1.k
            (ord s) (ord (s + 1)) (D.U (s + 1))).2 := rfl
      rw [hdef, hk_s]
      exact hLocal hReady C hPar_s
    have hEq : ((run (s + 1)).1.bun (C, b)).edges =
        (st₀.bun (C, b)).edges \ (Finset.Icc 1 (s + 1)).biUnion (fun i => batchDeletes (D.U i)) := by
      have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hstep_edges, ih_eq, hIcc, Finset.biUnion_insert]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    have hDisj : Disjoint ((run (s + 1)).1.bun (C, b)).edges (run (s + 1)).1.cs.insertedGlobal := by
      rw [Finset.disjoint_left]
      intro e he heIns
      rw [hstep_edges, Finset.mem_sdiff] at he
      have hPart_s1 := (hBase (s + 1) ht).2.2.2.1
      have hI_s1 := (hBase (s + 1) ht).2.1
      have hG_s1 := (hBase (s + 1) ht).2.2.1
      have heG_s : e ∈ (run s).1.cs.G.E := by
        have hP := hPart_s (hG_s.symm ▸ ρ_all s) hI_s.hG_val (compLSF_RF_isRSF hI_s)
          ((rotation_cast_order hG_s.symm (ρ_all s)).trans (hρ_ord s hs_le))
        exact (Finset.mem_sdiff.mp (hP.1 he.1)).1
      have heG_s1 : e ∈ ((run s).1.cs.G.applyBatch (D.U (s + 1))).E := by
        have hP1 := hPart_s1 (hG_s1.symm ▸ ρ_all (s + 1)) hI_s1.hG_val (compLSF_RF_isRSF hI_s1)
          ((rotation_cast_order hG_s1.symm (ρ_all (s + 1))).trans (hρ_ord (s + 1) ht))
        have h1 : e ∈ (run (s + 1)).1.cs.G.E := (Finset.mem_sdiff.mp (hP1.1 (by
          rw [hstep_edges]; exact Finset.mem_sdiff.mpr he))).1
        have hcs_eq : (run (s + 1)).1.cs = compLSFBatch (run s).1.cs (D.U (s + 1)) := rfl
        rwa [hcs_eq, compLSFBatch_G] at h1
      have hni : ∀ u ∈ D.U (s + 1), ¬ u.Inserts e :=
        not_inserts_of_not_mem_batchDeletes hBU_s heG_s he.2
      have hcs_eq : (run (s + 1)).1.cs = compLSFBatch (run s).1.cs (D.U (s + 1)) := rfl
      rw [hcs_eq, compLSFBatch_insertedGlobal] at heIns
      have heIns_s : e ∈ (run s).1.cs.insertedGlobal :=
        (mem_foldl_updateInserted_iff_of_mem_applyBatch_no_ins heG_s1 hni).mp heIns
      exact Finset.disjoint_left.mp ih_disj he.1 heIns_s
    exact ⟨hEq, hDisj⟩

/-- Every edge of `st.extraEdges C` is either globally inserted or was dropped from the initial
forest of component `C`. -/
lemma bundleRunSeq_extraEdges_sub
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    {ord : ℕ → ℕ → List End} (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ)
    {t : ℕ}
    (hActB_eq : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeBuckets =
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets)
    (hI_t : CompLSFInv C_lsst (D.ℓ 0) (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs)
    (hBun_eq : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.bun (C, b)).edges =
        ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.bun (C, b)).edges \
          (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)))
    {C : Finset ℕ} (hC : C ∈ components (D.G 0)) :
    let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    st.extraEdges C ⊆
      st.cs.insertedGlobal ∪ ((cs₀.compSt C).RF.F.E \ (st.cs.compSt C).RF.F.E) := by
  intro st cs₀ e he
  have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hCompG : ∀ C' ∈ components (D.G 0), (cs₀.compSt C').G = compGraph (D.G 0) C' :=
    fun C' hC' => (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC').2.1
  have hcs_eq : st.cs = compLSFBatch cs₀ (dynBatches D t).flatten :=
    bundleRunSeq_cs_eq oracle C_lsst L sparsify k M N D ord j t
  have hcs_G₀ : st.cs.G₀ = D.G 0 := by rw [hcs_eq, compLSFBatch_G₀]; rfl
  by_cases hins : e ∈ st.cs.insertedGlobal
  · exact Finset.mem_union_left _ hins
  · refine Finset.mem_union_right _ ?_
    have he1 := Finset.mem_sdiff.mp he
    have he2 := Finset.mem_sdiff.mp he1.1
    have heC : e ∈ (st.cs.compSt C).G.E := he2.1
    have hnF : e ∉ (st.cs.compSt C).RF.F.E := he2.2
    have hniC : e ∉ (st.cs.compSt C).insertedEdges := fun hm =>
      hins (hI_t.hCompIns_sub C (hcs_G₀ ▸ hC) hm)
    have heC₀ : e ∈ (cs₀.compSt C).G.E := by
      have hs := ((hI_t.hCompLSF C (hcs_G₀ ▸ hC)).1.hsurv_edge e heC hniC).1
      have hG₀C : (st.cs.compSt C).G₀ = (cs₀.compSt C).G := by
        rw [(hI_t.hCompLSF C (hcs_G₀ ▸ hC)).2.1, hcs_G₀, hCompG C hC]
      rwa [hG₀C] at hs
    by_cases hF₀ : e ∈ (cs₀.compSt C).RF.F.E
    · exact Finset.mem_sdiff.mpr ⟨hF₀, hnF⟩
    · exfalso
      let st₀ := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1
      have hmem := comp_sdiff_mem_bucketCoreEdges hI₀ rfl hCompG st₀.origBucket hC
        (Finset.mem_sdiff.mpr ⟨heC₀, hF₀⟩)
      set b := st₀.origBucket e
      have hb_act : b ∈ st.activeBuckets C := by
        rw [hActB_eq]; exact hmem.1
      obtain ⟨ρ_all, hρ_ord, _⟩ := hOrd
      have he_bun0 : e ∈ (st₀.bun (C, b)).edges := by
        have hed : (st₀.bun (C, b)).edges =
            bucketCoreEdges (coreGraph (D.G 0) cs₀.lsf) st₀.origBucket C b :=
          initBundleFor_edges hI₀ (hρ_ord 0 (Nat.zero_le τ)) _ k
        rw [hed]
        exact hmem.2
      have he_Dt : e ∈ ((D.G 0).applyBatch (dynBatches D t).flatten).E := by
        have h1 : e ∈ st.cs.G.E := hI_t.hCE_sub C (hcs_G₀ ▸ hC) heC
        rw [hcs_eq, compLSFBatch_G] at h1
        exact h1
      have hni_flat : ∀ u ∈ (dynBatches D t).flatten, ¬ u.Inserts e := by
        rw [hcs_eq, compLSFBatch_insertedGlobal] at hins
        exact (applyBatch_not_inserted_of_not_foldl (dynBatches D t).flatten (D.G 0) ∅ e he_Dt hins).2.2
      have hnd_flat : ∀ u ∈ (dynBatches D t).flatten, u ≠ .delete e :=
        not_delete_of_mem_applyBatch_of_not_inserts he_Dt hni_flat
      have hnd_union : e ∉ (Finset.Icc 1 t).biUnion (fun s => batchDeletes (D.U s)) := by
        intro hm
        rw [Finset.mem_biUnion] at hm
        rcases hm with ⟨s, hs, hdel⟩
        rw [mem_batchDeletes_iff] at hdel
        rcases hdel with ⟨u, hu, rfl⟩
        have hs' := Finset.mem_Icc.mp hs
        exact hnd_flat (.delete e) (mem_dynBatches_flatten_of_Icc D hs'.1 hs'.2 hu) rfl
      have he_bun : e ∈ (st.bun (C, b)).edges := by
        rw [hBun_eq C hC b]
        exact Finset.mem_sdiff.mpr ⟨he_bun0, hnd_union⟩
      exact he1.2 (Finset.mem_biUnion.mpr ⟨b, hb_act, he_bun⟩)

/-! ## 4. Spanner input vertex count bounds along `bundleRunSeq` -/

lemma bundleRunSeq_dyn_Gn_bounds
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N τ : ℕ} (hk : 1 ≤ k) {D : DynamicInstance}
    (hM : (D.G 0).m ≤ M) (ord : ℕ → ℕ → List End) (j : ℕ)
    {C : Finset ℕ} (hC : C ∈ components (D.G 0)) (b : ℤ)
    (hBase : ∀ t ≤ τ,
        let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1
        CompLSFInv C_lsst (D.ℓ 0) st.cs ∧
        GraphEq (st.dyn (C, b)).G (st.bun (C, b)).graph)
    (hStep : ∀ s < τ,
        let st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1
        let st' := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1
        let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j s
        st.cs.G.BatchIsValid (D.U (s + 1)) ∧
        (st.dyn (C, b)).G.BatchIsValid (info.U_B (C, b)) ∧
        (st'.dyn (C, b)).G = (st.dyn (C, b)).G.applyBatch (info.U_B (C, b)) ∧
        (∀ op ∈ info.U_B (C, b), isDelOrSplit op) ∧
        batchSplitCount (info.U_B (C, b)) ≤
          2 * ((st'.cs.compSt C).R \ (st.cs.compSt C).R).card)
    (hFlat :
        let st₀ := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1
        let Hb₀ := (st₀.bun (C, b)).graph
        let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
        Hb₀.BatchIsValid Us_b.flatten ∧
        (∀ op ∈ Us_b.flatten, isDelOrSplit op) ∧
        batchSplitCount Us_b.flatten ≤ bundleSplitBudget k M) :
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let st₀ := (run 0).1
    ∀ t ≤ τ,
      let st := (run t).1
      (st.dyn (C, b)).G.n ≤ bundleNMax M ∧
      (st.dyn (C, b)).G.n ≤
        (st₀.bun (C, b)).vertices.card + 2 * ((st.cs.compSt C).R \ (st₀.cs.compSt C).R).card := by
  intro run st₀ t ht
  have hPref : ∀ s ≤ τ,
      let Hb₀ := (st₀.bun (C, b)).graph
      let Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
      let pref := (Us_b.take s).flatten
      Hb₀.BatchIsValid pref ∧ GraphEq (Hb₀.applyBatch pref) ((run s).1.dyn (C, b)).G := by
    intro s
    induction s with
    | zero =>
      intro _
      exact ⟨trivial, graphEq_symm (hBase 0 (Nat.zero_le τ)).2⟩
    | succ s ih =>
      intro hs_le
      have hs_lt : s < τ := hs_le
      obtain ⟨hBV_p, hG_p⟩ := ih (Nat.le_of_succ_le hs_le)
      have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hs_lt
      have htake : ((bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b).take (s + 1)).flatten =
          ((bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b).take s).flatten ++
            (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b) := by
        rw [take_succ_of_getElem? hget, List.flatten_append]; simp
      obtain ⟨_, hBV_st, hG_st, _, _⟩ := hStep s hs_lt
      refine ⟨?_, ?_⟩
      · rw [htake, batchIsValid_append]; exact ⟨hBV_p, (graphEq_batchIsValid hG_p _).mpr hBV_st⟩
      · rw [htake, applyBatch_append, hG_st]; exact graphEq_applyBatch hG_p _
  have hNMax : ((run t).1.dyn (C, b)).G.n ≤ bundleNMax M := by
    set Us_b := bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b
    have hcat : (Us_b.take t).flatten ++ (Us_b.drop t).flatten = Us_b.flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    have hds_pref : ∀ op ∈ (Us_b.take t).flatten, isDelOrSplit op :=
      fun op hop => hFlat.2.1 op (by rw [← hcat, List.mem_append]; exact Or.inl hop)
    have hsc_pref : batchSplitCount (Us_b.take t).flatten ≤ batchSplitCount Us_b.flatten := by
      rw [← hcat, batchSplitCount_append]; omega
    have hv : ((run t).1.dyn (C, b)).G.n ≤
        (st₀.bun (C, b)).graph.n + batchSplitCount (Us_b.take t).flatten := by
      rw [← graphEq_n (hPref t ht).2]
      exact (applyBatch_V_card_eq_of_isDelOrSplit (hPref t ht).1 hds_pref).le
    have hsum : (st₀.bun (C, b)).graph.n + bundleSplitBudget k M ≤ bundleNMax M :=
      initBundleTree_nMax_le_bundleNMax (N := N) oracle C_lsst L sparsify hk hM (D.ℓ 0) (ord 0) j C b
    have hsc_le : batchSplitCount (Us_b.take t).flatten ≤ bundleSplitBudget k M :=
      le_trans hsc_pref hFlat.2.2
    omega
  have hGrowth : ∀ s ≤ τ,
      ((run s).1.dyn (C, b)).G.n ≤
        (st₀.bun (C, b)).vertices.card +
          2 * (((run s).1.cs.compSt C).R \ (st₀.cs.compSt C).R).card ∧
      (st₀.cs.compSt C).R ⊆ ((run s).1.cs.compSt C).R := by
    intro s
    induction s with
    | zero =>
      intro _
      have h0 : ((run 0).1.dyn (C, b)).G.n = (st₀.bun (C, b)).graph.n :=
        graphEq_n (hBase 0 (Nat.zero_le τ)).2
      rw [h0]
      exact ⟨by simp [BundleState.graph, MGraph.n], Finset.Subset.rfl⟩
    | succ s ih =>
      intro hs_le
      have hs_lt : s < τ := hs_le
      obtain ⟨ih_n, ih_R⟩ := ih (Nat.le_of_succ_le hs_le)
      obtain ⟨hBU_s, hBV_st, hG_st, hds_st, hsc_st⟩ := hStep s hs_lt
      have hI_s := (hBase s (Nat.le_of_succ_le hs_le)).1
      have hcs_G₀ : (run s).1.cs.G₀ = D.G 0 := by
        rw [bundleRunSeq_cs_eq, compLSFBatch_G₀]; rfl
      have hsp_cs := compLSFBatch_step_props (D.U (s + 1)) hI_s hBU_s
      have hR_step : ((run s).1.cs.compSt C).R ⊆ ((run (s + 1)).1.cs.compSt C).R := by
        have hcs1 : (run (s + 1)).1.cs = compLSFBatch (run s).1.cs (D.U (s + 1)) := rfl
        rw [hcs1]
        exact (hsp_cs.2.2.1 C (hcs_G₀ ▸ hC)).2.2.2.1
      have hcard_eq : ((run (s + 1)).1.dyn (C, b)).G.n =
          ((run s).1.dyn (C, b)).G.n +
            batchSplitCount ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) := by
        unfold MGraph.n
        rw [hG_st]
        exact applyBatch_V_card_eq_of_isDelOrSplit hBV_st hds_st
      have hR_tel : (((run s).1.cs.compSt C).R \ (st₀.cs.compSt C).R).card +
          (((run (s + 1)).1.cs.compSt C).R \ ((run s).1.cs.compSt C).R).card =
          (((run (s + 1)).1.cs.compSt C).R \ (st₀.cs.compSt C).R).card := by
        have h12 := Finset.Subset.trans ih_R hR_step
        rw [Finset.card_sdiff_of_subset ih_R, Finset.card_sdiff_of_subset hR_step,
          Finset.card_sdiff_of_subset h12]
        have c1 := Finset.card_le_card ih_R
        have c2 := Finset.card_le_card hR_step
        omega
      have hsc_st' : batchSplitCount ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)) ≤
          2 * (((run (s + 1)).1.cs.compSt C).R \ ((run s).1.cs.compSt C).R).card := hsc_st
      refine ⟨?_, Finset.Subset.trans ih_R hR_step⟩
      omega
  exact ⟨hNMax, (hGrowth t ht).1⟩

end

end MinCostFlow.SparseCore
