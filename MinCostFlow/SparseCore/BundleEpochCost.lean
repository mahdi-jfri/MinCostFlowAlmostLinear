module

public import MinCostFlow.SparseCore.BundleRun
public import MinCostFlow.SparseCore.BundleConstants

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Epoch-level runtime bounds for the sparse core on bundle graphs

This file proves the bundle-graph analogues of `SparseCoreEpochCost.lean` (paper Lemma 5.17, pages
23–24). No input-degree bound appears anywhere: every bundle graph has initial maximum degree at
most `k` and vertex count at most `2 * m`, with split budget
`bundleSplitBudget k M ≤ 2 * (56 * M + 1)`.

Main lemmas:
- `initBundleState_n_le_two_m`, `initBundleFor_n_le_two_m`, `initBundleTree_buckets_sum_le`:
  initial bucket counts, edge-count sum, `n ≤ 2 m`, and pairwise disjointness of bucket edges.
- `bundleInitCB_cost_le`, `bundleInitBuckets_cost_sum_le`: initialization and lazy-initialization
  cost of all bucket spanners in terms of `bundleLambda P_b M`.
- `length_eq_delete_add_split_of_delOrSplit`, `countP_deleteTag_le_card_of_delOrSplit`:
  counting deletions and splits in a valid deletion/split batch.
- `bundle_epoch_U_B_sum_le`: per-bucket and total bundle-batch lengths over an epoch.
- `bundle_epoch_dyn_cost_le`: total dynamic-spanner update cost over an epoch, with `k + 1` in
  place of `dC + 1` and `bundleNRoot` / `bundleLambda` in place of `coreNRoot` / `coreLambda`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

public section

/-! ## 1. Local constant bounds -/

private lemma bundleLambda_ge_one' (P_b : SparsifyParams) (M : ℕ) :
    1 ≤ bundleLambda P_b M := by
  unfold bundleLambda
  exact one_le_pow₀ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)])

private lemma bundleSplitBudget_le' {k M : ℕ} (hk : 1 ≤ k) :
    bundleSplitBudget k M ≤ 2 * (56 * M + 1) := by
  unfold bundleSplitBudget
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hceil : Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ 56 * M :=
    Nat.ceil_le.mpr ((div_le_self (by positivity) hk1).trans (by norm_cast))
  omega

/-! ## 2. Initial bundle-graph counts and disjointness -/

private lemma initialSlots_length_le_flatMap {C : MGraph} (ρ : Rotation C) (E : Finset ℕ)
    {k : ℕ} (hk : 0 < k) (vs : List ℕ) :
    (vs.flatMap fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)).length ≤
      (vs.flatMap (restrictedEnds ρ E)).length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, initialChunks_length]
    have hdiv : (restrictedEnds ρ E v).length ⌈/⌉ k ≤ (restrictedEnds ρ E v).length := by
      rw [ceilDiv_le_iff_le_mul hk]
      exact Nat.le_mul_of_pos_left _ hk
    exact Nat.add_le_add hdiv ih

/-- Every initial bundle graph has at most `2 * m` vertices, since every chunk of capacity `k ≥ 1`
is nonempty and there are `2 * m` ends in total. -/
lemma initBundleState_n_le_two_m {C : MGraph} (ρ : Rotation C)
    {E : Finset ℕ} (hE : E ⊆ C.E) {k : ℕ} (hk : 0 < k) :
    (initBundleState ρ E k).graph.n ≤ 2 * (initBundleState ρ E k).graph.m := by
  have hslots := initialSlots_length_le_flatMap ρ E hk (C.V.sort (· ≤ ·))
  have hnodup : ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).Nodup := by
    rw [List.nodup_flatMap]
    refine ⟨fun v _ => (ρ.nodup v).filter _, ?_⟩
    apply List.Pairwise.imp_of_mem _ (Finset.sort_nodup C.V (· ≤ ·))
    intro v w _ _ hne
    apply List.disjoint_left.mpr
    intro x hv hw
    exact hne (((mem_restrictedEnds ρ hE v x).mp hv).2.symm.trans
      ((mem_restrictedEnds ρ hE w x).mp hw).2)
  have hsub : ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).toFinset ⊆ edgeEnds E := by
    intro x hx
    rw [List.mem_toFinset, List.mem_flatMap] at hx
    obtain ⟨v, _, hv⟩ := hx
    exact (mem_edgeEnds E x).mpr ((mem_restrictedEnds ρ hE v x).mp hv).1
  have hflat_le : ((C.V.sort (· ≤ ·)).flatMap (restrictedEnds ρ E)).length ≤ 2 * E.card := by
    rw [← List.toFinset_card_of_nodup hnodup, ← card_edgeEnds E]
    exact Finset.card_le_card hsub
  have h_n : (initBundleState ρ E k).graph.n = (initialSlots ρ E k).length := by
    simp [MGraph.n, BundleState.graph, initBundleState]
  have h_m : (initBundleState ρ E k).graph.m = E.card := rfl
  rw [h_n, h_m]
  exact le_trans hslots hflat_le

/-- The admitted edges of `initBundleFor` are a subset of the requested edge set `E`. -/
lemma initBundleFor_edges_sub (cs : CompLSFState) (ord : ℕ → List End) (E : Finset ℕ) (k : ℕ) :
    (initBundleFor cs ord E k).edges ⊆ E := by
  classical
  unfold initBundleFor
  split_ifs with h
  · exact Finset.Subset.refl _
  · exact Finset.empty_subset _

/-- `initBundleFor` always produces a bundle graph with `n ≤ 2 * m` whenever `0 < k` and `E` is
a subset of the core graph's edges. -/
lemma initBundleFor_n_le_two_m (cs : CompLSFState) (ord : ℕ → List End)
    {E : Finset ℕ} (hE : E ⊆ (coreGraph cs.G cs.lsf).E) {k : ℕ} (hk : 0 < k) :
    (initBundleFor cs ord E k).graph.n ≤ 2 * (initBundleFor cs ord E k).graph.m := by
  classical
  unfold initBundleFor
  split_ifs with h
  · let hI := h.choose_spec.choose_spec.choose
    let ρ := h.choose_spec.choose_spec.choose_spec.choose
    exact initBundleState_n_le_two_m
      (coreRotation (L := cs.lsf) ρ hI.hG_val (compLSF_RF_isRSF hI)) hE hk
  · simp [MGraph.n, MGraph.m, BundleState.graph]

/-- Global bucket-count, edge-count, vertex-to-edge, and pairwise-disjointness bounds for
`initBundleTreeWith`. -/
lemma initBundleTreeWith_buckets_sum_le (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ ℓ₀ ord j
    (components G₀).sum (fun C => (st₀.activeBuckets C).card) ≤ G₀.m ∧
    (components G₀).sum (fun C => (st₀.activeBuckets C).sum fun b =>
      ((st₀.bun (C, b)).graph).m) ≤ G₀.m ∧
    (∀ C b, ((st₀.bun (C, b)).graph).n ≤ 2 * ((st₀.bun (C, b)).graph).m) ∧
    (∀ C₁ ∈ components G₀, ∀ C₂ ∈ components G₀, ∀ b₁ b₂ : ℤ, (C₁, b₁) ≠ (C₂, b₂) →
      Disjoint (st₀.bun (C₁, b₁)).edges (st₀.bun (C₂, b₂)).edges) := by
  classical
  intro st₀
  set cs₀ := initCompLSFWith lsfInit G₀ ℓ₀ k j
  set C₀ := coreGraph G₀ cs₀.lsf
  set origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e)
  have hC₀_sub : C₀.E ⊆ G₀.E := Finset.sdiff_subset
  have hdisj_comp : Set.PairwiseDisjoint (↑(components G₀) : Set (Finset ℕ))
      (fun C => C₀.E.filter fun e => C₀.tail e ∈ C) := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    have h1 := (Finset.mem_filter.mp he₁).2
    have h2 := (Finset.mem_filter.mp he₂).2
    exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hne) h1 h2
  have hcard_sum : (components G₀).sum (fun C => (st₀.activeBuckets C).card) ≤ G₀.m := by
    calc (components G₀).sum (fun C => (st₀.activeBuckets C).card)
        ≤ (components G₀).sum (fun C => (C₀.E.filter fun e => C₀.tail e ∈ C).card) :=
          Finset.sum_le_sum fun C _ => Finset.card_image_le
      _ = ((components G₀).biUnion fun C => C₀.E.filter fun e => C₀.tail e ∈ C).card :=
          (Finset.card_biUnion hdisj_comp).symm
      _ ≤ C₀.E.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)
      _ ≤ G₀.m := Finset.card_le_card hC₀_sub
  have hbun_sub : ∀ C b, (st₀.bun (C, b)).edges ⊆ bucketCoreEdges C₀ origB C b :=
    fun C b => initBundleFor_edges_sub cs₀ ord (bucketCoreEdges C₀ origB C b) k
  have hbucket_disj : ∀ C₁ ∈ components G₀, ∀ C₂ ∈ components G₀, ∀ b₁ b₂ : ℤ,
      (C₁, b₁) ≠ (C₂, b₂) →
      Disjoint (bucketCoreEdges C₀ origB C₁ b₁) (bucketCoreEdges C₀ origB C₂ b₂) := by
    intro C₁ hC₁ C₂ hC₂ b₁ b₂ hne
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    simp only [bucketCoreEdges, Finset.mem_filter] at he₁ he₂
    by_cases hCeq : C₁ = C₂
    · subst hCeq
      exact hne (Prod.ext rfl (he₁.2.2.symm.trans he₂.2.2))
    · exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hCeq) he₁.2.1 he₂.2.1
  have hm_sum : (components G₀).sum (fun C => (st₀.activeBuckets C).sum fun b =>
      ((st₀.bun (C, b)).graph).m) ≤ G₀.m := by
    have hperC : ∀ C ∈ components G₀,
        ((st₀.activeBuckets C).sum fun b => ((st₀.bun (C, b)).graph).m) ≤
          (C₀.E.filter fun e => C₀.tail e ∈ C).card := by
      intro C hC
      have hdb : Set.PairwiseDisjoint (↑(st₀.activeBuckets C) : Set ℤ)
          (fun b => bucketCoreEdges C₀ origB C b) := by
        intro b₁ _ b₂ _ hne
        exact hbucket_disj C hC C hC b₁ b₂ (fun h => hne (Prod.mk.inj h).2)
      calc (st₀.activeBuckets C).sum (fun b => ((st₀.bun (C, b)).graph).m)
          ≤ (st₀.activeBuckets C).sum (fun b => (bucketCoreEdges C₀ origB C b).card) :=
            Finset.sum_le_sum fun b _ => Finset.card_le_card (hbun_sub C b)
        _ = ((st₀.activeBuckets C).biUnion fun b => bucketCoreEdges C₀ origB C b).card :=
            (Finset.card_biUnion hdb).symm
        _ ≤ (C₀.E.filter fun e => C₀.tail e ∈ C).card := by
            refine Finset.card_le_card (Finset.biUnion_subset.mpr fun b _ e he => ?_)
            simp only [bucketCoreEdges, Finset.mem_filter] at he ⊢
            exact ⟨he.1, he.2.1⟩
    calc (components G₀).sum (fun C => (st₀.activeBuckets C).sum fun b =>
            ((st₀.bun (C, b)).graph).m)
        ≤ (components G₀).sum (fun C => (C₀.E.filter fun e => C₀.tail e ∈ C).card) :=
          Finset.sum_le_sum hperC
      _ = ((components G₀).biUnion fun C => C₀.E.filter fun e => C₀.tail e ∈ C).card :=
          (Finset.card_biUnion hdisj_comp).symm
      _ ≤ C₀.E.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.filter_subset _ _)
      _ ≤ G₀.m := Finset.card_le_card hC₀_sub
  have hn_le : ∀ C b, ((st₀.bun (C, b)).graph).n ≤ 2 * ((st₀.bun (C, b)).graph).m := by
    intro C b
    have hE_sub : bucketCoreEdges C₀ origB C b ⊆ (coreGraph cs₀.G cs₀.lsf).E := by
      have hG : cs₀.G = G₀ := rfl
      rw [hG]
      exact Finset.filter_subset _ _
    exact initBundleFor_n_le_two_m cs₀ ord hE_sub hk
  have hdisj_bun : ∀ C₁ ∈ components G₀, ∀ C₂ ∈ components G₀, ∀ b₁ b₂ : ℤ,
      (C₁, b₁) ≠ (C₂, b₂) → Disjoint (st₀.bun (C₁, b₁)).edges (st₀.bun (C₂, b₂)).edges :=
    fun C₁ hC₁ C₂ hC₂ b₁ b₂ hne =>
      Disjoint.mono (hbun_sub C₁ b₁) (hbun_sub C₂ b₂)
        (hbucket_disj C₁ hC₁ C₂ hC₂ b₁ b₂ hne)
  exact ⟨hcard_sum, hm_sum, hn_le, hdisj_bun⟩

/-- Global bucket-count, edge-count, vertex-to-edge, and pairwise-disjointness bounds for
`initBundleTree`. -/
lemma initBundleTree_buckets_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M N : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (ℓ₀ : ℕ → ℝ) (ord : ℕ → List End) (j : ℕ) :
    let st₀ := initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j
    (components G₀).sum (fun C => (st₀.activeBuckets C).card) ≤ G₀.m ∧
    (components G₀).sum (fun C => (st₀.activeBuckets C).sum fun b =>
      ((st₀.bun (C, b)).graph).m) ≤ G₀.m ∧
    (∀ C b, ((st₀.bun (C, b)).graph).n ≤ 2 * ((st₀.bun (C, b)).graph).m) ∧
    (∀ C₁ ∈ components G₀, ∀ C₂ ∈ components G₀, ∀ b₁ b₂ : ℤ, (C₁, b₁) ≠ (C₂, b₂) →
      Disjoint (st₀.bun (C₁, b₁)).edges (st₀.bun (C₂, b₂)).edges) :=
  initBundleTreeWith_buckets_sum_le (initLSFOnline oracle C_lsst) L sparsify hk ℓ₀ ord j

/-! ## 3. Initialization cost bounds with `bundleLambda` -/

/-- Single-bucket initialization cost bound in terms of `bundleLambda P_b m₀`. -/
lemma bundleInitCB_cost_le
    {L : ℕ} {P_b : SparsifyParams} {m₀ : ℕ}
    {Hb : MGraph} {initB : DynSpanner.InitOut L}
    (hm_le_m0 : Hb.m ≤ m₀) (hn_le_2m : Hb.n ≤ 2 * Hb.m)
    (h82_Hm : (initB.state.H.m : ℝ) ≤
      P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ * (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s)
    (h82_cost : (initB.cost : ℝ) ≤
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t +
        (Hb.n : ℝ) + (Hb.m : ℝ) + (initB.state.H.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
        (L : ℝ) + 1) :
    (initB.cost : ℝ) ≤
      ((L : ℝ) + 1) +
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * bundleLambda P_b m₀ + 3 + P_b.γ_ℓ +
          2 * P_b.K_s * P_b.γ_ℓ * bundleLambda P_b m₀) * (Hb.m : ℝ) := by
  set Λ := bundleLambda P_b m₀
  have hK_s := P_b.hK_s; have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hn_le_2m₀ : Hb.n ≤ 2 * m₀ := le_trans hn_le_2m (Nat.mul_le_mul_left 2 hm_le_m0)
  have hn_le_bun : Hb.n ≤ bundleNMax m₀ := by unfold bundleNMax; omega
  have hact_le_n : (activeSubgraph Hb).n ≤ Hb.n := Finset.card_le_card (Finset.filter_subset _ _)
  have hbase_ge1 : (1 : ℝ) ≤ 1 + Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2) := by
    linarith [Real.log_nonneg (show (1 : ℝ) ≤ (bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2 by linarith)]
  have hlog_pow_le : ∀ {a p : ℕ}, a ≤ bundleNMax m₀ → p ≤ max P_b.p_s P_b.p_t →
      (1 + Real.log ((a : ℝ) + (Hb.m : ℝ) + 2)) ^ p ≤ Λ := fun {a p} ha hp => by
    have hbase : 0 ≤ 1 + Real.log ((a : ℝ) + (Hb.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (a : ℝ) + (Hb.m : ℝ) + 2 by linarith)]
    have hsub : 1 + Real.log ((a : ℝ) + (Hb.m : ℝ) + 2) ≤
        1 + Real.log ((bundleNMax m₀ : ℝ) + (m₀ : ℝ) + 2) :=
      add_le_add le_rfl (Real.log_le_log (by linarith) (by
        have h1 : (a : ℝ) ≤ (bundleNMax m₀ : ℝ) := by exact_mod_cast ha
        have h2 : (Hb.m : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm_le_m0
        linarith))
    exact (pow_le_pow_left₀ hbase hsub p).trans (pow_le_pow_right₀ hbase_ge1 hp)
  have hnR : (Hb.n : ℝ) ≤ 2 * (Hb.m : ℝ) := by exact_mod_cast hn_le_2m
  have hactR : ((activeSubgraph Hb).n : ℝ) ≤ 2 * (Hb.m : ℝ) := by
    exact_mod_cast le_trans hact_le_n hn_le_2m
  have hinitH : (initB.state.H.m : ℝ) ≤ 2 * P_b.K_s * P_b.γ_ℓ * Λ * (Hb.m : ℝ) := by
    have hbase : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ (Hb.n : ℝ) + (Hb.m : ℝ) + 2 by linarith)]
    calc (initB.state.H.m : ℝ)
        ≤ P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ * (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s := h82_Hm
      _ ≤ P_b.K_s * (2 * (Hb.m : ℝ)) * P_b.γ_ℓ * Λ :=
            mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnR hK_s) hγℓ_nn)
              (hlog_pow_le hn_le_bun (le_max_left _ _)) (pow_nonneg hbase _) (by positivity)
      _ = 2 * P_b.K_s * P_b.γ_ℓ * Λ * (Hb.m : ℝ) := by ring
  have hpart1 :
      P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_t ≤
        P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ * (Hb.m : ℝ) := by
    have hbase : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 by linarith)]
    have hm_part : ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2 ≤
        (2 + P_b.γ_ℓ ^ 2) * (Hb.m : ℝ) := by linarith
    calc P_b.K_t * (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
            (1 + Real.log _) ^ P_b.p_t
        ≤ P_b.K_t * ((2 + P_b.γ_ℓ ^ 2) * (Hb.m : ℝ)) * Λ :=
            mul_le_mul (mul_le_mul_of_nonneg_left hm_part hK_t)
              (hlog_pow_le (le_trans hact_le_n hn_le_bun) (le_max_right _ _))
              (pow_nonneg hbase _) (by positivity)
      _ = P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ * (Hb.m : ℝ) := by ring
  linarith [h82_cost, hpart1, hinitH]

/-- Total initialization cost over all active components and their length buckets. -/
lemma bundleInitBuckets_cost_sum_le
    {L : ℕ} {P_b : SparsifyParams} {m₀ : ℕ} {G₀ : MGraph}
    (actComps : Finset (Finset ℕ)) (hact_sub : actComps ⊆ components G₀)
    (actB : Finset ℕ → Finset ℤ)
    (Hb : Finset ℕ → ℤ → MGraph)
    (initCB : Finset ℕ → ℤ → DynSpanner.InitOut L)
    (hact_card : (components G₀).sum (fun C => (actB C).card) ≤ m₀)
    (hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ m₀)
    (hn_2m : ∀ C ∈ components G₀, ∀ b ∈ actB C, (Hb C b).n ≤ 2 * (Hb C b).m)
    (h82_init : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ((initCB C b).state.H.m : ℝ) ≤
        P_b.K_s * ((Hb C b).n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
      ((initCB C b).cost : ℝ) ≤
        P_b.K_t * (((activeSubgraph (Hb C b)).n : ℝ) + ((Hb C b).m : ℝ) * P_b.γ_ℓ ^ 2) *
            (1 + Real.log (((activeSubgraph (Hb C b)).n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_t +
          ((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) + ((initCB C b).state.H.m : ℝ) +
          ((Hb C b).m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) :
    (actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ))) ≤
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * bundleLambda P_b m₀ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * bundleLambda P_b m₀) * (m₀ : ℝ) := by
  set Λ := bundleLambda P_b m₀
  have hK_s := P_b.hK_s; have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hΛ_nn : 0 ≤ Λ := by linarith [bundleLambda_ge_one' P_b m₀]
  have hC1 : 0 ≤ P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
      2 * P_b.K_s * P_b.γ_ℓ * Λ := by positivity
  have hsub : actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) ≤
      (components G₀).sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg hact_sub
      (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hcb_le :
      ((components G₀).sum fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ)) ≤
      (components G₀).sum fun C => (actB C).sum fun b =>
        (((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
            ((Hb C b).m : ℝ)) := by
    refine Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => ?_
    have hm_cb : (Hb C b).m ≤ m₀ := le_trans
      (Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb)
      (le_trans (Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
        (fun _ _ => Nat.zero_le _) hC) hm_sum)
    exact bundleInitCB_cost_le hm_cb (hn_2m C hC b hb) (h82_init C hC b hb).1 (h82_init C hC b hb).2
  have hsum_eq :
      ((components G₀).sum fun C => (actB C).sum fun b =>
        (((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
            ((Hb C b).m : ℝ))) =
      ((components G₀).sum fun C => ((actB C).card : ℝ)) * ((L : ℝ) + 1) +
        (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) *
          ((components G₀).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_mul]; ring
  have hcard_r : ((components G₀).sum fun C => ((actB C).card : ℝ)) ≤ (m₀ : ℝ) := by
    rw [← Nat.cast_sum]; exact_mod_cast hact_card
  have hm_r : ((components G₀).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) ≤ (m₀ : ℝ) := by
    simp only [← Nat.cast_sum]; exact_mod_cast hm_sum
  calc actComps.sum (fun C => (actB C).sum fun b => ((initCB C b).cost : ℝ))
      ≤ _ := hsub
    _ ≤ _ := hcb_le
    _ = _ := hsum_eq
    _ ≤ (m₀ : ℝ) * ((L : ℝ) + 1) +
          (P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ + 2 * P_b.K_s * P_b.γ_ℓ * Λ) * (m₀ : ℝ) := by gcongr
    _ = _ := by ring

/-! ## 4. Deletion and split counting in bundle batches -/

/-- A batch containing only deletions and splits has length equal to its deletions plus splits. -/
lemma length_eq_delete_add_split_of_delOrSplit {U : List Update}
    (h : ∀ op ∈ U, isDelOrSplit op) :
    U.length = U.countP deleteTag + batchSplitCount U := by
  induction U with
  | nil => simp [batchSplitCount]
  | cons op rest ih =>
    have hop := h op List.mem_cons_self
    have hrest := ih fun x hx => h x (List.mem_cons_of_mem op hx)
    cases op with
    | insert => exact False.elim hop
    | delete e =>
      simp only [List.length_cons, List.countP_cons, deleteTag, batchSplitCount, isSplit,
        Bool.false_eq_true, ↓reduceIte] at hrest ⊢
      omega
    | split v v' St Sh =>
      simp only [List.length_cons, List.countP_cons, deleteTag, batchSplitCount, isSplit,
        Bool.false_eq_true, ↓reduceIte] at hrest ⊢
      omega

/-- A valid deletion/split batch deletes each edge at most once, so its deletion count is at most
the cardinality of any set `S` containing all its deleted edges, intersected with `G.E`. -/
lemma countP_deleteTag_le_card_of_delOrSplit {G : MGraph} {U : List Update} {S : Finset ℕ}
    (hU : G.BatchIsValid U) (hds : ∀ op ∈ U, isDelOrSplit op)
    (hsub : ∀ op ∈ U, deleteTag op = true → ∃ e ∈ S, op = .delete e) :
    U.countP deleteTag ≤ (G.E ∩ S).card := by
  induction U generalizing G with
  | nil => simp
  | cons op rest ih =>
    have hop := hds op List.mem_cons_self
    have hrest_ds : ∀ x ∈ rest, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem op hx)
    have hrest_sub : ∀ x ∈ rest, deleteTag x = true → ∃ e ∈ S, x = .delete e :=
      fun x hx => hsub x (List.mem_cons_of_mem op hx)
    cases op with
    | insert => exact False.elim hop
    | split v v' St Sh =>
      have hE_eq : (G.applyUpdate (.split v v' St Sh)).E = G.E := rfl
      have hrec := ih hU.2 hrest_ds hrest_sub
      rw [hE_eq] at hrec
      simpa [List.countP_cons, deleteTag] using hrec
    | delete e =>
      have heG : e ∈ G.E := hU.1
      obtain ⟨e', he'S, heq⟩ := hsub (.delete e) List.mem_cons_self rfl
      have heS : e ∈ S := by cases heq; exact he'S
      have hrec := ih hU.2 hrest_ds hrest_sub
      have hE_eq : (G.applyUpdate (.delete e)).E = G.E.erase e := rfl
      have hinter : (G.E.erase e) ∩ S = (G.E ∩ S).erase e := by
        ext x; simp [Finset.mem_erase, Finset.mem_inter]
      rw [hE_eq, hinter] at hrec
      have heIS : e ∈ G.E ∩ S := Finset.mem_inter.mpr ⟨heG, heS⟩
      have hcard : ((G.E ∩ S).erase e).card + 1 = (G.E ∩ S).card :=
        Finset.card_erase_add_one heIS
      simp only [List.countP_cons, deleteTag, ↓reduceIte]
      omega

/-! ## 5. Epoch bundle-batch and dynamic-spanner cost bounds -/

/-- Bounds both the per-bucket and total bundle-batch lengths over an epoch `[s₀, s₀ + Δ]`. -/
lemma bundle_epoch_U_B_sum_le
    {G₀ : MGraph} {N B_bound s₀ Δ : ℕ} {D : DynamicInstance}
    (actB : Finset ℕ → Finset ℤ)
    (hB_bound : ∀ C ∈ components G₀, (actB C).card ≤ B_bound)
    (cs : ℕ → CompLSFState)
    (U_B : ℕ → Finset ℕ × ℤ → List Update)
    (hStep_ds : ∀ r < Δ, ∀ C ∈ components G₀, ∀ b ∈ actB C,
      ∀ op ∈ U_B r (C, b), isDelOrSplit op)
    (hStep_del : ∀ r < Δ,
      ((components G₀).sum fun C => (actB C).sum fun b => (U_B r (C, b)).countP deleteTag) ≤
        (D.U (s₀ + r + 1)).length)
    (hStep_split : ∀ r < Δ, ∀ C ∈ components G₀, ∀ b ∈ actB C,
      batchSplitCount (U_B r (C, b)) ≤ 2 * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card)
    (hR_comp_sum : ∀ r < Δ,
      ((components G₀).sum fun C => (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card) =
        ((cs (r + 1)).RF.R \ (cs r).RF.R).card)
    (hR_sum :
      let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
      ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) ≤
        112 * (q_ep : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    let uc_ep := 2 * bundleUCRatio N * (q_ep : ℝ)
    (∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) ≤ uc_ep) ∧
    ((components G₀).sum fun C => (actB C).sum fun b =>
      ∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) ≤ (B_bound : ℝ) * uc_ep := by
  intro q_ep uc_ep
  have hq_nat : q_ep = ∑ r ∈ Finset.range Δ, (D.U (s₀ + r + 1)).length := by
    have hshift : ∀ d, ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + d), (D.U s).length =
        ∑ r ∈ Finset.range d, (D.U (s₀ + r + 1)).length := fun d => by
      induction d with
      | zero => simp
      | succ d ih =>
        have hs1 : s₀ + (d + 1) = s₀ + d + 1 := by omega
        rw [hs1, Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
    exact hshift Δ
  have hq_eq : ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) = (q_ep : ℝ) := by
    rw [hq_nat, Nat.cast_sum]
  have hsingle : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) ≤ uc_ep := by
    intro C hC b hb
    have hstep_le : ∀ r ∈ Finset.range Δ,
        ((U_B r (C, b)).length : ℝ) ≤
          ((D.U (s₀ + r + 1)).length : ℝ) +
          2 * (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ) := by
      intro r hr
      have hr' := Finset.mem_range.mp hr
      have hlen := length_eq_delete_add_split_of_delOrSplit (hStep_ds r hr' C hC b hb)
      have hdel_le : (U_B r (C, b)).countP deleteTag ≤ (D.U (s₀ + r + 1)).length := by
        calc (U_B r (C, b)).countP deleteTag
            ≤ (actB C).sum (fun b' => (U_B r (C, b')).countP deleteTag) :=
              Finset.single_le_sum (f := fun b' => (U_B r (C, b')).countP deleteTag)
                (fun _ _ => Nat.zero_le _) hb
          _ ≤ (components G₀).sum (fun C' => (actB C').sum fun b' =>
                (U_B r (C', b')).countP deleteTag) :=
              Finset.single_le_sum
                (f := fun C' => (actB C').sum fun b' => (U_B r (C', b')).countP deleteTag)
                (fun _ _ => Nat.zero_le _) hC
          _ ≤ (D.U (s₀ + r + 1)).length := hStep_del r hr'
      have hsp_le : batchSplitCount (U_B r (C, b)) ≤
          2 * ((cs (r + 1)).RF.R \ (cs r).RF.R).card := by
        calc batchSplitCount (U_B r (C, b))
            ≤ 2 * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card :=
              hStep_split r hr' C hC b hb
          _ ≤ 2 * ((components G₀).sum fun C' =>
                (((cs (r + 1)).compSt C').R \ ((cs r).compSt C').R).card) :=
              Nat.mul_le_mul_left 2
                (Finset.single_le_sum
                  (f := fun C' => (((cs (r + 1)).compSt C').R \ ((cs r).compSt C').R).card)
                  (fun _ _ => Nat.zero_le _) hC)
          _ = 2 * ((cs (r + 1)).RF.R \ (cs r).RF.R).card := by rw [hR_comp_sum r hr']
      have hnat : (U_B r (C, b)).length ≤
          (D.U (s₀ + r + 1)).length + 2 * ((cs (r + 1)).RF.R \ (cs r).RF.R).card := by omega
      exact_mod_cast hnat
    have hsum1 : (∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) ≤
        (q_ep : ℝ) + 2 * ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) := by
      calc (∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ))
          ≤ ∑ r ∈ Finset.range Δ,
              (((D.U (s₀ + r + 1)).length : ℝ) +
                2 * (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ)) :=
            Finset.sum_le_sum hstep_le
        _ = (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) +
              2 * ∑ r ∈ Finset.range Δ, (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        _ = (q_ep : ℝ) +
              2 * ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) := by
            rw [hq_eq, Nat.cast_sum (s := Finset.range Δ)]
    have hq_nn : (0 : ℝ) ≤ (q_ep : ℝ) := Nat.cast_nonneg _
    dsimp only [uc_ep, bundleUCRatio]
    linarith [hsum1, hR_sum]
  have htotal : ((components G₀).sum fun C => (actB C).sum fun b =>
      ∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) ≤ (B_bound : ℝ) * uc_ep := by
    by_cases hB0 : B_bound = 0
    · subst hB0
      have hzero : ∀ C ∈ components G₀, actB C = ∅ := fun C hC =>
        Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (hB_bound C hC))
      have hlhs : ((components G₀).sum fun C => (actB C).sum fun b =>
          ∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) = 0 := by
        refine Finset.sum_eq_zero fun C hC => ?_
        rw [hzero C hC, Finset.sum_empty]
      rw [hlhs]; simp
    · have hB1 : (1 : ℝ) ≤ (B_bound : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hB0
      have hcomm' :
          ((components G₀).sum fun C => (actB C).sum fun b =>
            ∑ r ∈ Finset.range Δ, ((U_B r (C, b)).length : ℝ)) =
          ∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
            ((U_B r (C, b)).length : ℝ)) := by
        calc _ = (components G₀).sum (fun C => ∑ r ∈ Finset.range Δ, (actB C).sum fun b =>
                  ((U_B r (C, b)).length : ℝ)) :=
                Finset.sum_congr rfl fun C _ => Finset.sum_comm
          _ = _ := Finset.sum_comm
      rw [hcomm']
      have hper_step : ∀ r ∈ Finset.range Δ,
          ((components G₀).sum fun C => (actB C).sum fun b => ((U_B r (C, b)).length : ℝ)) ≤
            ((D.U (s₀ + r + 1)).length : ℝ) +
            2 * (B_bound : ℝ) * (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ) := by
        intro r hr
        have hr' := Finset.mem_range.mp hr
        have hdecomp :
            ((components G₀).sum fun C => (actB C).sum fun b => ((U_B r (C, b)).length : ℝ)) =
            ((components G₀).sum fun C => (actB C).sum fun b =>
              ((U_B r (C, b)).countP deleteTag : ℝ)) +
            ((components G₀).sum fun C => (actB C).sum fun b =>
              (batchSplitCount (U_B r (C, b)) : ℝ)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun C hC => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b hb => ?_
          exact_mod_cast length_eq_delete_add_split_of_delOrSplit (hStep_ds r hr' C hC b hb)
        have hdelR : ((components G₀).sum fun C => (actB C).sum fun b =>
            ((U_B r (C, b)).countP deleteTag : ℝ)) ≤ ((D.U (s₀ + r + 1)).length : ℝ) := by
          simp only [← Nat.cast_sum]
          exact_mod_cast hStep_del r hr'
        have hspR : ((components G₀).sum fun C => (actB C).sum fun b =>
            (batchSplitCount (U_B r (C, b)) : ℝ)) ≤
            2 * (B_bound : ℝ) * (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ) := by
          have h1 : ((components G₀).sum fun C => (actB C).sum fun b =>
              batchSplitCount (U_B r (C, b))) ≤
              2 * B_bound * ((cs (r + 1)).RF.R \ (cs r).RF.R).card := by
            calc (components G₀).sum (fun C => (actB C).sum fun b => batchSplitCount (U_B r (C, b)))
                ≤ (components G₀).sum (fun C => (actB C).sum fun _ =>
                    2 * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card) :=
                  Finset.sum_le_sum fun C hC =>
                    Finset.sum_le_sum fun b hb => hStep_split r hr' C hC b hb
              _ = (components G₀).sum (fun C =>
                    (actB C).card * (2 * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card)) := by
                  refine Finset.sum_congr rfl fun C _ => by simp [Finset.sum_const]
              _ ≤ (components G₀).sum (fun C =>
                    B_bound * (2 * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card)) :=
                  Finset.sum_le_sum fun C hC => Nat.mul_le_mul_right _ (hB_bound C hC)
              _ = (components G₀).sum (fun C =>
                    (2 * B_bound) * (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card) :=
                  Finset.sum_congr rfl fun C _ => by ring
              _ = (2 * B_bound) * ((components G₀).sum fun C =>
                    (((cs (r + 1)).compSt C).R \ ((cs r).compSt C).R).card) := by
                  rw [← Finset.mul_sum]
              _ = 2 * B_bound * ((cs (r + 1)).RF.R \ (cs r).RF.R).card := by
                  rw [hR_comp_sum r hr']
          simp only [← Nat.cast_sum]
          exact_mod_cast h1
        linarith [hdecomp, hdelR, hspR]
      have hsum2 :
          (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
            ((U_B r (C, b)).length : ℝ))) ≤
          (q_ep : ℝ) + 2 * (B_bound : ℝ) *
            ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) := by
        calc _ ≤ ∑ r ∈ Finset.range Δ,
                (((D.U (s₀ + r + 1)).length : ℝ) +
                  2 * (B_bound : ℝ) * (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ)) :=
              Finset.sum_le_sum hper_step
          _ = (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) +
                2 * (B_bound : ℝ) *
                  ∑ r ∈ Finset.range Δ, (((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℝ) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = (q_ep : ℝ) + 2 * (B_bound : ℝ) *
                ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) := by
              rw [hq_eq, Nat.cast_sum (s := Finset.range Δ)]
      have hq_nn : (0 : ℝ) ≤ (q_ep : ℝ) := Nat.cast_nonneg _
      have hB_nn : (0 : ℝ) ≤ (B_bound : ℝ) := Nat.cast_nonneg _
      have hq_le_Bq : (q_ep : ℝ) ≤ (B_bound : ℝ) * (q_ep : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hB1 hq_nn
      have hR_mul : 2 * (B_bound : ℝ) *
            ((∑ r ∈ Finset.range Δ, ((cs (r + 1)).RF.R \ (cs r).RF.R).card : ℕ) : ℝ) ≤
          2 * (B_bound : ℝ) * (112 * (q_ep : ℝ) * (Real.log ((N : ℝ) + 2)) ^ 2) :=
        mul_le_mul_of_nonneg_left hR_sum (by positivity)
      dsimp only [uc_ep, bundleUCRatio]
      linarith [hsum2, hq_le_Bq, hR_mul]
  exact ⟨hsingle, htotal⟩

/-- Dynamic-spanner update cost over an epoch `[s₀, s₀ + Δ]` on bundle graphs, using the
historical bundle-degree bound `Hb.maxDeg ≤ k` and Lemma 2.1 encoding size. -/
lemma bundle_epoch_dyn_cost_le
    {L : ℕ} (hL : 1 ≤ L) {P_b : SparsifyParams}
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {k M B_bound Δ : ℕ} (hk : 1 ≤ k) {G₀ : MGraph}
    (actB : Finset ℕ → Finset ℤ)
    (actComps_ep : ℕ → Finset (Finset ℕ))
    (Hb : Finset ℕ → ℤ → MGraph)
    (Us_ep : Finset ℕ → ℤ → List (List Update))
    (U_B_ep : ℕ → Finset ℕ × ℤ → List Update)
    (stepOut_ep : ℕ → Finset ℕ × ℤ → StepOut L)
    (uc_ep ucBound : ℝ) (huc_nn : 0 ≤ ucBound)
    (hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M)
    (hHb_2m : ∀ C ∈ components G₀, ∀ b ∈ actB C, (Hb C b).n ≤ 2 * (Hb C b).m)
    (hHb_deg : ∀ C ∈ components G₀, ∀ b ∈ actB C, (Hb C b).maxDeg ≤ k)
    (hUB_single : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)) ≤ ucBound)
    (hUB_sum : ((components G₀).sum fun C => (actB C).sum fun b =>
      ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)) ≤ (B_bound : ℝ) * uc_ep)
    (hact_sub : ∀ r < Δ, actComps_ep r ⊆ components G₀)
    (hDyn_G_val0 : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (DynSpanner.runBatchState (L := L) (Hb C b)
        (phaseBase ((Hb C b).n + bundleSplitBudget k M) L) (sparsify M) (Us_ep C b) 0).G.IsValid)
    (hDyn_G_m0 : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (DynSpanner.runBatchState (L := L) (Hb C b)
        (phaseBase ((Hb C b).n + bundleSplitBudget k M) L) (sparsify M) (Us_ep C b) 0).G.m =
        (Hb C b).m)
    (hStep_ep : ∀ r < Δ, ∀ C ∈ components G₀, ∀ b ∈ actB C,
      let G_r := (DynSpanner.runBatchState (L := L) (Hb C b)
        (phaseBase ((Hb C b).n + bundleSplitBudget k M) L) (sparsify M) (Us_ep C b) r).G
      let G_r1 := (DynSpanner.runBatchState (L := L) (Hb C b)
        (phaseBase ((Hb C b).n + bundleSplitBudget k M) L) (sparsify M) (Us_ep C b) (r + 1)).G
      G_r.BatchIsValid (U_B_ep r (C, b)) ∧ G_r1 = G_r.applyBatch (U_B_ep r (C, b)))
    (hStepOut_ep : ∀ C ∈ components G₀, ∀ b ∈ actB C, ∀ r < Δ,
      stepOut_ep r (C, b) =
        DynSpanner.runBatchStepOut (L := L) (Hb C b)
          (phaseBase ((Hb C b).n + bundleSplitBudget k M) L) (sparsify M) (Us_ep C b) r)
    (hT82_cost : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      let splitB := bundleSplitBudget k M
      let nMax_b := (Hb C b).n + splitB
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
            (Us_ep C b) r).G.batchEnc (U_B_ep r (C, b)) : ℝ)
      (∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
          (Us_ep C b) r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) :
    let Λ := bundleLambda P_b M
    (∑ r ∈ Finset.range Δ, ((actComps_ep r).sum fun C => (actB C).sum fun b =>
      ((stepOut_ep r (C, b)).cost : ℝ))) ≤
      90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((k : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro Λ
  have hK_s := P_b.hK_s
  have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hγc_nn := P_b.hγ_c
  have hΛ_ge1 : 1 ≤ Λ := bundleLambda_ge_one' P_b M
  have hΛ_nn : 0 ≤ Λ := by linarith
  have hSplitB : bundleSplitBudget k M ≤ 2 * (56 * M + 1) := bundleSplitBudget_le' hk
  have hcoeff_nn :
      0 ≤ 90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((k : ℝ) + 1) * Λ := by
    unfold bundleNRoot coreE_L
    positivity
  have hb_cost : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ, ((stepOut_ep r (C, b)).cost : ℝ)) ≤
        90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((k : ℝ) + 1) * Λ *
          (20 * (((Hb C b).m : ℝ) +
            (∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ))) *
            Real.log ((M : ℝ) + ucBound + 2)) := by
    intro C hC b hb
    set splitB := bundleSplitBudget k M
    set ub_tot := ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)
    have htb := hT82_cost C hC b hb
    dsimp only at htb
    have hm_le_m0 : (Hb C b).m ≤ M := le_trans
      (Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb)
      (le_trans (Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
        (fun _ _ => Nat.zero_le _) hC) hm_sum)
    have hnMax_le : (Hb C b).n + splitB ≤ bundleNMax M :=
      Nat.add_le_add (le_trans (hHb_2m C hC b hb) (Nat.mul_le_mul_left 2 hm_le_m0)) hSplitB
    have hnRoot_le :
        ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤ bundleNRoot L M :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast max_le_max_right 1 hnMax_le) (by positivity)
    have hbase_b :
        0 ≤ 1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) := by
      linarith [Real.log_nonneg
        (show (1 : ℝ) ≤ (((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2 by linarith)]
    have hΛ_le :
        (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^
          max P_b.p_s P_b.p_t ≤ Λ :=
      pow_le_pow_left₀ hbase_b (add_le_add le_rfl (Real.log_le_log (by linarith) (by
        have h1 : (((Hb C b).n + splitB : ℕ) : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hnMax_le
        have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_le_m0
        linarith))) _
    have hdeg_le : ((Hb C b).maxDeg : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (hHb_deg C hC b hb)
    have henc_b :
        (∑ r ∈ Finset.range Δ,
          ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) r).G.batchEnc (U_B_ep r (C, b)) : ℝ)) ≤
          20 * (((Hb C b).m : ℝ) + ub_tot) * Real.log ((M : ℝ) + ucBound + 2) := by
      let Gb : ℕ → MGraph := fun r =>
        (DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
          (sparsify M) (Us_ep C b) r).G
      let Ub : ℕ → List Update := fun r => if r = 0 then [] else U_B_ep (r - 1) (C, b)
      have hval_b : ∀ r, 1 ≤ r → r ≤ Δ →
          (Gb (r - 1)).BatchIsValid (Ub r) ∧ Gb r = (Gb (r - 1)).applyBatch (Ub r) := by
        intro r hr1 hrΔ
        obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
        simp only [Ub, Nat.succ_ne_zero, ↓reduceIte, Nat.succ_sub_one, Nat.succ_eq_add_one]
        exact hStep_ep s hrΔ C hC b hb
      have hL21 := MinCostFlow.Chain.lemma_2_1 (G := Gb) (U := Ub) (τ := Δ)
        (hDyn_G_val0 C hC b hb) hval_b
      have hsum_enc : ∑ r ∈ Finset.Icc 1 Δ, (Gb (r - 1)).batchEnc (Ub r) =
          ∑ r ∈ Finset.range Δ, (Gb r).batchEnc (U_B_ep r (C, b)) := by
        rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (Gb (r - 1)).batchEnc (Ub r)) Δ]
        refine Finset.sum_congr rfl fun r _ => by simp [Ub]
      have hsum_len : ((∑ r ∈ Finset.Icc 1 Δ, (Ub r).length : ℕ) : ℝ) = ub_tot := by
        rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (Ub r).length) Δ, Nat.cast_sum]
        refine Finset.sum_congr rfl fun r _ => by simp [Ub]
      rw [hDyn_G_m0 C hC b hb, hsum_enc, Nat.cast_sum, hsum_len] at hL21
      refine le_trans hL21 ?_
      have hub_le : ub_tot ≤ ucBound := hUB_single C hC b hb
      have hub_nn : 0 ≤ ub_tot := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      have hmR : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm_le_m0
      have hlog_le : Real.log (((Hb C b).m : ℝ) + ub_tot + 2) ≤
          Real.log ((M : ℝ) + ucBound + 2) :=
        Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) (Hb C b).m]) (by linarith)
      exact mul_le_mul_of_nonneg_left hlog_le (by linarith [Nat.cast_nonneg (α := ℝ) (Hb C b).m])
    have hcost_eq : ∀ r ∈ Finset.range Δ,
        ((stepOut_ep r (C, b)).cost : ℝ) =
          ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) r).cost : ℝ) := fun r hr => by
      rw [hStepOut_ep C hC b hb r (Finset.mem_range.mp hr)]
    rw [Finset.sum_congr rfl hcost_eq]
    refine le_trans htb (mul_le_mul ?_ henc_b
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hcoeff_nn)
    have hNR_nn : 0 ≤ bundleNRoot L M := Real.rpow_nonneg (Nat.cast_nonneg _) _
    unfold coreE_L
    refine mul_le_mul (mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnRoot_le (by positivity)) (by positivity)) (by positivity))
      hdeg_le (by positivity) (by positivity)) hΛ_le (pow_nonneg hbase_b _) (by positivity)
  have hstep_sub :
      (∑ r ∈ Finset.range Δ, ((actComps_ep r).sum fun C => (actB C).sum fun b =>
        ((stepOut_ep r (C, b)).cost : ℝ))) ≤
      ∑ r ∈ Finset.range Δ, (components G₀).sum fun C => (actB C).sum fun b =>
        ((stepOut_ep r (C, b)).cost : ℝ) :=
    Finset.sum_le_sum fun r hr =>
      Finset.sum_le_sum_of_subset_of_nonneg (hact_sub r (Finset.mem_range.mp hr))
        (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hcomm :
      (∑ r ∈ Finset.range Δ, (components G₀).sum fun C => (actB C).sum fun b =>
        ((stepOut_ep r (C, b)).cost : ℝ)) =
      (components G₀).sum fun C => (actB C).sum fun b =>
        ∑ r ∈ Finset.range Δ, ((stepOut_ep r (C, b)).cost : ℝ) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
  have hinner_sum :
      ((components G₀).sum fun C => (actB C).sum fun b =>
        (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ))) ≤
        (M : ℝ) + (B_bound : ℝ) * uc_ep := by
    have hm_r : ((components G₀).sum fun C => (actB C).sum fun b => ((Hb C b).m : ℝ)) ≤
        (M : ℝ) := by
      simp only [← Nat.cast_sum]
      exact_mod_cast hm_sum
    simp only [Finset.sum_add_distrib]
    linarith [hm_r, hUB_sum]
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + ucBound + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  calc _ ≤ _ := hstep_sub
    _ = _ := hcomm
    _ ≤ (components G₀).sum fun C => (actB C).sum fun b =>
          90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
            ((k : ℝ) + 1) * Λ *
            (20 * (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ)) *
              Real.log ((M : ℝ) + ucBound + 2)) :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hb_cost C hC b hb
    _ = 90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((k : ℝ) + 1) * Λ *
          (20 * ((components G₀).sum fun C => (actB C).sum fun b =>
            (((Hb C b).m : ℝ) + ∑ r ∈ Finset.range Δ, ((U_B_ep r (C, b)).length : ℝ))) *
            Real.log ((M : ℝ) + ucBound + 2)) := by
          simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
    _ ≤ _ := by
          gcongr

end

end MinCostFlow.SparseCore
