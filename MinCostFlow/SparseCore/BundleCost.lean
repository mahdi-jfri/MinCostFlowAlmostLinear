module

public import MinCostFlow.SparseCore.BundleEpochCost

import MinCostFlow.SparseCore.BundleStage
import MinCostFlow.SparseCore.BundleRunInv
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.BundleRecourse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime bound for the sparse core on bundle graphs (`bundleRunSeq_cost_le`)

Combines the exact cost decomposition `bundleRunSeq_cost_eq`, the bucket initialization bound
`bundleInitBuckets_cost_sum_le`, the bundle-batch length bound `bundle_epoch_U_B_sum_le`,
the recourse bound from `bundleRunSeq_recourse_and_enc`, and the dynamic-spanner update bound
`bundle_epoch_dyn_cost_le` into the per-branch runtime bound `bundleRunSeq_cost_le` (paper Lemma
5.17, pages 23–24).

Compared to `treeRunSeq_cost_le`, the bundle degree cap `k` replaces `dC`, `bundleNRoot` /
`bundleLambda` / `bundleUCRatio` / `bundleRecoursePerQ` replace the degree-dependent quotient
constants, and the bundle-step length sum `bunCost` carries the factor `B_bound` because
`stepBundleTree` sums `|U_B (C, b)|` over both components `C` and active buckets `b`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

public section

/-! ## 1. Helper lemmas connecting `bundleRunSeq` to epoch cost bounds -/

private lemma bundleStepReady_of_stage {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {B : BundleState} {k : ℕ} {ord ord' : ℕ → List End} {U : List Update} {G_t G_t1 : MGraph}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hG_eq : cs.G = G_t) (hBU : cs.G.BatchIsValid U)
    (ρ : Rotation G_t) (σ : Rotation G_t1) (hρ : ρ.order = ord) (hσ : σ.order = ord')
    (hstep_G : G_t1 = G_t.applyBatch U) (hrot : RotationBatch 2 U ρ (hstep_G ▸ σ))
    (hPart : ∀ (ρ' : Rotation cs.G) (hG : cs.G.IsValid)
      (hF : cs.RF.IsRootedSpanningForestOf cs.G), ρ'.order = ord →
      B.IsPartition (coreRotation (L := cs.lsf) ρ' hG hF) k) :
    BundleStepReady cs B k ord ord' U := by
  cases hG_eq
  cases hstep_G
  exact ⟨C_lsst, ℓ₀, hI, ρ, σ, hρ, hσ, hrot, hBU, hPart ρ hI.hG_val (compLSF_RF_isRSF hI) hρ⟩

/-! ## 2. Exact cost decomposition of `bundleRunSeq` -/

/-- Exact decomposition of `(bundleRunSeq ... t).1.cost` into initial setup, cumulative lazy
component initializations, input batch lengths, bundle-batch lengths, output batch lengths, and
dynamic-spanner update costs. -/
lemma bundleRunSeq_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ) :
    let st₀ := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1
    let actB := st₀.activeBuckets
    ∀ t ≤ τ,
      (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cost =
        (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
          ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.activeComps.sum
            st₀.lazyInitCost) +
          ∑ s ∈ Finset.range t,
            ((D.U (s + 1)).length +
              ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps.sum
                fun C => (actB C).sum fun b =>
                  ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length) +
              (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).2.length +
              ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps.sum
                fun C => (actB C).sum fun b =>
                  ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost)) := by
  intro st₀ actB t ht
  obtain ⟨hBase, hStep, _⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  induction t with
  | zero =>
    change (initBundleTree oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) (ord 0) j).cost =
      (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
        ((largeComps k (D.G 0)).sum st₀.lazyInitCost) + 0
    rfl
  | succ s ih =>
    have hs_lt : s < τ := ht
    have hs_le : s ≤ τ := Nat.le_of_succ_le ht
    have hbs := hBase s hs_le
    have hss := hStep s hs_lt
    have hact_b : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.activeBuckets = actB :=
      hbs.2.2.2.2.1
    have hlazy : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.lazyInitCost =
        st₀.lazyInitCost :=
      hbs.2.2.2.2.2.1
    have hact_eq : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps =
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.activeComps ∪
          (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive :=
      hss.2.1.2.2.1
    have hsum_act :
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps.sum
          st₀.lazyInitCost =
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.activeComps.sum
          st₀.lazyInitCost +
        (bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive.sum
          st₀.lazyInitCost := by
      rw [hact_eq, Finset.sum_union hss.2.1.2.1]
    have hstep_cost : (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.cost =
        (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.cost +
          ((D.U (s + 1)).length +
            ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps.sum
              fun C => ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.activeBuckets C).sum
                fun b => ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length) +
            (bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).2.length +
            ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j (s + 1)).1.activeComps.sum
              fun C => ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.activeBuckets C).sum
                fun b => ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost) +
            ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).newlyActive.sum
              (bundleRunSeq oracle C_lsst L sparsify k M N D ord j s).1.lazyInitCost)) := rfl
    simp_rw [hact_b, hlazy] at hstep_cost
    rw [hstep_cost, ih hs_le, hsum_act, Finset.sum_range_succ]
    ac_rfl

/-! ## 3. Per-branch runtime bounds -/

private lemma bundleRunSeq_step_del_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord) (j r : ℕ) (hr : r < τ) :
    let st₀ := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1
    let info := bundleRunInfo oracle C_lsst L sparsify k M N D ord j r
    ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
      (info.U_B (C, b)).countP deleteTag) ≤ (D.U (r + 1)).length := by
  classical
  intro st₀ info
  obtain ⟨hBase, hStep, _⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨_, _, _, hdisj_bun⟩ := initBundleTree_buckets_sum_le oracle C_lsst L sparsify (M := M)
    (N := N) hk (D.ℓ 0) (ord 0) j
  obtain ⟨ρ, hρ_ord, hρ_step⟩ := hOrd
  obtain ⟨hG_step, hrot⟩ := hρ_step r hr
  have hbr := hBase r (Nat.le_of_lt hr)
  have hsr := hStep r hr
  set st := (bundleRunSeq oracle C_lsst L sparsify k M N D ord j r).1
  have hper_cb : ∀ C ∈ components (D.G 0), ∀ b ∈ st₀.activeBuckets C,
      (info.U_B (C, b)).countP deleteTag ≤
        ((st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))).card := by
    intro C hC b _
    have hC_st := (hbr.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
    have hC_step := hsr.2.2.2.2 C hC b
    have hReady : BundleStepReady st.cs (st.bun (C, b)) k (ord r) (ord (r + 1)) (D.U (r + 1)) :=
      bundleStepReady_of_stage hbr.2.2.2.2.2.2.2.1 hbr.2.2.2.2.2.2.2.2.1 hsr.1
        (ρ r) (ρ (r + 1)) (hρ_ord r (Nat.le_of_lt hr)) (hρ_ord (r + 1) hr) hG_step hrot hC_st.1
    have hG0_eq : st.cs.G₀ = D.G 0 := by
      rw [hbr.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hloc := bundleCompStep_local hReady C (hG0_eq.symm ▸ hC) hC_st.2.2.1
    have hUB_eq : info.U_B (C, b) =
        (bundleCompStep st.cs (st.bun (C, b)) k (ord r) (ord (r + 1)) (D.U (r + 1))).1 := by
      change (bundleCompStep st.cs (st.bun (C, b)) st.k (ord r) (ord (r + 1)) (D.U (r + 1))).1 = _
      rw [hbr.1]
    have hsub : ∀ op ∈ info.U_B (C, b), deleteTag op = true →
        ∃ e ∈ (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1)), op = .delete e := by
      intro op hop hdel
      rw [hUB_eq] at hop
      obtain ⟨e, he_bun, heq, he_del⟩ := hloc.2 op hop hdel
      exact ⟨e, Finset.mem_inter.mpr ⟨hC_st.2.1 he_bun, he_del⟩, heq⟩
    have hcnt := countP_deleteTag_le_card_of_delOrSplit hC_step.1 hC_step.2.2.1 hsub
    exact le_trans hcnt (Finset.card_le_card Finset.inter_subset_right)
  have hper_C : ∀ C ∈ components (D.G 0),
      ((st₀.activeBuckets C).sum fun b => (info.U_B (C, b)).countP deleteTag) ≤
        ((st₀.activeBuckets C).biUnion fun b =>
          (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))).card := by
    intro C hC
    have hdisj_b : Set.PairwiseDisjoint (↑(st₀.activeBuckets C) : Set ℤ)
        (fun b => (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))) := by
      intro b₁ _ b₂ _ hne
      exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
        (hdisj_bun C hC C hC b₁ b₂ (fun h => hne (Prod.mk.inj h).2))
    rw [Finset.card_biUnion hdisj_b]
    exact Finset.sum_le_sum fun b hb => hper_cb C hC b hb
  have hdisj_C : Set.PairwiseDisjoint (↑(components (D.G 0)) : Set (Finset ℕ))
      (fun C => (st₀.activeBuckets C).biUnion fun b =>
        (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))) := by
    intro C₁ hC₁ C₂ hC₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨b₁, _, he₁'⟩ := Finset.mem_biUnion.mp he₁
    obtain ⟨b₂, _, he₂'⟩ := Finset.mem_biUnion.mp he₂
    exact Finset.disjoint_left.mp
      (hdisj_bun C₁ hC₁ C₂ hC₂ b₁ b₂ (fun h => hne (Prod.mk.inj h).1))
      (Finset.mem_inter.mp he₁').1 (Finset.mem_inter.mp he₂').1
  calc ((components (D.G 0)).sum fun C => (st₀.activeBuckets C).sum fun b =>
          (info.U_B (C, b)).countP deleteTag)
      ≤ (components (D.G 0)).sum (fun C => ((st₀.activeBuckets C).biUnion fun b =>
          (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))).card) :=
        Finset.sum_le_sum hper_C
    _ = ((components (D.G 0)).biUnion fun C => (st₀.activeBuckets C).biUnion fun b =>
          (st₀.bun (C, b)).edges ∩ batchDeletes (D.U (r + 1))).card :=
        (Finset.card_biUnion hdisj_C).symm
    _ ≤ (batchDeletes (D.U (r + 1))).card :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ =>
          Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right)
    _ ≤ (D.U (r + 1)).length := batchDeletes_card_le _

private lemma bundleRunSeq_R_bounds
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord) (j : ℕ) :
    let run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    (∀ r < τ,
      ((components (D.G 0)).sum fun C =>
        (((run (r + 1)).1.cs.compSt C).R \ ((run r).1.cs.compSt C).R).card) =
        ((run (r + 1)).1.cs.RF.R \ (run r).1.cs.RF.R).card) ∧
    ((∑ r ∈ Finset.range τ, ((run (r + 1)).1.cs.RF.R \ (run r).1.cs.RF.R).card : ℕ) : ℝ) ≤
      112 * (q_τ : ℝ) * (Real.log (((min N (M + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
  intro run q_τ
  obtain ⟨hBase, hStep, _⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  set cs₀ := (run 0).1.cs
  have hcomp_sum : ∀ r < τ,
      ((components (D.G 0)).sum fun C =>
        (((run (r + 1)).1.cs.compSt C).R \ ((run r).1.cs.compSt C).R).card) =
        ((run (r + 1)).1.cs.RF.R \ (run r).1.cs.RF.R).card := by
    intro r hr
    have hI_r := (hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.2.1
    have hI_r1 := (hBase (r + 1) hr).2.2.2.2.2.2.2.1
    have hG₀_r : (run r).1.cs.G₀ = D.G 0 := by
      rw [(hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hcs1 : (run (r + 1)).1.cs = compLSFBatch (run r).1.cs (D.U (r + 1)) :=
      bundleRunSeq_cs oracle C_lsst L sparsify k M N D ord j r
    have hsp := compLSFBatch_step_props (D.U (r + 1)) hI_r (hStep r hr).1
    have hR_mono : ∀ C ∈ components (run r).1.cs.G₀,
        ((run r).1.cs.compSt C).R ⊆ ((run (r + 1)).1.cs.compSt C).R := by
      intro C hC
      rw [hcs1]
      exact (hsp.2.2.1 C hC).2.2.2.1
    have heq := compLSF_sum_R_sdiff_eq hI_r hI_r1 (by rw [hcs1, compLSFBatch_G₀]) hR_mono
    rwa [hG₀_r] at heq
  have htel : ∀ t ≤ τ,
      (∑ r ∈ Finset.range t, ((run (r + 1)).1.cs.RF.R \ (run r).1.cs.RF.R).card) =
        ((run t).1.cs.RF.R \ cs₀.RF.R).card := by
    intro t ht
    induction t with
    | zero => simp [cs₀]
    | succ s ih =>
      have hs_lt : s < τ := ht
      have hs_le : s ≤ τ := Nat.le_of_succ_le ht
      have hdiff_s := compLSF_R_diff_le_min oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j s hs_le
      have hsub1 : cs₀.RF.R ⊆ (run s).1.cs.RF.R := by
        rw [(hBase s hs_le).2.2.2.2.2.2.1]; exact hdiff_s.1
      have hsub2 : (run s).1.cs.RF.R ⊆ (run (s + 1)).1.cs.RF.R := by
        rw [bundleRunSeq_cs oracle C_lsst L sparsify k M N D ord j s]
        exact (compLSFBatch_decremental (hBase s hs_le).2.2.2.2.2.2.2.1 (hStep s hs_lt).1).2
      have h1 := Finset.card_sdiff_add_card_inter (run s).1.cs.RF.R cs₀.RF.R
      have h2 := Finset.card_sdiff_add_card_inter (run (s + 1)).1.cs.RF.R (run s).1.cs.RF.R
      have h3 := Finset.card_sdiff_add_card_inter (run (s + 1)).1.cs.RF.R cs₀.RF.R
      rw [Finset.inter_eq_right.mpr hsub1] at h1
      rw [Finset.inter_eq_right.mpr hsub2] at h2
      rw [Finset.inter_eq_right.mpr (Finset.Subset.trans hsub1 hsub2)] at h3
      rw [Finset.sum_range_succ, ih hs_le]
      omega
  have hdiff_τ := compLSF_R_diff_le_min oracle hLSST hk hG₀ hV₀ hℓ₀ hD hN hThresh j τ le_rfl
  have hR_le_min0 :
      ((∑ r ∈ Finset.range τ, ((run (r + 1)).1.cs.RF.R \ (run r).1.cs.RF.R).card : ℕ) : ℝ) ≤
        112 * (q_τ : ℝ) * (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
    rw [htel τ le_rfl, (hBase τ le_rfl).2.2.2.2.2.2.1]
    exact hdiff_τ.2.1
  have hmin_le : min (D.G 0).n ((D.G 0).m + 1) ≤ min N (M + 1) :=
    le_min (le_trans (min_le_left _ _) hN) (le_trans (min_le_right _ _) (Nat.succ_le_succ hM))
  have hlog_le : (Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2)) ^ 2 ≤
      (Real.log (((min N (M + 1) : ℕ) : ℝ) + 2)) ^ 2 := by
    have hnn : 0 ≤ Real.log (((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) + 2) :=
      (half_lt_log_add_two (min (D.G 0).n ((D.G 0).m + 1))).le.trans' (by norm_num)
    refine pow_le_pow_left₀ hnn (Real.log_le_log (by positivity) ?_) 2
    have hR : ((min (D.G 0).n ((D.G 0).m + 1) : ℕ) : ℝ) ≤ ((min N (M + 1) : ℕ) : ℝ) := by
      exact_mod_cast hmin_le
    linarith
  exact ⟨hcomp_sum, le_trans hR_le_min0 (mul_le_mul_of_nonneg_left hlog_le (by positivity))⟩

/-- Active-vertex form of the per-branch runtime bound for `bundleRunSeq`, using `min N (M + 1)`
so that `bundleCoreParams E` applies without a component bound on `N` (paper Lemma 5.17, pages
23–24). -/
theorem bundleRunSeq_cost_le_active
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound) :
    let n_eff := min N (M + 1)
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := bundleLambda P_b M
    let ucBound := 2 * bundleUCRatio n_eff * (q_τ : ℝ)
    ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j τ).1.cost : ℝ) ≤
      ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) +
      (q_τ : ℝ) + (B_bound : ℝ) * ucBound +
      bundleRecoursePerQ L P_b M n_eff B_bound * (q_τ : ℝ) +
      90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((k : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
  classical
  intro n_eff q_τ Λ ucBound
  set run := bundleRunSeq oracle C_lsst L sparsify k M N D ord j
  set st₀ := (run 0).1
  set actB := st₀.activeBuckets
  set splitB := bundleSplitBudget k M
  obtain ⟨hBase, hStep, hFlat⟩ := bundleRunSeq_stage_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j
  obtain ⟨_, hStep_full, hT82_cum⟩ := bundleRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj
  obtain ⟨hAct_card_sum, hm_sum, hn_2m, _⟩ := initBundleTree_buckets_sum_le oracle C_lsst L
    sparsify (M := M) (N := N) hk (D.ℓ 0) (ord 0) j
  have hRec1 := (bundleRunSeq_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp ord hOrd j hj B_bound hB_bound τ le_rfl).1
  obtain ⟨hR_comp_sum, hR_sum⟩ := bundleRunSeq_R_bounds
    oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh ord hOrd j
  have hInit_sum :
      (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((run τ).1.activeComps.sum st₀.lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) := by
    have hlazy_eq : st₀.lazyInitCost = fun C => (actB C).sum fun b =>
        (DynSpanner.init (normGraph (st₀.bun (C, b)).graph) L
          (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)).cost := rfl
    rw [hlazy_eq]
    push_cast
    have hsum := bundleInitBuckets_cost_sum_le (m₀ := M) (G₀ := D.G 0)
      (run τ).1.activeComps (hBase τ le_rfl).2.2.2.2.2.2.2.2.2.1.2 actB
      (fun C b => normGraph (st₀.bun (C, b)).graph)
      (fun C b => DynSpanner.init (normGraph (st₀.bun (C, b)).graph) L
        (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M))
      (le_trans hAct_card_sum hM) (le_trans hm_sum hM)
      (fun C _ b _ => hn_2m C b)
      (fun C hC b _ => ⟨(hT82_cum C hC b τ le_rfl).1, (hT82_cum C hC b τ le_rfl).2.1⟩)
    have hMR : ((D.G 0).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith [hsum, hMR]
  obtain ⟨hUB_single, hUB_total⟩ :=
    bundle_epoch_U_B_sum_le (G₀ := D.G 0) (N := n_eff) (B_bound := B_bound) (s₀ := 0) (Δ := τ)
      (D := D) actB hB_bound (fun r => (run r).1.cs)
      (fun r p => (bundleRunInfo oracle C_lsst L sparsify k M N D ord j r).U_B p)
      (fun r hr C hC b _ => (hStep r hr).2.2.2.2 C hC b |>.2.2.1)
      (fun r hr => by
        rw [Nat.zero_add]
        exact bundleRunSeq_step_del_le
          oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j r hr)
      (fun r hr C hC b _ => (hStep r hr).2.2.2.2 C hC b |>.2.2.2.1)
      hR_comp_sum
      (by
        have hIcc : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
        dsimp only
        rw [hIcc]
        exact hR_sum)
  have hIcc0 : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
  rw [hIcc0] at hUB_single hUB_total
  have hBun_sum :
      (∑ s ∈ Finset.range τ, ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
        (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ))) ≤
        (B_bound : ℝ) * ucBound := by
    have h1 :
        (∑ s ∈ Finset.range τ, ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
          (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ))) ≤
        ∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ) :=
      Finset.sum_le_sum fun s hs =>
        Finset.sum_le_sum_of_subset_of_nonneg
          (hBase (s + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hs))).2.2.2.2.2.2.2.2.2.1.2
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    have hcomm :
        (∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ)) =
        (components (D.G 0)).sum fun C => (actB C).sum fun b =>
          ∑ s ∈ Finset.range τ,
            (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
    exact le_trans (le_trans h1 (le_of_eq hcomm)) hUB_total
  have huc_nn : 0 ≤ ucBound :=
    mul_nonneg (mul_nonneg zero_le_two (bundleUCRatio_pos n_eff).le) (Nat.cast_nonneg _)
  have hDyn_sum :
      (∑ s ∈ Finset.range τ, ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
        (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost : ℝ))) ≤
        90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((k : ℝ) + 1) * Λ *
          (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
    exact bundle_epoch_dyn_cost_le hL sparsify hk (G₀ := D.G 0)
      actB (fun r => (run (r + 1)).1.activeComps)
      (fun C b => normGraph (st₀.bun (C, b)).graph)
      (fun C b => bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b)
      (fun r p => (bundleRunInfo oracle C_lsst L sparsify k M N D ord j r).U_B p)
      (fun r p => (bundleRunInfo oracle C_lsst L sparsify k M N D ord j r).stepOut p)
      ucBound ucBound huc_nn
      (le_trans hm_sum hM)
      (fun C _ b _ => hn_2m C b)
      (fun C hC b _ => by rw [normGraph_maxDeg]; exact (hFlat C hC b).2.2.2)
      hUB_single hUB_total
      (fun r hr => (hBase (r + 1) hr).2.2.2.2.2.2.2.2.2.1.2)
      (fun C hC b _ => by
        have hdyn0 := ((hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b
        dsimp only [normGraph_n]
        rw [← hdyn0.2.2.2.2.2]
        exact hdyn0.2.2.2.2.1)
      (fun C hC b _ => rfl)
      (fun r hr C hC b _ => by
        have hdyn_r := ((hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.2.2.2.2.2
        have hdyn_r1 := ((hBase (r + 1) hr).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.2.2.2.2.2
        have hsr := (hStep r hr).2.2.2.2 C hC b
        dsimp only [normGraph_n]
        rw [← hdyn_r, ← hdyn_r1]
        exact ⟨hsr.1, hsr.2.1⟩)
      (fun C hC b _ r hr => by
        have hdyn_r := ((hBase r (Nat.le_of_lt hr)).2.2.2.2.2.2.2.2.2.2.2 C hC).2 b |>.2.2.2.2.2
        have hs1 := (hStep_full (r + 1) (Nat.succ_pos r) hr).2.2.2.1 C hC b
        simp only [Nat.add_sub_cancel] at hs1
        have hget := bundleBatchList_getElem? oracle C_lsst L sparsify k M N τ D ord j C b hr
        dsimp only [DynSpanner.runBatchStepOut, normGraph_n]
        rw [hget]
        change (bundleRunInfo oracle C_lsst L sparsify k M N D ord j r).stepOut (C, b) =
          DynSpanner.update
            (DynSpanner.runBatchState (normGraph (st₀.bun (C, b)).graph)
              (phaseBase ((st₀.bun (C, b)).graph.n + splitB) L) (sparsify M)
              (bundleBatchList oracle C_lsst L sparsify k M N τ D ord j C b) r)
            ((bundleRunInfo oracle C_lsst L sparsify k M N D ord j r).U_B (C, b)) (sparsify M)
        rw [← hdyn_r]
        exact hs1.1)
      (fun C hC b _ => (hT82_cum C hC b τ le_rfl).2.2.2.2)
  have hCost_eq := bundleRunSeq_cost_eq oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh ord hOrd j τ le_rfl
  have hCostR : ((run τ).1.cost : ℝ) =
      (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((run τ).1.activeComps.sum st₀.lazyInitCost : ℕ) : ℝ) +
        (∑ s ∈ Finset.range τ, ((D.U (s + 1)).length : ℝ)) +
        (∑ s ∈ Finset.range τ, ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
          (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).U_B (C, b)).length : ℝ))) +
        (∑ s ∈ Finset.range τ, ((run (s + 1)).2.length : ℝ)) +
        (∑ s ∈ Finset.range τ, ((run (s + 1)).1.activeComps.sum fun C => (actB C).sum fun b =>
          (((bundleRunInfo oracle C_lsst L sparsify k M N D ord j s).stepOut (C, b)).cost : ℝ))) := by
    change ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j τ).1.cost : ℝ) = _
    rw [hCost_eq]
    push_cast
    simp only [Finset.sum_add_distrib]
    ring
  have hq_eq : ∑ s ∈ Finset.range τ, ((D.U (s + 1)).length : ℝ) = (q_τ : ℝ) := by
    rw [sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ]
    simp [q_τ]
  have hus_eq : ∑ s ∈ Finset.range τ, ((run (s + 1)).2.length : ℝ) =
      ((∑ s ∈ Finset.Icc 1 τ, (run s).2.length : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact sum_range_eq_sum_Icc_succ (fun s => ((run s).2.length : ℝ)) τ
  rw [hCostR, hq_eq, hus_eq]
  linarith [hInit_sum, hBun_sum, hRec1, hDyn_sum]

/-- Per-branch runtime bound for `bundleRunSeq` (paper Lemma 5.17, pages 23–24). -/
theorem bundleRunSeq_cost_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (ord : ℕ → ℕ → List End) (hOrd : OrderedUpTo D τ 2 ord)
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound : ∀ C ∈ components (D.G 0),
      ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j 0).1.activeBuckets C).card ≤ B_bound) :
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := bundleLambda P_b M
    let ucBound := 2 * bundleUCRatio N * (q_τ : ℝ)
    ((bundleRunSeq oracle C_lsst L sparsify k M N D ord j τ).1.cost : ℝ) ≤
      ((M : ℝ) + (N : ℝ) + 1) +
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) +
      (q_τ : ℝ) + (B_bound : ℝ) * ucBound +
      bundleRecoursePerQ L P_b M N B_bound * (q_τ : ℝ) +
      90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((k : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro q_τ Λ ucBound
  have h := bundleRunSeq_cost_le_active
    oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp
    ord hOrd j hj B_bound hB_bound
  dsimp only at h
  have hact : ((activeSubgraph (D.G 0)).n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (activeSubgraph_n_le (D.G 0)) hN
  have huc_mono := bundleUCRatio_mono (min_le_left N (M + 1))
  have huc_min_nn : 0 ≤ 2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ) :=
    mul_nonneg (mul_nonneg zero_le_two (bundleUCRatio_pos _).le) (Nat.cast_nonneg _)
  have huc_le : 2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ) ≤ ucBound :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hBuc_le : (B_bound : ℝ) * (2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ)) ≤
      (B_bound : ℝ) * ucBound :=
    mul_le_mul_of_nonneg_left huc_le (Nat.cast_nonneg _)
  have hrec : bundleRecoursePerQ L P_b M (min N (M + 1)) B_bound * (q_τ : ℝ) ≤
      bundleRecoursePerQ L P_b M N B_bound * (q_τ : ℝ) :=
    mul_le_mul_of_nonneg_right (bundleRecoursePerQ_mono_N L P_b M (min_le_left N (M + 1)) B_bound)
      (Nat.cast_nonneg _)
  have hK_s := P_b.hK_s; have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hγc_nn := P_b.hγ_c
  have hΛ_nn : 0 ≤ Λ := (bundleLambda_pos P_b M).le
  have hcoeff_nn : 0 ≤ 90 * (L : ℝ) * bundleNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
      ((k : ℝ) + 1) * Λ := by unfold bundleNRoot coreE_L; positivity
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + 2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog_le : Real.log ((M : ℝ) + 2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ) + 2) ≤
      Real.log ((M : ℝ) + ucBound + 2) :=
    Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) M]) (by linarith)
  have hBuc_nn : 0 ≤ (B_bound : ℝ) * ucBound :=
    mul_nonneg (Nat.cast_nonneg _) (le_trans huc_min_nn huc_le)
  have hprod : 20 * ((M : ℝ) + (B_bound : ℝ) * (2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ))) *
        Real.log ((M : ℝ) + 2 * bundleUCRatio (min N (M + 1)) * (q_τ : ℝ) + 2) ≤
      20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2) :=
    mul_le_mul (by linarith) hlog_le hlog_nn (by linarith [Nat.cast_nonneg (α := ℝ) M, hBuc_nn])
  have hdyn := mul_le_mul_of_nonneg_left hprod hcoeff_nn
  linarith [h, hact, hBuc_le, hrec, hdyn]

end

end MinCostFlow.SparseCore
