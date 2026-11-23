module

public import MinCostFlow.SparseCore.SparseCoreEpochCost

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Runtime bound for `sparseCoreTool` (`treeRunSeq_cost_le_active`, `treeRunSeq_cost_le`)

Combines `initBuckets_cost_sum_le`, `epoch_U_C_sum_le_min`, `treeRunSeq_recourse_and_enc_min`,
and `epoch_dyn_cost_le_min` into per-branch runtime bounds for `treeRunSeq`, charging only
active non-isolated vertices `(activeSubgraph (D.G 0)).n` and using `min n₀ (m₀ + 1)` inside
`coreUCRatio` / `coreRecoursePerQ`, with the `n₀` versions as corollaries.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma epoch_dyn_cost_le
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
    (j B_bound : ℕ)
    (hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound)
    (s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L)
    (Hb : Finset ℕ → ℤ → MGraph)
    (Us_ep : Finset ℕ → ℤ → List (List Update))
    (hm_sum :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      (components (D.G 0)).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M)
    (hHb_2m : ∀ C ∈ components (D.G 0), ∀ b : ℤ, (Hb C b).n ≤ 2 * (Hb C b).m)
    (hHb_deg :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let ts₀ := fun C => initTildeState (cs₀.compSt C)
      ∀ C ∈ components (D.G 0), ∀ b : ℤ, (Hb C b).maxDeg ≤ (ts₀ C).C.maxDeg)
    (hact_sub : ∀ r ≤ Δ, (st r).activeComps ⊆ components (D.G 0))
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts)
    (hDyn_G_val0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ, ((st 0).dyn (C, b)).G.IsValid)
    (hDyn_G_m0 : ∀ C ∈ components (D.G 0), ∀ b : ℤ, ((st 0).dyn (C, b)).G.m = (Hb C b).m)
    (hStep_ep : ∀ r < Δ, ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let info := stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))
      ((st r).dyn (C, b)).G.BatchIsValid (info.U_b (C, b)) ∧
      ((st (r + 1)).dyn (C, b)).G = ((st r).dyn (C, b)).G.applyBatch (info.U_b (C, b)) ∧
      (info.U_b (C, b)).length ≤ (info.U_C C).length)
    (hRun_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      ∀ r ≤ Δ, ((st r).dyn (C, b)).G =
        (DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
          (sparsify M) (Us_ep C b) r).G)
    (hStepOut_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      ∀ r < Δ,
        (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b) =
          DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase ((Hb C b).n + splitB) L)
            (sparsify M) (Us_ep C b) r)
    (hT82_cost : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      let nMax_b := (Hb C b).n + splitB
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
            (Us_ep C b) r).G.batchEnc
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)) : ℝ)
      (∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchStepOut (L := L) (Hb C b) (phaseBase nMax_b L) (sparsify M)
          (Us_ep C b) r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let actB := fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    let Δ₀ := (D.G 0).maxDeg
    let dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda P_b M
    let uc_ep := 2 * coreUCRatio N Δ₀ * (q_ep : ℝ)
    let ucBound := 2 * coreUCRatio N Δ₀ * (q_τ : ℝ)
    (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
      (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).cost : ℝ))) ≤
      90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((dC : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro cs₀ ts₀ actB Δ₀ dC q_ep q_τ Λ uc_ep ucBound
  have h := epoch_dyn_cost_le_min oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hM hN hThresh j B_bound hB_bound s₀ Δ hsΔ st Hb Us_ep hm_sum hHb_2m hHb_deg hact_sub hcs_s hts_s
    hDyn_G_val0 hDyn_G_m0 hStep_ep hRun_ep hStepOut_ep hT82_cost
  have huc := coreUCRatio_mono (min_le_left N (M + 1)) Δ₀
  have huc_nn := coreUCRatio_pos (min N (M + 1)) Δ₀
  have hK_s := P_b.hK_s; have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hγc_nn := P_b.hγ_c
  have hΛ_nn : 0 ≤ Λ := le_trans zero_le_one (coreLambda_ge_one P_b M)
  have hcoeff_nn : 0 ≤ 90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
      ((dC : ℝ) + 1) * Λ := by unfold coreNRoot coreE_L; positivity
  have huc_ep_le : 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_ep : ℝ) ≤ uc_ep :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have huc_τ_le : 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) ≤ ucBound :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) :=
    Real.log_nonneg (by
      have : 0 ≤ 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog_le : Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      Real.log ((M : ℝ) + ucBound + 2) :=
    Real.log_le_log (by
      have : 0 ≤ 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) M]) (by linarith)
  have hprod : 20 * ((M : ℝ) + (B_bound : ℝ) * (2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_ep : ℝ))) *
        Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      20 * ((M : ℝ) + (B_bound : ℝ) * uc_ep) * Real.log ((M : ℝ) + ucBound + 2) := by
    refine mul_le_mul ?_ hlog_le hlog_nn (by
      have : 0 ≤ uc_ep := mul_nonneg (mul_nonneg zero_le_two (coreUCRatio_pos N Δ₀)) (Nat.cast_nonneg _)
      positivity)
    have := mul_le_mul_of_nonneg_left huc_ep_le (Nat.cast_nonneg (α := ℝ) B_bound)
    linarith
  exact le_trans h (mul_le_mul_of_nonneg_left hprod hcoeff_nn)

theorem treeRunSeq_cost_le_active
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
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let Δ₀ := (D.G 0).maxDeg
    let dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda P_b M
    let n_eff := min N (M + 1)
    let ucBound := 2 * coreUCRatio n_eff Δ₀ * (q_τ : ℝ)
    ((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cost : ℝ) ≤
      ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) +
      (q_τ : ℝ) + ucBound +
      coreRecoursePerQ L P_b M n_eff Δ₀ B_bound * (q_τ : ℝ) +
      90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((dC : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
  classical
  intro cs₀ ts₀ Δ₀ dC q_τ Λ n_eff ucBound
  let actB : Finset ℕ → Finset ℤ := fun C =>
    (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components (D.G 0),
      (cs₀.compSt C).G = compGraph (D.G 0) C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hCov₀ : ∀ C ∈ components (D.G 0),
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2
  have hHb : ∀ C ∈ components (D.G 0), ∀ b : ℤ, _ := fun C hC b =>
    initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, _, hT82_cum⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  obtain ⟨hAct_card_sum, hm_sum, _⟩ := all_buckets_sum_le oracle hLSST hk hG₀ hV₀ hℓ₀ j
  have hRec := treeRunSeq_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj B_bound hB_bound τ le_rfl
  have hmin_le : min (D.G 0).n ((D.G 0).m + 1) ≤ n_eff :=
    le_min (le_trans (min_le_left _ _) hN) (le_trans (min_le_right _ _) (Nat.succ_le_succ hM))
  have hRec1 : ((∑ s ∈ Finset.Icc 1 τ, (treeRunSeq oracle C_lsst L sparsify k M N D j s).2.length : ℕ) : ℝ) ≤
      coreRecoursePerQ L P_b M n_eff Δ₀ B_bound * (q_τ : ℝ) :=
    le_trans hRec.1 (mul_le_mul_of_nonneg_right
      (coreRecoursePerQ_mono_n L P_b M hmin_le Δ₀ B_bound) (Nat.cast_nonneg _))
  have hΛ_ge1 : 1 ≤ Λ := coreLambda_ge_one P_b M
  have hΛ_nn : 0 ≤ Λ := by linarith
  have hInit_sum :
      (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) ≤
        ((M : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
          ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
            2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) := by
    have hlazy0 : (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost =
        fun C => (actB C).sum fun b =>
          (DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
            (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
              (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
                Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L) (sparsify M)).cost :=
      (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.1
    rw [hlazy0]
    push_cast
    have hsum := initBuckets_cost_sum_le (m₀ := M)
      (treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps
      (hStage_all τ le_rfl).2.2.2.2.1 actB
      (fun C b => initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
      (fun C b => DynSpanner.init (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b) L
        (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
          (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
            Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L) (sparsify M))
      (le_trans hAct_card_sum hM) (le_trans hm_sum hM)
      (fun C hC b _ => (hHb C hC b).2.2.2.2.1)
      (fun C hC b _ => ⟨(hT82_cum C hC b τ le_rfl).1, (hT82_cum C hC b τ le_rfl).2.1⟩)
    have hMR : ((D.G 0).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith [hsum, hMR]
  have hUC_sum :
      (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
        fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).U_C C).length : ℝ)) ≤ ucBound := by
    have h1 :
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℝ))) ≤
        ∑ s ∈ Finset.range τ, (components (D.G 0)).sum fun C =>
          (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℝ) := by
      refine Finset.sum_le_sum fun s hs => Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun _ _ _ => Nat.cast_nonneg _)
      exact (hStage_all (s + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hs))).2.2.2.2.1
    have h2 := epoch_U_C_sum_le_min oracle C_lsst L sparsify hLSST k M N τ hk D
      hG₀ hV₀ hℓ₀ hD hN hThresh j 0 τ (by omega)
      (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).1)
      (fun r _ => by rw [Nat.zero_add]) (fun r _ => by rw [Nat.zero_add])
    dsimp only at h2
    have hIcc : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
    have huc_mono := coreUCRatio_mono hmin_le Δ₀
    calc _ ≤ (components (D.G 0)).sum (fun C => ∑ r ∈ Finset.range τ,
              (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                (D.U (r + 1))).U_C C).length : ℝ)) := by
            rw [← Finset.sum_comm]; exact h1
      _ = (components (D.G 0)).sum (fun C => ∑ r ∈ Finset.range τ,
              (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                (D.U (0 + r + 1))).U_C C).length : ℝ)) :=
            Finset.sum_congr rfl fun C _ => Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]
      _ ≤ 2 * coreUCRatio (min (D.G 0).n ((D.G 0).m + 1)) Δ₀ *
            ((∑ s ∈ Finset.Icc (0 + 1) (0 + τ), (D.U s).length : ℕ) : ℝ) := h2
      _ ≤ ucBound := by
            rw [hIcc]
            exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hDyn_sum :
      (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
        fun C => (actB C).sum fun b =>
          (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).stepOut (C, b)).cost : ℝ))) ≤
        90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
          ((dC : ℝ) + 1) * Λ *
          (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
    have hdyn := epoch_dyn_cost_le_min oracle C_lsst L hL P_b sparsify hLSST
      k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh j B_bound hB_bound
      0 τ (by omega)
      (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).1)
      (fun C b => initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
      (fun C b => bucketBatchList oracle C_lsst L sparsify k M N τ D j C b)
      (le_trans hm_sum hM)
      (fun C hC b => (hHb C hC b).2.2.2.2.1)
      (fun C hC b => (hHb C hC b).2.2.2.2.2.2.2.2)
      (fun r hr => (hStage_all r hr).2.2.2.2.1)
      (fun r _ => by rw [Nat.zero_add])
      (fun r _ => by rw [Nat.zero_add])
      (fun C hC b =>
        (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.2.2.2 b |>.1)
      (fun C hC b => by
        have he_dyn := (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.2.2.2 b |>.2.2.1
        have he_Hb := (hHb C hC b).2.2.1
        have hC0 : (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.ts C = ts₀ C := rfl
        change ((treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.dyn (C, b)).G.E.card =
          (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).E.card
        rw [he_dyn, hC0, he_Hb]
        congr 1
        refine Finset.filter_congr fun e he => ?_
        dsimp only
        rw [initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC e he])
      (fun r hr C hC b => by
        have hs_step := ((hStep r hr).2.2.2 C hC).2.2.2.2 b
        rw [Nat.zero_add]
        exact ⟨hs_step.1, hs_step.2.1, hs_step.2.2.2.1⟩)
      (fun C hC b r hr =>
        congrArg DynSpannerState.G
          ((hBase r hr).2.2.2.2.2.2.2.2.2.2.2.2 C hC |>.2.2.2.2 b |>.2.2.2))
      (fun C hC b r hr => by
        rw [Nat.zero_add]
        exact (runBatchStepOut_eq_stepOut oracle C_lsst L hL P_b sparsify hLSST
          k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj C hC b hr).symm)
      (fun C hC b => by
        have hT := (hT82_cum C hC b τ le_rfl).2.2.2.2
        dsimp only at hT ⊢
        have hUeq :
            (∑ r ∈ Finset.range τ,
              ((DynSpanner.runBatchState (L := L) (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
                  (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
                    (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
                      Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L)
                  (sparsify M) (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) r).G.batchEnc
                ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                  (D.U (r + 1))).U_b (C, b)) : ℝ)) =
            ∑ r ∈ Finset.range τ,
              ((DynSpanner.runBatchState (L := L) (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
                  (phaseBase ((initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n +
                    (Nat.floor (SparseCoreTool.updateThreshold k M N) * (Δ₀ + 1) +
                      Nat.ceil (56 * (M : ℝ) / (k : ℝ)))) L)
                  (sparsify M) (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) r).G.batchEnc
                ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
                  (D.U (0 + r + 1))).U_b (C, b)) : ℝ) :=
          Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]
        rw [← hUeq]
        exact hT)
    dsimp only at hdyn
    have hIcc : Finset.Icc (0 + 1) (0 + τ) = Finset.Icc 1 τ := by simp
    have hLhs :
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => (actB C).sum fun b =>
            (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
              (D.U (s + 1))).stepOut (C, b)).cost : ℝ))) =
        ∑ r ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (r + 1)).1.activeComps.sum
          fun C => (actB C).sum fun b =>
            (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
              (D.U (0 + r + 1))).stepOut (C, b)).cost : ℝ)) :=
      Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]
    rw [hIcc] at hdyn
    rw [hLhs]
    exact hdyn
  have hCost_eq := treeRunSeq_cost_eq oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hN hThresh j τ le_rfl
  have hCostR : ((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cost : ℝ) =
      (((D.G 0).m : ℝ) + ((activeSubgraph (D.G 0)).n : ℝ) + 1) +
        (((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost : ℕ) : ℝ) +
        (∑ s ∈ Finset.range τ, ((D.U (s + 1)).length : ℝ)) +
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_C C).length : ℝ)) +
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2.length : ℝ)) +
        (∑ s ∈ Finset.range τ, ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          fun C => (actB C).sum fun b =>
            (((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
              (D.U (s + 1))).stepOut (C, b)).cost : ℝ))) := by
    rw [hCost_eq]
    push_cast
    simp only [Finset.sum_add_distrib]
    ring
  have hq_eq : ∑ s ∈ Finset.range τ, ((D.U (s + 1)).length : ℝ) = (q_τ : ℝ) := by
    rw [sum_range_eq_sum_Icc_succ (fun s => ((D.U s).length : ℝ)) τ]
    simp [q_τ]
  have hus_eq : ∑ s ∈ Finset.range τ,
      ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2.length : ℝ) =
      ((∑ s ∈ Finset.Icc 1 τ, (treeRunSeq oracle C_lsst L sparsify k M N D j s).2.length : ℕ) : ℝ) := by
    rw [Nat.cast_sum]
    exact sum_range_eq_sum_Icc_succ
      (fun s => ((treeRunSeq oracle C_lsst L sparsify k M N D j s).2.length : ℝ)) τ
  rw [hCostR, hq_eq, hus_eq]
  linarith [hInit_sum, hUC_sum, hRec1, hDyn_sum]

theorem treeRunSeq_cost_le
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
    (j : ℕ) (hj : j < k) (B_bound : ℕ)
    (hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let Δ₀ := (D.G 0).maxDeg
    let dC := (components (D.G 0)).sup fun C => (ts₀ C).C.maxDeg
    let q_τ := ∑ s ∈ Finset.Icc 1 τ, (D.U s).length
    let Λ := coreLambda P_b M
    let ucBound := 2 * coreUCRatio N Δ₀ * (q_τ : ℝ)
    ((treeRunSeq oracle C_lsst L sparsify k M N D j τ).1.cost : ℝ) ≤
      ((M : ℝ) + (N : ℝ) + 1) +
      ((L : ℝ) + 1 + P_b.K_t * (2 + P_b.γ_ℓ ^ 2) * Λ + 3 + P_b.γ_ℓ +
        2 * P_b.K_s * P_b.γ_ℓ * Λ) * (M : ℝ) +
      (q_τ : ℝ) + ucBound +
      coreRecoursePerQ L P_b M N Δ₀ B_bound * (q_τ : ℝ) +
      90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
        ((dC : ℝ) + 1) * Λ *
        (20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2)) := by
  intro cs₀ ts₀ Δ₀ dC q_τ Λ ucBound
  have h := treeRunSeq_cost_le_active oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hM hN hThresh hSp j hj B_bound hB_bound
  have hact : ((activeSubgraph (D.G 0)).n : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (activeSubgraph_n_le (D.G 0)) hN
  have huc := coreUCRatio_mono (min_le_left N (M + 1)) Δ₀
  have huc_nn := coreUCRatio_pos (min N (M + 1)) Δ₀
  have huc_le : 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) ≤ ucBound :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hrec := mul_le_mul_of_nonneg_right
    (coreRecoursePerQ_mono_n L P_b M (min_le_left N (M + 1)) Δ₀ B_bound) (Nat.cast_nonneg (α := ℝ) q_τ)
  have hK_s := P_b.hK_s; have hK_t := P_b.hK_t
  have hγℓ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hγc_nn := P_b.hγ_c
  have hΛ_nn : 0 ≤ Λ := le_trans zero_le_one (coreLambda_ge_one P_b M)
  have hcoeff_nn : 0 ≤ 90 * (L : ℝ) * coreNRoot L M * (P_b.K_t + P_b.K_s + 1) * coreE_L L P_b *
      ((dC : ℝ) + 1) * Λ := by unfold coreNRoot coreE_L; positivity
  have hlog_nn : 0 ≤ Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) :=
    Real.log_nonneg (by
      have : 0 ≤ 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) M])
  have hlog_le : Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      Real.log ((M : ℝ) + ucBound + 2) :=
    Real.log_le_log (by
      have : 0 ≤ 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) := by positivity
      linarith [Nat.cast_nonneg (α := ℝ) M]) (by linarith)
  have hprod : 20 * ((M : ℝ) + (B_bound : ℝ) * (2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ))) *
        Real.log ((M : ℝ) + 2 * coreUCRatio (min N (M + 1)) Δ₀ * (q_τ : ℝ) + 2) ≤
      20 * ((M : ℝ) + (B_bound : ℝ) * ucBound) * Real.log ((M : ℝ) + ucBound + 2) := by
    refine mul_le_mul ?_ hlog_le hlog_nn (by
      have : 0 ≤ ucBound := mul_nonneg (mul_nonneg zero_le_two (coreUCRatio_pos N Δ₀)) (Nat.cast_nonneg _)
      positivity)
    have := mul_le_mul_of_nonneg_left huc_le (Nat.cast_nonneg (α := ℝ) B_bound)
    linarith
  have hdyn := mul_le_mul_of_nonneg_left hprod hcoeff_nn
  linarith [h, hact, huc_le, hrec, hdyn]

end

end MinCostFlow.SparseCore
