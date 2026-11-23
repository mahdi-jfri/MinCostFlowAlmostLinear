module

public import MinCostFlow.SparseCore.SparseCoreEpochRecourse

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recourse, batch encoding size, and cost-structure helpers for `sparseCoreTool`

Specializes `epoch_recourse_and_enc` to `treeRunSeq` (`treeRunSeq_recourse_and_enc`) and proves
global bucket-size bounds (`bucket_m_sum_le`, `all_buckets_sum_le`) and the step-cost
decomposition `treeRunSeq_cost_eq`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

lemma epoch_recourse_and_enc
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
    (j : ℕ) (B_bound : ℕ)
    (hB_bound :
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
      ∀ C ∈ components (D.G 0), (actB C).card ≤ B_bound)
    (s₀ Δ : ℕ) (hsΔ : s₀ + Δ ≤ τ)
    (st : ℕ → TreeCoreState L) (U_S : ℕ → List Update)
    (Hb : Finset ℕ → ℤ → MGraph)
    (hHb_bounds : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      (Hb C b).m ≤ M ∧ (Hb C b).n ≤ 2 * (Hb C b).m)
    (hst_step : ∀ r < Δ, st (r + 1) = (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).state)
    (hUS_step : ∀ r < Δ, U_S (r + 1) = (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S)
    (hcs_s : ∀ r ≤ Δ, (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs)
    (hts_s : ∀ r ≤ Δ, (st r).ts = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.ts)
    (hactB_s : ∀ r ≤ Δ, (st r).activeBuckets =
      (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.activeBuckets)
    (hStage_ep : ∀ r ≤ Δ,
      (st r).S_cur.IsValid ∧
      (st r).activeComps ⊆ components (D.G 0) ∧
      ∀ C ∈ components (D.G 0), ∀ b : ℤ,
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤
          ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
            (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b)
    (hStep_ep : ∀ r < Δ,
      let info := stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components (D.G 0), ∀ b : ℤ,
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H ∧
        (info.U_b (C, b)).length ≤ (info.U_C C).length) ∧
      info.newlyActive ⊆ components (D.G 0) \ largeComps k (D.G 0) ∧
      info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (st r).activeBuckets C |>.sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (st r).activeBuckets C |>.sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card)
    (hT82_ep : ∀ C ∈ components (D.G 0), ∀ b : ℤ,
      let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) *
        ((D.G 0).maxDeg + 1) + Nat.ceil (56 * (M : ℝ) / (k : ℝ))
      let nMax_b := (Hb C b).n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let nRoot_b := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length : ℝ)
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b) :
    let q_ep := ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), (D.U s).length
    ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) ≤
      coreRecoursePerQ L P_b M N (D.G 0).maxDeg B_bound * (q_ep : ℝ) ∧
    ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) ∧
    (q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0) := by
  intro q_ep
  have h := epoch_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD
    hM hN hThresh j B_bound hB_bound s₀ Δ hsΔ st U_S Hb hHb_bounds hst_step hUS_step hcs_s hts_s hactB_s
    hStage_ep hStep_ep hT82_ep
  exact ⟨le_trans h.1 (mul_le_mul_of_nonneg_right
    (coreRecoursePerQ_mono_n L P_b M (le_trans (min_le_left _ _) hN) (D.G 0).maxDeg B_bound)
    (Nat.cast_nonneg _)), h.2.1, h.2.2⟩

lemma treeRunSeq_recourse_and_enc_min
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
    ∀ t ≤ τ,
      let st := fun s => (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
      let U_S := fun s => (treeRunSeq oracle C_lsst L sparsify k M N D j s).2
      let q_t := ∑ s ∈ Finset.Icc 1 t, (D.U s).length
      ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) ≤
        coreRecoursePerQ L P_b M (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg B_bound *
          (q_t : ℝ) ∧
      ((∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
        20 * (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ)) *
          Real.log (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) + 2) ∧
      (q_t = 0 →
        ∑ s ∈ Finset.Icc 1 t, (U_S s).length = 0 ∧
        ∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) = 0) := by
  classical
  intro t ht st U_S q_t
  set G₀ := D.G 0
  set cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2
  have hHb : ∀ C ∈ components G₀, ∀ b : ℤ, _ := fun C hC b =>
    initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  obtain ⟨_, hStage_all, hStep_full, hT82_cum⟩ := treeRunSeq_inv oracle C_lsst L hL P_b sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  have hep := epoch_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D
    hG₀ hV₀ hℓ₀ hD hM hN hThresh j B_bound hB_bound 0 t (by omega)
    (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).1)
    (fun r => (treeRunSeq oracle C_lsst L sparsify k M N D j r).2)
    (fun C b => initBucketGraph (cs₀.compSt C) (D.ℓ 0) b)
    (fun C hC b => by
      have hspec := hHb C hC b
      have hm1 : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m ≤ (cs₀.compSt C).G.m :=
        hspec.2.2.2.2.2.2.2.1
      have hn1 : (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).n ≤
          2 * (initBucketGraph (cs₀.compSt C) (D.ℓ 0) b).m :=
        hspec.2.2.2.2.1
      have hmc : (cs₀.compSt C).G.m ≤ G₀.m := by rw [(hS₀C_spec C hC).1]; exact compGraph_m_le
      exact ⟨le_trans (le_trans hm1 hmc) hM, hn1⟩)
    (fun r _ => by rw [Nat.zero_add]; rfl)
    (fun r _ => by rw [Nat.zero_add]; rfl)
    (fun r _ => by rw [Nat.zero_add])
    (fun r _ => by rw [Nat.zero_add])
    (fun r _ => by rw [Nat.zero_add])
    (fun r hr => by
      have hS := hStage_all r (le_trans hr ht)
      exact ⟨hS.1, hS.2.2.2.2.1, fun C hC b =>
        ⟨(hS.2.2.2.2.2.2.2 C hC b).1, (hS.2.2.2.2.2.2.2 C hC b).2.1,
         (hS.2.2.2.2.2.2.2 C hC b).2.2.2.2.1⟩⟩)
    (fun r hr => by
      have hSt := hStep_full (r + 1) (Nat.succ_pos r) (le_trans (Nat.succ_le_of_lt hr) ht)
      simp only [Nat.add_sub_cancel] at hSt
      refine ⟨by rw [Nat.zero_add]; exact hSt.1,
        by rw [Nat.zero_add]; exact hSt.2.1,
        fun hn => by rw [Nat.zero_add] at hn ⊢; exact (hSt.2.2.1 hn).1,
        fun C hC b => ?_,
        by rw [Nat.zero_add]; exact hSt.2.2.2.2.2.1,
        by rw [Nat.zero_add]; exact hSt.2.2.2.2.2.2.1,
        by rw [Nat.zero_add]; exact hSt.2.2.2.2.2.2.2.1,
        ?_⟩
      · have hcb := hSt.2.2.2.1 C hC b
        have hbl := ((hStep r (lt_of_lt_of_le hr ht)).2.2.2 C hC).2.2.2.2 b |>.2.2.2.1
        rw [Nat.zero_add]
        exact ⟨hcb.2.1, hcb.2.2.2.1, hbl⟩
      · have hlen := hSt.2.2.2.2.2.2.2.2
        have hAB := (hBase r (le_trans (Nat.le_of_lt hr) ht)).2.2.2.2.2.1
        rw [Nat.zero_add, hAB]
        exact hlen)
    (fun C hC b => by
      have hT := hT82_cum C hC b t ht
      have hlen : ((bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).take t).flatten.length =
          ∑ r ∈ Finset.range t,
            ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1
              (D.U (0 + r + 1))).U_b (C, b)).length := by
        rw [bucketBatchList_take_flatten_length oracle C_lsst L sparsify k M N τ D j C b ht]
        exact Finset.sum_congr rfl fun r _ => by rw [Nat.zero_add]
      have hstep := fun r (hr : r ∈ Finset.range t) =>
        (runBatchStepOut_eq_stepOut oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D
          hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj C hC b
          (lt_of_lt_of_le (Finset.mem_range.mp hr) ht)).trans
          (congrArg (fun x => x.stepOut (C, b)) (by rw [Nat.zero_add] :
            stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1 (D.U (r + 1)) =
            stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j r).1 (D.U (0 + r + 1))))
      have h1 := hT.2.2.1
      have h2 := hT.2.2.2.1
      dsimp only at h1 h2
      rw [hlen, Nat.cast_sum] at h1 h2
      conv_lhs at h1 =>
        rw [Finset.sum_congr rfl fun r hr =>
          congrArg (fun x : StepOut L => (x.UH.length : ℝ)) (hstep r hr)]
      conv_lhs at h2 =>
        rw [Finset.sum_congr rfl fun r hr =>
          congrArg (fun x : StepOut L => (x.D.card : ℝ)) (hstep r hr)]
      exact ⟨h1, h2⟩)
  have hIcc : Finset.Icc (0 + 1) (0 + t) = Finset.Icc 1 t := by simp
  have h1 := hep.1
  have h2 := hep.2.1
  have h3 := hep.2.2
  rw [hIcc] at h1 h3
  exact ⟨h1, h2, h3⟩

lemma treeRunSeq_recourse_and_enc
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
    ∀ t ≤ τ,
      let st := fun s => (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
      let U_S := fun s => (treeRunSeq oracle C_lsst L sparsify k M N D j s).2
      let q_t := ∑ s ∈ Finset.Icc 1 t, (D.U s).length
      ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) ≤
        coreRecoursePerQ L P_b M N (D.G 0).maxDeg B_bound * (q_t : ℝ) ∧
      ((∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) : ℕ) : ℝ) ≤
        20 * (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ)) *
          Real.log (((st 0).S_cur.m : ℝ) + ((∑ s ∈ Finset.Icc 1 t, (U_S s).length : ℕ) : ℝ) + 2) ∧
      (q_t = 0 →
        ∑ s ∈ Finset.Icc 1 t, (U_S s).length = 0 ∧
        ∑ s ∈ Finset.Icc 1 t, (st (s - 1)).S_cur.batchEnc (U_S s) = 0) := by
  intro t ht st U_S q_t
  have h := treeRunSeq_recourse_and_enc_min oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D
    hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj B_bound hB_bound t ht
  exact ⟨le_trans h.1 (mul_le_mul_of_nonneg_right
    (coreRecoursePerQ_mono_n L P_b M (le_trans (min_le_left _ _) hN) (D.G 0).maxDeg B_bound)
    (Nat.cast_nonneg _)), h.2.1, h.2.2⟩

/-! ## 3. Global bucket-size bounds and step-cost decompositions -/

lemma bucket_m_sum_le
    {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S₀ : LSFState}
    (hI₀ : LSFInvWith thresh K_σ ℓ₀ S₀) (hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E) :
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen S₀.lsf ℓ₀ e)
    let actB := (initTildeState S₀).C.E.image origB
    actB.sum (fun b => (initBucketGraph S₀ ℓ₀ b).m) ≤ S₀.G.m :=
  (sum_initBucketGraph_le hI₀ hCov₀).2.1

lemma all_buckets_sum_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k : ℕ} (hk : 1 ≤ k) {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
      (fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e))
    (components G₀).sum (fun C => (actB C).card) ≤ G₀.m ∧
    (components G₀).sum (fun C => (actB C).sum fun b =>
      (initBucketGraph (cs₀.compSt C) ℓ₀ b).m) ≤ G₀.m ∧
    (components G₀).sum (fun C => (actB C).sum fun b =>
      (initBucketGraph (cs₀.compSt C) ℓ₀ b).n) ≤ 2 * G₀.m := by
  intro cs₀ actB
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hS₀C : ∀ C ∈ components G₀,
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    (initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC).2
  have hB_each : ∀ C ∈ components G₀,
      (actB C).card ≤ (compGraph G₀ C).m ∧
      (actB C).sum (fun b => (initBucketGraph (cs₀.compSt C) ℓ₀ b).m) ≤ (compGraph G₀ C).m ∧
      (actB C).sum (fun b => (initBucketGraph (cs₀.compSt C) ℓ₀ b).n) ≤ 2 * (compGraph G₀ C).m := by
    intro C hC
    have hsum := sum_initBucketGraph_le (hI₀.hCompLSF C hC).1 (hS₀C C hC).2
    have horig : actB C = (initTildeState (cs₀.compSt C)).C.E.image
        (fun e => bucketOf (coreLen (cs₀.compSt C).lsf ℓ₀ e)) :=
      Finset.image_congr (initCompLSF_origBucket_congr oracle hLSST hG₀ hV₀ hℓ₀ hk j hC)
    dsimp only at hsum
    rw [horig]
    rw [← (hS₀C C hC).1]
    exact hsum
  have hsum_m := components_sum_m G₀ hG₀
  refine ⟨?_, ?_, ?_⟩
  · calc (components G₀).sum (fun C => (actB C).card)
        ≤ (components G₀).sum (fun C => (compGraph G₀ C).m) :=
            Finset.sum_le_sum fun C hC => (hB_each C hC).1
      _ = G₀.m := hsum_m
  · calc (components G₀).sum (fun C => (actB C).sum fun b =>
            (initBucketGraph (cs₀.compSt C) ℓ₀ b).m)
        ≤ (components G₀).sum (fun C => (compGraph G₀ C).m) :=
            Finset.sum_le_sum fun C hC => (hB_each C hC).2.1
      _ = G₀.m := hsum_m
  · calc (components G₀).sum (fun C => (actB C).sum fun b =>
            (initBucketGraph (cs₀.compSt C) ℓ₀ b).n)
        ≤ (components G₀).sum (fun C => 2 * (compGraph G₀ C).m) :=
            Finset.sum_le_sum fun C hC => (hB_each C hC).2.2
      _ = 2 * (components G₀).sum (fun C => (compGraph G₀ C).m) := by rw [← Finset.mul_sum]
      _ = 2 * G₀.m := by rw [hsum_m]

lemma treeRunSeq_cost_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (j : ℕ) :
    let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
    let actB := fun C => (initTildeState (cs₀.compSt C)).C.E.image
      (fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e))
    ∀ t ≤ τ,
      (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cost =
        (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
          ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.activeComps.sum
            (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost) +
          ∑ s ∈ Finset.range t,
            ((D.U (s + 1)).length +
              ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
                ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                  (D.U (s + 1))).U_C C).length) +
              (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2.length +
              ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
                (actB C).sum fun b =>
                  ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                    (D.U (s + 1))).stepOut (C, b)).cost)) := by
  intro cs₀ actB t ht
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  induction t with
  | zero =>
    change (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).cost =
      (D.G 0).m + (activeSubgraph (D.G 0)).n + 1 +
        ((largeComps k (D.G 0)).sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost) + 0
    rfl
  | succ s ih =>
    have hs_lt : s < τ := ht
    have hs_le : s ≤ τ := Nat.le_of_succ_le ht
    have hbs := hBase s hs_le
    have hss := hStep s hs_lt
    have hact_b : (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeBuckets = actB :=
      hbs.2.2.2.2.2.1
    have hlazy : (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.lazyInitCost =
        (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost :=
      hbs.2.2.2.2.2.2.1.trans (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.2.1.symm
    have hact_eq : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps =
        (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps ∪
          (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).newlyActive :=
      hss.2.1.2.2.1
    have hsum_act :
        (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost =
        (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost +
        (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
          (D.U (s + 1))).newlyActive.sum
          (initTreeCore oracle C_lsst L sparsify k M N (D.G 0) (D.ℓ 0) j).lazyInitCost := by
      rw [hact_eq, Finset.sum_union hss.2.1.2.1]
    have hstep_cost : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.cost =
        (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.cost +
          ((D.U (s + 1)).length +
            ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
              ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                (D.U (s + 1))).U_C C).length) +
            (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).2.length +
            ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps.sum fun C =>
              ((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeBuckets C).sum fun b =>
                ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                  (D.U (s + 1))).stepOut (C, b)).cost) +
            ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
              (D.U (s + 1))).newlyActive.sum
              (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.lazyInitCost)) := rfl
    simp_rw [hact_b, hlazy] at hstep_cost
    rw [hstep_cost, ih hs_le, hsum_act, Finset.sum_range_succ]
    ac_rfl

end

end MinCostFlow.SparseCore
