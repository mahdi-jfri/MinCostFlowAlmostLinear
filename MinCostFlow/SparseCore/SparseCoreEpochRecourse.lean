module

public import MinCostFlow.SparseCore.SparseCoreRecourseBase

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Per-epoch recourse and encoding-size bound (`epoch_recourse_and_enc`)

Proves `epoch_recourse_and_enc`: cumulative recourse `∑ |U_S|` and Lemma 2.1 batch encoding size
`∑ S.batchEnc U_S` over an arbitrary valid suffix epoch `s₀ .. s₀ + Δ`, together with exact
vanishing when `q_ep = 0`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

private lemma mem_batchDeletes_of_sdiff_applyBatch (H : MGraph) (U : List Update) {e : ℕ}
    (he : e ∈ H.E) (he' : e ∉ (H.applyBatch U).E) : e ∈ batchDeletes U := by
  rw [mem_batchDeletes_iff]
  induction U generalizing H with
  | nil => exact absurd he he'
  | cons u rest ih =>
    by_cases hdel : u = .delete e
    · exact ⟨u, List.mem_cons_self, hdel⟩
    · have he1 : e ∈ (H.applyUpdate u).E := by
        cases u with
        | delete e' =>
          have hne : e ≠ e' := fun h => hdel (congrArg Update.delete h.symm)
          simpa [MGraph.applyUpdate, hne] using he
        | insert _ _ _ => simp [MGraph.applyUpdate, he]
        | split _ _ _ _ => exact he
      obtain ⟨u', hu', heq⟩ := ih (H.applyUpdate u) he1 he'
      exact ⟨u', List.mem_cons_of_mem _ hu', heq⟩

private lemma empty_batches_of_sum_zero {D : DynamicInstance} {t : ℕ}
    (h : ∑ s ∈ Finset.Icc 1 t, (D.U s).length = 0) :
    ∀ s, 1 ≤ s → s ≤ t → D.U s = [] := by
  intro s hs1 hst
  have hzero := (Finset.sum_eq_zero_iff.mp h) s (Finset.mem_Icc.mpr ⟨hs1, hst⟩)
  exact List.eq_nil_of_length_eq_zero hzero

private lemma sum_Icc_shift_eq_sum_range (s₀ Δ : ℕ) (f : ℕ → ℕ) :
    ∑ s ∈ Finset.Icc (s₀ + 1) (s₀ + Δ), f s = ∑ r ∈ Finset.range Δ, f (s₀ + r + 1) := by
  induction Δ with
  | zero => simp
  | succ d ih =>
    have hs1 : s₀ + (d + 1) = s₀ + d + 1 := by omega
    rw [hs1, Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Cumulative recourse `∑ |U_S|` and Lemma 2.1 encoding size over an arbitrary valid suffix epoch
`s₀ .. s₀ + Δ` (with `s₀ + Δ ≤ τ`) for any state sequence `st : ℕ → TreeCoreState L` starting at
`(post s₀)` and stepping via `stepTreeCoreAux`. -/
lemma epoch_recourse_and_enc_min
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
      coreRecoursePerQ L P_b M (min (D.G 0).n ((D.G 0).m + 1)) (D.G 0).maxDeg B_bound * (q_ep : ℝ) ∧
    ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) ∧
    (q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0) := by
  classical
  intro q_ep
  set G₀ := D.G 0
  set n_eff := min G₀.n (G₀.m + 1)
  set cs₀ := initCompLSF oracle C_lsst G₀ (D.ℓ 0) k j
  set ts₀ : Finset ℕ → TildeState := fun C => initTildeState (cs₀.compSt C)
  set origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e)
  set actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
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
  have hT₀ : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (cs₀.compSt C) (ts₀ C) :=
    fun C hC => initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
  obtain ⟨hBase, hStep, _⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hsum_step_eq : (∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) =
      ∑ r ∈ Finset.range Δ, (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S.length := by
    rw [← sum_range_nat_eq_sum_Icc_succ (fun r => (U_S r).length) Δ]
    refine Finset.sum_congr rfl fun r hr =>
      congrArg List.length (hUS_step r (Finset.mem_range.mp hr))
  have hq_nat : q_ep = ∑ r ∈ Finset.range Δ, (D.U (s₀ + r + 1)).length :=
    sum_Icc_shift_eq_sum_range s₀ Δ (fun s => (D.U s).length)
  have hq_eq : ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) = (q_ep : ℝ) := by
    rw [hq_nat, Nat.cast_sum]
  have hactB_base : ∀ r (hr : r ≤ Δ), (st r).activeBuckets = actB := fun r hr => by
    rw [hactB_s r hr]; exact (hBase (s₀ + r) (by omega)).2.2.2.2.2.1
  have hcs_base : ∀ r (hr : r ≤ Δ), (st r).cs = (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs :=
    hcs_s
  have hsum_UC :
      ((components G₀).sum fun C => ∑ r ∈ Finset.range Δ,
        ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ) ≤
        2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ) := by
    have hstep_sum : ∀ r ∈ Finset.range Δ,
        ((components G₀).sum fun C =>
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ≤
          2 * ((D.U (s₀ + r + 1)).length : ℝ) * coreUCRatio n_eff G₀.maxDeg := fun r hr => by
      have hr_lt_Δ : r < Δ := Finset.mem_range.mp hr
      have hs_lt : s₀ + r < τ := by omega
      have hst_s := hStep (s₀ + r) hs_lt
      have hUC_eq : ∀ C,
          (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C =
          (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1
            (D.U (s₀ + r + 1))).U_C C := fun C => by
        dsimp only [stepTreeCoreAux, stepTreeCoreAuxWith]
        rw [hcs_base r (Nat.le_of_lt hr_lt_Δ), hts_s r (Nat.le_of_lt hr_lt_Δ)]
      calc (components G₀).sum (fun C =>
              (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))
          ≤ (components G₀).sum (fun C =>
              (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.G
                ((treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.compSt C).G
                (D.U (s₀ + r + 1)) : ℝ) * coreUCRatio n_eff G₀.maxDeg) := by
              refine Finset.sum_le_sum fun C hC => ?_
              rw [hUC_eq C]
              exact treeRunSeq_U_C_len_le_min oracle C_lsst L sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD j (s₀ + r) (by omega) C hC
        _ = ((components G₀).sum fun C =>
              (projCompBatchWeight (treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.G
                ((treeRunSeq oracle C_lsst L sparsify k M N D j (s₀ + r)).1.cs.compSt C).G
                (D.U (s₀ + r + 1)) : ℝ)) * coreUCRatio n_eff G₀.maxDeg := by
              rw [← Finset.sum_mul]
        _ ≤ (2 * ((D.U (s₀ + r + 1)).length : ℝ)) * coreUCRatio n_eff G₀.maxDeg := by
              refine mul_le_mul_of_nonneg_right ?_ (coreUCRatio_pos n_eff G₀.maxDeg)
              exact_mod_cast hst_s.2.2.1
    rw [Finset.sum_comm]
    calc (∑ r ∈ Finset.range Δ, (components G₀).sum fun C =>
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ))
        ≤ ∑ r ∈ Finset.range Δ, (2 * ((D.U (s₀ + r + 1)).length : ℝ) * coreUCRatio n_eff G₀.maxDeg) :=
            Finset.sum_le_sum hstep_sum
      _ = 2 * coreUCRatio n_eff G₀.maxDeg * ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) := by
            rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
      _ = 2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ) := by rw [hq_eq]
  have hSplitB : Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ)) ≤ coreSplitMax M :=
    splitB_le_coreSplitMax_at hk (le_trans (Finset.card_pos.mpr hV₀) hN) hM
  have hUH_D_cb : ∀ C ∈ components G₀, ∀ b ∈ actB C,
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        coreBucketRecUH L P_b M *
          (∑ r ∈ Finset.range Δ,
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) ∧
      (∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        coreBucketRecD L P_b M *
          (∑ r ∈ Finset.range Δ,
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) := by
    intro C hC b _
    set splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    have htb := hT82_ep C hC b
    have hnMax_le : (Hb C b).n + splitB ≤ coreNMax M := by
      have hbm := (hHb_bounds C hC b).1
      have hbn := (hHb_bounds C hC b).2
      dsimp only [splitB] at hbm hbn ⊢
      unfold coreNMax
      omega
    have hnr_le : ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤ coreNRoot L M := by
      unfold coreNRoot
      refine Real.rpow_le_rpow (Nat.cast_nonneg _) ?_ (by positivity)
      exact_mod_cast (max_le_max_right 1 hnMax_le)
    have hbase_ge1 : (1 : ℝ) ≤ (((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2 := by linarith
    have hbase_nn : 0 ≤ 1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) := by
      linarith [Real.log_nonneg hbase_ge1]
    have hlog_le : Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2) ≤
        Real.log ((coreNMax M : ℝ) + (M : ℝ) + 2) := by
      refine Real.log_le_log (by linarith) ?_
      have h1 : (((Hb C b).n + splitB : ℕ) : ℝ) ≤ (coreNMax M : ℝ) := by exact_mod_cast hnMax_le
      have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hHb_bounds C hC b).1
      linarith
    have hlam_le : (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
        coreLambdaS P_b M := by
      unfold coreLambdaS
      exact pow_le_pow_left₀ hbase_nn (by linarith [hlog_le]) _
    have hbatch_le : (∑ r ∈ Finset.range Δ,
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length : ℝ)) ≤
        ∑ r ∈ Finset.range Δ,
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ) :=
      Finset.sum_le_sum fun r hr => by
        exact_mod_cast ((hStep_ep r (Finset.mem_range.mp hr)).2.2.2.1 C hC b).2.2
    have hK_nn := P_b.hK_s
    have hγ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
    have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hlam_nn := coreLambdaS_pos P_b M
    have hnr_nn : 0 ≤ ((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by positivity
    have hnr2_nn : 0 ≤ coreNRoot L M := by unfold coreNRoot; positivity
    have hbatch_nn : 0 ≤ ∑ r ∈ Finset.range Δ,
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_b (C, b)).length : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    have hUH_nn : 0 ≤ coreBucketRecUH L P_b M := (coreBucketRec_pos L P_b M).1
    have hD_nn : 0 ≤ coreBucketRecD L P_b M := (coreBucketRec_pos L P_b M).2.1
    have hcoeff_uh :
        2 + 12 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
          coreBucketRecUH L P_b M := by
      unfold coreBucketRecUH
      have h1 : 12 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ ≤
          12 * (L : ℝ) * coreNRoot L M * P_b.K_s * P_b.γ_ℓ := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnr_le (by positivity)) hK_nn) hγ_nn
      have h2 := mul_le_mul h1 hlam_le (pow_nonneg hbase_nn _) (by positivity)
      linarith
    have hcoeff_d :
        6 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
            (1 + Real.log ((((Hb C b).n + splitB : ℕ) : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
          coreBucketRecD L P_b M := by
      unfold coreBucketRecD
      have h3g : (0 : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1 := by positivity
      have h1 : 6 * (L : ℝ) * (((max ((Hb C b).n + splitB) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))) * P_b.K_s * P_b.γ_ℓ *
            (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) ≤
          6 * (L : ℝ) * coreNRoot L M * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hnr_le (by positivity)) hK_nn) hγ_nn) h3g
      exact mul_le_mul h1 hlam_le (pow_nonneg hbase_nn _) (by positivity)
    exact ⟨le_trans htb.1 (le_trans (mul_le_mul_of_nonneg_right hcoeff_uh hbatch_nn)
        (mul_le_mul_of_nonneg_left hbatch_le hUH_nn)),
      le_trans htb.2 (le_trans (mul_le_mul_of_nonneg_right hcoeff_d hbatch_nn)
        (mul_le_mul_of_nonneg_left hbatch_le hD_nn))⟩
  have hsum_buckets : ∀ (g : StepOut L → ℝ) (B_per : ℝ), 0 ≤ B_per →
      (∀ o : StepOut L, 0 ≤ g o) →
      (∀ C ∈ components G₀, ∀ b ∈ actB C,
        ∑ r ∈ Finset.range Δ, g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)) ≤
          B_per * ∑ r ∈ Finset.range Δ,
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) →
      (∑ r ∈ Finset.range Δ, (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b))) ≤
        (B_bound : ℝ) * B_per * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) := by
    intro g B_per hB_nn hg_nn hg_cb
    have hAct_sub : ∀ r ∈ Finset.range Δ, (st (r + 1)).activeComps ⊆ components G₀ := fun r hr =>
      (hStage_ep (r + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hr))).2.1
    have hstep_sub :
        (∑ r ∈ Finset.range Δ, (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b))) ≤
        ∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
          g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b))) :=
      Finset.sum_le_sum fun r hr =>
        Finset.sum_le_sum_of_subset_of_nonneg (hAct_sub r hr) (fun _ _ _ => Finset.sum_nonneg fun _ _ => hg_nn _)
    have hcomm :
        (∑ r ∈ Finset.range Δ, ((components G₀).sum fun C => (actB C).sum fun b =>
          g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)))) =
        (components G₀).sum fun C => (actB C).sum fun b =>
          ∑ r ∈ Finset.range Δ,
            g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun C _ => Finset.sum_comm
    have hC_sum :
        ((components G₀).sum fun C => (actB C).sum fun b =>
          ∑ r ∈ Finset.range Δ,
            g ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b))) ≤
        (B_bound : ℝ) * B_per *
          ((components G₀).sum fun C => ∑ r ∈ Finset.range Δ,
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun C hC => ?_
      have hb_le := Finset.sum_le_sum (s := actB C) fun b hb => hg_cb C hC b hb
      have hcard : (actB C).sum (fun _ => B_per *
          ∑ r ∈ Finset.range Δ, (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) =
          ((actB C).card : ℝ) * (B_per *
            ∑ r ∈ Finset.range Δ, (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      have hB_r : ((actB C).card : ℝ) ≤ (B_bound : ℝ) := by exact_mod_cast hB_bound C hC
      have hUC_nn : 0 ≤ ∑ r ∈ Finset.range Δ,
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_C C).length : ℝ) :=
        Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      calc (actB C).sum _ ≤ ((actB C).card : ℝ) * (B_per * ∑ r ∈ Finset.range Δ, _) := by
            rw [← hcard]; exact hb_le
        _ ≤ (B_bound : ℝ) * (B_per * ∑ r ∈ Finset.range Δ, _) :=
            mul_le_mul_of_nonneg_right hB_r (mul_nonneg hB_nn hUC_nn)
        _ = (B_bound : ℝ) * B_per * ∑ r ∈ Finset.range Δ, _ := by ring
    have hBper_nn : 0 ≤ (B_bound : ℝ) * B_per := mul_nonneg (Nat.cast_nonneg _) hB_nn
    exact le_trans hstep_sub (le_trans (le_of_eq hcomm)
      (le_trans hC_sum (mul_le_mul_of_nonneg_left hsum_UC hBper_nn)))
  have hUH_total :
      (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ))) ≤
        (B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) :=
    hsum_buckets (fun o => (o.UH.length : ℝ)) (coreBucketRecUH L P_b M)
      (coreBucketRec_pos L P_b M).1 (fun o => Nat.cast_nonneg _) fun C hC b hb => (hUH_D_cb C hC b hb).1
  have hD_total :
      (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
        (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ))) ≤
        (B_bound : ℝ) * coreBucketRecD L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) :=
    hsum_buckets (fun o => (o.D.card : ℝ)) (coreBucketRecD L P_b M)
      (coreBucketRec_pos L P_b M).2.1 (fun o => Nat.cast_nonneg _) fun C hC b hb => (hUH_D_cb C hC b hb).2
  have hNew_total :
      (∑ r ∈ Finset.range Δ,
        ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum fun C =>
          (actB C).sum fun b => ((st r).dyn (C, b)).H.E.card : ℝ)) ≤
        22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (q_ep : ℝ) := by
    have hK_nn := P_b.hK_s
    have hγ_nn : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
    have hlam_nn := coreLambdaS_pos P_b M
    have hterm : ∀ r ∈ Finset.range Δ,
        ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum fun C =>
          (actB C).sum fun b => (((st r).dyn (C, b)).H.E.card : ℝ)) ≤
        22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
          ((D.U (s₀ + r + 1)).length : ℝ) := by
      intro r hr
      have hr_lt : r < Δ := Finset.mem_range.mp hr
      have hSt := hStep_ep r hr_lt
      have hSa := hStage_ep r (Nat.le_of_lt hr_lt)
      have hC_sum : ∀ C ∈ (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive,
          ((actB C).sum fun b => (((st r).dyn (C, b)).H.E.card : ℝ)) ≤
            11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M := by
        intro C hCN
        have hC : C ∈ components G₀ := (Finset.mem_sdiff.mp (hSt.2.2.2.2.1 hCN)).1
        have hb_le : ∀ b ∈ actB C,
            (((st r).dyn (C, b)).H.E.card : ℝ) ≤
              11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M := by
          intro b hb
          have hsp := hSa.2.2 C hC b
          have hgn11 : ((st r).dyn (C, b)).G.n ≤ 11 := hSt.2.2.2.2.2.2.1 C hCN b
          have hM_pos : 1 ≤ M := by
            rcases Finset.mem_image.mp hb with ⟨e₀, he₀, _⟩
            have he₀_G : e₀ ∈ (cs₀.compSt C).G.E :=
              (Finset.mem_sdiff.mp ((hT₀ C hC).hCE_sub he₀)).1
            rw [(hS₀C_spec C hC).1] at he₀_G
            have hm₀_pos : 1 ≤ G₀.m := Finset.card_pos.mpr ⟨e₀, Finset.filter_subset _ _ he₀_G⟩
            omega
          have hgn_core : ((st r).dyn (C, b)).G.n ≤ coreNMax M := by
            unfold coreNMax coreSplitMax
            have h1 : 1 * (2 * 1 + 1) ≤ M * (2 * M + 1) := Nat.mul_le_mul hM_pos (by omega)
            omega
          have harg_ge1 : (1 : ℝ) ≤ (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 := by linarith
          have harg_le : (((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2 ≤
              (coreNMax M : ℝ) + (M : ℝ) + 2 := by
            have h1 : (((st r).dyn (C, b)).G.n : ℝ) ≤ (coreNMax M : ℝ) := by exact_mod_cast hgn_core
            have h2 : ((Hb C b).m : ℝ) ≤ (M : ℝ) := by exact_mod_cast (hHb_bounds C hC b).1
            linarith
          have hlog_nn : 0 ≤ 1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2) := by
            linarith [Real.log_nonneg harg_ge1]
          have hlam_le : (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ≤
              coreLambdaS P_b M := by
            unfold coreLambdaS
            exact pow_le_pow_left₀ hlog_nn
              (add_le_add le_rfl (Real.log_le_log (by linarith) harg_le)) _
          have hgn_r : (((st r).dyn (C, b)).G.n : ℝ) ≤ 11 := by exact_mod_cast hgn11
          have hpre_le : ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ ≤
              11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ := by
            calc ((L : ℝ) + 1) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ
                ≤ ((L : ℝ) + 1) * P_b.K_s * 11 * P_b.γ_ℓ := by
                    refine mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left hgn_r (by positivity)) hγ_nn
              _ = 11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ := by ring
          have hm_e : (((st r).dyn (C, b)).H.E.card : ℝ) = (((st r).dyn (C, b)).H.m : ℝ) := rfl
          rw [hm_e]
          exact le_trans hsp.2.1 (mul_le_mul hpre_le hlam_le (pow_nonneg hlog_nn _) (by positivity))
        calc (actB C).sum (fun b => (((st r).dyn (C, b)).H.E.card : ℝ))
            ≤ (actB C).sum (fun _ => 11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) :=
                Finset.sum_le_sum hb_le
          _ = ((actB C).card : ℝ) * (11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) := by
                simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (B_bound : ℝ) * (11 * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast hB_bound C hC) (by positivity)
          _ = 11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M := by ring
      have hN_card : (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.card : ℝ)) ≤
          2 * ((D.U (s₀ + r + 1)).length : ℝ) := by exact_mod_cast hSt.2.2.2.2.2.1
      calc ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum _)
          ≤ (stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum
              (fun _ => 11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) :=
              Finset.sum_le_sum hC_sum
        _ = ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.card : ℝ) *
              (11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) := by
              simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * ((D.U (s₀ + r + 1)).length : ℝ)) *
              (11 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M) :=
              mul_le_mul_of_nonneg_right hN_card (by positivity)
        _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
              ((D.U (s₀ + r + 1)).length : ℝ) := by ring
    calc ∑ r ∈ Finset.range Δ, _
        ≤ ∑ r ∈ Finset.range Δ,
            (22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
              ((D.U (s₀ + r + 1)).length : ℝ)) := Finset.sum_le_sum hterm
      _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M *
            ∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ) := by rw [← Finset.mul_sum]
      _ = 22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (q_ep : ℝ) := by
            rw [hq_eq]
  have hrec : ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) ≤
      coreRecoursePerQ L P_b M n_eff G₀.maxDeg B_bound * (q_ep : ℝ) := by
    rw [hsum_step_eq, Nat.cast_sum]
    have hR_sum : (∑ r ∈ Finset.range Δ,
        (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)) ≤
        112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
      have hterm_R : ∀ r ∈ Finset.range Δ,
          (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) ≤
            112 * ((D.U (s₀ + r + 1)).length : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
        intro r hr
        have hr_lt : r < Δ := Finset.mem_range.mp hr
        have hbr := hBase (s₀ + r) (by omega)
        have hsr := hStep (s₀ + r) (by omega)
        have hI_r : CompLSFInv C_lsst (D.ℓ 0) (st r).cs := hcs_base r (Nat.le_of_lt hr_lt) ▸ hbr.2.2.2.2.2.2.2.2.1
        have hBV_r : (st r).cs.G.BatchIsValid (D.U (s₀ + r + 1)) := hcs_base r (Nat.le_of_lt hr_lt) ▸ hsr.1
        have hcs1_eq : (st (r + 1)).cs = compLSFBatch (st r).cs (D.U (s₀ + r + 1)) := by
          rw [hst_step r hr_lt]; rfl
        have hsub_R : (st r).cs.RF.R ⊆ (st (r + 1)).cs.RF.R := by
          rw [hcs1_eq]; exact (compLSFBatch_decremental hI_r hBV_r).2
        have hcard_eq := Finset.card_sdiff_add_card_inter (st (r + 1)).cs.RF.R (st r).cs.RF.R
        rw [Finset.inter_eq_right.mpr hsub_R] at hcard_eq
        have hR_le := compLSF_R_sum_le_min hI_r hBV_r
        rw [← hcs1_eq] at hR_le
        have hG0_r : (st r).cs.G₀ = G₀ := by
          rw [hcs_base r (Nat.le_of_lt hr_lt), hbr.2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
        rw [hG0_r] at hR_le
        have hdiff_R : (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) =
            ((st (r + 1)).cs.RF.R.card : ℝ) - ((st r).cs.RF.R.card : ℝ) := by
          have : (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) + ((st r).cs.RF.R.card : ℝ) =
              ((st (r + 1)).cs.RF.R.card : ℝ) := by exact_mod_cast hcard_eq
          linarith
        rw [hdiff_R]
        have hpush2 : ((2 * (D.U (s₀ + r + 1)).length : ℕ) : ℝ) = 2 * ((D.U (s₀ + r + 1)).length : ℝ) := by
          push_cast; rfl
        rw [hpush2] at hR_le
        linarith
      calc ∑ r ∈ Finset.range Δ, (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)
          ≤ ∑ r ∈ Finset.range Δ,
              (112 * ((D.U (s₀ + r + 1)).length : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) :=
              Finset.sum_le_sum hterm_R
        _ = 112 * (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) *
              (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by
              rw [← Finset.sum_mul, ← Finset.mul_sum]
        _ = 112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2 := by rw [hq_eq]
    have hD_tot_step : ∀ r ∈ Finset.range Δ,
        ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).D_total.card : ℝ) ≤
          ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) +
          coreE82Len L P_b *
            ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
              (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) := by
      intro r hr
      have hr_lt : r < Δ := Finset.mem_range.mp hr
      have hSt := hStep_ep r hr_lt
      have hSa1 := hStage_ep (r + 1) (Nat.succ_le_of_lt hr_lt)
      have hAB_r : (st r).activeBuckets = actB := hactB_base r (Nat.le_of_lt hr_lt)
      set info := stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))
      have hU_card : (info.D_total.card : ℝ) ≤ (info.D_spanner.card : ℝ) + (info.D_leftS.card : ℝ) := by
        exact_mod_cast Finset.card_union_le info.D_spanner info.D_leftS
      have hDs_le : (info.D_spanner.card : ℝ) ≤
          (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b => ((info.stepOut (C, b)).D.card : ℝ) := by
        have hbi : info.D_spanner.card ≤
            (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).D.card := by
          change ((info.state.activeComps.biUnion fun C => ((st r).activeBuckets C).biUnion fun b =>
            (info.stepOut (C, b)).D).card) ≤ _
          rw [hAB_r, ← hst_step r hr_lt]
          exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        exact_mod_cast hbi
      let A : Finset ℕ → ℤ → Finset ℕ := fun C b =>
        (((st r).dyn (C, b)).H.E ∩ (info.stepOut (C, b)).state.G.E) \ (info.stepOut (C, b)).state.H.E
      have hDl_cb : ∀ C ∈ (st (r + 1)).activeComps, ∀ b ∈ actB C,
          (((A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) ≤
            coreE82Len L P_b * ((info.stepOut (C, b)).UH.length : ℝ) := by
        intro C hCA b _
        have hC : C ∈ components G₀ := hSa1.2.1 hCA
        have hCb := hSt.2.2.2.1 C hC b
        have hEmb := hSa1.2.2 C hC b
        have hA_sub : A C b ⊆ batchDeletes (info.stepOut (C, b)).UH := by
          intro e he
          rcases Finset.mem_sdiff.mp he with ⟨he1, heNot⟩
          have heHprev : e ∈ ((st r).dyn (C, b)).H.E := (Finset.mem_inter.mp he1).1
          rw [hCb.1, ← hCb.2.1] at heNot
          exact mem_batchDeletes_of_sdiff_applyBatch _ _ heHprev heNot
        have hA_card : (A C b).card ≤ (info.stepOut (C, b)).UH.length :=
          le_trans (Finset.card_le_card hA_sub) (batchDeletes_card_le _)
        have hWalk_le : ∀ e ∈ A C b,
            ((walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) ≤ coreE82Len L P_b := by
          intro e he
          have heG : e ∈ ((st (r + 1)).dyn (C, b)).G.E := by
            rw [← hCb.1]; exact (Finset.mem_inter.mp (Finset.mem_sdiff.mp he).1).2
          have hlen1 : (walkEdges (piTotal (info.stepOut (C, b)).state e)).card ≤
              (piTotal ((st (r + 1)).dyn (C, b)) e).length := by
            rw [hCb.1]
            simpa [walkEdges] using
              ((piTotal ((st (r + 1)).dyn (C, b)) e).map Prod.fst).toFinset_card_le
          have hlen2 : (piTotal ((st (r + 1)).dyn (C, b)) e).length ≤
              Embedding.length (piTotal ((st (r + 1)).dyn (C, b))) ((st (r + 1)).dyn (C, b)).G := by
            unfold Embedding.length
            exact Finset.le_sup (f := fun x => (piTotal ((st (r + 1)).dyn (C, b)) x).length) heG
          have hlen3 : (Embedding.length (piTotal ((st (r + 1)).dyn (C, b)))
              ((st (r + 1)).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b := by
            unfold coreE82Len; exact hEmb.2.2
          exact le_trans (by exact_mod_cast le_trans hlen1 hlen2) hlen3
        have hbi : (((A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) ≤
            ∑ e ∈ A C b, ((walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
        calc (((A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ)
            ≤ ∑ e ∈ A C b, ((walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) := hbi
          _ ≤ ∑ _ ∈ A C b, coreE82Len L P_b := Finset.sum_le_sum hWalk_le
          _ = ((A C b).card : ℝ) * coreE82Len L P_b := by simp [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ((info.stepOut (C, b)).UH.length : ℝ) * coreE82Len L P_b :=
              mul_le_mul_of_nonneg_right (by exact_mod_cast hA_card)
                (coreBucketRec_pos L P_b M).2.2
          _ = coreE82Len L P_b * ((info.stepOut (C, b)).UH.length : ℝ) := mul_comm _ _
      have hDl_le : (info.D_leftS.card : ℝ) ≤ coreE82Len L P_b *
          ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b => ((info.stepOut (C, b)).UH.length : ℝ)) := by
        have hbi0 : info.D_leftS.card ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
            ((A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)).card := by
          change ((info.state.activeComps.biUnion fun C => ((st r).activeBuckets C).biUnion fun b =>
            (A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e))).card ≤ _
          rw [hAB_r, ← hst_step r hr_lt]
          exact le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
        calc (info.D_leftS.card : ℝ)
            ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                (((A C b).biUnion fun e => walkEdges (piTotal (info.stepOut (C, b)).state e)).card : ℝ) := by
                exact_mod_cast hbi0
          _ ≤ (st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                coreE82Len L P_b * ((info.stepOut (C, b)).UH.length : ℝ) :=
              Finset.sum_le_sum fun C hCA => Finset.sum_le_sum fun b hb => hDl_cb C hCA b hb
          _ = coreE82Len L P_b * ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                ((info.stepOut (C, b)).UH.length : ℝ)) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun C _ => (Finset.mul_sum _ _ _).symm
      linarith
    have hD_tot_sum : (∑ r ∈ Finset.range Δ, ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).D_total.card : ℝ)) ≤
        (B_bound : ℝ) * coreBucketRecD L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) +
        coreE82Len L P_b *
          ((B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ))) := by
      have hs := Finset.sum_le_sum hD_tot_step
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
      exact le_trans hs (add_le_add hD_total
        (mul_le_mul_of_nonneg_left hUH_total (coreBucketRec_pos L P_b M).2.2))
    have hstep_b : ∑ r ∈ Finset.range Δ, ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S.length : ℝ) ≤
        (∑ r ∈ Finset.range Δ, ((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
          (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ))) +
        (∑ r ∈ Finset.range Δ,
          ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum fun C =>
            (actB C).sum fun b => ((st r).dyn (C, b)).H.E.card : ℝ)) +
        7 * (∑ r ∈ Finset.range Δ, ((D.U (s₀ + r + 1)).length : ℝ)) +
        2 * (∑ r ∈ Finset.range Δ, (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ)) +
        2 * (∑ r ∈ Finset.range Δ, ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).D_total.card : ℝ)) := by
      calc ∑ r ∈ Finset.range Δ, ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S.length : ℝ)
          ≤ ∑ r ∈ Finset.range Δ,
              (((st (r + 1)).activeComps.sum fun C => (actB C).sum fun b =>
                (((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) +
              ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).newlyActive.sum fun C =>
                (actB C).sum fun b => ((st r).dyn (C, b)).H.E.card : ℝ) +
              7 * ((D.U (s₀ + r + 1)).length : ℝ) +
              2 * (((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card : ℝ) +
              2 * ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).D_total.card : ℝ)) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have h1 := (hStep_ep r (Finset.mem_range.mp hr)).2.2.2.2.2.2.2
            rw [hactB_base r (Nat.le_of_lt (Finset.mem_range.mp hr))] at h1
            exact_mod_cast h1
        _ = _ := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    have hcomb_rec :
        (B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) +
          2 * ((B_bound : ℝ) * coreBucketRecD L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) +
            coreE82Len L P_b *
              ((B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)))) ≤
        (B_bound : ℝ) * ((3 + 2 * coreE82Len L P_b) * coreBucketRecUH L P_b M +
          2 * coreBucketRecD L P_b M) * (2 * coreUCRatio n_eff G₀.maxDeg) * (q_ep : ℝ) := by
      have hUH_nn := (coreBucketRec_pos L P_b M).1
      have huc := coreUCRatio_pos n_eff G₀.maxDeg
      have hterm_nn : 0 ≤ (B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hUH_nn) (mul_nonneg (mul_nonneg zero_le_two huc) (Nat.cast_nonneg _))
      nlinarith
    calc ∑ r ∈ Finset.range Δ, ((stepTreeCoreAux sparsify (st r) (D.U (s₀ + r + 1))).U_S.length : ℝ)
        ≤ _ := hstep_b
      _ ≤ (B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) +
            22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (q_ep : ℝ) +
            7 * (q_ep : ℝ) + 2 * (112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) +
            2 * ((B_bound : ℝ) * coreBucketRecD L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)) +
              coreE82Len L P_b *
                ((B_bound : ℝ) * coreBucketRecUH L P_b M * (2 * coreUCRatio n_eff G₀.maxDeg * (q_ep : ℝ)))) := by
          rw [hq_eq]
          gcongr
      _ ≤ (B_bound : ℝ) * ((3 + 2 * coreE82Len L P_b) * coreBucketRecUH L P_b M +
            2 * coreBucketRecD L P_b M) * (2 * coreUCRatio n_eff G₀.maxDeg) * (q_ep : ℝ) +
            22 * (B_bound : ℝ) * ((L : ℝ) + 1) * P_b.K_s * P_b.γ_ℓ * coreLambdaS P_b M * (q_ep : ℝ) +
            7 * (q_ep : ℝ) + 2 * (112 * (q_ep : ℝ) * (Real.log ((n_eff : ℝ) + 2)) ^ 2) := by linarith [hcomb_rec]
      _ = coreRecoursePerQ L P_b M n_eff G₀.maxDeg B_bound * (q_ep : ℝ) := by
          unfold coreRecoursePerQ; ring
  have hEnc : ((∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) : ℕ) : ℝ) ≤
      20 * (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ)) *
        Real.log (((st 0).S_cur.m : ℝ) + ((∑ r ∈ Finset.Icc 1 Δ, (U_S r).length : ℕ) : ℝ) + 2) := by
    let U' : ℕ → List Update := fun r => if r = 0 then [] else U_S r
    have hval0 : (st 0).S_cur.IsValid := (hStage_ep 0 (Nat.zero_le Δ)).1
    have hval : ∀ r, 1 ≤ r → r ≤ Δ →
        (st (r - 1)).S_cur.BatchIsValid (U' r) ∧ (st r).S_cur = (st (r - 1)).S_cur.applyBatch (U' r) := by
      intro r hr1 hrΔ
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hn' := hStep_ep m (by omega)
      simp only at hn' ⊢
      have hU' : U' (m + 1) = (stepTreeCoreAux sparsify (st m) (D.U (s₀ + m + 1))).U_S := by
        simp only [U', Nat.succ_ne_zero, ↓reduceIte]
        exact hUS_step m (by omega)
      rw [hU']
      exact ⟨hn'.1, hn'.2.1⟩
    have hL21 := MinCostFlow.Chain.lemma_2_1 (G := fun r => (st r).S_cur) (U := U') (τ := Δ) hval0 hval
    have hsum1 : ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U' r) =
        ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      simp [U', hne0]
    have hsum2 : ∑ r ∈ Finset.Icc 1 Δ, (U' r).length = ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length := by
      refine Finset.sum_congr rfl fun r hr => ?_
      have hne0 : r ≠ 0 := by have := (Finset.mem_Icc.mp hr).1; omega
      simp [U', hne0]
    rwa [hsum1, hsum2] at hL21
  have hZero : q_ep = 0 →
      ∑ r ∈ Finset.Icc 1 Δ, (U_S r).length = 0 ∧
      ∑ r ∈ Finset.Icc 1 Δ, (st (r - 1)).S_cur.batchEnc (U_S r) = 0 := by
    intro hq0
    rw [hq_nat] at hq0
    have hUS_nil : ∀ r, 1 ≤ r → r ≤ Δ → U_S r = [] := by
      intro r hr1 hrΔ
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
      have hm_lt : m < Δ := by omega
      have hU0 : (D.U (s₀ + m + 1)).length = 0 :=
        Finset.sum_eq_zero_iff.mp hq0 m (Finset.mem_range.mpr hm_lt)
      have hnil := (hStep_ep m hm_lt).2.2.1 (List.eq_nil_of_length_eq_zero hU0)
      exact (hUS_step m hm_lt).trans hnil
    refine ⟨Finset.sum_eq_zero fun r hr => ?_, Finset.sum_eq_zero fun r hr => ?_⟩
    · rw [hUS_nil r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]; rfl
    · rw [hUS_nil r (Finset.mem_Icc.mp hr).1 (Finset.mem_Icc.mp hr).2]; rfl
  exact ⟨hrec, hEnc, hZero⟩


end

end MinCostFlow.SparseCore
