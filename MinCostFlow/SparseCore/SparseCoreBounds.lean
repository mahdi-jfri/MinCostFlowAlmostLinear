module

public import MinCostFlow.SparseCore.SparseCoreStepBounds

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Trajectory invariants for `sparseCoreTool` (`treeRunSeq_invWith`, `treeRunSeq_inv`)

Invokes `DynSpanner.theorem_8_2` per `(C, b)` bucket and proves the full inductive `S_cur`
invariant `treeRunSeq_invWith` / `treeRunSeq_inv` via `stepTreeCoreAux_stage_stepWith` and
`stepTreeCoreAux_US_lenWith`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner

@[expose] public section

/-- Parameterized trajectory invariant (`reinsertD = true` re-inserts `D_total`,
`reinsertD = false` keeps `buildUS` behavior) combining `treeRunSeq_tilde_inv`,
`DynSpanner.theorem_8_2`, `DynSpanner.sparsity_H`, and `buildUSReinsert_spec` across `t = 0..τ`. -/
lemma treeRunSeq_invWith (reinsertD : Bool)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (j : ℕ) (hj : j < k) :
    let G₀ := D.G 0
    let ℓ₀ := D.ℓ 0
    let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    (∀ C ∈ components G₀, C ∉ largeComps k G₀ → (ts₀ C).C.V.card ≤ 11) ∧
    (∀ t ≤ τ,
      let st := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
      st.S_cur.IsValid ∧
      st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur ∧
      st.activeComps ⊆ components G₀ ∧
      largeComps k G₀ ⊆ st.activeComps ∧
      (st.activeComps \ largeComps k G₀).card ≤ 2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
        let nMax_b := Hb₀.n + splitB
        let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
        (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
        Embedding.IsEmbedding (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
        (Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        Embedding.vcong (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            (Hb₀.maxDeg : ℝ))) ∧
    (∀ t, 1 ≤ t → t ≤ τ →
      let stPrev := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (t - 1)).1
      let stCur := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
      let info := stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U t)
      stPrev.S_cur.BatchIsValid info.U_S ∧
      stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
      (D.U t = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify M) ∧
        (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
        (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
        (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
        (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
        (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
          eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG))) ∧
      ((reinsertD = false → NoBatchReinsert stPrev.cs.G (D.U t) → NoBatchReinsert stPrev.S_cur info.U_S) ∧
        (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
          (reinsertD = true → e ∉ info.D_total) ∧ ∀ u ∈ D.U t, ¬ u.Inserts e)) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U t).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, (stPrev.dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
        (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
        7 * (D.U t).length +
        2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        2 * (if reinsertD then info.D_total.card else 0)) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ, ∀ t ≤ τ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
      let nMax_b := Hb₀.n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let initB := DynSpanner.init Hb₀ L (phaseBase nMax_b L) (sparsify M)
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      let res_b : ℕ → StepOut L := fun s =>
        DynSpanner.runBatchStepOut (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s
      let batchTot_b : ℝ := ((Us_b.take t).flatten.length : ℝ)
      let encTot_b : ℝ := ∑ s ∈ Finset.range t,
        ((DynSpanner.runBatchState (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s).G.batchEnc
          ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
            (D.U (s + 1))).U_b (C, b)) : ℝ)
      ((initB.state.H.m : ℝ) ≤ P_b.K_s * (Hb₀.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log ((Hb₀.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s) ∧
      ((initB.cost : ℝ) ≤ P_b.K_t * (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_t +
          (Hb₀.n : ℝ) + (Hb₀.m : ℝ) + (initB.state.H.m : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) ∧
      (∑ s ∈ Finset.range t, ((res_b s).UH.length : ℝ) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).D.card : ℝ) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) *
          Λ_s_b * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).cost : ℝ) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b * ((Hb₀.maxDeg : ℝ) + 1) *
          Λ_b * encTot_b)) := by
  classical
  intro G₀ ℓ₀ cs₀ ts₀ origB actB splitB
  have _ := hj
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hI₀ : CompLSFInv C_lsst ℓ₀ cs₀ := compLSFInv_init oracle hLSST hG₀ hV₀ hℓ₀ hk j
  have hcs₀_G₀ : cs₀.G₀ = G₀ := rfl
  have hS₀C_spec : ∀ C ∈ components G₀,
      (cs₀.compSt C).G₀ = compGraph G₀ C ∧
      (cs₀.compSt C).G = compGraph G₀ C ∧
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) =
        (cs₀.compSt C).RF.F.E := fun C hC =>
    initCompLSF_compSt_basic oracle hLSST hG₀ hℓ₀ hk j hC
  have hCov₀ : ∀ C ∈ components G₀,
      (cs₀.compSt C).W_init.biUnion (inducedEdges (cs₀.compSt C).RF.F) = (cs₀.compSt C).RF.F.E :=
    fun C hC => (hS₀C_spec C hC).2.2
  have hS₀_G : ∀ C ∈ components G₀, (cs₀.compSt C).G = compGraph G₀ C :=
    fun C hC => (hS₀C_spec C hC).2.1
  have hT₀ : ∀ C ∈ components G₀, TildeInv (cs₀.compSt C) (cs₀.compSt C) (ts₀ C) :=
    fun C hC => initTildeState_inv (hI₀.hCompLSF C hC).1 (hCov₀ C hC)
  have hHb : ∀ C ∈ components G₀, ∀ b : ℤ, _ := fun C hC b =>
    initBucketGraph_spec (hI₀.hCompLSF C hC).1 (hCov₀ C hC) b
  have hSmall : ∀ C ∈ components G₀, C ∉ largeComps k G₀ → (ts₀ C).C.V.card ≤ 11 :=
    fun C hC hNL => smallComp_tildeV_le oracle hLSST hG₀ hℓ₀ hk j hC hNL
  obtain ⟨hBase, hStep, hFlat⟩ := treeRunSeq_tilde_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD hN hThresh j
  have hT82 : ∀ C ∈ components G₀, ∀ b : ℤ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      let nMax_b := Hb₀.n + splitB
      let q_b := phaseBase nMax_b L
      let initOut := DynSpanner.init Hb₀ L q_b (sparsify M)
      let st_b : ℕ → DynSpannerState L := fun t =>
        DynSpanner.runBatchState (L := L) Hb₀ q_b (sparsify M) Us_b t
      let res_b : ℕ → StepOut L := fun t =>
        DynSpanner.runBatchStepOut (L := L) Hb₀ q_b (sparsify M) Us_b t
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTotal := fun t => ((Us_b.take t).flatten.length : ℝ)
      let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us_b[t']? with
        | some U => ((st_b t').G.batchEnc U : ℝ)
        | none => 0
      ((initOut.state.H.m : ℝ) ≤ P_b.K_s * (Hb₀.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log ((Hb₀.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s) ∧
      ((initOut.cost : ℝ) ≤ P_b.K_t * (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ ^ 2) *
          (1 + Real.log (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_t +
          (Hb₀.n : ℝ) + (Hb₀.m : ℝ) + (initOut.state.H.m : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) ∧
      (∀ t ≤ τ,
        (st_b t).G.IsSubgraph (st_b t).H ∧
        ((st_b t).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st_b t).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st_b t).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((st_b t).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
        Embedding.IsEmbedding (piTotal (st_b t)) (st_b t).G (st_b t).H ∧
        (Embedding.length (piTotal (st_b t)) (st_b t).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        Embedding.vcong (piTotal (st_b t)) (st_b t).G (st_b t).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            (Hb₀.maxDeg : ℝ)) ∧
      (∀ t < τ, ∀ U, Us_b[t]? = some U →
        res_b t = DynSpanner.update (DynSpanner.runState (L := L) Hb₀ q_b (sparsify M) Us_b.flatten
          (batchPrefixLen Us_b t)) U (sparsify M) ∧
        (res_b t).state = st_b (t + 1) ∧
        (st_b t).H.BatchIsValid (res_b t).UH ∧
        (st_b t).H.applyBatch (res_b t).UH = (st_b (t + 1)).H ∧
        (res_b t).D ⊆ (st_b (t + 1)).H.E ∧
        (∀ eG ∈ (st_b (t + 1)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (st_b (t + 1)) eG) → eH ∉ (res_b t).D →
          eH ∈ walkEdges (piTotal (st_b t) eG))) ∧
      (∀ t ≤ τ,
        (∑ t' ∈ Finset.range t, ((res_b t').UH.length : ℝ) ≤
          (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((res_b t').D.card : ℝ) ≤
          6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
            batchTotal t) ∧
        (∑ t' ∈ Finset.range t, ((res_b t').cost : ℝ) ≤
          90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b * ((Hb₀.maxDeg : ℝ) + 1) *
            Λ_b * encTotal t)) := by
    intro C hC b
    obtain ⟨hBV_b, hds_b, hsc_b⟩ := hFlat C hC b
    have hGm_b : (initBucketGraph (cs₀.compSt C) ℓ₀ b).m ≤ M :=
      le_trans (le_trans (hHb C hC b).2.2.2.2.2.2.2.1 (by rw [hS₀_G C hC]; exact compGraph_m_le)) hM
    have hlen_Us : (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).length = τ := by
      simp [bucketBatchList]
    have hthm := DynSpanner.theorem_8_2 (hHb C hC b).1 hL hGm_b hSp hBV_b hds_b hsc_b
    rcases hthm with ⟨hSp0, hCost0, hStage, hStep82, hCum⟩
    have hq1 : 1 ≤ phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L :=
      le_trans (by omega) (two_le_phaseBase _ L)
    have hSpars := DynSpanner.sparsity_H (hHb C hC b).1 hL hq1 hGm_b hSp hBV_b hds_b
    have hTrace := DynSpanner.batchTrace_spec (hHb C hC b).1 hL hq1 hGm_b hSp hBV_b hds_b
    refine ⟨hSp0, hCost0, ?_, ?_, ?_⟩
    · intro t ht
      have hs := hStage t (le_trans ht hlen_Us.symm.le)
      have hbp_le : batchPrefixLen (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) t ≤
          (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b).flatten.length := by
        set Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
        have hsp : Us_b = Us_b.take t ++ Us_b.drop t := (List.take_append_drop t Us_b).symm
        change (Us_b.take t).flatten.length ≤ Us_b.flatten.length
        conv_rhs => rw [hsp, List.flatten_append, List.length_append]
        exact Nat.le_add_right _ _
      have htr := (hTrace.1 t (le_trans ht hlen_Us.symm.le))
      have hsp_t := hSpars.2 (batchPrefixLen _ t) hbp_le
      dsimp only at hsp_t
      rw [← htr.1, ← htr.2.1] at hsp_t
      exact ⟨hs.2.1, hsp_t, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    · intro t ht U hget
      exact hStep82 t (lt_of_lt_of_le ht hlen_Us.symm.le) U hget
    · intro t ht
      have hc := hCum t (le_trans ht hlen_Us.symm.le)
      exact ⟨hc.1, hc.2.2.1, hc.2.2.2⟩
  have hStepB : ∀ s, ∀ hs_lt : s < τ,
      let stPrev := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j s).1
      let stCur := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1
      let info := stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))
      ∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify M) ∧
        (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
        (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
        (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
        (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
        (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
          eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG)) := by
    intro s hs_lt
    dsimp only
    intro C hC b
    obtain ⟨hm₀, _, _, _, _, _, _, _, _, _, _, _, hC_s⟩ := hBase s (Nat.le_of_lt hs_lt)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC_s1⟩ := hBase (s + 1) hs_lt
    obtain ⟨hm₀_s, _, _, _, _, hAB_eq_s, _, hcs_eq_s, hact_eq_s, hts_eq_s, hdyn_eq_s⟩ :=
      treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j s
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hdyn_eq_s1⟩ :=
      treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j (s + 1)
    set stPrev := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j s).1
    set stCur := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1
    set info := stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))
    obtain ⟨_, _, hUb_s, _, _, _, _⟩ := stepTreeCoreAuxWith_fields_eq reinsertD sparsify
      stPrev (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 (D.U (s + 1))
      hm₀_s hcs_eq_s hact_eq_s hAB_eq_s hts_eq_s hdyn_eq_s
    have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_lt
    have hs82 := (hT82 C hC b).2.2.2.1 s hs_lt _ hget
    have hdyn_prev : stPrev.dyn (C, b) = DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
        (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
        (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) s :=
      hdyn_eq_s ▸ (hC_s C hC).2.2.2.2 b |>.2.2.2
    have hdyn_cur : stCur.dyn (C, b) = DynSpanner.runBatchState (initBucketGraph (cs₀.compSt C) ℓ₀ b)
        (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
        (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) (s + 1) :=
      hdyn_eq_s1 ▸ (hC_s1 C hC).2.2.2.2 b |>.2.2.2
    have hres_eq : DynSpanner.runBatchStepOut (initBucketGraph (cs₀.compSt C) ℓ₀ b)
        (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L) (sparsify M)
        (bucketBatchList oracle C_lsst L sparsify k M N τ D j C b) s = info.stepOut (C, b) := by
      dsimp only [DynSpanner.runBatchStepOut]
      rw [hget, ← hdyn_prev, ← congrFun hUb_s (C, b)]
      change DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify M) =
        DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify stPrev.m₀)
      rw [hm₀_s, hm₀]
    dsimp only at hs82
    rw [hres_eq] at hs82
    refine ⟨by change DynSpanner.update _ _ (sparsify stPrev.m₀) = _; rw [hm₀_s, hm₀]; rfl,
      rfl, ?_, ?_, ?_, ?_⟩
    · rw [hdyn_prev]; exact hs82.2.2.1
    · rw [hdyn_prev, hdyn_cur]; exact hs82.2.2.2.1
    · rw [hdyn_cur]; exact hs82.2.2.2.2.1
    · intro eG heG eH heH hnD
      rw [hdyn_cur] at heG heH
      rw [hdyn_prev]
      exact hs82.2.2.2.2.2 eG heG eH heH hnD
  have hS_stage : ∀ t ≤ τ,
      let st := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
      st.S_cur.IsValid ∧
      st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur := by
    intro t
    induction t with
    | zero =>
      intro _
      dsimp only [treeRunSeqWith, initTreeCore]
      have hRF₀ := compLSF_RF_isRSF hI₀
      have hSub_E : (largeComps k G₀).biUnion (fun C => (actB C).biUnion fun b =>
          (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
            (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L)
            (sparsify M)).state.H.E) ⊆
          cs₀.G.E \ cs₀.RF.F.E := by
        intro e he
        rw [Finset.mem_biUnion] at he
        rcases he with ⟨C, hCL, heB⟩
        rw [Finset.mem_biUnion] at heB
        rcases heB with ⟨b, _, heb⟩
        have hC := largeComps_sub hCL
        have hb_st := (hT82 C hC b).2.2.1 0 (Nat.zero_le τ)
        dsimp only at hb_st
        have heHb : e ∈ (initBucketGraph (cs₀.compSt C) ℓ₀ b).E := hb_st.1.2.1 heb
        have heC₀ : e ∈ (ts₀ C).C.E := (hHb C hC b).2.1.2.1 heHb
        exact compLSF_comp_sdiff_sub hI₀ (hcs₀_G₀ ▸ hC) ((hT₀ C hC).hCE_sub heC₀)
      set E₀ := (largeComps k G₀).biUnion fun C => (actB C).biUnion fun b =>
        (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
          (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L)
          (sparsify M)).state.H.E
      have hVal : (MGraph.mk cs₀.RF.R E₀
          (coreGraph G₀ cs₀.lsf).tail (coreGraph G₀ cs₀.lsf).head).IsValid := by
        intro e he
        have heG := (Finset.mem_sdiff.mp (hSub_E he)).1
        have hth := hI₀.hG_val e heG
        dsimp only [coreGraph]
        exact ⟨(root_mem_R hRF₀ hth.1).1, (root_mem_R hRF₀ hth.2).1⟩
      have hSubC : (coreGraph cs₀.G cs₀.lsf).IsSubgraph
          (MGraph.mk cs₀.RF.R E₀ (coreGraph G₀ cs₀.lsf).tail (coreGraph G₀ cs₀.lsf).head) := by
        refine ⟨Finset.Subset.rfl, hSub_E, fun e _ => ?_⟩
        dsimp only [coreGraph]; exact ⟨rfl, rfl⟩
      have hEx_empty : (largeComps k G₀).biUnion (fun C =>
          extraSet (cs₀.compSt C) (ts₀ C)) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro e he; rw [Finset.mem_biUnion] at he; rcases he with ⟨C, _, heC⟩
        rw [extraSet_init] at heC; exact Finset.notMem_empty e heC
      have hX_empty : cs₀.crossEdges = ∅ := rfl
      have hAB₀ : (fun C => (ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e))) =
          actB := (hBase 0 (Nat.zero_le τ)).2.2.2.2.2.1
      have hS₀_E :
          ((largeComps k G₀).biUnion fun C =>
            ((ts₀ C).C.E.image (fun e => bucketOf (coreLen cs₀.lsf (safeLen G₀ ℓ₀) e))).biUnion fun b =>
              (DynSpanner.init (initBucketGraph (cs₀.compSt C) ℓ₀ b) L
                (phaseBase ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB) L)
                (sparsify M)).state.H.E) = E₀ :=
        Finset.biUnion_congr rfl fun C _ => by rw [congrFun hAB₀ C]
      refine ⟨hS₀_E.symm ▸ hVal, rfl, ?_, hS₀_E.symm ▸ hSubC⟩
      change _ = E₀ ∪ (largeComps k G₀).biUnion (fun C => extraSet (cs₀.compSt C) (ts₀ C)) ∪
        cs₀.crossEdges
      rw [hS₀_E, hEx_empty, hX_empty, Finset.union_empty, Finset.union_empty]
    | succ s ih =>
      intro hs_le
      obtain ⟨hVal_s, hV_s, hE_s, hSub_s⟩ := ih (Nat.le_of_succ_le hs_le)
      obtain ⟨_, _, _, _, _, hAB_s, _, hcs_s, hI_s, _, hAct_s, hUnt_s, hC_s⟩ :=
        hBase s (Nat.le_of_succ_le hs_le)
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hC_s1⟩ := hBase (s + 1) hs_le
      obtain ⟨_, _, _, _, _, hAB_eq_s, _, hcs_eq_s, hact_eq_s, hts_eq_s, _⟩ :=
        treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j s
      obtain ⟨_, _, _, _, _, _, _, _, _, hts_eq_s1, hdyn_eq_s1⟩ :=
        treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j (s + 1)
      have hStep_s := hStep s hs_le
      set st_s := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j s).1
      have hG₀_s : st_s.cs.G₀ = G₀ := by rw [← hcs₀_G₀, hcs_eq_s, hcs_s, compLSFBatch_G₀]
      have hst1 : (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1 =
          (stepTreeCoreAuxWith reinsertD sparsify st_s (D.U (s + 1))).state := rfl
      have hsp := stepTreeCoreAux_stage_stepWith reinsertD sparsify hI₀ hcs₀_G₀ hCov₀
        st_s (D.U (s + 1)) actB (hAB_eq_s.trans hAB_s) hG₀_s (hcs_eq_s ▸ hI_s)
        (hact_eq_s ▸ hAct_s.2)
        (fun C hC hna => by
          rw [hcs_eq_s, hts_eq_s]
          exact hUnt_s C hC (hact_eq_s ▸ hna))
        (fun C hC => hcs_eq_s ▸ (hC_s C hC).1)
        (fun C hC => hcs_eq_s ▸ hts_eq_s ▸ (hC_s C hC).2.1)
        (hcs_eq_s ▸ hStep_s.1) hVal_s hV_s hE_s hSub_s
        (fun C hC b _ => by
          have hb_st := (hT82 C hC b).2.2.1 (s + 1) hs_le
          dsimp only at hb_st
          rw [← ((hC_s1 C hC).2.2.2.2 b).2.2.2] at hb_st
          rw [← hst1, congrFun hdyn_eq_s1 (C, b)]
          exact hb_st.1.2.1)
        (fun C hC b _ => by
          rw [← hst1, congrFun hdyn_eq_s1 (C, b), congrFun hts_eq_s1 C]
          exact ((hC_s1 C hC).2.2.2.2 b).2.1.2.1)
        (fun hUnil C _ b => by
          have hUb : (stepTreeCoreAuxWith reinsertD sparsify st_s (D.U (s + 1))).U_b (C, b) = [] := by
            dsimp only [stepTreeCoreAuxWith]; rw [hUnil]; rfl
          change DynSpanner.update (st_s.dyn (C, b))
            ((stepTreeCoreAuxWith reinsertD sparsify st_s (D.U (s + 1))).U_b (C, b)) (sparsify st_s.m₀) = _
          rw [hUb, update_nil])
      dsimp only at hsp
      rw [hst1]
      exact ⟨hsp.1, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1⟩
  have hAct_diff_card : ∀ t ≤ τ,
      ((treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1.activeComps \ largeComps k G₀).card ≤
        2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) := by
    have hBaseCard : ∀ t ≤ τ,
        ((treeRunSeq oracle C_lsst L sparsify k M N D j t).1.activeComps \ largeComps k G₀).card ≤
          2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) := by
      intro t
      induction t with
      | zero =>
        intro _
        have hact0 : (treeRunSeq oracle C_lsst L sparsify k M N D j 0).1.activeComps = largeComps k G₀ := rfl
        rw [hact0, Finset.sdiff_self, Finset.card_empty]
        simp
      | succ s ih =>
        intro hs_le
        have hss := hStep s hs_le
        have ih' := ih (Nat.le_of_succ_le hs_le)
        have hsub : (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps \ largeComps k G₀ ⊆
            ((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps \ largeComps k G₀) ∪
              (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                (D.U (s + 1))).newlyActive := by
          intro C hC
          rw [Finset.mem_sdiff] at hC
          rw [hss.2.1.2.2.1, Finset.mem_union] at hC
          rw [Finset.mem_union]
          rcases hC with ⟨h1 | h2, hNL⟩
          · exact Or.inl (Finset.mem_sdiff.mpr ⟨h1, hNL⟩)
          · exact Or.inr h2
        have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
          ext x; simp [Finset.mem_Icc]; omega
        calc ((treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps \ largeComps k G₀).card
            ≤ (((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps \ largeComps k G₀) ∪
                (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                  (D.U (s + 1))).newlyActive).card := Finset.card_le_card hsub
          _ ≤ ((treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps \ largeComps k G₀).card +
                (stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1
                  (D.U (s + 1))).newlyActive.card := Finset.card_union_le _ _
          _ ≤ 2 * (Finset.Icc 1 s).sum (fun i => (D.U i).length) + 2 * (D.U (s + 1)).length :=
                Nat.add_le_add ih' hss.2.1.2.2.2
          _ = 2 * (Finset.Icc 1 (s + 1)).sum (fun i => (D.U i).length) := by
                rw [hIcc, Finset.sum_insert (by simp)]; omega
    intro t ht
    rw [(treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j t).2.2.2.2.2.2.2.2.1]
    exact hBaseCard t ht
  have hStage_all : ∀ t ≤ τ,
      let st := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
      st.S_cur.IsValid ∧
      st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E =
        (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
          (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)) ∪
          st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur ∧
      st.activeComps ⊆ components G₀ ∧
      largeComps k G₀ ⊆ st.activeComps ∧
      (st.activeComps \ largeComps k G₀).card ≤ 2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b
        let nMax_b := Hb₀.n + splitB
        let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
        (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
        Embedding.IsEmbedding (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
        (Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        Embedding.vcong (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            (Hb₀.maxDeg : ℝ)) := by
    intro t ht
    obtain ⟨h1, h2, h3, h4⟩ := hS_stage t ht
    have hb_t := hBase t ht
    have hact_eq := (treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j t).2.2.2.2.2.2.2.2.1
    have hdyn_eq := (treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j t).2.2.2.2.2.2.2.2.2.2
    refine ⟨h1, h2, h3, h4, hact_eq ▸ hb_t.2.2.2.2.2.2.2.2.2.2.1.2,
      hact_eq ▸ hb_t.2.2.2.2.2.2.2.2.2.2.1.1, hAct_diff_card t ht, fun C hC b => ?_⟩
    have hrun := ((hb_t.2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.2.2 b).2.2.2
    rw [congrFun hdyn_eq (C, b), hrun]
    have ht82 := (hT82 C hC b).2.2.1 t ht
    dsimp only at ht82
    exact ht82
  have hStep_full : ∀ t, 1 ≤ t → t ≤ τ →
      let stPrev := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (t - 1)).1
      let stCur := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j t).1
      let info := stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U t)
      stPrev.S_cur.BatchIsValid info.U_S ∧
      stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
      (D.U t = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify M) ∧
        (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
        (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
        (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
        (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
        (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
          eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG))) ∧
      ((reinsertD = false → NoBatchReinsert stPrev.cs.G (D.U t) → NoBatchReinsert stPrev.S_cur info.U_S) ∧
        (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
          (reinsertD = true → e ∉ info.D_total) ∧ ∀ u ∈ D.U t, ¬ u.Inserts e)) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U t).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, (stPrev.dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
        (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
        7 * (D.U t).length +
        2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card +
        2 * (if reinsertD then info.D_total.card else 0) := by
    intro t ht1 htτ
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    simp only [Nat.add_sub_cancel]
    have hs_lt : s < τ := htτ
    obtain ⟨_, _, _, _, _, hAB_s, _, _, hI_s, _, hAct_s, hUnt_s, hC_s⟩ := hBase s (Nat.le_of_lt hs_lt)
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hAct_s1, _, hC_s1⟩ := hBase (s + 1) htτ
    obtain ⟨hm₀_s, _, _, _, _, hAB_eq_s, _, hcs_eq_s, hact_eq_s, hts_eq_s, hdyn_eq_s⟩ :=
      treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j s
    obtain ⟨_, _, _, _, _, _, _, _, hact_eq_s1, hts_eq_s1, hdyn_eq_s1⟩ :=
      treeRunSeqWith_fields_eq reinsertD oracle C_lsst L sparsify k M N D j (s + 1)
    have hStep_s := hStep s hs_lt
    have hS_prev := hStage_all s (Nat.le_of_lt hs_lt)
    have hS_cur := hStage_all (s + 1) htτ
    set stPrev := (treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j s).1
    obtain ⟨hnew_eq_s, _, _, _, _, _, _⟩ := stepTreeCoreAuxWith_fields_eq reinsertD sparsify
      stPrev (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 (D.U (s + 1))
      hm₀_s hcs_eq_s hact_eq_s hAB_eq_s hts_eq_s hdyn_eq_s
    have hG₀_s : stPrev.cs.G₀ = G₀ := by
      rw [hcs_eq_s, (hBase s (Nat.le_of_lt hs_lt)).2.2.2.2.2.2.2.1, compLSFBatch_G₀]; rfl
    have hsp := stepTreeCoreAux_stage_stepWith reinsertD sparsify hI₀ hcs₀_G₀ hCov₀ stPrev (D.U (s + 1)) actB
      (hAB_eq_s.trans hAB_s) hG₀_s (hcs_eq_s ▸ hI_s) (hact_eq_s ▸ hAct_s.2)
      (fun C hC hna => by rw [hcs_eq_s, hts_eq_s]; exact hUnt_s C hC (hact_eq_s ▸ hna))
      (fun C hC => hcs_eq_s ▸ (hC_s C hC).1)
      (fun C hC => hcs_eq_s ▸ hts_eq_s ▸ (hC_s C hC).2.1)
      (hcs_eq_s ▸ hStep_s.1) hS_prev.1 hS_prev.2.1 hS_prev.2.2.1 hS_prev.2.2.2.1
      (fun C hC b _ => by
        change ((treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1.dyn (C, b)).H.E ⊆
          ((treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1.dyn (C, b)).G.E
        exact (hS_cur.2.2.2.2.2.2.2 C hC b).1.2.1)
      (fun C hC b _ => by
        change ((treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1.dyn (C, b)).G.E ⊆
          ((treeRunSeqWith reinsertD oracle C_lsst L sparsify k M N D j (s + 1)).1.ts C).C.E
        rw [congrFun hdyn_eq_s1 (C, b), congrFun hts_eq_s1 C]
        exact ((hC_s1 C hC).2.2.2.2 b).2.1.2.1)
      (fun hUnil C _ b => by
        have hUb : (stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))).U_b (C, b) = [] := by
          dsimp only [stepTreeCoreAuxWith]; rw [hUnil]; rfl
        change DynSpanner.update (stPrev.dyn (C, b))
          ((stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))).U_b (C, b)) (sparsify stPrev.m₀) = _
        rw [hUb, update_nil])
    dsimp only at hsp
    have hNew_sub : (stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))).newlyActive ⊆
        components G₀ \ largeComps k G₀ := by
      intro C hC
      rw [hnew_eq_s] at hC
      have hC1 : C ∈ (treeRunSeq oracle C_lsst L sparsify k M N D j (s + 1)).1.activeComps := by
        rw [hStep_s.2.1.2.2.1]; exact Finset.mem_union_right _ hC
      have hna : C ∉ (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps := by
        rw [hStep_s.2.1.1, Finset.mem_sdiff] at hC; exact hC.2
      exact Finset.mem_sdiff.mpr ⟨hAct_s1.2 hC1, fun hL => hna (hAct_s.1 hL)⟩
    have hNew_n : ∀ C ∈ (stepTreeCoreAuxWith reinsertD sparsify stPrev (D.U (s + 1))).newlyActive, ∀ b : ℤ,
        (stPrev.dyn (C, b)).G.n ≤ 11 := by
      intro C hC b
      have hC_comp := (Finset.mem_sdiff.mp (hNew_sub hC)).1
      have hNL := (Finset.mem_sdiff.mp (hNew_sub hC)).2
      rw [hnew_eq_s] at hC
      have hna : C ∉ (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.activeComps := by
        rw [hStep_s.2.1.1, Finset.mem_sdiff] at hC; exact hC.2
      have hts_eq : (treeRunSeq oracle C_lsst L sparsify k M N D j s).1.ts C = ts₀ C :=
        (hUnt_s C hC_comp hna).2
      have hsub := ((hC_s C hC_comp).2.2.2.2 b).2.1.1
      rw [hts_eq] at hsub
      rw [congrFun hdyn_eq_s (C, b)]
      exact le_trans (Finset.card_le_card hsub) (hSmall C hC_comp hNL)
    have hLen := stepTreeCoreAux_US_lenWith reinsertD sparsify hI₀ hcs₀_G₀ hCov₀ stPrev (D.U (s + 1)) actB
      hG₀_s (hcs_eq_s ▸ hI_s) (hact_eq_s ▸ hAct_s.2) (hact_eq_s1 ▸ hAct_s1.2)
      (fun C hC hna => by rw [hcs_eq_s, hts_eq_s]; exact hUnt_s C hC (hact_eq_s ▸ hna))
      (fun C hC => hcs_eq_s ▸ (hC_s C hC).1)
      (fun C hC => hcs_eq_s ▸ hts_eq_s ▸ (hC_s C hC).2.1)
      (hcs_eq_s ▸ hStep_s.1) hS_prev.2.2.1 hsp.2.2.1 hsp.2.2.2.2.2.2.2.2
      (fun C hC b _ => (hStepB s hs_lt C ((hact_eq_s1 ▸ hAct_s1.2) hC) b).2.2.2.1)
    exact ⟨hsp.2.2.2.2.1, hsp.2.2.2.2.2.1, hsp.2.2.2.2.2.2.1,
      hStepB s hs_lt, hsp.2.2.2.2.2.2.2.1, hNew_sub, hnew_eq_s ▸ hStep_s.2.1.2.2.2, hNew_n, hLen⟩
  refine ⟨hSmall, hStage_all, hStep_full, fun C hC b t ht => ?_⟩
  have hm0 := (hT82 C hC b).1
  have h0 := (hT82 C hC b).2.1
  have hc := (hT82 C hC b).2.2.2.2 t ht
  refine ⟨hm0, h0, hc.1, hc.2.1, ?_⟩
  refine le_trans hc.2.2 ?_
  refine mul_le_mul_of_nonneg_left ?_ ?_
  · refine Finset.sum_le_sum fun s hs => ?_
    have hs_lt : s < τ := lt_of_lt_of_le (Finset.mem_range.mp hs) ht
    have hget := bucketBatchList_getElem? oracle C_lsst L sparsify k M N τ D j C b hs_lt
    rw [hget]
  · have hK_t := P_b.hK_t
    have hK_s := P_b.hK_s
    have hγc := P_b.hγ_c
    have hγl := P_b.hγ_ℓ
    have hL_nn : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hnm_ge : (1 : ℝ) ≤ ((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB : ℕ) +
        ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) + 2 := by linarith
    have hΛ_nn : 0 ≤ (1 + Real.log (((initBucketGraph (cs₀.compSt C) ℓ₀ b).n + splitB : ℕ) +
        ((initBucketGraph (cs₀.compSt C) ℓ₀ b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t :=
      pow_nonneg (by linarith [Real.log_nonneg hnm_ge]) _
    positivity

/-- Full trajectory invariant for `sparseCoreTool` (`reinsertD = true`), combining
`treeRunSeq_tilde_inv`, `DynSpanner.theorem_8_2`, `DynSpanner.sparsity_H`, and
`buildUSReinsert_spec` across `t = 0..τ`. -/
lemma treeRunSeq_inv
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst) (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hSp : SparsifySpec M P_b (sparsify M)) (j : ℕ) (hj : j < k) :
    let G₀ := D.G 0; let ℓ₀ := D.ℓ 0; let cs₀ := initCompLSF oracle C_lsst G₀ ℓ₀ k j
    let ts₀ := fun C => initTildeState (cs₀.compSt C)
    let origB : ℕ → ℤ := fun e => bucketOf (coreLen cs₀.lsf ℓ₀ e)
    let actB : Finset ℕ → Finset ℤ := fun C => (ts₀ C).C.E.image origB
    let splitB := Nat.floor (SparseCoreTool.updateThreshold k M N) * (G₀.maxDeg + 1) +
      Nat.ceil (56 * (M : ℝ) / (k : ℝ))
    (∀ C ∈ components G₀, C ∉ largeComps k G₀ → (ts₀ C).C.V.card ≤ 11) ∧
    (∀ t ≤ τ,
      let st := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      st.S_cur.IsValid ∧ st.S_cur.V = st.cs.RF.R ∧
      st.S_cur.E = (st.activeComps.biUnion fun C => (actB C).biUnion fun b => (st.dyn (C, b)).H.E) ∪
        (st.activeComps.biUnion fun C => extraSet (st.cs.compSt C) (st.ts C)) ∪ st.cs.crossEdges ∧
      (coreGraph st.cs.G st.cs.lsf).IsSubgraph st.S_cur ∧
      st.activeComps ⊆ components G₀ ∧ largeComps k G₀ ⊆ st.activeComps ∧
      (st.activeComps \ largeComps k G₀).card ≤ 2 * (Finset.Icc 1 t).sum (fun s => (D.U s).length) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b; let nMax_b := Hb₀.n + splitB
        let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
        (st.dyn (C, b)).G.IsSubgraph (st.dyn (C, b)).H ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st.dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st.dyn (C, b)).G.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s ∧
        ((st.dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (nMax_b : ℝ) * P_b.γ_ℓ * Λ_s_b ∧
        Embedding.IsEmbedding (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H ∧
        (Embedding.length (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        Embedding.vcong (piTotal (st.dyn (C, b))) (st.dyn (C, b)).G (st.dyn (C, b)).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) * (Hb₀.maxDeg : ℝ))) ∧
    (∀ t, 1 ≤ t → t ≤ τ →
      let stPrev := (treeRunSeq oracle C_lsst L sparsify k M N D j (t - 1)).1
      let stCur := (treeRunSeq oracle C_lsst L sparsify k M N D j t).1
      let info := stepTreeCoreAux sparsify stPrev (D.U t)
      stPrev.S_cur.BatchIsValid info.U_S ∧ stCur.S_cur = stPrev.S_cur.applyBatch info.U_S ∧
      (D.U t = [] → info.U_S = [] ∧ stCur.cost = stPrev.cost) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) = DynSpanner.update (stPrev.dyn (C, b)) (info.U_b (C, b)) (sparsify M) ∧
        (info.stepOut (C, b)).state = stCur.dyn (C, b) ∧
        (stPrev.dyn (C, b)).H.BatchIsValid (info.stepOut (C, b)).UH ∧
        (stPrev.dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = (stCur.dyn (C, b)).H ∧
        (info.stepOut (C, b)).D ⊆ (stCur.dyn (C, b)).H.E ∧
        (∀ eG ∈ (stCur.dyn (C, b)).G.E, ∀ eH,
          eH ∈ walkEdges (piTotal (stCur.dyn (C, b)) eG) → eH ∉ (info.stepOut (C, b)).D →
          eH ∈ walkEdges (piTotal (stPrev.dyn (C, b)) eG))) ∧
      (∀ e ∈ stPrev.S_cur.E, e ∈ stCur.S_cur.E → (∀ u ∈ info.U_S, ¬ u.Inserts e) →
        e ∉ info.D_total ∧ ∀ u ∈ D.U t, ¬ u.Inserts e) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧ info.newlyActive.card ≤ 2 * (D.U t).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, (stPrev.dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (stCur.activeComps.sum fun C => (actB C).sum fun b => (info.stepOut (C, b)).UH.length) +
        (info.newlyActive.sum fun C => (actB C).sum fun b => (stPrev.dyn (C, b)).H.E.card) +
        7 * (D.U t).length + 2 * (stCur.cs.RF.R \ stPrev.cs.RF.R).card + 2 * info.D_total.card) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ, ∀ t ≤ τ,
      let Hb₀ := initBucketGraph (cs₀.compSt C) ℓ₀ b; let nMax_b := Hb₀.n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + (Hb₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) * P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let initB := DynSpanner.init Hb₀ L (phaseBase nMax_b L) (sparsify M)
      let Us_b := bucketBatchList oracle C_lsst L sparsify k M N τ D j C b
      let res_b : ℕ → StepOut L := fun s => DynSpanner.runBatchStepOut (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s
      let batchTot_b : ℝ := ((Us_b.take t).flatten.length : ℝ)
      let encTot_b : ℝ := ∑ s ∈ Finset.range t, ((DynSpanner.runBatchState (L := L) Hb₀ (phaseBase nMax_b L) (sparsify M) Us_b s).G.batchEnc ((stepTreeCoreAux sparsify (treeRunSeq oracle C_lsst L sparsify k M N D j s).1 (D.U (s + 1))).U_b (C, b)) : ℝ)
      ((initB.state.H.m : ℝ) ≤ P_b.K_s * (Hb₀.n : ℝ) * P_b.γ_ℓ * (1 + Real.log ((Hb₀.n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_s) ∧
      ((initB.cost : ℝ) ≤ P_b.K_t * (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ ^ 2) * (1 + Real.log (((activeSubgraph Hb₀).n : ℝ) + (Hb₀.m : ℝ) + 2)) ^ P_b.p_t + (Hb₀.n : ℝ) + (Hb₀.m : ℝ) + (initB.state.H.m : ℝ) + (Hb₀.m : ℝ) * P_b.γ_ℓ + (L : ℝ) + 1) ∧
      (∑ s ∈ Finset.range t, ((res_b s).UH.length : ℝ) ≤ (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).D.card : ℝ) ≤ 6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b * batchTot_b) ∧
      (∑ s ∈ Finset.range t, ((res_b s).cost : ℝ) ≤ 90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b * ((Hb₀.maxDeg : ℝ) + 1) * Λ_b * encTot_b)) := by
  have h := treeRunSeq_invWith true oracle C_lsst L hL P_b sparsify hLSST k M N τ hk D hG₀ hV₀ hℓ₀ hD hM hN hThresh hSp j hj
  refine ⟨h.1, h.2.1, fun t ht1 htτ => ?_, h.2.2.2⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h.2.2.1 t ht1 htτ
  refine ⟨h1, h2, h3, h4, fun e he1 he2 hni => ⟨(h5.2 e he1 he2 hni).1 rfl, (h5.2 e he1 he2 hni).2⟩, h6, h7, h8, by simpa using h9⟩

end

end MinCostFlow.SparseCore