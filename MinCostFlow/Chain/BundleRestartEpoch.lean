module

public import MinCostFlow.Chain.BundleRestartInv
public import MinCostFlow.SparseCore.BundleConstants
import MinCostFlow.SparseCore.BundleConstantsLemmas
import MinCostFlow.SparseCore.BundleRunInvBase
import MinCostFlow.DynSpanner.Complexity
import MinCostFlow.DynSpanner.WalkCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Epoch Theorem 8.2 Invariants of `sparseCoreBundleRestartTool`

An epoch of branch `j` is the run of its bundle-tree state from its last restart `s₀` (or from
`s₀ = 0`) up to a stage `t`, with no restart of `j` strictly between `s₀` and `t`. This file proves
`epochBundleSeq_inv`: along any such epoch under `hThresh`, every bucket spanner satisfies the
stage, step, walk-count, recourse, re-embedding, and runtime bounds of Theorem 8.2
(`DynSpanner.theorem_8_2`, `DynSpanner.sparsity_H`, `DynSpanner.batchTrace_walkCount_le`), with
the bundle degree cap `k` and degree-free `bundleNMax M` / `bundleLambdaS P_b M`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

private lemma batchPrefixLen_le_flatten' (Us : List (List Update)) (t : ℕ) :
    batchPrefixLen Us t ≤ Us.flatten.length := by
  dsimp only [batchPrefixLen]
  conv_rhs => rw [← List.take_append_drop t Us, List.flatten_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Full Theorem 8.2 epoch invariants for `epochBundleSeq` over `[s₀, t]` under `hThresh`
(paper Theorem 8.2, page 39). -/
theorem epochBundleSeq_inv
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hs₀ : s₀ = 0 ∨ j ∈ restarts s₀)
    (hNoRest : ∀ r, s₀ < r → r < t → j ∉ restarts r) :
    let G₀ := D.G 0
    let st₀ := initBundleTreeWith lsfInit L sparsify k M N G₀ (D.ℓ 0) (ord 0) j
    let actB := st₀.activeBuckets
    let splitB := bundleSplitBudget k M
    let Δ := t - s₀
    let st := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    let Hb := fun C b => ((st 0).bun (C, b)).graph
    let Us_ep : Finset ℕ → ℤ → List (List Update) := fun C b =>
      (List.range Δ).map fun r =>
        (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)
    (∀ C ∈ components G₀, ∀ b : ℤ,
      (Hb C b).IsValid ∧ (Hb C b).m ≤ G₀.m ∧ (Hb C b).n ≤ 2 * (Hb C b).m ∧
      (Hb C b).maxDeg ≤ k ∧
      k * ((st 0).bun (C, b)).vertices.card ≤
        k * ((st 0).cs.compSt C).R.card + 2 * ((st 0).bun (C, b)).edges.card ∧
      batchSplitCount (Us_ep C b).flatten ≤ splitB) ∧
    ((components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ G₀.m) ∧
    (∀ r ≤ Δ,
      (st r).S_cur.IsValid ∧ (st r).activeComps ⊆ components G₀ ∧
      ∀ C ∈ components G₀, ∀ b : ℤ,
        GraphEq ((st r).dyn (C, b)).G ((st r).bun (C, b)).graph ∧
        ((st r).dyn (C, b)).G.IsValid ∧
        ((st r).dyn (C, b)).G.n ≤ bundleNMax M ∧
        ((st r).dyn (C, b)).G.IsSubgraph ((st r).dyn (C, b)).H ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) *
          P_b.γ_ℓ * (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        (((st r).dyn (C, b)).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) *
          P_b.γ_ℓ * bundleLambdaS P_b M ∧
        (piTotal ((st r).dyn (C, b))).IsEmbedding ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H ∧
        ((piTotal ((st r).dyn (C, b))).length ((st r).dyn (C, b)).G : ℝ) ≤ coreE82Len L P_b ∧
        (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H (fun _ => 1) ≤
          coreE82Cong L P_b * (k : ℝ)) ∧
    (∀ r < Δ,
      let info := stepBundleTree sparsify (st r) (D.U (s₀ + r + 1)) (ord (s₀ + r)) (ord (s₀ + r + 1))
      (st r).S_cur.BatchIsValid info.U_S ∧
      (st (r + 1)).S_cur = (st r).S_cur.applyBatch info.U_S ∧
      (D.U (s₀ + r + 1) = [] → info.U_S = []) ∧
      (∀ C ∈ components G₀, ∀ b : ℤ,
        info.stepOut (C, b) =
          DynSpanner.update ((st r).dyn (C, b)) (info.U_B (C, b)) (sparsify (st r).m₀) ∧
        (info.stepOut (C, b)).state = (st (r + 1)).dyn (C, b) ∧
        ((st r).dyn (C, b)).H.applyBatch (info.stepOut (C, b)).UH = ((st (r + 1)).dyn (C, b)).H ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E,
          ∀ eH ∈ walkEdges (piTotal ((st (r + 1)).dyn (C, b)) eG),
            eH ∉ (info.stepOut (C, b)).D → eH ∈ walkEdges (piTotal ((st r).dyn (C, b)) eG)) ∧
        (∀ eG ∈ ((st (r + 1)).dyn (C, b)).G.E, ∀ x : ℕ, x ∉ (info.stepOut (C, b)).D →
          walkCount (piTotal ((st (r + 1)).dyn (C, b)) eG) x ≤
            walkCount (piTotal ((st r).dyn (C, b)) eG) x)) ∧
      info.newlyActive ⊆ components G₀ \ largeComps k G₀ ∧
      info.newlyActive.card ≤ 2 * (D.U (s₀ + r + 1)).length ∧
      (∀ C ∈ info.newlyActive, ∀ b : ℤ, ((st r).dyn (C, b)).G.n ≤ 11) ∧
      info.U_S.length ≤
        (st (r + 1)).activeComps.sum (fun C => (actB C).sum fun b =>
          (info.stepOut (C, b)).UH.length) +
        info.newlyActive.sum (fun C => (actB C).sum fun b =>
          ((st r).dyn (C, b)).H.E.card) +
        7 * (D.U (s₀ + r + 1)).length +
        2 * ((st (r + 1)).cs.RF.R \ (st r).cs.RF.R).card +
        2 * info.D_total.card) ∧
    (∀ C ∈ components G₀, ∀ b : ℤ,
      let nMax_b := (Hb C b).n + splitB
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length : ℝ)
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchState (L := L) (normGraph (Hb C b)) (phaseBase nMax_b L) (sparsify M)
            (Us_ep C b) r).G.batchEnc
          ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
            (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)) : ℝ)
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        ((DynSpanner.runBatchStepOut (L := L) (normGraph (Hb C b)) (phaseBase nMax_b L) (sparsify M)
          (Us_ep C b) r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) := by
  intro G₀ st₀ actB splitB Δ st Hb Us_ep
  have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀ hNoRest
  have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
    k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit
  have hStp := epochBundleSeq_step_spec lsfInit C_lsst L hL P_b sparsify
    k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ hs₀ hNoRest
  obtain ⟨hSt_base, _⟩ := epochBundleSeq_steps lsfInit C_lsst L sparsify
    k M N D ord restarts hV₀ s₀ t j hst hNoRest
  have hSplit : ∀ C ∈ components G₀, ∀ b : ℤ, batchSplitCount (Us_ep C b).flatten ≤ splitB :=
    fun C hC b => epochBundleSeq_batchSplitCount_le_splitB lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd hThresh s₀ t j hInit hst htτ hs₀ hNoRest
      hC b
  have hm_sum : (components G₀).sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ G₀.m :=
    epochBundleSeq_Hb_m_sum_le lsfInit C_lsst L sparsify
      k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd s₀ t j hInit hst htτ
  have hbase_m0 : ∀ r ≤ Δ, (st r).m₀ = M := fun r hr => by
    have hb := hBun (s₀ + r) (by omega)
    have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
      hV₀ j (s₀ + r)).1
    exact ((hSt_base r hr).m₀.trans hbp.m₀.symm).trans hb.2.1
  have hT82 : ∀ C ∈ components G₀, ∀ b : ℤ,
      let nMax_b := (Hb C b).n + splitB
      let q_b := phaseBase nMax_b L
      let st_b := fun r => DynSpanner.runBatchState (L := L) (normGraph (Hb C b)) q_b (sparsify M) (Us_ep C b) r
      let res_b := fun r => DynSpanner.runBatchStepOut (L := L) (normGraph (Hb C b)) q_b (sparsify M) (Us_ep C b) r
      let Λ_s_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s
      let Λ_b := (1 + Real.log ((nMax_b : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t
      let E_L_b := 3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)
      let nRoot_b : ℝ := ((max nMax_b 1 : ℕ) : ℝ) ^ (1 / (L : ℝ))
      let batchTot_b := ∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length : ℝ)
      let encTot_b : ℝ := ∑ r ∈ Finset.range Δ,
        ((st_b r).G.batchEnc ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)) : ℝ)
      (∀ r ≤ Δ,
        (st_b r).G.IsSubgraph (st_b r).H ∧
        ((st_b r).H.m : ℝ) ≤ (L + 1 : ℝ) * P_b.K_s * ((st_b r).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log (((st_b r).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s ∧
        (piTotal (st_b r)).IsEmbedding (st_b r).G (st_b r).H ∧
        ((piTotal (st_b r)).length (st_b r).G : ℝ) ≤ 3 ^ L * P_b.γ_ℓ ^ (L + 1) ∧
        (piTotal (st_b r)).vcong (st_b r).G (st_b r).H (fun _ => 1) ≤
          3 ^ ((L + 1) * (L + 2) / 2) * P_b.γ_ℓ ^ (L * (L + 1) / 2) * P_b.γ_c ^ (L + 1) *
            ((Hb C b).maxDeg : ℝ)) ∧
      (∀ r < Δ, ∀ U, (Us_ep C b)[r]? = some U →
        res_b r = DynSpanner.update
          (DynSpanner.runState (L := L) (normGraph (Hb C b)) q_b (sparsify M) (Us_ep C b).flatten
            (batchPrefixLen (Us_ep C b) r)) U (sparsify M) ∧
        (res_b r).state = st_b (r + 1) ∧
        (st_b r).H.BatchIsValid (res_b r).UH ∧
        (st_b r).H.applyBatch (res_b r).UH = (st_b (r + 1)).H ∧
        (res_b r).D ⊆ (st_b (r + 1)).H.E ∧
        (∀ eG ∈ (st_b (r + 1)).G.E, ∀ eH ∈ walkEdges (piTotal (st_b (r + 1)) eG),
          eH ∉ (res_b r).D → eH ∈ walkEdges (piTotal (st_b r) eG)) ∧
        (∀ eG ∈ (st_b (r + 1)).G.E, ∀ x : ℕ, x ∉ (res_b r).D →
          walkCount (piTotal (st_b (r + 1)) eG) x ≤ walkCount (piTotal (st_b r) eG) x)) ∧
      ((∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).UH.length : ℝ)) ≤
        (2 + 12 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * Λ_s_b) * batchTot_b ∧
      (∑ r ∈ Finset.range Δ,
        (((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
          (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b)).D.card : ℝ)) ≤
        6 * (L : ℝ) * nRoot_b * P_b.K_s * P_b.γ_ℓ * (3 ^ L * P_b.γ_ℓ ^ (L + 1) + 1) * Λ_s_b *
          batchTot_b ∧
      (∑ r ∈ Finset.range Δ, ((res_b r).cost : ℝ)) ≤
        90 * (L : ℝ) * nRoot_b * (P_b.K_t + P_b.K_s + 1) * E_L_b *
          (((Hb C b).maxDeg : ℝ) + 1) * Λ_b * encTot_b) := by
    intro C hC b nMax_b q_b st_b res_b Λ_s_b Λ_b E_L_b nRoot_b batchTot_b encTot_b
    have hdC := hDyn C hC b
    have hHb_val : (normGraph (Hb C b)).IsValid := normGraph_isValid hdC.1
    have hHb_mM : (normGraph (Hb C b)).m ≤ M := le_trans hdC.2.1 hM
    have hBV : (normGraph (Hb C b)).BatchIsValid (Us_ep C b).flatten :=
      (graphEq_batchIsValid (graphEq_symm (normGraph_graphEq _)) _).mp hdC.2.2.2.2.2.1
    have hds := hdC.2.2.2.2.2.2.1
    have hsc := hSplit C hC b
    have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
    have hthm := DynSpanner.theorem_8_2 hHb_val hL hHb_mM hSp hBV hds hsc
    rcases hthm with ⟨_, _, hStage, hStep82, hCum⟩
    dsimp only at hStage hStep82 hCum
    simp only [normGraph_n, normGraph_m, normGraph_maxDeg] at hStage hStep82 hCum
    have hq1 : 1 ≤ q_b := le_trans (by omega) (two_le_phaseBase _ L)
    have hSpars := DynSpanner.sparsity_H hHb_val hL hq1 hHb_mM hSp hBV hds
    have hTrace := DynSpanner.batchTrace_spec hHb_val hL hq1 hHb_mM hSp hBV hds
    refine ⟨?_, ?_, ?_⟩
    · intro r hr
      have hs := hStage r (le_trans hr hlen_Us.symm.le)
      have hbp_le : batchPrefixLen (Us_ep C b) r ≤ (Us_ep C b).flatten.length :=
        batchPrefixLen_le_flatten' (Us_ep C b) r
      have htr := hTrace.1 r (le_trans hr hlen_Us.symm.le)
      have hsp_r := hSpars.2 (batchPrefixLen (Us_ep C b) r) hbp_le
      dsimp only at hsp_r
      rw [← htr.1, ← htr.2.1] at hsp_r
      exact ⟨hs.2.1, hsp_r, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2⟩
    · intro r hr U hU
      have hs := hStep82 r (lt_of_lt_of_le hr hlen_Us.symm.le) U hU
      have hwc : ∀ eG ∈ (st_b (r + 1)).G.E, ∀ x : ℕ, x ∉ (res_b r).D →
          walkCount (piTotal (st_b (r + 1)) eG) x ≤ walkCount (piTotal (st_b r) eG) x := by
        intro eG heG x hnotD
        have hcnt := DynSpanner.batchTrace_walkCount_le hHb_val hL hq1 hHb_mM hSp hBV hds
          r (lt_of_lt_of_le hr hlen_Us.symm.le) U hU eG (hs.2.1.symm ▸ heG) x hnotD
        rw [hs.2.1] at hcnt
        exact Nat.cast_le (α := ℝ).mpr hcnt
      exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2, hwc⟩
    · have hc := hCum Δ (le_trans le_rfl hlen_Us.symm.le)
      have hstep_eq : ∀ r ∈ Finset.range Δ,
          (stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
            (ord (s₀ + r)) (ord (s₀ + r + 1))).stepOut (C, b) = res_b r := fun r hr =>
        (hdC.2.2.2.2.2.2.2.2.2.2 r (Finset.mem_range.mp hr)).1
      have hbt_eq : ((Us_ep C b).take Δ).flatten.length =
          ∑ r ∈ Finset.range Δ,
            ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
              (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length := by
        have hgen : ∀ n ≤ Δ, ((Us_ep C b).take n).flatten.length =
            ∑ r ∈ Finset.range n,
              ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
                (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)).length := by
          intro n
          induction n with
          | zero => intro _; simp
          | succ m ih =>
            intro hm
            have hm_lt : m < Δ := hm
            have hget : (Us_ep C b)[m]? =
                some ((stepBundleTree sparsify (st m) (D.U (s₀ + m + 1))
                  (ord (s₀ + m)) (ord (s₀ + m + 1))).U_B (C, b)) := by
              dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hm_lt]; rfl
            rw [take_succ_of_getElem? hget, List.flatten_append, List.flatten_singleton,
              List.length_append, ih (Nat.le_of_lt hm_lt), Finset.sum_range_succ]
        simpa [hlen_Us] using hgen Δ le_rfl
      have hbtR : (((Us_ep C b).take Δ).flatten.length : ℝ) = batchTot_b := by
        dsimp only [batchTot_b]; rw [hbt_eq, Nat.cast_sum]
      have henc_eq : (∑ t' ∈ Finset.range Δ, match (Us_ep C b)[t']? with
            | some U => ((st_b t').G.batchEnc U : ℝ)
            | none => 0) = encTot_b := by
        refine Finset.sum_congr rfl fun r hr => ?_
        have hr_lt : r < Δ := Finset.mem_range.mp hr
        have hget : (Us_ep C b)[r]? =
            some ((stepBundleTree sparsify (st r) (D.U (s₀ + r + 1))
              (ord (s₀ + r)) (ord (s₀ + r + 1))).U_B (C, b)) := by
          dsimp only [Us_ep]; rw [List.getElem?_map, List.getElem?_range hr_lt]; rfl
        rw [hget]
      refine ⟨?_, ?_, ?_⟩
      · have h1 := hc.1
        rw [hbtR] at h1
        exact le_trans (le_of_eq (Finset.sum_congr rfl fun r hr => by rw [hstep_eq r hr])) h1
      · have h2 := hc.2.2.1
        rw [hbtR] at h2
        exact le_trans (le_of_eq (Finset.sum_congr rfl fun r hr => by rw [hstep_eq r hr])) h2
      · have h3 := hc.2.2.2
        exact h3.trans_eq (by rw [← henc_eq]; rfl)
  refine ⟨fun C hC b => ?_, hm_sum, ?_, ?_, fun C hC b => (hT82 C hC b).2.2⟩
  · have hdC := hDyn C hC b
    exact ⟨hdC.1, hdC.2.1, hdC.2.2.1, hdC.2.2.2.1, hdC.2.2.2.2.1, hSplit C hC b⟩
  · -- Stage invariants (`r ≤ Δ`)
    intro r hr
    have hSc_r : (st r).S_cur.IsValid := by
      dsimp only [st, epochBundleSeq]
      split_ifs with hcond
      · exact (hSc t htτ).1.1
      · exact (hSc (s₀ + r) (by omega)).2.1
    have hAct_r : (st r).activeComps ⊆ components G₀ := by
      have hb := hBun (s₀ + r) (by omega)
      have hbp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts
        hV₀ j (s₀ + r)).1
      rw [(hSt_base r hr).activeComps, ← hbp.activeComps]
      exact hb.2.2.2.2.2.2.2.2.2.1.2
    refine ⟨hSc_r, hAct_r, fun C hC b => ?_⟩
    have hdC := hDyn C hC b
    have hdr := hdC.2.2.2.2.2.2.2.2.2.1 r hr
    have ht82 := (hT82 C hC b).1 r hr
    have hm_b : (Hb C b).m ≤ M := le_trans hdC.2.1 hM
    have hn_b : (Hb C b).n ≤ 2 * M := le_trans hdC.2.2.1 (Nat.mul_le_mul_left 2 hm_b)
    have hSplitB : splitB ≤ 2 * (56 * M + 1) := bundleSplitBudget_le_add_one hk
    have hGn_le_nMax : ((st r).dyn (C, b)).G.n ≤ bundleNMax M := by
      have hBV_n : (normGraph (Hb C b)).BatchIsValid (Us_ep C b).flatten :=
        (graphEq_batchIsValid (graphEq_symm (normGraph_graphEq _)) _).mp hdC.2.2.2.2.2.1
      have hBV_take : (normGraph (Hb C b)).BatchIsValid ((Us_ep C b).take r).flatten := by
        have h := hBV_n
        rw [show (Us_ep C b).flatten =
            ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
          rw [← List.flatten_append, List.take_append_drop],
          SparseCore.batchIsValid_append] at h
        exact h.1
      have hds_take : ∀ op ∈ ((Us_ep C b).take r).flatten, isDelOrSplit op := fun op hop =>
        hdC.2.2.2.2.2.2.1 op (by
          rw [show (Us_ep C b).flatten =
              ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
            rw [← List.flatten_append, List.take_append_drop]]
          exact List.mem_append_left _ hop)
      have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
      have hTrace := DynSpanner.batchTrace_spec (normGraph_isValid hdC.1) hL hq1 hm_b hSp hBV_n
        hdC.2.2.2.2.2.2.1
      have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
      have hG_eq : (normGraph (Hb C b)).applyBatch ((Us_ep C b).take r).flatten = ((st r).dyn (C, b)).G := by
        rw [hdr.1, (hTrace.1 r (le_trans hr hlen_Us.symm.le)).2.1]
        congr 1
        change ((Us_ep C b).take r).flatten =
          (Us_ep C b).flatten.take ((Us_ep C b).take r).flatten.length
        rw [show (Us_ep C b).flatten =
            ((Us_ep C b).take r).flatten ++ ((Us_ep C b).drop r).flatten by
          rw [← List.flatten_append, List.take_append_drop]]
        simp
      have hv : ((st r).dyn (C, b)).G.n ≤ (Hb C b).n + batchSplitCount ((Us_ep C b).take r).flatten := by
        unfold MGraph.n
        rw [← hG_eq]
        exact (applyBatch_V_card_eq_of_isDelOrSplit hBV_take hds_take).le
      have hsc_take : batchSplitCount ((Us_ep C b).take r).flatten ≤ splitB := by
        have h1 : batchSplitCount ((Us_ep C b).take r).flatten ≤ batchSplitCount (Us_ep C b).flatten := by
          conv_rhs =>
            rw [← List.take_append_drop r (Us_ep C b), List.flatten_append,
              SparseCore.batchSplitCount_append]
          exact Nat.le_add_right _ _
        exact le_trans h1 (hSplit C hC b)
      unfold bundleNMax
      omega
    have hΛ_le := bundleLambdaS_of_le P_b hGn_le_nMax hm_b
    have hHm_le1 : (((st r).dyn (C, b)).H.m : ℝ) ≤
        (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ *
          (1 + Real.log ((((st r).dyn (C, b)).G.n : ℝ) + ((Hb C b).m : ℝ) + 2)) ^ P_b.p_s := by
      rw [hdr.1]; exact ht82.2.1
    have hHm_le2 : (((st r).dyn (C, b)).H.m : ℝ) ≤
        (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ * bundleLambdaS P_b M := by
      have hK_s := P_b.hK_s
      have hγℓ : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
      have hfac : 0 ≤ (L + 1 : ℝ) * P_b.K_s * (((st r).dyn (C, b)).G.n : ℝ) * P_b.γ_ℓ := by positivity
      exact le_trans hHm_le1 (mul_le_mul_of_nonneg_left hΛ_le hfac)
    have hvc : (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H
        (fun _ => 1) ≤ coreE82Cong L P_b * (k : ℝ) := by
      have h1 : (piTotal ((st r).dyn (C, b))).vcong ((st r).dyn (C, b)).G ((st r).dyn (C, b)).H
          (fun _ => 1) ≤ coreE82Cong L P_b * ((Hb C b).maxDeg : ℝ) := by
        rw [hdr.1]; exact ht82.2.2.2.2
      have hdeg_le : ((Hb C b).maxDeg : ℝ) ≤ (k : ℝ) := by exact_mod_cast hdC.2.2.2.1
      have hce_nn : 0 ≤ coreE82Cong L P_b := by
        unfold coreE82Cong; have := P_b.hγ_ℓ; have := P_b.hγ_c; positivity
      exact le_trans h1 (mul_le_mul_of_nonneg_left hdeg_le hce_nn)
    refine ⟨hdr.2.1, hdr.2.2.1, hGn_le_nMax, ?_, hHm_le1, hHm_le2, ?_, ?_, hvc⟩
    · rw [hdr.1]; exact ht82.1
    · rw [hdr.1]; exact ht82.2.2.1
    · rw [hdr.1]; exact ht82.2.2.2.1
  · -- Step invariants (`r < Δ`)
    intro r hr info
    have hsp := hStp r hr
    refine ⟨hsp.1, hsp.2.1, fun hU => (hsp.2.2.1 hU).1, fun C hC b => ?_,
      hsp.2.2.2.2.1.2.2.2.1, hsp.2.2.2.2.1.2.2.2.2.1, hsp.2.2.2.2.1.2.2.2.2.2, hsp.2.2.2.2.2⟩
    have hdC := hDyn C hC b
    have hget : (Us_ep C b)[r]? = some (info.U_B (C, b)) := by
      dsimp only [Us_ep, info]; rw [List.getElem?_map, List.getElem?_range hr]; rfl
    have ht82 := (hT82 C hC b).2.1 r hr (info.U_B (C, b)) hget
    dsimp only at ht82
    have hres_eq := (hdC.2.2.2.2.2.2.2.2.2.2 r hr).1
    have hst_r := (hdC.2.2.2.2.2.2.2.2.2.1 r hr.le).1
    have hst_r1 := (hdC.2.2.2.2.2.2.2.2.2.1 (r + 1) hr).1
    have hq1 : 1 ≤ phaseBase ((Hb C b).n + splitB) L := le_trans (by omega) (two_le_phaseBase _ L)
    have hTrace := DynSpanner.batchTrace_spec (normGraph_isValid hdC.1) hL hq1 (le_trans hdC.2.1 hM) hSp
      ((graphEq_batchIsValid (graphEq_symm (normGraph_graphEq _)) _).mp hdC.2.2.2.2.2.1) hdC.2.2.2.2.2.2.1
    have hlen_Us : (Us_ep C b).length = Δ := by simp [Us_ep]
    have hst_flat := (hTrace.1 r (le_trans hr.le hlen_Us.symm.le)).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hbase_m0 r hr.le, hres_eq, ht82.1, ← hst_flat, ← hst_r]
    · rw [hres_eq, ht82.2.1, ← hst_r1]
    · rw [hst_r, hst_r1, hres_eq]; exact ht82.2.2.2.1
    · intro eG heG eH heH hnotD
      rw [hst_r1] at heG heH
      rw [hres_eq] at hnotD
      rw [hst_r]
      exact ht82.2.2.2.2.2.1 eG heG eH heH hnotD
    · intro eG heG x hnotD
      rw [hst_r1] at heG ⊢
      rw [hres_eq] at hnotD
      rw [hst_r]
      exact ht82.2.2.2.2.2.2 eG heG x hnotD

end MinCostFlow.Chain

end
