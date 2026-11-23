module

public import MinCostFlow.Chain.Ordered.Theorem5_1Asymptotics
public import MinCostFlow.Chain.Ordered.RebuildCollapse
import MinCostFlow.Chain.Ordered.UpdatePreLoop
import MinCostFlow.Chain.Ordered.RenameFacts
import MinCostFlow.Chain.Ordered.CyclePathRep
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Small-`κ` Generalization of Lemma 6.5 and Theorem 5.1 for the Ordered Chain

Ordered-chain counterpart of `MinCostFlow/Chain/Theorem5_1SmallKappa.lean`: generalizes the shift
step (`alg2HiddenTrace_shiftAt_with`), inner loop (`alg2HiddenTrace_loopAt_with`), update step
(`alg2HiddenTrace_updateAt_with`), `lemma_6_5_at_with`, `alg2KappaAt_lower_of_params`, and
`theorem_5_1_param_at_of_collapsed_with` to any quality threshold `κ` with
`0 < κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle
open Theorem5_1Deps

/-- **Shift step for any `κ ≤ alg2KappaAt ...`**: if the cycle fails ratio `-(κ * α)`, it also
fails ratio `-(alg2KappaAt ... * α)`, so `alg2HiddenTrace_shiftAt` gives both the shift-count cap
and the advanced `Alg2HiddenTraceAt`. -/
lemma alg2HiddenTrace_shiftAt_with
    (nLast : ℕ) (κ : ℝ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    (hκ_le : κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ}
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBudget : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k)
    (hn : (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G t) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hNotGood : ¬ (st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) /
        st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) ≤
      -(κ * cfg.α)))
    (i : Fin (cfg.P.d + 1))
    (hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) st.passes = some i) :
    (st.chain.shiftCount i.val : ℝ) + 1 ≤
        gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain.rebuildCount i.val ∧
    let curB := if i.val < cfg.P.d then st.chain.bran i.val else st.branD
    let wrapped := (curB + 1) % cfg.P.k = 0
    let ch' := (algorithm1_shift cfg.T cfg.L cfg.P st.chain i.val).1
    let branD' := if i.val < cfg.P.d then 0 else (st.branD + 1) % cfg.P.k
    let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
      if i < j then 0
      else if j = i then (if wrapped then st.passes i + 1 else st.passes i)
      else st.passes j
    let st' := { st with chain := ch', branD := branD', passes := passes' }
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st') := by
  have hNotGoodAt : ¬ (st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) /
      st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) ≤
    -(alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast * cfg.α)) := by
    intro hle
    exact hNotGood (hle.trans (neg_le_neg (mul_le_mul_of_nonneg_right hκ_le hV.hα.le)))
  exact alg2HiddenTrace_shiftAt nLast hV tr hInv hBudget hFresh hExtG hExtℓ hExtg hℓ hg hBranD
    hn hLastBound hHS hNotGoodAt i hElig

/-- Well-founded trace and quality proof for ordered `algorithm2_loopWith cfg κ` for any
`κ ≤ alg2KappaAt ... nLast` under `HiddenStableAt` on `0 .. t`. -/
lemma alg2HiddenTrace_loopAt_with
    (nLast : ℕ) (κ : ℝ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    (hκ_le : κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ}
    (hm : (D.G t).m ≤ cfg.P.M₀) (hn : (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G t) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (st : Alg2State cfg) (lctOps : ℕ)
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k) :
    let res := algorithm2_loopWith cfg κ
      st.extG st.extToInt st.extg st.extℓ st.chain st.branD st.passes lctOps
    ∃ Δ, res.2.2.2.2 = some Δ ∧
      (D.G t).inner (D.g t) Δ / (D.G t).lnorm (D.ℓ t) Δ ≤ -(κ * cfg.α) ∧
      Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t
        { st with chain := res.1, branD := res.2.1, passes := res.2.2.1 }) := by
  let fc := algorithm1_findCycle st.chain
  let Δ_ext := liftEdgeFn st.extG st.extToInt fc.1
  by_cases hGood : st.extG.inner st.extg Δ_ext / st.extG.lnorm st.extℓ Δ_ext ≤ -(κ * cfg.α)
  · have hUnfold : algorithm2_loopWith cfg κ
        st.extG st.extToInt st.extg st.extℓ st.chain st.branD st.passes lctOps =
        (st.chain, st.branD, st.passes, lctOps + 2 * ((walkEdges fc.2.1 \ st.chain.toTreeChain.chainTree.E).card + 1),
          some Δ_ext) := by
      rw [algorithm2_loopWith]
      dsimp only
      split_ifs with hG
      · rfl
      · exact absurd hGood hG
    refine ⟨Δ_ext, ?_, ?_, ⟨by simpa [hUnfold] using tr⟩⟩
    · simp [hUnfold]
    · rw [← hExtG, ← hExtg, ← hExtℓ]; exact hGood
  · have hP0 := Game.passes_zero_lt cfg.gameParams tr.hv tr.hf tr.hmne (le_refl _)
    have hP0_st : (st.passes 0 : ℝ) < 2 * alg2PsiGame cfg.Ψ cfg.P.M₀ := by
      rw [← tr.hPassMatch 0]; exact hP0
    have hElig_ne : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) st.passes ≠ none := by
      intro hNone
      have hGE := findEligibleLevel_none_iff.mp hNone 0
      linarith
    obtain ⟨i, hElig⟩ := Option.ne_none_iff_exists'.mp hElig_ne
    have hShift := alg2HiddenTrace_shiftAt_with nLast κ hV hκ_le tr hInv hBud
      hFresh hExtG hExtℓ hExtg hℓ hg hBranD hn hLastBound hHS hGood i hElig
    dsimp only at hShift
    rcases hShift with ⟨hCap, ⟨tr'⟩⟩
    have hVNH := hV.toNoHidden
    have hℓR : LenInRange (max 0 cfg.Ψ) (st.chain.G 0) st.chain.ℓ := fun e he => by
      rw [hℓ, hExtℓ]
      exact lenInRange_of_hiddenStableAt (hHS t le_rfl) _ ((hExtG ▸ hFresh).hRight e he).2
    have hShP := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
      hV.hTP hV.hLP hVNH.hT hV.hL hV.hγM₀ hV.hγk hInv hℓR hBud i.val (Nat.le_of_lt_succ i.isLt)
    dsimp only at hShP
    rcases hShP with ⟨hInv', hBud', hG0', hℓ', hg', _, _, _, _⟩
    let curB := if i.val < cfg.P.d then st.chain.bran i.val else st.branD
    let wrapped := (curB + 1) % cfg.P.k = 0
    let ch' := (algorithm1_shift cfg.T cfg.L cfg.P st.chain i.val).1
    let branD' := if i.val < cfg.P.d then 0 else (st.branD + 1) % cfg.P.k
    let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
      if i < j then 0
      else if j = i then (if wrapped then st.passes i + 1 else st.passes i)
      else st.passes j
    let st' : Alg2State cfg := { st with chain := ch', branD := branD', passes := passes' }
    have hFresh' : FreshInv st'.extG (st'.chain.G 0) st'.extToInt st'.intToExt st'.nextFresh := by
      simpa [st', ch', hG0'] using hFresh
    have hBranD' : st'.branD < cfg.P.k := by
      dsimp only [st', branD']
      split_ifs
      · exact cfg.P.hk
      · exact Nat.mod_lt _ cfg.P.hk
    let offTree := (walkEdges fc.2.1 \ st.chain.toTreeChain.chainTree.E).card
    let lctOps' := lctOps + 2 * (offTree + 1)
    have hStepEq : algorithm2_loopWith cfg κ
        st.extG st.extToInt st.extg st.extℓ st.chain st.branD st.passes lctOps =
        algorithm2_loopWith cfg κ
          st'.extG st'.extToInt st'.extg st'.extℓ st'.chain st'.branD st'.passes lctOps' := by
      have dite_T : ∀ {P : Prop} [Decidable P] {α : Sort _} (h : P) (f : P → α) (g : ¬ P → α),
          dite P f g = f h := fun h _ _ => by split_ifs; rfl
      have dite_F : ∀ {P : Prop} [Decidable P] {α : Sort _} (h : ¬ P) (f : P → α) (g : ¬ P → α),
          dite P f g = g h := fun h _ _ => by split_ifs; rfl
      conv_lhs => rw [algorithm2_loopWith]
      dsimp only
      rw [dite_F (by exact hGood)]
      split
      · rename_i hN; rw [hElig] at hN; contradiction
      · rename_i i' hi'
        rw [hElig] at hi'
        obtain rfl := Option.some.inj hi'
        rw [dite_T (by exact hCap)]
    have ih := alg2HiddenTrace_loopAt_with
      nLast κ hV hκ_le hm hn hLastBound hHS st' lctOps' tr' hInv' hBud' hFresh'
      hExtG hExtℓ hExtg (by simpa [st', ch', hℓ'] using hℓ) (by simpa [st', ch', hg'] using hg)
      hBranD'
    simpa [hStepEq, st'] using ih
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step st.chain i hCap

/-- One full ordered `algorithm2_updateWith cfg κ` step preserves `Alg2HiddenTraceAt`, never fails
(`optΔ = some Δ`), and produces a direction `Δ` with ratio `≤ -(κ * cfg.α)`, for any
`κ ≤ alg2KappaAt ... nLast`. -/
lemma alg2HiddenTrace_updateAt_with
    (nLast : ℕ) (κ : ℝ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    (hκ_le : κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G (t + 1)) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS : ∀ s ≤ t + 1, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k) (η : ℝ) :
    let res := algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) η
    ∃ Δ, res.2 = some Δ ∧
      (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤ -(κ * cfg.α) ∧
      Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
        cfg D c_ext w_ext (t + 1) res.1) := by
  have hVNH := hV.toNoHidden
  have hPre := alg2HiddenTrace_update_preLoopAt nLast hVNH hHist hEdge ht1 hisUpd hm1 hn1 hLastBound
    (hHS (t + 1) (le_refl _)) tr hInv hBud hFresh hExtG hExtℓ hℓ
  obtain ⟨trPre⟩ := hPre
  have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht1
  have hG1Valid := (hHist.2.1 (t + 1) ht1).1
  have hℓ1Pos := (hHist.2.1 (t + 1) ht1).2
  have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
  let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  let extG' := tb.1
  let e2i' := tb.2.1
  let i2e' := tb.2.2.1
  let nf' := tb.2.2.2.1
  let U_int := tb.2.2.2.2
  have hTB_all := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
  dsimp only at hTB_all
  rcases hTB_all with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hEdge_int : ∀ u ∈ U_int, IsEdgeUpdate u :=
    translateBatch_isEdgeUpdate st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      (hEdge (t + 1) (Nat.succ_pos t) ht1)
  have hExtEq : extG' = D.G (t + 1) := by
    dsimp only [extG', tb]; rw [hExtG', hExtG]; simpa [Nat.add_sub_cancel] using hD.2.symm
  have hG0'Valid : ((st.chain.G 0).applyBatch U_int).IsValid :=
    (hFresh'.isValid_iff).mpr (by simpa [extG', tb, hExtEq] using hG1Valid)
  have hG0'm : ((st.chain.G 0).applyBatch U_int).m ≤ cfg.P.M₀ := by
    dsimp only [U_int, tb]; rw [hFresh'.m_eq]; simpa [extG', tb, hExtEq] using hm1
  have hG0'n : ((st.chain.G 0).applyBatch U_int).n ≤ cfg.N₀ := by
    dsimp only [U_int, tb]; rw [hFresh'.n_eq]; simpa [extG', tb, hExtEq] using hn1
  let g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
  let ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
  have hℓ_intPos : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, 0 < ℓ_int e' :=
    fun e' he' => hℓ1Pos _ (by rw [← hExtEq]; exact (hFresh'.hRight e' he').2)
  have hℓ_intR : LenInRange (max 0 cfg.Ψ) ((st.chain.G 0).applyBatch U_int) ℓ_int :=
    fun e' he' => lenInRange_of_hiddenStableAt (hHS (t + 1) le_rfl) _
      (by rw [← hExtEq]; exact (hFresh'.hRight e' he').2)
  have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, e' ∈ (st.chain.G 0).E →
      (∀ u' ∈ U_int, ¬ u'.Inserts e') → ℓ_int e' = st.chain.ℓ e' := by
    intro e' he' he'0 _
    have hi2e_eq : i2e' e' = st.intToExt e' := hi2e_old e' (hFresh.hLtFresh e' he'0)
    have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by
      rw [← hExtEq, ← hi2e_eq]; exact (hFresh'.hRight e' he').2
    have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
      intro s hs1 hs2 u hu hIns
      have hseq : s = t + 1 := by omega
      subst hseq
      have hge := hYesInsExt (st.intToExt e') (by rw [show tb.1 = D.G (t + 1) from hExtEq]; exact he_ext1)
        ⟨u, hu, hIns⟩
      change st.nextFresh ≤ e2i' (st.intToExt e') at hge
      have he2i'_eq : e2i' (st.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      have := hFresh.hLtFresh e' he'0
      omega
    have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 _ he_ext1 hNoIns_ext).2
    dsimp only [ℓ_int]
    rw [hi2e_eq, hℓ_same, hℓ, hExtℓ]; rfl
  have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hVNH.hT hV.hL hVNH.hNoReins hV.hγM₀ hV.hγk hInv hBud U_int g_int ℓ_int
    hBatch_int hNR_int hEdge_int hG0'Valid hG0'm hG0'n hℓ_intR hℓ_intStable
  dsimp only at hU
  rcases hU with ⟨hInv1, hBud1, _, _, _, _⟩
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hRen := update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain
    (D.g (t + 1)) (D.ℓ (t + 1)) hFresh'
  dsimp only at hRen
  let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
  let G₀' := (st.chain.G 0).applyBatch U_int
  let e2iN := level0E2I ren G₀' e2i'
  let i2eN := level0I2E ren G₀' i2e'
  let nfN := level0NF ren G₀' nf'
  let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let stPre : Alg2State cfg :=
    { st with
      chain := ch1, branD := bp1.1, passes := bp1.2,
      extG := extG', extToInt := e2iN, intToExt := i2eN, nextFresh := nfN,
      extℓ := D.ℓ (t + 1), extg := D.g (t + 1),
      largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
      updateCount := st.updateCount + 1 }
  have hFresh1 : FreshInv stPre.extG (stPre.chain.G 0) stPre.extToInt stPre.intToExt stPre.nextFresh :=
    hRen.1
  have hBranD1 : stPre.branD < cfg.P.k := by
    dsimp only [stPre, bp1]
    cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount <;> [exact hBranD; exact cfg.P.hk]
  let trPre' : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext (t + 1) stPre :=
    Theorem5_1Deps.alg2HiddenTrace_congr trPre rfl rfl rfl rfl rfl rfl
  obtain ⟨Δ, hSome, hRatio, ⟨trEnd⟩⟩ := alg2HiddenTrace_loopAt_with
    nLast κ hV hκ_le hm1 hn1 hLastBound hHS stPre
    (st.lctUpdateOps + (D.U (t + 1)).length) trPre' hInv1 hBud1 hFresh1 hExtEq rfl rfl
    hRen.2.1 hRen.2.2 hBranD1
  have hLoopUnfold : algorithm2_updateWith cfg κ
      st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) η =
      (let res := algorithm2_loopWith cfg κ
          extG' e2iN (D.g (t + 1)) (D.ℓ (t + 1))
          ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
       let inc := fun e => if e ∈ extG'.E then -(η / extG'.inner (D.g (t + 1)) Δ) * Δ e else 0
       ({ chain := res.1
          branD := res.2.1
          passes := res.2.2.1
          extG := extG'
          extToInt := e2iN
          intToExt := i2eN
          nextFresh := nfN
          extℓ := D.ℓ (t + 1)
          extg := D.g (t + 1)
          flow := fun e => st.flow e + inc e
          detectAccum := fun e => st.detectAccum e + |inc e|
          lctUpdateOps := res.2.2.2.1
          lctDetectOps := st.lctDetectOps
          largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
          updateCount := st.updateCount + 1 }, some Δ)) := by
    rw [algorithm2_updateWith]
    dsimp only
    change (match (algorithm2_loopWith cfg κ
        extG' e2iN (D.g (t + 1)) (D.ℓ (t + 1))
        ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)).2.2.2.2 with
      | none => _ | some _ => _) = _
    rw [hSome]
    rfl
  refine ⟨Δ, ?_, hRatio, ?_⟩
  · rw [hLoopUnfold]
  · refine ⟨Theorem5_1Deps.alg2HiddenTrace_congr trEnd ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> · rw [hLoopUnfold]

/-- Parameterized **Lemma 6.5** for ordered `algorithm2_dsWith cfg κ` at last-level vertex cap
`nLast`, for any threshold `κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast`. -/
theorem lemma_6_5_at_with
    (nLast : ℕ) (κ : ℝ) {cfg : Alg2Config} (hV : cfg.ValidOrd)
    (hκ_le : κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ t ≤ T, ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G t) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    {c_ext w_ext : ℕ → ℕ → ℝ}
    (hHS : ∀ t ≤ T, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext t) :
    let ds := algorithm2_dsWith cfg κ
    (∀ t ≤ T, Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext t (minRatioFailState ds D η isUpdate t))) ∧
    (∀ t ≤ T, ¬ minRatioFailFailedBefore ds D η isUpdate t) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir ds D η isUpdate t = some Δ ∧
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤ -(κ * cfg.α)) := by
  dsimp only
  set ds := algorithm2_dsWith cfg κ
  have hVNH := hV.toNoHidden
  have hUncond := algorithm2_uncond_preserves_with
    (cfg := cfg) (η := η) κ hVNH hHist hEdge (historyLengthsInRange_of_hiddenStable hHS)
    hmBound hnBound
  have hExtLG := alg2UncondInv_extℓ_extg_with (cfg := cfg) (η := η) κ hHist hEdge
  have hTraces : ∀ t ≤ T, Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext t (minRatioFailState ds D η isUpdate t)) := by
    intro t
    induction t with
    | zero =>
      intro ht0
      simpa [minRatioFailState, ds, algorithm2_dsWith] using
        alg2HiddenTrace_initAt nLast hVNH hHist hEdge (hmBound 0 ht0) (hnBound 0 ht0)
          (hLastBound 0 ht0) (hHS 0 ht0)
    | succ t ih =>
      intro ht1
      have ht_le : t ≤ T := Nat.le_of_succ_le ht1
      obtain ⟨tr⟩ := ih ht_le
      obtain ⟨hExtℓ, _⟩ := hExtLG t ht_le
      have hUI := hUncond.1 t ht_le
      rcases hUI with ⟨hInv, hBud, _, _, hFresh, hExtG, _, hChℓ, _, _, _, _, hBranD, _, _⟩
      by_cases hupd : isUpdate (t + 1) = true
      · obtain ⟨_, _, _, ⟨tr1⟩⟩ := alg2HiddenTrace_updateAt_with
          nLast κ hV hκ_le hHist hEdge ht1 hupd
          (hmBound (t + 1) ht1) (hnBound (t + 1) ht1) (hLastBound (t + 1) ht1)
          (fun s hs => hHS s (le_trans hs ht1)) tr hInv hBud hFresh hExtG hExtℓ hChℓ hBranD (η (t + 1))
        simpa [minRatioFailState, hupd, ds, algorithm2_dsWith] using ⟨tr1⟩
      · have hfalse : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
        have hChℓ_D : (minRatioFailState ds D η isUpdate t).chain.ℓ =
            fun e' => D.ℓ t ((minRatioFailState ds D η isUpdate t).intToExt e') := by
          rw [hChℓ]; ext e'; rw [hExtℓ]
        simpa [minRatioFailState, hupd, ds, algorithm2_dsWith] using
          alg2HiddenTrace_detectAt nLast hVNH hHist hEdge ht1 hfalse (hmBound (t + 1) ht1)
            (hnBound (t + 1) ht1) (hLastBound (t + 1) ht1) (hHS (t + 1) ht1) tr hInv hFresh
            hExtG hChℓ_D
  have hOpt : ∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir ds D η isUpdate t = some Δ ∧
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤ -(κ * cfg.α) := by
    intro t ht1 hupd
    have ht_le : t ≤ T := Nat.le_of_succ_le ht1
    obtain ⟨tr⟩ := hTraces t ht_le
    obtain ⟨hExtℓ, _⟩ := hExtLG t ht_le
    obtain ⟨hInv, hBud, _, _, hFresh, hExtG, _, hChℓ, _, _, _, _, hBranD, _, _⟩ := hUncond.1 t ht_le
    obtain ⟨Δ, hSome, hRatio, _⟩ := alg2HiddenTrace_updateAt_with
      nLast κ hV hκ_le hHist hEdge ht1 hupd
      (hmBound (t + 1) ht1) (hnBound (t + 1) ht1) (hLastBound (t + 1) ht1)
      (fun s hs => hHS s (le_trans hs ht1)) tr hInv hBud hFresh hExtG hExtℓ hChℓ hBranD (η (t + 1))
    have hCirc := hUncond.2.2.1 t ht1 hupd Δ hSome
    exact ⟨Δ, hSome, hCirc, hRatio⟩
  refine ⟨hTraces, fun t ht ⟨s, hs, hus, hnone⟩ => ?_, hOpt⟩
  obtain ⟨Δ, hSome, _, _⟩ := hOpt s (by omega) hus
  rw [hSome] at hnone
  simp at hnone

/-- Asymptotic positivity and `alg2KappaLower` bound on `alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last`,
independent of any query sequence `(D, η, isUpdate, T)`. -/
lemma alg2KappaAt_lower_of_params (n_last : ℕ) {cfg : Alg2Config} (hVNH : cfg.ValidOrdNoHidden)
    {β C_γ C_ψ C_N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last n_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2)) :
    let κ_at := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last
    0 < κ_at ∧ alg2KappaLower (15 + 5 * C_γ) ((1 + β) / 2) cfg.P.M₀ ≤ κ_at := by
  have hAsymp := theorem_5_1_asymptotic_exponents_at n_last hβ0 hβ1 cfg.P.hM₀ hD hVNH.hTP hVNH.hLP
    hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN
  dsimp only at hAsymp
  have hκ_pos : 0 < alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last :=
    Ordered.alg2KappaAt_pos hVNH n_last
  have hExp_eq : alg2KappaLower (15 + 5 * C_γ) ((1 + β) / 2) cfg.P.M₀ =
      (Real.exp ((15 + 5 * C_γ) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))⁻¹ := by
    simp only [alg2KappaLower, Real.exp_neg, mul_assoc]
  have hinv : (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last)⁻¹ ≤
      Real.exp ((15 + 5 * C_γ) * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)) := by
    simpa only [one_div, mul_assoc] using hAsymp.1
  exact ⟨hκ_pos, hExp_eq ▸ inv_le_of_inv_le₀ hκ_pos hinv⟩

/-- Generalization of `theorem_5_1_param_at_of_collapsed` to ordered `algorithm2_dsWithFailureWith cfg κ`
for any `κ` satisfying `0 < κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last`. -/
theorem theorem_5_1_param_at_of_collapsed_with
    (n_last : ℕ) (κ : ℝ)
    {cfg : Alg2Config} (hV : cfg.ValidOrd) (hκ_pos : 0 < κ)
    (hκ_le : κ ≤ alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last)
    {β C_γ C_ψ C_N : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hD : cfg.P.d = chosenD β cfg.P.M₀)
    (hCγ : 0 ≤ C_γ) (hCψ : 0 ≤ C_ψ) (hCN : 1 ≤ C_N)
    (hγℓ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hγr : cfg.TP.γ_r (cfg.P.M₀ ^ 2) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσT : cfg.TP.σ cfg.P.k cfg.N₀ ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσL : cfg.LP.σ_last n_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hσM : max 0 (cfg.σ_mwu cfg.N₀) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcT : cfg.TP.c_T ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hcL : cfg.LP.c_last ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hΨ : alg2PsiGame cfg.Ψ cfg.P.M₀ ≤
      Real.exp (C_ψ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ β *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogF : (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 3) ≤
      Real.exp (C_γ * (Real.log ((cfg.P.M₀ : ℝ) + 2)) ^ ((1 + β) / 2) *
        Real.log (Real.log ((cfg.P.M₀ : ℝ) + 2) + 2)))
    (hlogN : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤ C_N * Real.log ((cfg.P.M₀ : ℝ) + 2))
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ t ≤ T, ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G t) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ n_last)
    (hColl :
      let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
      let Q_upd := alg2UpdateQueries D isUpdate T
      let K_upd := alg2UpdateCount isUpdate T
      let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
      let K_det := alg2DetectCount isUpdate T
      let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
      ((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        alg2CollapsedFactor cfg * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          alg2CollapsedFactor cfg * Q_tot)) :
    let κ_at := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ n_last
    let A := algorithm2_dsWithFailureWith cfg κ
    let a := (1 + β) / 2
    let C_κ := 15 + 5 * C_γ
    let C_rt := theorem51RuntimeConstant C_γ C_ψ C_N
    let f := alg2TimeFactor C_rt a
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)
    (0 < κ ∧ alg2KappaLower C_κ a cfg.P.M₀ ≤ κ_at) ∧
    (Filter.Tendsto (fun m : ℕ => Real.log (f m) / Real.log (m : ℝ)) Filter.atTop (nhds 0) ∧
      ∀ δ : ℝ, 0 < δ → ∃ B : ℝ, 1 ≤ B ∧ ∀ m : ℕ, 1 ≤ m → f m ≤ B * (m : ℝ) ^ δ) ∧
    (∀ t ≤ T,
      A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) =
        (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).flow ∧
      ∀ e ∈ (D.G t).E,
        A.query (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t) e =
          MinCostFlow.IPM.minRatioFlow A.eraseFailure D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      (D.G (t + 1)).IsCirculation
          (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ∧
      (D.HiddenStable (t + 1) cfg.α cfg.Ψ →
        (MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t).isSome = true ∧
        (D.G (t + 1)).inner (D.g (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) /
          (D.G (t + 1)).lnorm (D.ℓ (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.eraseFailure D η isUpdate t) ≤ -(κ * cfg.α)) ∧
      ∀ Δ, MinCostFlow.IPM.minRatioFailureDirection A D η isUpdate t = some Δ →
        let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
        let T_tree := stNext.extTree
        (D.G (t + 1)).IsSubgraph T_tree ∧
        T_tree.IsForest ∧
        (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
          (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
        ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
          T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
        ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
          (offTreeEdges.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
          (treePaths.length : ℝ) ≤ f cfg.P.M₀ ∧
          (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
          ∀ e : ℕ, Δ e =
            (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
            (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      (A.detect (MinCostFlow.IPM.minRatioState A.eraseFailure D η isUpdate t)).1 =
        MinCostFlow.IPM.minRatioDetectSet A.eraseFailure D η isUpdate cfg.ε t) ∧
    (D.HiddenStable T cfg.α cfg.Ψ →
      ¬ minRatioFailFailedBefore (algorithm2_dsWith cfg κ) D η isUpdate T) ∧
    (alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤ f cfg.P.M₀ * ((Q_det : ℝ) + (K_det : ℝ)) ∧
      st.chain.rebuildCount cfg.P.d = 0 ∧
      st.chain.rebuildCount 0 + st.chain.updCount 0 ≤ Q_upd ∧
      (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
      (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
      (∀ i : Fin (cfg.P.d + 1),
        (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
      (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
        Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        st.largeBatchEnc = 0)) ∧
    (((st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        f cfg.P.M₀ * Q_tot +
          40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2)) ∧
      ((∀ s, 1 ≤ s → s ≤ T → isUpdate s = true → (D.U s).length ≤ cfg.P.M₀) →
        (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
          f cfg.P.M₀ * Q_tot)) := by
  have hVNH := hV.toNoHidden
  have hUnc := algorithm2_uncond_preserves_with
    (cfg := cfg) (η := η) κ hVNH hHist hEdge hLen hmBound hnBound
  have hComp := theorem_5_1_uncond_complexity_with
    (cfg := cfg) (η := η) κ hVNH hHist hEdge hLen hmBound hnBound
  dsimp only at hComp
  have hAsymp := theorem_5_1_asymptotic_exponents_at n_last hβ0 hβ1 cfg.P.hM₀ hD hV.hTP hV.hLP
    hCγ hCψ hCN hγℓ hγr hσT hσL hσM hcT hcL hΨ hlogF hlogN
  dsimp only at hAsymp
  have hκ_lo := (alg2KappaAt_lower_of_params n_last hVNH hβ0 hβ1 hD hCγ hCψ hCN hγℓ hγr
    hσT hσL hσM hcT hcL hΨ hlogF hlogN).2
  have hf_col : alg2CollapsedFactor cfg ≤
      alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ := by
    simpa only [alg2TimeFactor, mul_assoc] using hAsymp.2
  have ha0 : (0 : ℝ) ≤ (1 + β) / 2 := by linarith
  have ha1 : (1 + β) / 2 < 1 := by linarith
  refine ⟨⟨hκ_pos, hκ_lo⟩,
    ⟨tendsto_log_alg2TimeFactor_div_log _ ha0 ha1,
      fun δ hδ => alg2TimeFactor_le_rpow ha0 ha1 hδ⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨?_, fun e he => ?_⟩
    · rw [algorithm2_eraseFailure_state_eq_with]
      rfl
    · rw [algorithm2_eraseFailure_state_eq_with, algorithm2_eraseFailure_flow_eq_with]
      exact hUnc.2.1 t ht e he
  · intro t ht1 hupd
    have hdir_eq : MinCostFlow.IPM.minRatioDirection (algorithm2_dsWithFailureWith cfg κ).eraseFailure
          D η isUpdate t =
        minRatioFailDirection (algorithm2_dsWith cfg κ) D η isUpdate t := by
      unfold MinCostFlow.IPM.minRatioDirection minRatioFailDirection
      change ((algorithm2_dsWithFailureWith cfg κ).update
        (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)
        (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).2.getD (fun _ => 0) = _
      rw [algorithm2_eraseFailure_state_eq_with]
      rfl
    have hCirc : (D.G (t + 1)).IsCirculation
        (MinCostFlow.IPM.minRatioDirection (algorithm2_dsWithFailureWith cfg κ).eraseFailure
          D η isUpdate t) := by
      rw [hdir_eq]
      unfold minRatioFailDirection
      cases hopt : minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t with
      | none => exact fun _ => by simp [MGraph.demand]
      | some Δ => exact hUnc.2.2.1 t ht1 hupd Δ hopt
    refine ⟨hCirc, fun ⟨c_ext, w_ext, hHS⟩ => ?_, fun Δ hFailSome => ?_⟩
    · have hPref := lemma_6_5_at_with
        n_last κ (cfg := cfg) (η := η) hV hκ_le
        (hHist.mono D isUpdate T (t + 1) ht1) (HistoryEdgeOnly.of_le hEdge ht1)
        (fun s hs => hmBound s (le_trans hs ht1))
        (fun s hs => hnBound s (le_trans hs ht1))
        (fun s hs _ _ _ _ hIc hFc => hLastBound s (le_trans hs ht1) hIc hFc)
        hHS
      obtain ⟨Δ, hSome, _, hRatio⟩ := hPref.2.2 t (le_refl _) hupd
      have hSome' : MinCostFlow.IPM.minRatioFailureDirection (algorithm2_dsWithFailureWith cfg κ)
          D η isUpdate t = some Δ := by
        rw [algorithm2_failureDirection_eq_with]
        simpa [minRatioFailOptDir] using hSome
      have hdir_Δ : MinCostFlow.IPM.minRatioDirection (algorithm2_dsWithFailureWith cfg κ).eraseFailure
          D η isUpdate t = Δ :=
        MinCostFlow.IPM.minRatioDirection_of_success (algorithm2_dsWithFailureWith cfg κ) D η isUpdate t Δ hSome'
      refine ⟨?_, ?_⟩
      · rw [hSome']; rfl
      · rw [hdir_Δ]; exact hRatio
    · have hOptSome : minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = some Δ := by
        rw [← algorithm2_failureDirection_eq_with]
        exact hFailSome
      have hRep := alg2_update_optDir_cycle_rep_with κ hVNH hHist hEdge hLen hmBound hnBound t ht1 hupd Δ hOptSome
      rcases hRep with ⟨hSubG, hFor, hConn, hSpan, off, tp, hoffLen, hoffE, htpLen, htpConn, hEqΔ⟩
      have hCeilLe := two_ceil_γℓ_succ_le_alg2TimeFactor hβ0 hβ1 cfg.P.hM₀ hV.hTP hCγ hCψ hCN hγℓ
      have hoff_f : (off.length : ℝ) ≤
          alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ := by
        have h1 : (off.length : ℝ) ≤ (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1 := by exact_mod_cast hoffLen
        have h2 : (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1 ≤
            2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) := by linarith
        exact le_trans (le_trans h1 h2) hCeilLe
      have htp_f : (tp.length : ℝ) ≤
          alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ := by
        have h1 : (tp.length : ℝ) ≤ 2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 1) := by
          exact_mod_cast htpLen
        exact le_trans h1 hCeilLe
      exact ⟨hSubG, hFor, hConn, hSpan, off, tp, hoff_f, hoffE, htp_f, htpConn, hEqΔ⟩
  · intro t ht1 hfalse
    rw [algorithm2_eraseFailure_state_eq_with, algorithm2_eraseFailure_detectSet_eq_with]
    exact hUnc.2.2.2 t ht1 hfalse
  · intro ⟨c_ext, w_ext, hHS⟩
    exact (lemma_6_5_at_with
      n_last κ hV hκ_le hHist hEdge hmBound hnBound hLastBound hHS).2.1 T (le_refl T)
  · have hDet1 := alg2Detect_work_le_with (η := η) κ hVNH hHist hEdge hLen hmBound hnBound
    have hlog_le : 1 + Real.log ((cfg.N₀ : ℝ) + 2) ≤
        alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ :=
      le_trans (one_add_log_le_alg2CollapsedFactor cfg hVNH) hf_col
    have hQK_nn : (0 : ℝ) ≤ (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
        (alg2DetectCount isUpdate T : ℝ) := by positivity
    have hDetF : alg2LctAmortizedCharge cfg.N₀
        (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).lctDetectOps ≤
        alg2TimeFactor (theorem51RuntimeConstant C_γ C_ψ C_N) ((1 + β) / 2) cfg.P.M₀ *
          ((alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) :=
      le_trans hDet1 (mul_le_mul_of_nonneg_right hlog_le hQK_nn)
    exact ⟨hDetF,
      alg2_rebuildCount_last_eq_zero_with cfg κ D η isUpdate T,
      alg2_rebuildCount_zero_le_upd_with cfg κ D η isUpdate T,
      hComp.1, hComp.2.1, hComp.2.2.1, hComp.2.2.2.2.2.1,
      fun hSmall => largeBatchEnc_eq_zero_of_le_M₀_with κ hVNH hHist hEdge hLen hmBound hnBound hSmall⟩
  · dsimp only at hColl
    have hQtot_nn : (0 : ℝ) ≤ (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
        (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
        (alg2DetectCount isUpdate T : ℝ) := by positivity
    have hMul := mul_le_mul_of_nonneg_right hf_col hQtot_nn
    refine ⟨by linarith [hColl.1, hMul], fun hSmall => le_trans (hColl.2 hSmall) hMul⟩

end MinCostFlow.Chain.Ordered
