module

public import MinCostFlow.Chain.Ordered.InitPreserves
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bookkeeping transport of `ChainInv` for Algorithm 1 with Orders

This file proves `chainInv_with_bookkeeping`, which transports `Ordered.ChainInv` across pure
bookkeeping updates. The rebuild inside `Update` is handled in `UpdateSteps.lean` through
`rebuildSuffix_preserves_noHidden`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section OpPreservation

/-- Transport `ChainInv` to another `ChainState` agreeing on all structural and cost-tracking
fields, given the new `rebuildCount` inequality. -/
lemma chainInv_with_bookkeeping {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams} {P : ChainParams} {N₀ : ℕ}
    {st st' : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    (hG : st'.G = st.G) (hsc : st'.scState = st.scState)
    (hCRest : st'.curRestarts = st.curRestarts) (hbran : st'.bran = st.bran)
    (hupd : st'.updCount = st.updCount) (hrec : st'.recUpdates = st.recUpdates)
    (hcfwd : st'.curFwd = st.curFwd)
    (hlk : st'.lastK = st.lastK) (hlLSF : st'.lastLSFs = st.lastLSFs) (hlBran : st'.lastBran = st.lastBran)
    (hℓ : st'.ℓ = st.ℓ) (hg : st'.g = st.g)
    (hLastR : st'.curLastRebuilds = st.curLastRebuilds) (hLastC : st'.curLastCost = st.curLastCost)
    (hEnc : st'.curEnc = st.curEnc) (hDec : st'.curDecUpdates = st.curDecUpdates)
    (hLastT : st'.curLastTreeUpdates = st.curLastTreeUpdates)
    (hLvlM : st'.lvlM = st.lvlM) (hN0 : st'.N₀ = st.N₀)
    (hReb : ∀ i < P.d,
      (st'.rebuildCount i : ℝ) * ((intRebuildThreshold P N₀ i : ℝ) + 1) +
        (st'.updCount i : ℝ) ≤ (st'.recUpdates i : ℝ)) :
    ChainInv T L TP LP P N₀ st' := by
  have hToTC : st'.toTreeChain = st.toTreeChain := by
    simp [ChainState.toTreeChain, hG, hsc, hbran, hlk, hlLSF, hlBran]
  have hOrdEq : ∀ i, st'.levelOrd i = st.levelOrd i := fun i => by
    simp [ChainState.levelOrd, chainLevelOrd, hG, hsc, hbran]
  have hHist' : ∀ i < P.d, Nonempty (LevelHistory T TP P N₀ st' i) := by
    intro i hi
    obtain ⟨H⟩ := hInv.hHist i hi
    exact ⟨{
      D := H.D, len := H.len, s₀ := H.s₀, hs₀ := H.hs₀,
      restarts := H.restarts, hRestartsLt := H.hRestartsLt,
      hRestartsCount := by rw [hCRest]; exact H.hRestartsCount,
      hS0Fresh := by rw [hbran]; exact H.hS0Fresh,
      hNoRestartAfterS0 := by rw [hbran]; exact H.hNoRestartAfterS0,
      hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
      hEndG := by rw [hG]; exact H.hEndG,
      hEndℓ := fun e he => by
        have he' : e ∈ (st.G i).E := by rwa [← hG]
        rw [hToTC, hℓ]; exact H.hEndℓ e he'
      hEndg := by rw [hToTC, hg]; exact H.hEndg
      hUpd := by rw [hupd]; exact H.hUpd
      hThresh := by rw [hupd]; exact H.hThresh
      hInitMBound := H.hInitMBound
      hInitNBound := H.hInitNBound
      ord := H.ord
      hOrd := H.hOrd
      hEndOrd := by rw [hOrdEq]; exact H.hEndOrd
      hRun := by rw [hsc]; exact H.hRun
      hOK := H.hOK
      branchSeq := H.branchSeq
      hBranch := H.hBranch
      hBranchTail := by rw [hbran]; exact H.hBranchTail
      hWinFwdBound := H.hWinFwdBound
      hCurFwdEq := by rw [hcfwd]; exact H.hCurFwdEq
      hDecEq := by rw [hDec, hsc, hbran]; exact H.hDecEq
      hEnc0Le := by rw [hEnc]; exact H.hEnc0Le
      hEncLe := fun h1 => by rw [hEnc, hbran]; exact H.hEncLe h1 }⟩
  have hRecFwd' : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) st' := by
    intro i hi
    rw [hcfwd, hupd, hrec]
    exact hInv.hRecFwd i hi
  refine ⟨hG ▸ hInv.hG0Valid, hG ▸ hInv.hG0m, hG ▸ hInv.hG0n, (hG ▸ hℓ ▸ hInv.hℓPos),
    hlk ▸ hInv.hLastK, hlk ▸ hlBran ▸ hInv.hLastBran,
    fun j hj => ?_, hG ▸ hlLSF ▸ hlk ▸ hInv.hLastMWU, hG ▸ hlLSF ▸ hlk ▸ hInv.hLastSpans,
    hbran ▸ hInv.hBran, hG ▸ hsc ▸ hbran ▸ hInv.hGSucc, hHist', hReb, hRecFwd',
    hEnc ▸ hupd ▸ hInv.hEnc0, fun hd => ?_, hLvlM ▸ hInv.hLvlM, hN0 ▸ hInv.hN0⟩
  · have h := hInv.hLastHolds j (hlk ▸ hj)
    rw [hG, hlLSF, hToTC, hℓ]; exact h
  · obtain ⟨⟨H, hReb⟩, hCost, hTree⟩ := hInv.hLastCap hd
    have hG0n : (st'.G 0).n = (st.G 0).n := by rw [hG]
    let H' : LevelHistory T TP P N₀ st' (P.d - 1) :=
      { H with
        hRestartsCount := by rw [hCRest]; exact H.hRestartsCount
        hS0Fresh := by rw [hbran]; exact H.hS0Fresh
        hNoRestartAfterS0 := by rw [hbran]; exact H.hNoRestartAfterS0
        hEndG := by rw [hG]; exact H.hEndG
        hEndℓ := fun e he => by rw [hToTC, hℓ]; exact H.hEndℓ e (hG ▸ he)
        hEndg := by rw [hToTC, hg]; exact H.hEndg
        hUpd := by rw [hupd]; exact H.hUpd
        hThresh := by rw [hupd]; exact H.hThresh
        hEndOrd := by rw [hOrdEq]; exact H.hEndOrd
        hRun := by rw [hsc]; exact H.hRun
        hBranchTail := by rw [hbran]; exact H.hBranchTail
        hCurFwdEq := by rw [hcfwd]; exact H.hCurFwdEq
        hDecEq := by rw [hDec, hsc, hbran]; exact H.hDecEq
        hEnc0Le := by rw [hEnc]; exact H.hEnc0Le
        hEncLe := fun h1 => by rw [hEnc, hbran]; exact H.hEncLe h1 }
    have hReb' : st'.curLastRebuilds ≤ (Finset.Icc (H'.s₀ + 1) H'.len).sum fun s =>
        ((T.runOrdAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H'.D H'.ord H'.restarts s).2
          (st'.bran (P.d - 1))).length := by
      rw [hLastR, hbran]; exact hReb
    refine ⟨⟨H', hReb'⟩, ?_, ?_⟩
    · rw [hLastC, hLastR, hG0n]; exact hCost
    · rw [hLastT, hLastR]; exact hTree

end OpPreservation

end MinCostFlow.Chain.Ordered
