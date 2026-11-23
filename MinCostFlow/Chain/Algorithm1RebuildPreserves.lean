module

public import MinCostFlow.Chain.Algorithm1InitPreserves
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# `algorithm1_rebuild` Preservation (Algorithm 1 Proofs Helpers)

Split from `MinCostFlow.Chain.Algorithm1Proofs`: `chainInv_with_bookkeeping` and `rebuild_preserves*`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section OpPreservation

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
      hRun := by rw [hsc]; exact H.hRun
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
        hRun := by rw [hsc]; exact H.hRun
        hBranchTail := by rw [hbran]; exact H.hBranchTail
        hCurFwdEq := by rw [hcfwd]; exact H.hCurFwdEq
        hDecEq := by rw [hDec, hsc, hbran]; exact H.hDecEq
        hEnc0Le := by rw [hEnc]; exact H.hEnc0Le
        hEncLe := fun h1 => by rw [hEnc, hbran]; exact H.hEncLe h1 }
    have hReb' : st'.curLastRebuilds ≤ (Finset.Icc (H'.s₀ + 1) H'.len).sum fun s =>
        ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H'.D H'.restarts s).2
          (st'.bran (P.d - 1))).length := by
      rw [hLastR, hbran]; exact hReb
    refine ⟨⟨H', hReb'⟩, ?_, ?_⟩
    · rw [hLastC, hLastR, hG0n]; exact hCost
    · rw [hLastT, hLastR]; exact hTree

lemma rebuild_preserves_with_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st)
    {overflow extraOverflow : ℝ} (hBudget : ChainBudgetInvWith TP LP N₀ st overflow)
    (i₀ : ℕ) (hi₀ : i₀ ≤ P.d) (Gnew : MGraph) (extraEnc : ℕ)
    (hGi0 : if i₀ = 0 then
      Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧ (∀ e ∈ Gnew.E, 0 < st.ℓ e)
      else Gnew = st.G i₀)
    (hTrig : i₀ < P.d →
      ((intRebuildThreshold P N₀ i₀ : ℝ) + 1) ≤ (st.updCount i₀ : ℝ))
    (hExtra : (extraEnc : ℝ) ≤ (if i₀ = 0 then extraEncCap P else 0) + extraOverflow) :
    let (st', changes) := algorithm1_rebuild T L P st i₀ Gnew extraEnc
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInvWith TP LP N₀ st' (overflow + extraOverflow) ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    st'.ℓ = st.ℓ ∧
    st'.g = st.g ∧
    st'.shiftCount = st.shiftCount ∧
    st'.rebuildCount = (fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j) ∧
    applyTreeChanges st.toTreeChain.chainTree.E changes = st'.toTreeChain.chainTree.E ∧
    st'.totalTreeUpdates = st.totalTreeUpdates + changes.length := by
  have hCostB := hInv.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hLevB := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInv
  by_cases hlt : i₀ < P.d
  · dsimp only [algorithm1_rebuild]
    rw [dite_eq_left_iff.mpr fun h => absurd hlt h]
    set G0 := fun j => if j = i₀ then Gnew else st.G j
    set res := rebuildSuffix T L P st.lvlM st.N₀ st.ℓ st.g (P.d - i₀) i₀
      G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
    set retiredTool := (Finset.Ico i₀ P.d).sum fun j => T.cost (st.scState j) + st.curEnc j
    set retiredDec := (Finset.Ico i₀ P.d).sum fun j => st.curDecUpdates j
    set oldE := st.toTreeChain.chainTree.E
    set stMidCore : ChainState T P :=
      { st with
        G := res.1, scState := res.2.1,
        curRestarts := fun j => if i₀ ≤ j ∧ j < P.d then 0 else st.curRestarts j,
        bran := res.2.2.1, updCount := res.2.2.2.1,
        curFwd := res.2.2.2.2.2.2.1,
        lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
        curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
        curEnc := res.2.2.2.2.1, curDecUpdates := res.2.2.2.2.2.1,
        curLastTreeUpdates := 0 }
    have hG0Valid : (G0 0).IsValid := by
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte]; exact hGi.1
      · have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0; simp only [G0, hne0, ↓reduceIte]; exact hInv.hG0Valid
    have hG0m : (G0 0).m ≤ P.M₀ := by
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte]; exact hGi.2.1
      · have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0; simp only [G0, hne0, ↓reduceIte]; exact hInv.hG0m
    have hG0n : (G0 0).n ≤ N₀ := by
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte]; exact hGi.2.2.1
      · have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0; simp only [G0, hne0, ↓reduceIte]; exact hInv.hG0n
    have hℓ0 : ∀ e ∈ (G0 0).E, 0 < st.ℓ e := by
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte]; exact hGi.2.2.2.2
      · have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0; simp only [G0, hne0, ↓reduceIte]; exact hInv.hℓPos
    have hGi0Valid : (G0 i₀).IsValid := by
      simp only [G0, ↓reduceIte]
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        exact hGi.1
      · have hGeq : Gnew = st.G i₀ := by simpa [h0] using hGi0
        rw [hGeq]; exact (hLevB i₀ hi₀).1
    have hGi0V : (G0 i₀).V ⊆ (G0 0).V := by
      by_cases h0 : i₀ = 0
      · subst h0; exact Finset.Subset.refl _
      · have hGeq : Gnew = st.G i₀ := by simpa [h0] using hGi0
        have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0
        simp only [G0, ↓reduceIte, hne0, hGeq]
        exact (hLevB i₀ hi₀).2.1
    have hGi0m : ((G0 i₀).m : ℝ) ≤ (levelM TP P i₀ : ℝ) := by
      simp only [G0, ↓reduceIte]
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0
        have hm0 : (Gnew.m : ℝ) ≤ P.M₀ := by exact_mod_cast hGi.2.1
        have hM0_le : (P.M₀ : ℝ) ≤ (levelM TP P 0 : ℝ) := by
          have hγ1 := hTP.2.2.1 (P.M₀ ^ 2)
          have hmul : (P.M₀ : ℝ) ≤ (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) := by
            nlinarith [show (0 : ℝ) ≤ P.M₀ from Nat.cast_nonneg _]
          have hceil : (P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ 0 ≤
              (levelM TP P 0 : ℝ) := Nat.le_ceil _
          simp only [pow_zero, mul_one] at hceil
          linarith
        exact le_trans hm0 hM0_le
      · have hGeq : Gnew = st.G i₀ := by simpa [h0] using hGi0
        rw [hGeq]; exact (hLevB i₀ hi₀).2.2.1
    have hℓ_i0 : ∀ e ∈ (G0 i₀).E,
        0 < (mkPartialChain T P G0 st.scState st.bran (G0 i₀)).chainLen st.ℓ i₀ e := by
      intro e he
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte] at he; exact hGi.2.2.2.2 e he
      · have hGeq : Gnew = st.G i₀ := by simpa [h0] using hGi0
        have heq : (mkPartialChain T P G0 st.scState st.bran (G0 i₀)).chainLen st.ℓ i₀ =
            st.toTreeChain.chainLen st.ℓ i₀ := by
          apply chainLen_congr_lt st.ℓ i₀ (fun j hj => by
            dsimp only [mkPartialChain, ChainState.toTreeChain]
            simp [G0, show j ≠ i₀ by omega])
          · intro j hj
            have hjlt : j < P.d := by omega
            have h1 : (mkPartialChain T P G0 st.scState st.bran (G0 i₀)).activeLSF j =
                T.lsfs (st.scState j) (st.bran j) := by
              unfold TreeChain.activeLSF
              exact ite_eq_left_iff.mpr fun h => absurd (by simpa [mkPartialChain] using hjlt) h
            have h2 : st.toTreeChain.activeLSF j = T.lsfs (st.scState j) (st.bran j) := by
              unfold TreeChain.activeLSF
              exact ite_eq_left_iff.mpr fun h => absurd (by simpa [ChainState.toTreeChain] using hjlt) h
            rw [h1, h2]
        rw [heq]
        simp only [G0, ↓reduceIte, hGeq] at he
        exact (hLevB i₀ hi₀).2.2.2.1 e he
    let stTmp : ChainState T P := { st with G := G0 }
    have hPreHist : ∀ j < i₀, Nonempty (LevelHistory T TP P N₀ stTmp j) := by
      intro j hj
      obtain ⟨H⟩ := hInv.hHist j (lt_trans hj hlt)
      have hjne : j ≠ i₀ := Nat.ne_of_lt hj
      refine ⟨{
        D := H.D, len := H.len, s₀ := H.s₀, hs₀ := H.hs₀,
        restarts := H.restarts, hRestartsLt := H.hRestartsLt,
        hRestartsCount := H.hRestartsCount,
        hS0Fresh := H.hS0Fresh, hNoRestartAfterS0 := H.hNoRestartAfterS0,
        hG0 := H.hG0, hD := H.hD, hLen := H.hLen, hℓPos := H.hℓPos,
        hEndG := by simp [stTmp, G0, hjne]; exact H.hEndG,
        hEndℓ := fun e he => by
          have he' : e ∈ (st.G j).E := by simpa [stTmp, G0, hjne] using he
          have hCL := chainLen_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := st.toTreeChain) st.ℓ j
            (fun m hm => by
              dsimp only [stTmp, ChainState.toTreeChain]
              simp [G0, show m ≠ i₀ by omega])
            (fun _ _ => rfl)
          change H.D.ℓ H.len e = _
          rw [hCL]; exact H.hEndℓ e he',
        hEndg := by
          have hCG := chainGrad_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := st.toTreeChain) st.g j
            (fun m hm => by
              dsimp only [stTmp, ChainState.toTreeChain]
              simp [G0, show m ≠ i₀ by omega])
            (fun _ _ => rfl)
          rw [hCG]; exact H.hEndg,
        hUpd := H.hUpd, hThresh := H.hThresh,
        hInitMBound := H.hInitMBound, hInitNBound := H.hInitNBound, hRun := H.hRun,
        branchSeq := H.branchSeq, hBranch := H.hBranch,
        hBranchTail := H.hBranchTail, hWinFwdBound := H.hWinFwdBound,
        hCurFwdEq := H.hCurFwdEq,
        hDecEq := H.hDecEq, hEnc0Le := H.hEnc0Le, hEncLe := H.hEncLe }⟩
    have hPreGSucc : ∀ j < i₀, G0 (j + 1) = T.S (st.scState j) (st.bran j) := by
      intro j hj
      by_cases h1 : j + 1 = i₀
      · have hne0 : i₀ ≠ 0 := by omega
        have hGeq : Gnew = st.G i₀ := by simpa [hne0] using hGi0
        simp only [G0, h1, ↓reduceIte, hGeq]
        rw [← h1]
        exact hInv.hGSucc j (lt_trans hj hlt)
      · simp only [G0, h1, ↓reduceIte]; exact hInv.hGSucc j (lt_trans hj hlt)
    have hPreRecReb : ∀ j < P.d,
        (st.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
          (if j < i₀ then (st.updCount j : ℝ) else 0) ≤ (st.recUpdates j : ℝ) := by
      intro j hj
      split_ifs
      · exact hInv.hRecRebuild j hj
      · linarith [hInv.hRecRebuild j hj, show (0 : ℝ) ≤ st.updCount j from Nat.cast_nonneg _]
    have hInvMid : ChainInv T L TP LP P N₀ stMidCore :=
      rebuildSuffix_preserves_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk hlt
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
        hG0Valid hGi0Valid hGi0V hGi0m hG0m hG0n hℓ0 hℓ_i0 hPreHist
        (fun j hj => hInv.hBran j (lt_trans hj hlt)) hPreGSucc hPreRecReb hInv.hRecFwd
        (fun _ => hInv.hEnc0) hInv.hLvlM hInv.hN0 rfl
    set stMid : ChainState T P :=
      { stMidCore with
        rebuildCount := fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j
        closedRuntime := st.closedRuntime + retiredTool + st.curLastCost + extraEnc
        closedTreeUpdates := st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates }
    set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    set stFinal : ChainState T P := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk st.ℓ st.g (P.d - i₀) i₀
      G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd
      (by omega) hGi0Valid hGi0V hG0n hGi0m hℓ_i0
    have hResEq : res = rebuildSuffix T L P (levelM TP P) N₀ st.ℓ st.g (P.d - i₀) i₀
        G0 st.scState st.bran st.updCount st.curEnc st.curDecUpdates st.curFwd := by
      dsimp only [res]; rw [hInv.hLvlM, hInv.hN0]
    rw [← hResEq] at hRS
    have hInvFinal : ChainInv T L TP LP P N₀ stFinal :=
      chainInv_with_bookkeeping hInvMid rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun j hj => by
          by_cases hjeq : j = i₀
          · subst hjeq
            have hu0 : stFinal.updCount j = 0 := (hRS.2.2.1 j (le_refl j) hlt).2.1
            have hreb1 : stFinal.rebuildCount j = st.rebuildCount j + 1 := by
              simp [stFinal, stMid]
            have hrec : stFinal.recUpdates j = st.recUpdates j := rfl
            rw [hreb1, hu0, hrec]
            push_cast
            nlinarith [hTrig hlt, hInv.hRecRebuild j hlt]
          · have hrebEq : stFinal.rebuildCount j = stMidCore.rebuildCount j := by
              simp [stFinal, stMid, stMidCore, hjeq]
            rw [hrebEq]
            exact hInvMid.hRecRebuild j hj)
    have hn_le : (st.G 0).n ≤ (stFinal.G 0).n := by
      have hG0Final : stFinal.G 0 = G0 0 := hRS.1 0 (Nat.zero_le _)
      rw [hG0Final]
      by_cases h0 : i₀ = 0
      · have hGi : Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧
            (∀ e ∈ Gnew.E, 0 < st.ℓ e) := by simpa [h0] using hGi0
        subst h0; simp only [G0, ↓reduceIte]; exact Finset.card_le_card hGi.2.2.2.1
      · have hne0 : (0 : ℕ) ≠ i₀ := Ne.symm h0; simp only [G0, hne0, ↓reduceIte]; exact le_refl _
    have hPreActive : ∀ j < i₀,
        (st.toTreeChain.activeLSF j).F.F.E = (stMidCore.toTreeChain.activeLSF j).F.F.E := by
      intro j hj
      rcases hRS.2.1 j hj with ⟨a1, a2, _⟩
      have hjlt : j < P.d := lt_trans hj hlt
      simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjlt, ↓reduceIte]
      change (T.lsfs (st.scState j) (st.bran j)).F.F.E =
        (T.lsfs (res.2.1 j) (res.2.2.1 j)).F.F.E
      rw [a1, a2]
    have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P i₀ :=
      diffTreeChanges_chainTree_le_cap_noHidden hTP hLP hT hγM₀ hγk hInv hInvMid hi₀ hPreActive
    have hBudget : ChainBudgetInvWith TP LP N₀ stFinal (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · have hOldR := hBudget.1
        have hSumEq := sum_range_inc_coeff P.d i₀ hi₀
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid, stMidCore]; split_ifs with h <;> [subst h; rfl]; omega)
          (opRuntimeBudget TP LP P N₀)
        have hRetTool : (retiredTool : ℝ) ≤
            (Finset.Ico i₀ P.d).sum (levelToolCap TP P N₀) +
              ∑ j ∈ Finset.Ico i₀ P.d, (st.curRestarts j : ℝ) * restartCostCap TP P N₀ j := by
          push_cast [retiredTool]
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun j hj => hCostB.1 j (Finset.mem_Ico.mp hj).2
        have hLastC : (st.curLastCost : ℝ) ≤ lastCostCap TP LP P N₀ := hCostB.2.2.1 P.hd
        have hCR : (stFinal.closedRuntime : ℝ) =
            (st.closedRuntime : ℝ) + (retiredTool : ℝ) + (st.curLastCost : ℝ) + (extraEnc : ℝ) := by
          change ((st.closedRuntime + retiredTool + st.curLastCost + extraEnc : ℕ) : ℝ) = _
          push_cast; rfl
        have hAR : activeRestartCap TP P N₀ stFinal.curRestarts +
            ∑ j ∈ Finset.Ico i₀ P.d, (st.curRestarts j : ℝ) * restartCostCap TP P N₀ j =
              activeRestartCap TP P N₀ st.curRestarts :=
          activeRestartCap_rebuild TP P N₀ i₀ hi₀ st.curRestarts
        have hOpR : opRuntimeBudget TP LP P N₀ i₀ =
            (Finset.Ico i₀ P.d).sum (levelToolCap TP P N₀) +
              lastCostCap TP LP P N₀ + (if i₀ = 0 then extraEncCap P else 0) := by
          unfold opRuntimeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hlt h]
        rw [hCR, hSumEq, hOpR]
        linarith [hOldR]
      · have hSumEq := sum_range_inc_coeff P.d i₀ hi₀
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid, stMidCore]; split_ifs with h <;> [subst h; rfl]; omega)
          (opTreeBudget TP P)
        have hRetDec : (retiredDec : ℝ) ≤ (Finset.Ico i₀ P.d).sum (levelDecCap TP P) := by
          push_cast [retiredDec]
          exact Finset.sum_le_sum fun j hj => hCostB.2.1 j (Finset.mem_Ico.mp hj).2
        have hCL : (stFinal.closedTreeUpdates : ℝ) =
            (st.closedTreeUpdates : ℝ) + (retiredDec : ℝ) + (st.curLastTreeUpdates : ℝ) +
              (changes.length : ℝ) := by
          change ((st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates + changes.length : ℕ) : ℝ) = _
          push_cast; rfl
        have hOpT : opTreeBudget TP P i₀ =
            (Finset.Ico i₀ P.d).sum (levelDecCap TP P) + lastTreeCap TP P + diffTreeCap TP P i₀ := by
          unfold opTreeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hlt h]
        rw [hCL, hSumEq, hOpT]
        linarith [hBudget.2, hCostB.2.2.2.1]
    refine ⟨hInvFinal, hBudget, hn_le, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change applyTreeChanges st.toTreeChain.chainTree.E
          (diffTreeChanges st.toTreeChain.chainTree.E stMid.toTreeChain.chainTree.E) =
        stMid.toTreeChain.chainTree.E
      exact applyTreeChanges_diffTreeChanges _ _
    · have hSumDec :
          (Finset.range P.d).sum stFinal.curDecUpdates + retiredDec =
            (Finset.range P.d).sum st.curDecUpdates := by
        have hsplit : Finset.range P.d = Finset.range i₀ ∪ Finset.Ico i₀ P.d := by
          ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
        have hdisj : Disjoint (Finset.range i₀) (Finset.Ico i₀ P.d) := by
          rw [Finset.disjoint_left]; intro j h1 h2
          simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
        rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
        have hPreEq : (Finset.range i₀).sum stFinal.curDecUpdates = (Finset.range i₀).sum st.curDecUpdates := by
          refine Finset.sum_congr rfl fun j hj => ?_
          exact (hRS.2.1 j (Finset.mem_range.mp hj)).2.2.2.2.1
        have hZero : (Finset.Ico i₀ P.d).sum stFinal.curDecUpdates = 0 := by
          refine Finset.sum_eq_zero fun j hj => ?_
          have hmem := Finset.mem_Ico.mp hj
          exact (hRS.2.2.1 j hmem.1 hmem.2).2.2.2.1
        change (Finset.range i₀).sum stFinal.curDecUpdates + (Finset.Ico i₀ P.d).sum stFinal.curDecUpdates +
            retiredDec = _
        rw [hPreEq, hZero, add_zero]
      unfold ChainState.totalTreeUpdates
      change st.closedTreeUpdates + retiredDec + st.curLastTreeUpdates + changes.length +
          (Finset.range P.d).sum stFinal.curDecUpdates + 0 =
        st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + st.curLastTreeUpdates + changes.length
      omega
  · have hi0_eq : i₀ = P.d := by omega
    subst hi0_eq
    have hd_ne : P.d ≠ 0 := Nat.ne_of_gt P.hd
    have hGnewEq : Gnew = st.G P.d := by simpa [hd_ne] using hGi0
    dsimp only [algorithm1_rebuild]
    rw [dite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d)]
    set ℓd := st.toTreeChain.chainLen st.ℓ P.d
    set lastRes := L.build Gnew ℓd
    set lastCost := L.cost Gnew
    set oldE := st.toTreeChain.chainTree.E
    set stMid : ChainState T P :=
      { st with
        G := fun j => if j = P.d then Gnew else st.G j
        lastK := lastRes.1, lastLSFs := lastRes.2, lastBran := 0,
        rebuildCount := fun j => if j = P.d then st.rebuildCount P.d + 1 else st.rebuildCount j,
        closedRuntime := st.closedRuntime + st.curLastCost + extraEnc,
        curLastRebuilds := 0, curLastCost := lastCost,
        closedTreeUpdates := st.closedTreeUpdates + st.curLastTreeUpdates, curLastTreeUpdates := 0 }
    set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
    set stFinal : ChainState T P := { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
    have hGeq : stFinal.G = st.G := by
      ext j; simp only [stFinal, stMid]; split_ifs with h <;> [rw [h, hGnewEq]; rfl]
    have hGdValid := (hLevB P.d (le_refl P.d)).1
    have hGdℓ := (hLevB P.d (le_refl P.d)).2.2.2.1
    have hLspec := hL Gnew ℓd (hGnewEq ▸ hGdValid) (hGnewEq ▸ hGdℓ)
    have hInvFinal : ChainInv T L TP LP P N₀ stFinal := by
      have hToTC : ∀ j < P.d, stFinal.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
        intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stFinal, stMid]
      have hℓdEq : stFinal.toTreeChain.chainLen stFinal.ℓ P.d = ℓd := by
        apply chainLen_congr_lt st.ℓ P.d (fun j _ => by change stFinal.G j = st.G j; rw [hGeq]) hToTC
      have hCostBd : (lastCost : ℝ) ≤
          ((0 + 1 : ℕ) : ℝ) *
            (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
              (Real.log ((levelM TP P P.d : ℝ) + ((stFinal.G 0).n : ℝ) + 2)) ^ LP.p_last) := by
        have hGdm := (hLevB P.d (le_refl P.d)).2.2.1
        have hGdn : (st.G P.d).n ≤ (st.G 0).n := Finset.card_le_card (hLevB P.d (le_refl P.d)).2.1
        have hlog0 : 0 ≤ Real.log ((Gnew.m : ℝ) + (Gnew.n : ℝ) + 2) :=
          Real.log_nonneg (by linarith [show (0 : ℝ) ≤ Gnew.m from Nat.cast_nonneg _,
            show (0 : ℝ) ≤ Gnew.n from Nat.cast_nonneg _])
        have hlogLe : Real.log ((Gnew.m : ℝ) + (Gnew.n : ℝ) + 2) ≤
            Real.log ((levelM TP P P.d : ℝ) + ((stFinal.G 0).n : ℝ) + 2) := by
          apply Real.log_le_log (by positivity)
          rw [hGnewEq, hGeq]
          have hn_real : ((st.G P.d).n : ℝ) ≤ (st.G 0).n := by exact_mod_cast hGdn
          linarith
        have hpowLog := pow_le_pow_left₀ hlog0 hlogLe LP.p_last
        have hmPlus : (Gnew.m : ℝ) + 1 ≤ (levelM TP P P.d : ℝ) + 1 := by
          rw [hGnewEq]; linarith
        have hcL := hLP.2.2.2.2
        have hMain : (lastCost : ℝ) ≤
            LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
              (Real.log ((levelM TP P P.d : ℝ) + ((stFinal.G 0).n : ℝ) + 2)) ^ LP.p_last := by
          refine le_trans hLspec.2.2.2.2 ?_
          apply mul_le_mul _ hpowLog (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmPlus 2) hcL
        simpa using hMain
      refine ⟨hGeq ▸ hInv.hG0Valid, hGeq ▸ hInv.hG0m, hGeq ▸ hInv.hG0n,
        by rw [hGeq]; exact hInv.hℓPos,
        hLspec.1, hLspec.1, fun j hj => ?_, hGeq ▸ hGnewEq ▸ hLspec.2.2.1,
        hGeq ▸ hGnewEq ▸ hLspec.2.2.2.1,
        hInv.hBran, hGeq ▸ hInv.hGSucc, ?_, ?_, hInv.hRecFwd, hInv.hEnc0, fun hd => ?_,
        hInv.hLvlM, hInv.hN0⟩
      · change (lastRes.2 j).Holds (stFinal.G P.d) _ _
        rw [hGeq, ← hGnewEq, hℓdEq]; exact hLspec.2.1 j hj
      · intro i hi
        obtain ⟨H⟩ := hInv.hHist i hi
        exact ⟨{ H with
          hEndG := by rw [hGeq]; exact H.hEndG
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.ℓ i
              (fun j _ => by change stFinal.G j = st.G j; rw [hGeq]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndℓ e (hGeq ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.g i
              (fun j _ => by change stFinal.G j = st.G j; rw [hGeq]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndg }⟩
      · intro i hi
        have hrebEq : stFinal.rebuildCount i = st.rebuildCount i := by
          simp [stFinal, stMid, Nat.ne_of_lt hi]
        rw [hrebEq]
        exact hInv.hRecRebuild i hi
      · obtain ⟨H⟩ := hInv.hHist (P.d - 1) (Nat.sub_lt hd zero_lt_one)
        refine ⟨⟨{ H with
          hEndG := by rw [hGeq]; exact H.hEndG
          hEndℓ := fun e he => by
            have hSub := Nat.sub_lt hd zero_lt_one
            rw [chainLen_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.ℓ (P.d - 1)
              (fun j _ => by change stFinal.G j = st.G j; rw [hGeq]) (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndℓ e (hGeq ▸ he)
          hEndg := by
            have hSub := Nat.sub_lt hd zero_lt_one
            rw [chainGrad_congr_lt (C₁ := stFinal.toTreeChain) (C₂ := st.toTreeChain) st.g (P.d - 1)
              (fun j _ => by change stFinal.G j = st.G j; rw [hGeq]) (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndg }, by simp [stFinal, stMid]⟩, hCostBd, by simp [stFinal, stMid]⟩
    have hPreActive : ∀ j < P.d, (st.toTreeChain.activeLSF j).F.F.E =
        (stFinal.toTreeChain.activeLSF j).F.F.E := fun j hj => by
      simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stFinal, stMid]
    have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P P.d :=
      diffTreeChanges_chainTree_le_cap_noHidden hTP hLP hT hγM₀ hγk hInv hInvFinal (le_refl P.d) hPreActive
    have hBudget : ChainBudgetInvWith TP LP N₀ stFinal (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · have hSumEq := sum_range_inc_coeff P.d P.d (le_refl P.d)
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid]; split_ifs with h <;> [subst h; rfl]; omega)
          (opRuntimeBudget TP LP P N₀)
        have hEx0 : (extraEnc : ℝ) ≤ extraOverflow := by simpa [hd_ne] using hExtra
        have hCR : (stFinal.closedRuntime : ℝ) + activeRestartCap TP P N₀ stFinal.curRestarts =
            (st.closedRuntime : ℝ) + activeRestartCap TP P N₀ st.curRestarts +
              (st.curLastCost : ℝ) + (extraEnc : ℝ) := by
          have hAR : activeRestartCap TP P N₀ stFinal.curRestarts =
              activeRestartCap TP P N₀ st.curRestarts := rfl
          have hC : (stFinal.closedRuntime : ℝ) =
              (st.closedRuntime : ℝ) + (st.curLastCost : ℝ) + (extraEnc : ℝ) := by
            change ((st.closedRuntime + st.curLastCost + extraEnc : ℕ) : ℝ) = _; push_cast; rfl
          linarith
        have hOpR : opRuntimeBudget TP LP P N₀ P.d = lastCostCap TP LP P N₀ := by
          unfold opRuntimeBudget
          rw [ite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d),
            ite_eq_right_iff.mpr fun h => absurd h hd_ne]
          ring
        rw [hCR, hSumEq, hOpR]
        linarith [hBudget.1, hCostB.2.2.1 P.hd]
      · have hSumEq := sum_range_inc_coeff P.d P.d (le_refl P.d)
          (fun j => st.shiftCount j + st.rebuildCount j)
          (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
          (fun j _ => by dsimp only [stFinal, stMid]; split_ifs with h <;> [subst h; rfl]; omega)
          (opTreeBudget TP P)
        have hCL : (stFinal.closedTreeUpdates : ℝ) =
            (st.closedTreeUpdates : ℝ) + (st.curLastTreeUpdates : ℝ) + (changes.length : ℝ) := by
          change ((st.closedTreeUpdates + st.curLastTreeUpdates + changes.length : ℕ) : ℝ) = _; push_cast; rfl
        have hOpT : opTreeBudget TP P P.d = lastTreeCap TP P + diffTreeCap TP P P.d := by
          unfold opTreeBudget
          rw [ite_eq_right_iff.mpr fun h => absurd h (lt_irrefl P.d)]
          ring
        rw [hCL, hSumEq, hOpT]
        linarith [hBudget.2, hCostB.2.2.2.1, hDiffCap]
    refine ⟨hInvFinal, hBudget, by rw [hGeq], rfl, rfl, rfl, rfl, ?_, ?_⟩
    · change applyTreeChanges st.toTreeChain.chainTree.E
          (diffTreeChanges st.toTreeChain.chainTree.E stMid.toTreeChain.chainTree.E) =
        stMid.toTreeChain.chainTree.E
      exact applyTreeChanges_diffTreeChanges _ _
    · change stFinal.totalTreeUpdates = st.totalTreeUpdates + changes.length
      unfold ChainState.totalTreeUpdates
      change st.closedTreeUpdates + st.curLastTreeUpdates + changes.length +
          (Finset.range P.d).sum st.curDecUpdates + 0 =
        st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + st.curLastTreeUpdates + changes.length
      omega

lemma rebuild_preserves_noHidden (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st)
    (i₀ : ℕ) (hi₀ : i₀ ≤ P.d) (Gnew : MGraph) (extraEnc : ℕ)
    (hGi0 : if i₀ = 0 then
      Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧ (∀ e ∈ Gnew.E, 0 < st.ℓ e)
      else Gnew = st.G i₀)
    (hTrig : i₀ < P.d →
      ((intRebuildThreshold P N₀ i₀ : ℝ) + 1) ≤ (st.updCount i₀ : ℝ))
    (hExtra : (extraEnc : ℝ) ≤ if i₀ = 0 then extraEncCap P else 0) :
    let (st', changes) := algorithm1_rebuild T L P st i₀ Gnew extraEnc
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInv TP LP N₀ st' ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    st'.ℓ = st.ℓ ∧
    st'.g = st.g ∧
    st'.shiftCount = st.shiftCount ∧
    st'.rebuildCount = (fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j) ∧
    applyTreeChanges st.toTreeChain.chainTree.E changes = st'.toTreeChain.chainTree.E ∧
    st'.totalTreeUpdates = st.totalTreeUpdates + changes.length := by
  have h := rebuild_preserves_with_noHidden T L TP LP P hTP hLP hT hL hγM₀ hγk hInv
    (overflow := 0) (extraOverflow := 0) hBudget.toWith i₀ hi₀ Gnew extraEnc hGi0 hTrig
    (by simpa using hExtra)
  dsimp only at h ⊢
  rcases h with ⟨h1, h2, h3⟩
  exact ⟨h1, (ChainBudgetInvWith.toZero (by simpa using h2)), h3⟩

lemma rebuild_preserves (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestart TP) (hL : L.IsSpec LP)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {st : ChainState T P} (hInv : ChainInv T L TP LP P N₀ st) (hBudget : ChainBudgetInv TP LP N₀ st)
    (i₀ : ℕ) (hi₀ : i₀ ≤ P.d) (Gnew : MGraph) (extraEnc : ℕ)
    (hGi0 : if i₀ = 0 then
      Gnew.IsValid ∧ Gnew.m ≤ P.M₀ ∧ Gnew.n ≤ N₀ ∧ (st.G 0).V ⊆ Gnew.V ∧ (∀ e ∈ Gnew.E, 0 < st.ℓ e)
      else Gnew = st.G i₀)
    (hTrig : i₀ < P.d →
      ((intRebuildThreshold P N₀ i₀ : ℝ) + 1) ≤ (st.updCount i₀ : ℝ))
    (hExtra : (extraEnc : ℝ) ≤ if i₀ = 0 then extraEncCap P else 0) :
    let (st', changes) := algorithm1_rebuild T L P st i₀ Gnew extraEnc
    ChainInv T L TP LP P N₀ st' ∧
    ChainBudgetInv TP LP N₀ st' ∧
    (st.G 0).n ≤ (st'.G 0).n ∧
    st'.ℓ = st.ℓ ∧
    st'.g = st.g ∧
    st'.shiftCount = st.shiftCount ∧
    st'.rebuildCount = (fun j => if j = i₀ then st.rebuildCount i₀ + 1 else st.rebuildCount j) ∧
    applyTreeChanges st.toTreeChain.chainTree.E changes = st'.toTreeChain.chainTree.E ∧
    st'.totalTreeUpdates = st.totalTreeUpdates + changes.length :=
  rebuild_preserves_noHidden T L TP LP P hTP hLP hT.toNoHidden hL hγM₀ hγk hInv hBudget
    i₀ hi₀ Gnew extraEnc hGi0 hTrig hExtra


end OpPreservation

end MinCostFlow.Chain
