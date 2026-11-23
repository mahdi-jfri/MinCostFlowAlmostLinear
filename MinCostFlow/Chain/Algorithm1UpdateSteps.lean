module

public import MinCostFlow.Chain.Algorithm1Proofs
import MinCostFlow.Chain.EncodingSize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Update-loop invariant and budget preservation for Algorithm 1

This file proves `updateLoop_preserves` and `update_preserves`, showing that
`algorithm1_update` preserves `ChainInv` and `ChainBudgetInv`, emits exact `TreeChange`
diffs for `T^𝒢`, and increases `totalTreeUpdates` by at least `changes.length`.
-/

@[expose] public section

namespace MinCostFlow.Chain

private lemma finset_Icc_sdiff_subset (a b : ℕ) (_h : a ≤ b) :
    Finset.Icc a b ⊆ Finset.Icc a (b + 1) := by
  intro x hx
  simp only [Finset.mem_Icc] at hx ⊢
  omega

/-- Loop invariant for `updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEncAcc` relative
to the pre-update state `stOrig` and top-level batch `(U, g', ℓ')`, maintaining the unconditional
tight `TP.γ_r (P.M₀ ^ 2)` recourse bound via restart-aware windowed recourse (`LevelHistory`). -/
structure UpdateLoopInv {T : SparseCoreRestartTool} (TP : SparseCoreParams) {P : ChainParams}
    (N₀ : ℕ) (extraOverflow : ℝ) (stOrig st : ChainState T P) (ℓ' g' : ℕ → ℝ)
    (rem idx : ℕ) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ) : Prop where
  hidxSum : idx + rem = P.d
  hGGe : ∀ j, idx ≤ j → st.G j = stOrig.G j
  hScGe : ∀ j, idx ≤ j → st.scState j = stOrig.scState j
  hRestarts : st.curRestarts = stOrig.curRestarts
  hUpdGe : ∀ j, idx ≤ j → st.updCount j = stOrig.updCount j
  hDecGe : ∀ j, idx ≤ j → st.curDecUpdates j = stOrig.curDecUpdates j
  hEncGt : ∀ j, idx < j → st.curEnc j = stOrig.curEnc j
  hCurFwdGe : ∀ j, idx ≤ j → st.curFwd j = stOrig.curFwd j
  hRecGt : ∀ j, idx < j → st.recUpdates j = stOrig.recUpdates j
  hCurRecAt : st.recUpdates idx = stOrig.recUpdates idx + curU.length
  hBran : st.bran = stOrig.bran
  hLast : st.lastK = stOrig.lastK ∧ st.lastLSFs = stOrig.lastLSFs ∧ st.lastBran = stOrig.lastBran
  hLG : st.ℓ = stOrig.ℓ ∧ st.g = stOrig.g
  hCnt : st.shiftCount = stOrig.shiftCount ∧ st.rebuildCount = stOrig.rebuildCount
  hClosed : st.closedRuntime = stOrig.closedRuntime ∧ st.closedTreeUpdates = stOrig.closedTreeUpdates
  hLastStats : st.curLastRebuilds = stOrig.curLastRebuilds ∧
    st.curLastCost = stOrig.curLastCost ∧ st.curLastTreeUpdates = stOrig.curLastTreeUpdates
  hG0New : 0 < idx → (st.G 0).IsValid ∧ (st.G 0).m ≤ P.M₀ ∧ (st.G 0).n ≤ N₀ ∧
    (stOrig.G 0).V ⊆ (st.G 0).V ∧ (∀ e ∈ (st.G 0).E, 0 < ℓ' e)
  hPreHist : ∀ j < idx, Nonempty (LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } j)
  hPreGSucc : ∀ j, j + 1 < idx → st.G (j + 1) = T.S (st.scState j) (st.bran j)
  hPreV : ∀ j < idx, (st.G j).V ⊆ (st.G 0).V
  hPreM : ∀ j < idx, ((st.G j).m : ℝ) ≤ (levelM TP P j : ℝ)
  hPreEnc0 : 0 < idx → (st.curEnc 0 : ℝ) ≤
    20 * ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ)) *
      Real.log ((levelM TP P 0 : ℝ) + (st.updCount 0 : ℝ) + 2)
  hLoopRecReb : ∀ j < idx,
    (st.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
      (st.updCount j : ℝ) ≤ (st.recUpdates j : ℝ)
  hLoopRecFwd : ∀ j < idx,
    (st.curFwd j : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) * (st.updCount j : ℝ) ∧
    ((st.recUpdates (j + 1) : ℝ) - (st.curFwd j : ℝ)) ≤
      TP.γ_r (P.M₀ ^ 2) * ((st.recUpdates j : ℝ) - (st.updCount j : ℝ))
  hPreLastReb : idx = P.d → 0 < P.d →
    ∃ H : LevelHistory T TP P N₀ { st with ℓ := ℓ', g := g' } (P.d - 1),
      st.curLastRebuilds + (if curU = [] then 0 else 1) ≤
        (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
          ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.restarts s).2
            (st.bran (P.d - 1))).length
  hCurGEq : curG = (stOrig.G idx).applyBatch curU
  hCurGBatch : (stOrig.G idx).BatchIsValid curU
  hCurGValid : curG.IsValid
  hCurGM : (curG.m : ℝ) ≤ (levelM TP P idx : ℝ)
  hCurGV0 : idx = 0 → curG.m ≤ P.M₀ ∧ curG.n ≤ N₀ ∧ (stOrig.G 0).V ⊆ curG.V ∧
    (∀ e ∈ curG.E, 0 < ℓ' e)
  hCurGVPos : 0 < idx → curG.V ⊆ (st.G 0).V
  hCurGFromPrev : 0 < idx → curG = T.S (st.scState (idx - 1)) (st.bran (idx - 1))
  hCurEnc0 : idx = 0 → st.curEnc 0 = stOrig.curEnc 0 ∧ curEncAcc = (stOrig.G 0).batchEnc curU ∧
    (curEncAcc : ℝ) ≤ extraEncCap P + extraOverflow
  hCurEncPos : 0 < idx → curEncAcc = 0 ∧
    (idx < P.d → (st.curEnc idx : ℝ) ≤
      5 * TP.γ_r (P.M₀ ^ 2) * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (idx - 1) / (P.k : ℝ) + 1))
  hCurLenPos : ∀ e ∈ curG.E, 0 <
    ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx e
  hCurLenStable : ∀ e ∈ curG.E, e ∈ (stOrig.G idx).E → (∀ u ∈ curU, ¬ u.Inserts e) →
    ({ st.toTreeChain with G := fun j => if j = idx then curG else st.G j } : TreeChain).chainLen ℓ' idx e =
      stOrig.toTreeChain.chainLen stOrig.ℓ idx e
  hDecMono : ∀ j < P.d, stOrig.curDecUpdates j ≤ st.curDecUpdates j
  hTreeDiff : (diffTreeChanges stOrig.toTreeChain.chainTree.E st.toTreeChain.chainTree.E).length +
    (Finset.range P.d).sum stOrig.curDecUpdates ≤ (Finset.range P.d).sum st.curDecUpdates
  hLvlM : st.lvlM = stOrig.lvlM
  hN0 : st.N₀ = stOrig.N₀


lemma updateLoop_zero_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (_hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ extraOverflow stOrig st ℓ' g' 0 idx curG curU curEncAcc) :
    let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' 0 idx st curG curU curEncAcc
    ChainInv T L TP LP P N₀ stEnd ∧
    ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
    (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
    (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
    (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
    (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
      stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  have hOrigCost := hInvOrig.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInvOrig
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_ge := hTP.2.2.1
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / P.k := div_nonneg hγℓ_nonneg hk_pos.le
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
  have hidx : idx = P.d := by have := hLoop.hidxSum; omega
  subst hidx
  dsimp only [updateLoop]
  by_cases hEmp : curU = []
  · subst hEmp
    simp only [↓reduceIte]
    set stEnd : ChainState T P :=
      { st with G := fun j => if j = P.d then curG else st.G j, ℓ := ℓ', g := g' }
    have hCurEqOrig : curG = stOrig.G P.d := by
      simpa [MGraph.applyBatch] using hLoop.hCurGEq
    have hGEqSt : stEnd.G = st.G := by
      ext j
      dsimp only [stEnd]
      split_ifs with h
      · rw [h, hCurEqOrig, hLoop.hGGe P.d (le_refl P.d)]
      · rfl
    have hGEndPd : stEnd.G P.d = stOrig.G P.d := by
      rw [hGEqSt, hLoop.hGGe P.d (le_refl P.d)]
    have hG0Props := hLoop.hG0New P.hd
    have h0n : (stOrig.G 0).n ≤ (stEnd.G 0).n := by
      rw [hGEqSt]; exact Finset.card_le_card hG0Props.2.2.2.1
    have hToTC : ∀ j < P.d, stEnd.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
      intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stEnd]
    have hℓdEq : ∀ e ∈ (stOrig.G P.d).E,
        stEnd.toTreeChain.chainLen stEnd.ℓ P.d e =
          stOrig.toTreeChain.chainLen stOrig.ℓ P.d e := by
      intro e he
      set Cpartial : TreeChain :=
        { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
      have hC := chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := Cpartial) ℓ' P.d
        (fun j hj => by change stEnd.G j = Cpartial.G j; simp [stEnd, Cpartial, show j ≠ P.d by omega])
        (fun j hj => by simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, stEnd, hj])
      have heCur : e ∈ curG.E := by rwa [hCurEqOrig]
      change stEnd.toTreeChain.chainLen ℓ' P.d e = _
      rw [hC]
      exact hLoop.hCurLenStable e heCur he (fun u hu => nomatch hu)
    have hLastEq : stEnd.lastK = stOrig.lastK ∧ stEnd.lastLSFs = stOrig.lastLSFs ∧
        stEnd.lastBran = stOrig.lastBran := hLoop.hLast
    have hInvEnd : ChainInv T L TP LP P N₀ stEnd := {
      hG0Valid := hGEqSt ▸ hG0Props.1
      hG0m := hGEqSt ▸ hG0Props.2.1
      hG0n := hGEqSt ▸ hG0Props.2.2.1
      hℓPos := hGEqSt ▸ hG0Props.2.2.2.2
      hLastK := hLastEq.1 ▸ hInvOrig.hLastK
      hLastBran := hLastEq.1 ▸ hLastEq.2.2 ▸ hInvOrig.hLastBran
      hLastHolds := fun j hj => by
        have hOrigH := hInvOrig.hLastHolds j (hLastEq.1 ▸ hj)
        have h1 := LSF.Holds.congr_len hOrigH fun e he => (hℓdEq e he).symm
        rw [hGEndPd, hLastEq.2.1]
        exact h1
      hLastMWU := by rw [hGEndPd, hLastEq.1, hLastEq.2.1]; exact hInvOrig.hLastMWU
      hLastSpans := by rw [hGEndPd, hLastEq.1, hLastEq.2.1]; exact hInvOrig.hLastSpans
      hBran := by rw [hLoop.hBran]; exact hInvOrig.hBran
      hGSucc := fun i hi => by
        by_cases h1 : i + 1 < P.d
        · rw [hGEqSt]; exact hLoop.hPreGSucc i h1
        · have hieq : i = P.d - 1 := by omega
          subst hieq
          rw [hGEqSt, show P.d - 1 + 1 = P.d by omega, hLoop.hGGe P.d (le_refl P.d), ← hCurEqOrig]
          exact hLoop.hCurGFromPrev P.hd
      hHist := fun i hi => by
        obtain ⟨H⟩ := hLoop.hPreHist i hi
        exact ⟨{ H with
          hEndG := by rw [hGEqSt]; exact H.hEndG
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' i
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndℓ e (hGEqSt ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' i
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt]) (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndg }⟩
      hEnc0 := hLoop.hPreEnc0 P.hd
      hLastCap := fun hd => by
        obtain ⟨H, hReb⟩ := hLoop.hPreLastReb rfl hd
        have hSub := Nat.sub_lt hd zero_lt_one
        have hReb' : stEnd.curLastRebuilds ≤ (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
            ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.restarts s).2
              (stEnd.bran (P.d - 1))).length := by
          simpa [stEnd] using hReb
        refine ⟨⟨{ H with
          hEndG := by rw [hGEqSt]; exact H.hEndG
          hEndℓ := fun e he => by
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' (P.d - 1)
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndℓ e (hGEqSt ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' (P.d - 1)
              (fun j _ => by change stEnd.G j = st.G j; rw [hGEqSt])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndg }, hReb'⟩, ?_, ?_⟩
        · obtain ⟨_, hCostO, _⟩ := hInvOrig.hLastCap hd
          rw [hLoop.hLastStats.2.1, hLoop.hLastStats.1]
          refine le_trans hCostO ?_
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hLP.2.2.2.2 (by positivity))
          have harg_pos : 0 < (levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2 := by
            positivity
          have hlog_pos : 0 ≤ Real.log ((levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2) :=
            Real.log_nonneg (by
              have hnn : 0 ≤ (levelM TP P P.d : ℝ) := Nat.cast_nonneg _
              linarith [show (0 : ℝ) ≤ (stOrig.G 0).n from Nat.cast_nonneg _])
          refine pow_le_pow_left₀ hlog_pos (Real.log_le_log harg_pos ?_) _
          have h0n' : ((stOrig.G 0).n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast h0n
          linarith
        · rw [hLoop.hLastStats.2.2, hLoop.hLastStats.1]
          exact (hInvOrig.hLastCap hd).2.2
      hRecRebuild := fun j hj => hLoop.hLoopRecReb j hj
      hRecFwd := fun j hj => hLoop.hLoopRecFwd j hj
      hLvlM := hLoop.hLvlM.trans hInvOrig.hLvlM
      hN0 := hLoop.hN0.trans hInvOrig.hN0 }
    have hBudgetEnd : ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · rw [show stEnd.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1,
          show stEnd.curRestarts = stOrig.curRestarts from hLoop.hRestarts,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact le_trans hBudgetOrig.1 (by linarith)
      · rw [show stEnd.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact hBudgetOrig.2
    have hEeq : stEnd.toTreeChain.chainTree.E = st.toTreeChain.chainTree.E := by
      change stEnd.toTreeChain.chainTreeEdges = st.toTreeChain.chainTreeEdges
      unfold TreeChain.chainTreeEdges
      refine Finset.biUnion_congr rfl fun j hj => ?_
      by_cases hjt : j < P.d
      · have hjt' : j < P.d := by change j < stEnd.toTreeChain.d at hjt; exact hjt
        rw [hToTC j hjt']
      · have hjlt : j < P.d + 1 := Finset.mem_range.mp hj
        have hjeq : j = P.d := by omega
        subst hjeq
        simp [TreeChain.activeLSF, ChainState.toTreeChain, stEnd]
    refine ⟨hInvEnd, hBudgetEnd, h0n, fun i => by rw [hLoop.hCnt.1], fun i => by rw [hLoop.hCnt.2], ?_⟩
    unfold ChainState.totalTreeUpdates
    rw [hEeq, hLoop.hClosed.2, hLoop.hLastStats.2.2]
    change (diffTreeChanges stOrig.toTreeChain.chainTree.E st.toTreeChain.chainTree.E).length +
        (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates + stOrig.curLastTreeUpdates) ≤
      stOrig.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates + stOrig.curLastTreeUpdates
    have hTD := hLoop.hTreeDiff
    omega
  · simp only [hEmp, ↓reduceIte]
    set Cpartial : TreeChain :=
      { st.toTreeChain with G := fun j => if j = P.d then curG else st.G j }
    set ℓd := Cpartial.chainLen ℓ' P.d
    set lastRes := L.build curG ℓd
    set lastCost := L.cost curG
    set oldFdE := (st.lastLSFs st.lastBran).F.F.E
    set newFdE := (lastRes.2 0).F.F.E
    set fdChanges := diffTreeChanges oldFdE newFdE
    set stEnd : ChainState T P :=
      { st with
        G := fun j => if j = P.d then curG else st.G j
        lastK := lastRes.1
        lastLSFs := lastRes.2
        lastBran := 0
        ℓ := ℓ'
        g := g'
        curLastRebuilds := st.curLastRebuilds + 1
        curLastCost := st.curLastCost + lastCost
        curLastTreeUpdates := st.curLastTreeUpdates + fdChanges.length }
    have hG0Props := hLoop.hG0New P.hd
    have hG0Eq : stEnd.G 0 = st.G 0 := by
      have h0d : (0 : ℕ) ≠ P.d := Nat.ne_of_lt P.hd
      simp [stEnd, h0d]
    have h0n : (stOrig.G 0).n ≤ (stEnd.G 0).n := by
      rw [hG0Eq]; exact Finset.card_le_card hG0Props.2.2.2.1
    have hG0Endn : (stEnd.G 0).n ≤ N₀ := by
      rw [hG0Eq]; exact hG0Props.2.2.1
    have hℓdPos : ∀ e ∈ curG.E, 0 < ℓd e := by
      intro e he
      have heq : ℓd = ({ st.toTreeChain with G := fun j => if j = P.d then curG else st.G j } : TreeChain).chainLen ℓ' P.d :=
        rfl
      rw [heq]; exact hLoop.hCurLenPos e he
    have hLspec := hL curG ℓd hLoop.hCurGValid hℓdPos
    have hCurGV : curG.V ⊆ (stEnd.G 0).V := by
      rw [hG0Eq]; exact hLoop.hCurGVPos P.hd
    have hCurn : curG.n ≤ (stEnd.G 0).n := Finset.card_le_card hCurGV
    have hLastCostBd : (lastCost : ℝ) ≤
        LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
          (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^
            LP.p_last := by
      have hlog0 : 0 ≤ Real.log ((curG.m : ℝ) + (curG.n : ℝ) + 2) :=
        Real.log_nonneg (by linarith [show (0 : ℝ) ≤ curG.m from Nat.cast_nonneg _,
          show (0 : ℝ) ≤ curG.n from Nat.cast_nonneg _])
      have hlogLe : Real.log ((curG.m : ℝ) + (curG.n : ℝ) + 2) ≤
          Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2) := by
        apply Real.log_le_log (by positivity)
        have hn' : (curG.n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast hCurn
        linarith [hLoop.hCurGM]
      have hpowLog := pow_le_pow_left₀ hlog0 hlogLe LP.p_last
      have hmPlus : (curG.m : ℝ) + 1 ≤ (levelM TP P P.d : ℝ) + 1 := by
        linarith [hLoop.hCurGM]
      refine le_trans hLspec.2.2.2.2 ?_
      apply mul_le_mul _ hpowLog (by positivity) (mul_nonneg hLP.2.2.2.2 (by positivity))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hmPlus 2) hLP.2.2.2.2
    have hFdCap : (fdChanges.length : ℝ) ≤ 2 * (levelM TP P P.d : ℝ) := by
      have hOldSub : oldFdE ⊆ (stOrig.G P.d).E := by
        change (st.lastLSFs st.lastBran).F.F.E ⊆ (stOrig.G P.d).E
        rw [hLoop.hLast.2.1, hLoop.hLast.2.2]
        exact (hInvOrig.hLastHolds stOrig.lastBran hInvOrig.hLastBran).2.1.2.2.2.2.2.1
      have hNewSub : newFdE ⊆ curG.E := (hLspec.2.1 0 hLspec.1).2.1.2.2.2.2.2.1
      have hOldCard : (oldFdE.card : ℝ) ≤ (levelM TP P P.d : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hOldSub) (hOrigLev P.d (le_refl P.d)).2.2.1
      have hNewCard : (newFdE.card : ℝ) ≤ (levelM TP P P.d : ℝ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hNewSub) hLoop.hCurGM
      have hle : (fdChanges.length : ℝ) ≤ (oldFdE.card : ℝ) + (newFdE.card : ℝ) := by
        exact_mod_cast diffTreeChanges_length_le_add oldFdE newFdE
      linarith
    have hToTC : ∀ j < P.d, stEnd.toTreeChain.activeLSF j = st.toTreeChain.activeLSF j := by
      intro j hj; simp [TreeChain.activeLSF, ChainState.toTreeChain, hj, stEnd]
    have hℓdEq : stEnd.toTreeChain.chainLen stEnd.ℓ P.d = ℓd :=
      chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := Cpartial) ℓ' P.d
        (fun j hj => by change stEnd.G j = Cpartial.G j; simp [stEnd, Cpartial, show j ≠ P.d by omega])
        (fun j hj => by simp [TreeChain.activeLSF, ChainState.toTreeChain, Cpartial, stEnd, hj])
    have hInvEnd : ChainInv T L TP LP P N₀ stEnd := {
      hG0Valid := hG0Eq ▸ hG0Props.1
      hG0m := hG0Eq ▸ hG0Props.2.1
      hG0n := hG0Endn
      hℓPos := hG0Eq ▸ hG0Props.2.2.2.2
      hLastK := hLspec.1
      hLastBran := hLspec.1
      hLastHolds := fun j hj => by
        have hGdEq : stEnd.G P.d = curG := by simp [stEnd]
        change (lastRes.2 j).Holds (stEnd.G P.d) (stEnd.toTreeChain.chainLen stEnd.ℓ P.d)
          (LP.σ_last (stEnd.G P.d).n)
        rw [hGdEq, hℓdEq]; exact hLspec.2.1 j hj
      hLastMWU := by simpa [stEnd] using hLspec.2.2.1
      hLastSpans := by simpa [stEnd] using hLspec.2.2.2.1
      hBran := by rw [hLoop.hBran]; exact hInvOrig.hBran
      hGSucc := fun i hi => by
        by_cases h1 : i + 1 < P.d
        · simp only [stEnd, show i + 1 ≠ P.d by omega, ↓reduceIte]
          exact hLoop.hPreGSucc i h1
        · have hieq : i = P.d - 1 := by omega
          subst hieq
          simp only [stEnd, show P.d - 1 + 1 = P.d by omega, ↓reduceIte]
          exact hLoop.hCurGFromPrev P.hd
      hHist := fun i hi => by
        obtain ⟨H⟩ := hLoop.hPreHist i hi
        exact ⟨{ H with
          hEndG := by simp [stEnd, show i ≠ P.d by omega]; exact H.hEndG
          hEndℓ := fun e he => by
            have hGi : stEnd.G i = st.G i := by simp [stEnd, show i ≠ P.d by omega]
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' i
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndℓ e (hGi ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' i
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hi))]
            exact H.hEndg }⟩
      hEnc0 := hLoop.hPreEnc0 P.hd
      hLastCap := fun hd => by
        obtain ⟨H, hReb⟩ := hLoop.hPreLastReb rfl hd
        have hSub := Nat.sub_lt hd zero_lt_one
        have hReb' : stEnd.curLastRebuilds ≤ (Finset.Icc (H.s₀ + 1) H.len).sum fun s =>
            ((T.runAfterUpdate P.k (levelM TP P (P.d - 1)) N₀ H.D H.restarts s).2
              (stEnd.bran (P.d - 1))).length := by
          simpa [stEnd, hEmp] using hReb
        refine ⟨⟨{ H with
          hEndG := by simp [stEnd, show P.d - 1 ≠ P.d by omega]; exact H.hEndG
          hEndℓ := fun e he => by
            have hGi : stEnd.G (P.d - 1) = st.G (P.d - 1) := by
              simp [stEnd, show P.d - 1 ≠ P.d by omega]
            rw [chainLen_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) ℓ' (P.d - 1)
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndℓ e (hGi ▸ he)
          hEndg := by
            rw [chainGrad_congr_lt (C₁ := stEnd.toTreeChain) (C₂ := st.toTreeChain) g' (P.d - 1)
              (fun j hj => by change stEnd.G j = st.G j; simp [stEnd, show j ≠ P.d by omega])
              (fun j hj => hToTC j (lt_trans hj hSub))]
            exact H.hEndg }, hReb'⟩, ?_, ?_⟩
        · obtain ⟨_, hCostO, _⟩ := hInvOrig.hLastCap hd
          have hCostO' : (st.curLastCost : ℝ) ≤
              ((st.curLastRebuilds + 1 : ℕ) : ℝ) *
                (LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
                  (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^
                    LP.p_last) := by
            rw [hLoop.hLastStats.2.1, hLoop.hLastStats.1]
            refine le_trans hCostO ?_
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hLP.2.2.2.2 (by positivity))
            have harg_pos : 0 < (levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2 := by
              positivity
            have hlog_pos : 0 ≤ Real.log ((levelM TP P P.d : ℝ) + ((stOrig.G 0).n : ℝ) + 2) :=
              Real.log_nonneg (by
                have hnn : 0 ≤ (levelM TP P P.d : ℝ) := Nat.cast_nonneg _
                linarith [show (0 : ℝ) ≤ (stOrig.G 0).n from Nat.cast_nonneg _])
            refine pow_le_pow_left₀ hlog_pos (Real.log_le_log harg_pos ?_) _
            have h0n' : ((stOrig.G 0).n : ℝ) ≤ (stEnd.G 0).n := by exact_mod_cast h0n
            linarith
          set cap := LP.c_last * ((levelM TP P P.d : ℝ) + 1) ^ 2 *
            (Real.log ((levelM TP P P.d : ℝ) + ((stEnd.G 0).n : ℝ) + 2)) ^ LP.p_last
          change ((st.curLastCost + lastCost : ℕ) : ℝ) ≤ ((st.curLastRebuilds + 1 + 1 : ℕ) : ℝ) * cap
          calc
            ((st.curLastCost + lastCost : ℕ) : ℝ)
                = (st.curLastCost : ℝ) + (lastCost : ℝ) := by push_cast; rfl
            _ ≤ ((st.curLastRebuilds + 1 : ℕ) : ℝ) * cap + cap := add_le_add hCostO' hLastCostBd
            _ = ((st.curLastRebuilds + 1 + 1 : ℕ) : ℝ) * cap := by push_cast; ring
        · have hTreeO := (hInvOrig.hLastCap hd).2.2
          rw [← hLoop.hLastStats.2.2, ← hLoop.hLastStats.1] at hTreeO
          change ((st.curLastTreeUpdates + fdChanges.length : ℕ) : ℝ) ≤
            2 * ((st.curLastRebuilds + 1 : ℕ) : ℝ) * (levelM TP P P.d : ℝ)
          push_cast
          linarith
      hRecRebuild := fun j hj => hLoop.hLoopRecReb j hj
      hRecFwd := fun j hj => hLoop.hLoopRecFwd j hj
      hLvlM := hLoop.hLvlM.trans hInvOrig.hLvlM
      hN0 := hLoop.hN0.trans hInvOrig.hN0 }
    have hBudgetEnd : ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) := by
      refine ⟨?_, ?_⟩
      · rw [show stEnd.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1,
          show stEnd.curRestarts = stOrig.curRestarts from hLoop.hRestarts,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact le_trans hBudgetOrig.1 (by linarith)
      · rw [show stEnd.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2,
          show stEnd.shiftCount = stOrig.shiftCount from hLoop.hCnt.1,
          show stEnd.rebuildCount = stOrig.rebuildCount from hLoop.hCnt.2]
        exact hBudgetOrig.2
    have hStepDiff : (diffTreeChanges st.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length ≤
        fdChanges.length := by
      have hbi := diffTreeChanges_length_biUnion (Finset.range (P.d + 1))
        (fun j => (st.toTreeChain.activeLSF j).F.F.E)
        (fun j => (stEnd.toTreeChain.activeLSF j).F.F.E)
      have hsplit : Finset.range (P.d + 1) = insert P.d (Finset.range P.d) := by
        ext j; simp only [Finset.mem_range, Finset.mem_insert]; omega
      have hnot : P.d ∉ Finset.range P.d := by simp
      have hzero : (Finset.range P.d).sum (fun j =>
          (diffTreeChanges (st.toTreeChain.activeLSF j).F.F.E
            (stEnd.toTreeChain.activeLSF j).F.F.E).length) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hToTC j (Finset.mem_range.mp hj), diffTreeChanges_length]
        simp
      change (diffTreeChanges st.toTreeChain.chainTreeEdges stEnd.toTreeChain.chainTreeEdges).length ≤ _
      unfold TreeChain.chainTreeEdges
      refine le_trans hbi ?_
      rw [hsplit, Finset.sum_insert hnot, hzero, add_zero]
      simp [TreeChain.activeLSF, ChainState.toTreeChain, stEnd, fdChanges, oldFdE, newFdE]
    have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
      st.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E
    refine ⟨hInvEnd, hBudgetEnd, h0n, fun i => by rw [hLoop.hCnt.1], fun i => by rw [hLoop.hCnt.2], ?_⟩
    unfold ChainState.totalTreeUpdates
    change (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
        (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates +
          stOrig.curLastTreeUpdates) ≤
      st.closedTreeUpdates + (Finset.range P.d).sum st.curDecUpdates +
        (st.curLastTreeUpdates + fdChanges.length)
    rw [hLoop.hClosed.2, hLoop.hLastStats.2.2]
    linarith [hLoop.hTreeDiff]

lemma updateLoop_succ_over_step
    (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (LP : LastLevelParams) (P : ChainParams) {N₀ : ℕ}
    (hTP : TP.Valid) (hLP : LP.Valid) (hT : T.IsSpecRestartNoHidden TP) (hL : L.IsSpec LP)
    (_hNoReinsTool : T.ToolNoReinsertRestartNoHidden)
    (hγM₀ : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀) (hγk : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k)
    {stOrig : ChainState T P} (hInvOrig : ChainInv T L TP LP P N₀ stOrig)
    {overflow extraOverflow : ℝ}
    (hBudgetOrig : ChainBudgetInvWith TP LP N₀ stOrig overflow) (hExtraNN : 0 ≤ extraOverflow)
    (ℓ' g' : ℕ → ℝ)
    (rem' idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEncAcc : ℕ)
    (hLoop : UpdateLoopInv TP N₀ extraOverflow stOrig st ℓ' g' (rem' + 1) idx curG curU curEncAcc)
    (hOver : intRebuildThreshold P N₀ idx < st.updCount idx + curU.length) :
    let (stEnd, _) := updateLoop T L TP P N₀ ℓ' g' (rem' + 1) idx st curG curU curEncAcc
    ChainInv T L TP LP P N₀ stEnd ∧
    ChainBudgetInvWith TP LP N₀ stEnd (overflow + extraOverflow) ∧
    (stOrig.G 0).n ≤ (stEnd.G 0).n ∧
    (∀ i, stOrig.shiftCount i = stEnd.shiftCount i) ∧
    (∀ i, stOrig.rebuildCount i ≤ stEnd.rebuildCount i) ∧
    (diffTreeChanges stOrig.toTreeChain.chainTree.E stEnd.toTreeChain.chainTree.E).length +
      stOrig.totalTreeUpdates ≤ stEnd.totalTreeUpdates := by
  have hOrigCost := hInvOrig.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
  have hOrigLev := level_bounds_aux_noHidden T L TP LP P N₀ hTP hT hγM₀ hγk hInvOrig
  have hk_pos : (0 : ℝ) < P.k := Nat.cast_pos.mpr P.hk
  have hγℓ_ge := hTP.2.2.1
  have hγℓ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) := le_trans zero_le_one (hγℓ_ge (P.M₀ ^ 2))
  have hγ_nonneg : 0 ≤ TP.γ_ℓ (P.M₀ ^ 2) / P.k := div_nonneg hγℓ_nonneg hk_pos.le
  have hγr_nn : 0 ≤ TP.γ_r (P.M₀ ^ 2) := le_trans zero_le_one (hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2))
  have hidxLt : idx < P.d := by have := hLoop.hidxSum; omega
  dsimp only [updateLoop]
  rw [ite_eq_left_iff.mpr fun h => absurd hOver h]
  set stWithLG := { st with ℓ := ℓ', g := g' }
  set oldE := stWithLG.toTreeChain.chainTree.E
  set G0 := fun j => if j = idx then curG else stWithLG.G j
  set res := rebuildSuffix T L P stWithLG.lvlM stWithLG.N₀ ℓ' g' (P.d - idx) idx
    G0 stWithLG.scState stWithLG.bran stWithLG.updCount
    stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
  set retiredTool := (Finset.Ico idx P.d).sum fun j =>
    T.cost (stWithLG.scState j) + stWithLG.curEnc j
  set retiredDec := (Finset.Ico idx P.d).sum fun j => stWithLG.curDecUpdates j
  set stMidCore : ChainState T P :=
    { stWithLG with
      G := res.1, scState := res.2.1,
      curRestarts := fun j => if idx ≤ j ∧ j < P.d then 0 else stWithLG.curRestarts j,
      bran := res.2.2.1, updCount := res.2.2.2.1,
      lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2, lastBran := 0,
      curLastRebuilds := 0, curLastCost := res.2.2.2.2.2.2.2.2,
      curEnc := res.2.2.2.2.1, curDecUpdates := res.2.2.2.2.2.1,
      curFwd := res.2.2.2.2.2.2.1,
      curLastTreeUpdates := 0 }
  have hG0Valid : (G0 0).IsValid := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).1
  have hG0m : (G0 0).m ≤ P.M₀ := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.1
  have hG0n : (G0 0).n ≤ N₀ := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).2.1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.1
  have hℓ0 : ∀ e ∈ (G0 0).E, 0 < stWithLG.ℓ e := by
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact (hLoop.hCurGV0 rfl).2.2.2
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.2.2
  have hGi0V : (G0 idx).V ⊆ (G0 0).V := by
    by_cases h0 : idx = 0
    · subst h0; exact Finset.Subset.refl _
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, ↓reduceIte, hne0]; exact hLoop.hCurGVPos (Nat.pos_of_ne_zero h0)
  have hGi0m : ((G0 idx).m : ℝ) ≤ (levelM TP P idx : ℝ) := by
    simp only [G0, ↓reduceIte]; exact hLoop.hCurGM
  have hℓ_idx : ∀ e ∈ (G0 idx).E,
      0 < (mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx)).chainLen ℓ' idx e := by
    intro e he
    simp only [G0, ↓reduceIte] at he
    set Cpartial0 : TreeChain :=
      { st.toTreeChain with G := fun j => if j = idx then curG else st.G j }
    have heq : (mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx)).chainLen ℓ' idx =
        Cpartial0.chainLen ℓ' idx := by
      apply chainLen_congr_lt
        (C₁ := mkPartialChain T P G0 stWithLG.scState stWithLG.bran (G0 idx))
        (C₂ := Cpartial0)
      · intro j hj
        change G0 j = Cpartial0.G j
        simp [G0, Cpartial0, stWithLG, Nat.ne_of_lt hj]
      · intro j hj
        simp [mkPartialChain, Cpartial0, ChainState.toTreeChain, TreeChain.activeLSF,
          stWithLG, show j < P.d by omega]
    rw [heq]; exact hLoop.hCurLenPos e he
  let stTmp : ChainState T P := { stWithLG with G := G0 }
  have hPreHist' : ∀ j < idx, Nonempty (LevelHistory T TP P N₀ stTmp j) := by
    intro j hj
    obtain ⟨H⟩ := hLoop.hPreHist j hj
    have hjne : j ≠ idx := Nat.ne_of_lt hj
    refine ⟨{ H with
      hEndG := by simpa [stTmp, G0, stWithLG, hjne] using H.hEndG
      hEndℓ := fun e he => by
        have he' : e ∈ (stWithLG.G j).E := by simpa [stTmp, G0, hjne] using he
        have hCL := chainLen_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := stWithLG.toTreeChain) ℓ' j
          (fun m hm => by change stTmp.G m = stWithLG.G m; simp [stTmp, G0, show m ≠ idx by omega])
          (fun m hm => by simp [ChainState.toTreeChain, TreeChain.activeLSF, stTmp, show m < P.d by omega])
        change H.D.ℓ H.len e = stTmp.toTreeChain.chainLen ℓ' j e
        rw [hCL]; exact H.hEndℓ e he'
      hEndg := by
        have hCG := chainGrad_congr_lt (C₁ := stTmp.toTreeChain) (C₂ := stWithLG.toTreeChain) g' j
          (fun m hm => by change stTmp.G m = stWithLG.G m; simp [stTmp, G0, show m ≠ idx by omega])
          (fun m hm => by simp [ChainState.toTreeChain, TreeChain.activeLSF, stTmp, show m < P.d by omega])
        change H.D.g H.len = stTmp.toTreeChain.chainGrad g' j
        rw [hCG]; exact H.hEndg }⟩
  have hPreGSucc' : ∀ j < idx, G0 (j + 1) = T.S (stWithLG.scState j) (stWithLG.bran j) := by
    intro j hj
    by_cases h1 : j + 1 = idx
    · have hpos : 0 < idx := by omega
      have hprev := hLoop.hCurGFromPrev hpos
      rw [show idx - 1 = j by omega] at hprev
      simp only [G0, h1, ↓reduceIte, stWithLG]
      exact hprev
    · simp only [G0, h1, ↓reduceIte, stWithLG]
      exact hLoop.hPreGSucc j (by omega)
  have hStRecFwd : ChainRecBound P (TP.γ_r (P.M₀ ^ 2)) st := by
    intro j hj
    refine ⟨?_, ?_⟩
    · by_cases hjt : j < idx
      · exact (hLoop.hLoopRecFwd j hjt).1
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        rw [hLoop.hCurFwdGe j hge, hLoop.hUpdGe j hge]
        exact (hInvOrig.hRecFwd j hj).1
    · by_cases hjt : j < idx
      · exact (hLoop.hLoopRecFwd j hjt).2
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        rw [hLoop.hCurFwdGe j hge, hLoop.hUpdGe j hge, hLoop.hRecGt (j + 1) (by omega)]
        by_cases hjeq : j = idx
        · rw [hjeq, hLoop.hCurRecAt]
          have h1 := (hInvOrig.hRecFwd idx hidxLt).2
          have hle : (stOrig.recUpdates idx : ℝ) - (stOrig.updCount idx : ℝ) ≤
              ((stOrig.recUpdates idx + curU.length : ℕ) : ℝ) - (stOrig.updCount idx : ℝ) := by
            push_cast; linarith
          exact le_trans h1 (mul_le_mul_of_nonneg_left hle hγr_nn)
        · have hgt : idx < j := lt_of_le_of_ne hge (Ne.symm hjeq)
          rw [hLoop.hRecGt j hgt]
          exact (hInvOrig.hRecFwd j hj).2
  have hPreRecReb : ∀ j < P.d,
      ((stWithLG.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        if j < idx then (stWithLG.updCount j : ℝ) else 0) ≤ (stWithLG.recUpdates j : ℝ) := by
    intro j hj
    split_ifs with hjt
    · exact hLoop.hLoopRecReb j hjt
    · have hge : idx ≤ j := Nat.le_of_not_lt hjt
      dsimp only [stWithLG]
      rw [congrFun hLoop.hCnt.2 j, add_zero]
      have hOrigJ := hInvOrig.hRecRebuild j hj
      have hupdNN : (0 : ℝ) ≤ (stOrig.updCount j : ℝ) := Nat.cast_nonneg _
      by_cases hjeq : j = idx
      · rw [hjeq] at hOrigJ ⊢
        rw [hLoop.hCurRecAt]
        push_cast
        linarith
      · rw [hLoop.hRecGt j (lt_of_le_of_ne hge (Ne.symm hjeq))]; linarith
  have hInvMid : ChainInv T L TP LP P N₀ stMidCore :=
    rebuildSuffix_preserves_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk hidxLt
      G0 stWithLG.scState stWithLG.bran stWithLG.updCount
      stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
      hG0Valid (by simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid) hGi0V hGi0m hG0m hG0n hℓ0 hℓ_idx
      hPreHist' (fun j hj => by dsimp only [stWithLG]; rw [hLoop.hBran]; exact hInvOrig.hBran j (lt_trans hj hidxLt))
      hPreGSucc' hPreRecReb hStRecFwd (fun hpos => by dsimp only [stWithLG]; exact hLoop.hPreEnc0 hpos)
      (hLoop.hLvlM.trans hInvOrig.hLvlM) (hLoop.hN0.trans hInvOrig.hN0) rfl
  set stMid : ChainState T P :=
    { stMidCore with
      rebuildCount := fun j => if j = idx then stWithLG.rebuildCount idx + 1 else stWithLG.rebuildCount j
      closedRuntime := stWithLG.closedRuntime + retiredTool + stWithLG.curLastCost + curEncAcc
      closedTreeUpdates := stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates }
  set changes := diffTreeChanges oldE stMid.toTreeChain.chainTree.E
  set stFinal : ChainState T P :=
    { stMid with closedTreeUpdates := stMid.closedTreeUpdates + changes.length }
  have hAlgoEq : algorithm1_rebuild T L P stWithLG idx curG curEncAcc = (stFinal, changes) := by
    dsimp only [algorithm1_rebuild]
    rw [dite_eq_left_iff.mpr fun h => absurd hidxLt h]
  have hRS := rebuildSuffix_spec_noHidden T L TP LP P N₀ hTP hLP hT hL hγM₀ hγk ℓ' g' (P.d - idx) idx
    G0 stWithLG.scState stWithLG.bran stWithLG.updCount
    stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd
    (by omega) (by simp only [G0, ↓reduceIte]; exact hLoop.hCurGValid) hGi0V hG0n hGi0m hℓ_idx
  have hResEq : res = rebuildSuffix T L P (levelM TP P) N₀ ℓ' g' (P.d - idx) idx
      G0 stWithLG.scState stWithLG.bran stWithLG.updCount
      stWithLG.curEnc stWithLG.curDecUpdates stWithLG.curFwd := by
    dsimp only [res, stWithLG]; rw [hLoop.hLvlM, hInvOrig.hLvlM, hLoop.hN0, hInvOrig.hN0]
  rw [← hResEq] at hRS
  have hRebFinal : ∀ j < P.d,
      (stFinal.rebuildCount j : ℝ) * ((intRebuildThreshold P N₀ j : ℝ) + 1) +
        (stFinal.updCount j : ℝ) ≤ (stFinal.recUpdates j : ℝ) := by
    intro j hj
    dsimp only [stFinal, stMid, stMidCore, stWithLG]
    by_cases hjt : j < idx
    · have hne : j ≠ idx := Nat.ne_of_lt hjt
      simp only [hne, ↓reduceIte]
      rw [(hRS.2.1 j hjt).2.2.1]
      exact hLoop.hLoopRecReb j hjt
    · have hge : idx ≤ j := Nat.le_of_not_lt hjt
      rw [(hRS.2.2.1 j hge hj).2.1]
      by_cases hjeq : j = idx
      · subst hjeq
        simp only [↓reduceIte, Nat.cast_add, Nat.cast_one]
        have hOverMax : (intRebuildThreshold P N₀ j : ℝ) + 1 ≤
            ((st.updCount j + curU.length : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hOver)
        have hOrigJ := hInvOrig.hRecRebuild j hj
        rw [← congrFun hLoop.hCnt.2 j, ← hLoop.hUpdGe j (le_refl j)] at hOrigJ
        rw [hLoop.hCurRecAt]
        push_cast at hOverMax ⊢
        nlinarith
      · have hgt : idx < j := lt_of_le_of_ne hge (Ne.symm hjeq)
        simp only [hjeq, ↓reduceIte, Nat.cast_zero, add_zero]
        have hOrigJ := hInvOrig.hRecRebuild j hj
        have hupdNN : (0 : ℝ) ≤ stOrig.updCount j := Nat.cast_nonneg _
        rw [congrFun hLoop.hCnt.2 j, hLoop.hRecGt j hgt]
        linarith
  have hInvFinal : ChainInv T L TP LP P N₀ stFinal :=
    chainInv_with_bookkeeping hInvMid rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hRebFinal
  have hG0Final : stFinal.G 0 = G0 0 := hRS.1 0 (Nat.zero_le _)
  have hn_le : (stOrig.G 0).n ≤ (stFinal.G 0).n := by
    rw [hG0Final]
    by_cases h0 : idx = 0
    · subst h0; simp only [G0, ↓reduceIte]; exact Finset.card_le_card (hLoop.hCurGV0 rfl).2.2.1
    · have hne0 : (0 : ℕ) ≠ idx := Ne.symm h0
      simp only [G0, hne0, ↓reduceIte]; exact Finset.card_le_card (hLoop.hG0New (Nat.pos_of_ne_zero h0)).2.2.2.1
  have hPreActive : ∀ j < idx,
      (stWithLG.toTreeChain.activeLSF j).F.F.E = (stMidCore.toTreeChain.activeLSF j).F.F.E := by
    intro j hj
    rcases hRS.2.1 j hj with ⟨a1, a2, _⟩
    have hjlt : j < P.d := lt_trans hj hidxLt
    simp only [TreeChain.activeLSF, ChainState.toTreeChain, hjlt, ↓reduceIte]
    change (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E =
      (T.lsfs (res.2.1 j) (res.2.2.1 j)).F.F.E
    rw [a1, a2]
  have hDiffCap : (changes.length : ℝ) ≤ diffTreeCap TP P idx := by
    have hCostMid := hInvMid.level_cost_bounds_noHidden hTP hLP hT hγM₀ hγk
    have htri := diffTreeChanges_chainTree_le_suffix (Nat.le_succ_of_le (Nat.le_of_lt hidxLt)) hPreActive
    have hStCard : ∀ j ≤ P.d, ((stWithLG.toTreeChain.activeLSF j).F.F.E.card : ℝ) ≤
        (levelM TP P j : ℝ) := by
      intro j hj
      by_cases hjt : j < idx
      · obtain ⟨H⟩ := hLoop.hPreHist j hjt
        have hSpec := hT P.k H.len (levelM TP P j) N₀ H.D H.restarts
          P.hk H.hG0 H.hD H.hLen H.hℓPos H.hInitMBound H.hInitNBound H.hRestartsLt
          (by rw [H.hUpd]; exact H.hThresh)
        have hAt := hSpec.1 H.len (le_refl _) (stWithLG.bran j) (by
          dsimp only [stWithLG]; rw [hLoop.hBran]; exact hInvOrig.hBran j (lt_trans hjt hidxLt))
        have hsubE : (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E ⊆ (stWithLG.G j).E := by
          rw [H.hRun, ← H.hEndG]
          exact hAt.1.2.1.2.2.2.2.2.1
        have hactive : (stWithLG.toTreeChain.activeLSF j).F.F.E =
            (T.lsfs (stWithLG.scState j) (stWithLG.bran j)).F.F.E := by
          simp [TreeChain.activeLSF, ChainState.toTreeChain, lt_trans hjt hidxLt]
        rw [hactive]
        exact le_trans (by exact_mod_cast Finset.card_le_card hsubE) (hLoop.hPreM j hjt)
      · have hge : idx ≤ j := Nat.le_of_not_lt hjt
        have hActEq : (stWithLG.toTreeChain.activeLSF j).F.F.E =
            (stOrig.toTreeChain.activeLSF j).F.F.E := by
          by_cases hjd : j < P.d
          · simp [TreeChain.activeLSF, ChainState.toTreeChain, hjd, stWithLG,
              hLoop.hScGe j hge, hLoop.hBran]
          · have hjeq : j = P.d := by omega
            subst hjeq
            simp [TreeChain.activeLSF, ChainState.toTreeChain, stWithLG,
              hLoop.hLast.2.1, hLoop.hLast.2.2]
        rw [hActEq]
        exact hOrigCost.2.2.2.2 j hj
    unfold diffTreeCap
    calc
      (changes.length : ℝ)
          ≤ ∑ j ∈ Finset.Ico idx (P.d + 1),
              (((stWithLG.toTreeChain.activeLSF j).F.F.E.card : ℝ) +
                ((stMid.toTreeChain.activeLSF j).F.F.E.card : ℝ)) := by exact_mod_cast htri
      _ ≤ ∑ j ∈ Finset.Ico idx (P.d + 1),
            ((levelM TP P j : ℝ) + (levelM TP P j : ℝ)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjd := Nat.lt_succ_iff.mp (Finset.mem_Ico.mp hj).2
        exact add_le_add (hStCard j hjd) (hCostMid.2.2.2.2 j hjd)
      _ = 2 * ∑ j ∈ Finset.Ico idx (P.d + 1), (levelM TP P j : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
  have hBudget : ChainBudgetInvWith TP LP N₀ stFinal (overflow + extraOverflow) := by
    refine ⟨?_, ?_⟩
    · have hOldR := hBudgetOrig.1
      have hSumEq := sum_range_inc_coeff P.d idx (Nat.le_of_lt hidxLt)
        (fun j => stOrig.shiftCount j + stOrig.rebuildCount j)
        (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
        (fun j _ => by
          dsimp only [stFinal, stMid, stMidCore, stWithLG]
          rw [hLoop.hCnt.1, hLoop.hCnt.2]
          split_ifs with h <;> [subst h; rfl]; omega)
        (opRuntimeBudget TP LP P N₀)
      have hRetTool : (retiredTool : ℝ) ≤
          (Finset.Ico idx P.d).sum (levelToolCap TP P N₀) +
            ∑ j ∈ Finset.Ico idx P.d, (stOrig.curRestarts j : ℝ) * restartCostCap TP P N₀ j := by
        push_cast [retiredTool]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_le_sum fun j hj => ?_
        have hmem := Finset.mem_Ico.mp hj
        by_cases hjeq : j = idx
        · subst hjeq
          rw [show stWithLG.scState j = stOrig.scState j from hLoop.hScGe j (le_refl j)]
          by_cases h0 : j = 0
          · subst h0
            rw [show stWithLG.curEnc 0 = stOrig.curEnc 0 from (hLoop.hCurEnc0 rfl).1]
            exact hOrigCost.1 0 hidxLt
          · have hpos := Nat.pos_of_ne_zero h0
            have hEncBd := (hLoop.hCurEncPos hpos).2 hidxLt
            obtain ⟨Ho⟩ := hInvOrig.hHist j hidxLt
            have hCostO := Ho.cost_le_cap_add_restart hTP hT hγM₀ hγk hidxLt
            have hCapJ : levelToolCap TP P N₀ j =
                2 * TP.c_T * ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ j + 1) *
                  (P.k : ℝ) * TP.γ_r (P.M₀ ^ 2) * (2 * logFactor P N₀) ^ TP.p_T +
                5 * TP.γ_r (P.M₀ ^ 2) *
                  ((P.M₀ : ℝ) * TP.γ_ℓ (P.M₀ ^ 2) * (TP.γ_ℓ (P.M₀ ^ 2) / P.k) ^ (j - 1) / (P.k : ℝ) + 1) := by
              unfold levelToolCap; rw [ite_eq_right_iff.mpr fun h => absurd h h0]
            change (T.cost (stOrig.scState j) : ℝ) + (st.curEnc j : ℝ) ≤ _
            linarith
        · have hgt : idx < j := lt_of_le_of_ne hmem.1 (Ne.symm hjeq)
          rw [show stWithLG.scState j = stOrig.scState j from hLoop.hScGe j hmem.1,
            show stWithLG.curEnc j = stOrig.curEnc j from hLoop.hEncGt j hgt]
          exact hOrigCost.1 j hmem.2
      have hLastC : (stWithLG.curLastCost : ℝ) ≤ lastCostCap TP LP P N₀ := by
        rw [show stWithLG.curLastCost = stOrig.curLastCost from hLoop.hLastStats.2.1]
        exact hOrigCost.2.2.1 P.hd
      have hExBd : (curEncAcc : ℝ) ≤ (if idx = 0 then extraEncCap P else 0) + extraOverflow := by
        by_cases h0 : idx = 0
        · subst h0; simp only [↓reduceIte]; exact (hLoop.hCurEnc0 rfl).2.2
        · simp only [h0, ↓reduceIte]; rw [(hLoop.hCurEncPos (Nat.pos_of_ne_zero h0)).1]; simpa using hExtraNN
      have hCR : (stFinal.closedRuntime : ℝ) =
          (stOrig.closedRuntime : ℝ) + (retiredTool : ℝ) + (stWithLG.curLastCost : ℝ) +
            (curEncAcc : ℝ) := by
        change ((stWithLG.closedRuntime + retiredTool + stWithLG.curLastCost + curEncAcc : ℕ) : ℝ) = _
        rw [show stWithLG.closedRuntime = stOrig.closedRuntime from hLoop.hClosed.1]
        push_cast; rfl
      have hCRest : stFinal.curRestarts =
          fun j => if idx ≤ j ∧ j < P.d then 0 else stOrig.curRestarts j := by
        ext j; dsimp only [stFinal, stMid, stMidCore, stWithLG]; rw [hLoop.hRestarts]
      have hAR := activeRestartCap_rebuild TP P N₀ idx (Nat.le_of_lt hidxLt) stOrig.curRestarts
      have hOpR : opRuntimeBudget TP LP P N₀ idx =
          (Finset.Ico idx P.d).sum (levelToolCap TP P N₀) +
            lastCostCap TP LP P N₀ + (if idx = 0 then extraEncCap P else 0) := by
        unfold opRuntimeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hidxLt h]
      rw [hCR, hCRest, hSumEq, hOpR]
      linarith [hOldR]
    · have hSumEq := sum_range_inc_coeff P.d idx (Nat.le_of_lt hidxLt)
        (fun j => stOrig.shiftCount j + stOrig.rebuildCount j)
        (fun j => stFinal.shiftCount j + stFinal.rebuildCount j)
        (fun j _ => by
          dsimp only [stFinal, stMid, stMidCore, stWithLG]
          rw [hLoop.hCnt.1, hLoop.hCnt.2]
          split_ifs with h <;> [subst h; rfl]; omega)
        (opTreeBudget TP P)
      have hRetDec : (retiredDec : ℝ) ≤ (Finset.Ico idx P.d).sum (levelDecCap TP P) := by
        push_cast [retiredDec]
        refine Finset.sum_le_sum fun j hj => ?_
        have hmem := Finset.mem_Ico.mp hj
        rw [show stWithLG.curDecUpdates j = stOrig.curDecUpdates j from hLoop.hDecGe j hmem.1]
        exact hOrigCost.2.1 j hmem.2
      have hLastT : (stWithLG.curLastTreeUpdates : ℝ) ≤ lastTreeCap TP P := by
        rw [show stWithLG.curLastTreeUpdates = stOrig.curLastTreeUpdates from hLoop.hLastStats.2.2]
        exact hOrigCost.2.2.2.1
      have hCL : (stFinal.closedTreeUpdates : ℝ) =
          (stOrig.closedTreeUpdates : ℝ) + (retiredDec : ℝ) + (stWithLG.curLastTreeUpdates : ℝ) +
            (changes.length : ℝ) := by
        change ((stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates + changes.length : ℕ) : ℝ) = _
        rw [show stWithLG.closedTreeUpdates = stOrig.closedTreeUpdates from hLoop.hClosed.2]
        push_cast; rfl
      have hOpT : opTreeBudget TP P idx =
          (Finset.Ico idx P.d).sum (levelDecCap TP P) + lastTreeCap TP P + diffTreeCap TP P idx := by
        unfold opTreeBudget; rw [ite_eq_left_iff.mpr fun h => absurd hidxLt h]
      rw [hCL, hSumEq, hOpT]
      linarith [hBudgetOrig.2]
  rw [hAlgoEq]
  refine ⟨hInvFinal, hBudget, hn_le,
    fun i => by dsimp only [stFinal, stMid, stMidCore, stWithLG]; exact (congrFun hLoop.hCnt.1 i).symm,
    fun i => by
      change stOrig.rebuildCount i ≤ if i = idx then stWithLG.rebuildCount idx + 1 else stWithLG.rebuildCount i
      have hRc := congrFun hLoop.hCnt.2
      dsimp only [stWithLG] at hRc ⊢
      split_ifs with h
      · rw [h, hRc]; exact Nat.le_succ _
      · rw [hRc],
    ?_⟩
  have hSumDec :
      (Finset.range P.d).sum stFinal.curDecUpdates + retiredDec =
        (Finset.range P.d).sum st.curDecUpdates := by
    have hsplit : Finset.range P.d = Finset.range idx ∪ Finset.Ico idx P.d := by
      ext j; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
    have hdisj : Disjoint (Finset.range idx) (Finset.Ico idx P.d) := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [Finset.mem_range, Finset.mem_Ico] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj, Finset.sum_union hdisj]
    have hPreEq : (Finset.range idx).sum stFinal.curDecUpdates = (Finset.range idx).sum st.curDecUpdates := by
      refine Finset.sum_congr rfl fun j hj => ?_
      exact (hRS.2.1 j (Finset.mem_range.mp hj)).2.2.2.2.1
    have hZero : (Finset.Ico idx P.d).sum stFinal.curDecUpdates = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hmem := Finset.mem_Ico.mp hj
      exact (hRS.2.2.1 j hmem.1 hmem.2).2.2.2.1
    change (Finset.range idx).sum stFinal.curDecUpdates + (Finset.Ico idx P.d).sum stFinal.curDecUpdates +
        retiredDec = _
    rw [hPreEq, hZero, add_zero]
  have hStepLen : (diffTreeChanges st.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E).length =
      changes.length := rfl
  have hTri := diffTreeChanges_length_triangle stOrig.toTreeChain.chainTree.E
    st.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E
  unfold ChainState.totalTreeUpdates
  change (diffTreeChanges stOrig.toTreeChain.chainTree.E stFinal.toTreeChain.chainTree.E).length +
      (stOrig.closedTreeUpdates + (Finset.range P.d).sum stOrig.curDecUpdates +
        stOrig.curLastTreeUpdates) ≤
    stWithLG.closedTreeUpdates + retiredDec + stWithLG.curLastTreeUpdates + changes.length +
      (Finset.range P.d).sum stFinal.curDecUpdates + 0
  rw [hLoop.hClosed.2, hLoop.hLastStats.2.2]
  rw [hStepLen] at hTri
  have hTD := hLoop.hTreeDiff
  omega

end MinCostFlow.Chain
