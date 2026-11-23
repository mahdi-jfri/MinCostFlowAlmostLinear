module

public import MinCostFlow.Chain.UpdatePreLoopHelpers

/-!
# Pre-loop hidden-strategy bridge across `algorithm1_update`

This file proves `alg2HiddenTrace_update_preLoop` (via the two cases `firstRebuiltLevel = none`
and `firstRebuiltLevel = some iStar`), advancing `Alg2HiddenTrace` from `t` across
`translateBatch` + `algorithm1_update` and appending the round-completing step `m₁` plus the
adversary step `m₂` (`.advDoNothing` or `.advRebuild iStar newStr`) to reach `(t + 1)` ready for
`algorithm2_loop`.
-/

@[expose] public section

namespace MinCostFlow.Chain

/-- Case 1 of `alg2HiddenTrace_update_preLoop`: no level rebuild occurred (`firstRebuiltLevel = none`). -/
private lemma alg2HiddenTrace_update_preLoop_none (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (_hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (_ht1 : t + 1 ≤ T)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    {extG' : MGraph} {e2i' i2e' : ℕ → ℕ} {nf' : ℕ} {U_int : List Update}
    (hTB : translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1)) =
      (extG', e2i', i2e', nf', U_int))
    (hExtG' : extG' = (D.G t).applyBatch (D.U (t + 1)))
    (hG1eq : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)))
    (hi2e_old : ∀ e' < st.nextFresh, i2e' e' = st.intToExt e')
    (hYesInsExt : ∀ e ∈ extG'.E, (∃ u ∈ D.U (t + 1), u.Inserts e) → st.nextFresh ≤ e2i' e)
    (hInv1 : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1)
    (hn1Last : ((algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.G cfg.P.d).n ≤ nLast)
    (hFresh' : FreshInv extG'
      ((algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.G 0)
      e2i' i2e' nf')
    (hShEq : ∀ i, st.chain.shiftCount i =
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.shiftCount i)
    (H1 : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1 k)
    (hCore1 : ChainCoreRel cfg.T cfg.TP cfg.P
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1 H1)
    (hNone : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.rebuildCount = none)
    (hNoneData : ∀ k (hk : k < cfg.P.d),
      (H1 k hk).len = (tr.H k hk).len + 1 ∧
      (∀ s ≤ (tr.H k hk).len,
        (H1 k hk).D.G s = (tr.H k hk).D.G s ∧ (H1 k hk).D.U s = (tr.H k hk).D.U s ∧
        (H1 k hk).D.ℓ s = (tr.H k hk).D.ℓ s ∧ (H1 k hk).D.g s = (tr.H k hk).D.g s) ∧
      (k = 0 → (H1 k hk).D.U ((tr.H k hk).len + 1) = U_int) ∧
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.bran k =
          st.chain.bran k ∧
      (H1 k hk).s₀ = (tr.H k hk).s₀ ∧
      (∀ s ≤ (tr.H k hk).len, (H1 k hk).restarts s = (tr.H k hk).restarts s)) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext (t + 1)
      { st with
        chain := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
          (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
        extG := extG'
        extToInt := e2i'
        intToExt := i2e'
        nextFresh := nf'
        extℓ := D.ℓ (t + 1)
        extg := D.g (t + 1) }) := by
  let g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
  let ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
  have hRebEq : ch1.rebuildCount = st.chain.rebuildCount :=
    rebuildCount_of_updateLoop_none cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int st.chain U_int hNone
  have hExtEq : extG' = D.G (t + 1) := by rw [hExtG', hG1eq]
  have hFrD1 : FreshInv (D.G (t + 1)) (ch1.G 0) e2i' i2e' nf' := hExtEq ▸ hFresh'
  have hℓ1 : ch1.ℓ = fun e' => D.ℓ (t + 1) (i2e' e') := hG0ℓ1.2.1
  have hSH1 := chainState_snapHoldsAt nLast hV hInv1 hFrD1 hℓ1 hn1 hn1Last
  let gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  let R := (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round
  let W' : ℕ → ℝ := fun r => if r = R + 1 then (D.G (t + 1)).norm1 (w_ext (t + 1)) else tr.W_game r
  have hW_le : ∀ r ≤ R, tr.W_game r = W' r := fun r hr => by
    simp [W', Nat.ne_of_lt (lt_of_le_of_lt hr (Nat.lt_succ_self R))]
  let m₁ : Game.Move cfg.P.d cfg.P.k := .roundStep .roundCompleting .doNothing (fun _ _ => 0)
  let m₂ : Game.Move cfg.P.d cfg.P.k := .advDoNothing
  have hPh : gSt.phase = .stage34 := tr.hPhase
  have hm1_v : Game.ValidStep cfg.gameParams W' gSt m₁ := by simp [Game.ValidStep, hPh, m₁]
  have hm1_s : Game.StrategyStep cfg.gameParams gSt
      (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁ := by
    simp [Game.StrategyStep, hPh, m₁]
    exact rfl
  have hm2_v : Game.ValidStep cfg.gameParams W' (Game.stepState W' cfg.P.hk gSt m₁) m₂ := by
    have hgr : gSt.round = R := rfl
    simp only [Game.ValidStep, Game.stepState, m₁, m₂, W', hgr, ↓reduceIte]
    exact ⟨weightValid_norm1_of_hiddenStableAt hV.hα hm1 hHS1, trivial⟩
  have hm2_s : Game.StrategyStep cfg.gameParams (Game.stepState W' cfg.P.hk gSt m₁)
      (Game.stepPasses cfg.P.hk gSt
        (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁) m₂ := by
    simp [Game.StrategyStep, Game.stepState, m₁]
  have hTwo := game_append_two_steps cfg.gameParams hW_le tr.hv tr.hf m₁ m₂
    hm1_v hm1_s hm2_v hm2_s
  let moves' := tr.moves ++ [m₁, m₂]
  let gSt' := Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length
  have hgSt' : gSt' = { gSt with round := R + 1, phase := .stage34 } :=
    hTwo.2.2.1.trans (by simp only [Game.stepState, m₁, m₂]; rfl)
  have hPas' : Game.passesAt W' cfg.P.hk tr.initStr moves' moves'.length =
      Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length :=
    hTwo.2.2.2.trans (by simp only [Game.stepPasses, m₁, m₂]; rfl)
  have hREnd : (Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length).round = R + 1 := by
    change gSt'.round = R + 1; simp [hgSt']
  let timeOfRound' : ℕ → ℕ := fun r => if r = R + 1 then t + 1 else tr.timeOfRound r
  let snapC' : ℕ → TreeChain := fun r => if r = R + 1 then ch1.toTreeChain else tr.snapC r
  let snapE2I' : ℕ → ℕ → ℕ := fun r => if r = R + 1 then e2i' else tr.snapE2I r
  let snapI2E' : ℕ → ℕ → ℕ := fun r => if r = R + 1 then i2e' else tr.snapI2E r
  let snapNF' : ℕ → ℕ := fun r => if r = R + 1 then nf' else tr.snapNF r
  let lvlIdx' : ℕ → ℕ → ℕ := fun r k =>
    if r = R + 1 then (if hk : k < cfg.P.d then (H1 k hk).len else 0) else tr.lvlIdx r k
  let updRound' : ℕ → ℕ := fun τ =>
    if τ = (tr.H 0 cfg.P.hd).len + 1 then R + 1 else tr.updRound τ
  refine ⟨⟨moves', by simp [moves'], tr.initStr, W', hTwo.1, hTwo.2.1, ?_, timeOfRound', ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, snapC', snapE2I', snapI2E', snapNF', ?_, ?_, ?_, ?_, ?_, ?_, tr.reinit,
    ?_, ?_, ?_, ?_, H1, lvlIdx', ?_, ?_, ?_, ?_, ?_, fun k hk => by simpa using (hCore1 k hk).2,
    updRound', ?_, ?_, ?_, ?_, ?_⟩⟩
  · change gSt'.phase = .stage34; simp [hgSt']
  · intro r₁ r₂ hr₁₂ hr₂
    rw [hREnd] at hr₂
    by_cases h2 : r₂ = R + 1
    · subst h2
      by_cases h1 : r₁ = R + 1
      · simp [h1]
      · simp only [timeOfRound', h1, ↓reduceIte]
        have hr₁_le : r₁ ≤ R := by omega
        calc tr.timeOfRound r₁ ≤ tr.timeOfRound R := tr.hTimeMono r₁ R hr₁_le (le_refl R)
          _ = t := tr.hTimeEnd
          _ ≤ t + 1 := Nat.le_succ t
    · have hr₂_le : r₂ ≤ R := by omega
      simp only [timeOfRound', show r₁ ≠ R + 1 by omega, h2, ↓reduceIte]
      exact tr.hTimeMono r₁ r₂ hr₁₂ hr₂_le
  · rw [hREnd]; simp [timeOfRound']
  · intro r hr
    rw [hREnd] at hr
    by_cases hR : r = R + 1
    · simp [W', timeOfRound', hR]
    · simp only [W', timeOfRound', hR, ↓reduceIte]
      exact tr.hW_eq r (by omega)
  · intro i
    rw [shiftCount_append_round_adv tr.moves m₂ (Or.inl rfl) i, tr.hShiftMatch i, ← hShEq i.val]
  · intro i
    have hrc : Game.rebuildCount moves' i = Game.rebuildCount tr.moves i := by
      simp [Game.rebuildCount, moves', m₁, m₂, List.countP_append]
    rw [hrc, tr.hRebMatch i, hRebEq]
  · intro i; rw [hPas']; exact tr.hPassMatch i
  · intro i
    change (gSt'.bran i).val = _
    rw [hgSt']
    by_cases hi : i.val < cfg.P.d
    · simp only [hi, ↓reduceIte, (hNoneData i.val hi).2.2.2.1]
      simpa [hi] using tr.hBranMatch i
    · simpa [hi] using tr.hBranMatch i
  · rw [hREnd]; simp [snapC', ch1, g_int, ℓ_int]
  · rw [hREnd]; simp [snapE2I']
  · rw [hREnd]; simp [snapI2E']
  · rw [hREnd]; simp [snapNF']
  · intro r hr; rw [hREnd] at hr
    by_cases hR : r = R + 1
    · subst hR
      simpa [snapC', snapE2I', snapI2E', snapNF', timeOfRound', ChainState.toTreeChain] using hFrD1
    · simp only [snapC', snapE2I', snapI2E', snapNF', timeOfRound', hR, ↓reduceIte]
      exact tr.hSnapFresh r (by omega)
  · intro r hr; rw [hREnd] at hr
    by_cases hR : r = R + 1
    · subst hR
      simpa [snapC', snapI2E', timeOfRound', ChainState.toTreeChain, ch1, g_int, ℓ_int] using hSH1
    · simp only [snapC', snapI2E', timeOfRound', hR, ↓reduceIte]
      exact tr.hSnapHolds r (by omega)
  · intro i
    change tr.reinit i ≤ gSt'.repT i
    rw [hgSt']; exact tr.hRebRep i
  · intro i
    change gSt'.repT ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ tr.reinit ⟨i.val + 1, _⟩
    rw [hgSt']; exact tr.hRepRe i
  · intro i hi r hr1 hr2 b hb
    rw [hREnd] at hr2
    by_cases hR : r = R + 1
    · subst hR
      simp only [snapC', ↓reduceIte, ChainState.toTreeChain, ↓reduceIte]
      rfl
    · simp only [snapC', hR, ↓reduceIte]
      rw [tr.hSnapBran i hi r hr1 (by omega) b hb]
      exact ((hNoneData b (lt_of_lt_of_le hb hi)).2.2.2.1).symm
  · intro i j
    change gSt'.str i j = if h : i.val < cfg.P.d then
        hstrAt (snapC' (gSt'.repT i))
          (fun e' => w_ext (timeOfRound' (gSt'.repT i)) (snapI2E' (gSt'.repT i) e'))
          i.val j.val
      else 0
    rw [hgSt']
    dsimp only [gSt]
    have hrep_le : (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i ≤ R :=
      (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length i).2
    have hneq : (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i ≠ R + 1 :=
      Nat.ne_of_lt (Nat.lt_succ_of_le hrep_le)
    simp only [snapC', snapI2E', timeOfRound', hneq, ↓reduceIte]
    exact tr.hStrMatch i j
  · intro i hi
    have hneq : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≠ R + 1 := by
      have := (tr.hRebRep ⟨i, Nat.lt_succ_of_le hi.le⟩).trans
        (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
      omega
    simp [lvlIdx', hneq, tr.hLvlReinit i hi]
  · intro i hi; rw [hREnd]; simp [lvlIdx', hi]
  · intro i hi r₁ r₂ hr1 hr12 hr2; rw [hREnd] at hr2
    by_cases h2 : r₂ = R + 1
    · subst h2
      by_cases h1 : r₁ = R + 1
      · simp [h1]
      · simp only [lvlIdx', h1, ↓reduceIte, hi, ↓reduceDIte]
        have hr1_le : r₁ ≤ R := by omega
        calc tr.lvlIdx r₁ i ≤ tr.lvlIdx R i := tr.hLvlMono i hi r₁ R hr1 hr1_le (le_refl R)
          _ = (tr.H i hi).len := tr.hLvlEnd i hi
          _ ≤ (H1 i hi).len := by rw [(hNoneData i hi).1]; exact Nat.le_succ _
    · simp only [lvlIdx', show r₁ ≠ R + 1 by omega, h2, ↓reduceIte]
      exact tr.hLvlMono i hi r₁ r₂ hr1 hr12 (by omega)
  · intro i hi
    have hi0 : i < cfg.P.d := Nat.lt_of_succ_lt hi
    have hlen1 : (H1 (i + 1) hi).len = (tr.H (i + 1) hi).len + 1 := (hNoneData (i + 1) hi).1
    have hlen0 : (H1 i hi0).len = (tr.H i hi0).len + 1 := (hNoneData i hi0).1
    have hOld := tr.hLvlSucc i hi
    refine ⟨by omega, fun r hr1 hr2 => ?_⟩
    rw [hREnd] at hr2
    by_cases hR : r = R + 1
    · subst hR
      simp only [lvlIdx', hi, hi0, ↓reduceIte, ↓reduceDIte]
      exact Nat.add_sub_of_le (by omega)
    · simp only [lvlIdx', hR, ↓reduceIte]
      have hdiff : (H1 i hi0).len - (H1 (i + 1) hi).len =
          (tr.H i hi0).len - (tr.H (i + 1) hi).len := by omega
      rw [hdiff]
      exact hOld.2 r hr1 (by omega)
  · intro i hi r hr1 hr2; rw [hREnd] at hr2
    have hData := lvlSnap_unrebuilt tr i hi (H1 i hi) (hNoneData i hi).1 (hNoneData i hi).2.1
      (hNoneData i hi).2.2.2.2.2 r hr1 hr2
    simp only [lvlIdx', hi, ↓reduceDIte]
    exact hData
  · intro τ hτ
    have hlen0 : (H1 0 cfg.P.hd).len = (tr.H 0 cfg.P.hd).len + 1 := (hNoneData 0 cfg.P.hd).1
    rw [hlen0] at hτ
    by_cases htop : τ = (tr.H 0 cfg.P.hd).len + 1
    · simp only [updRound', htop, ↓reduceIte, hREnd]
      exact ⟨le_trans (tr.hRebRep ⟨0, Nat.succ_pos _⟩)
        (le_trans (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
          (Nat.le_succ R)), le_refl _⟩
    · have hB := tr.hUpdBound τ (by omega)
      simp only [updRound', htop, ↓reduceIte, hREnd]
      exact ⟨hB.1, Nat.le_succ_of_le hB.2⟩
  · intro τ₁ τ₂ h12 h2
    have hlen0 : (H1 0 cfg.P.hd).len = (tr.H 0 cfg.P.hd).len + 1 := (hNoneData 0 cfg.P.hd).1
    rw [hlen0] at h2
    by_cases htop : τ₂ = (tr.H 0 cfg.P.hd).len + 1
    · have h1_le : τ₁ ≤ (tr.H 0 cfg.P.hd).len := by omega
      simp only [updRound', htop, ↓reduceIte, show τ₁ ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
      exact Nat.lt_succ_of_le (tr.hUpdBound τ₁ h1_le).2
    · simp only [updRound', htop, ↓reduceIte, show τ₁ ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
      exact tr.hUpdMono τ₁ τ₂ h12 (by omega)
  · intro r hr1 hr2; rw [hREnd] at hr2
    have hlen0 : (H1 0 cfg.P.hd).len = (tr.H 0 cfg.P.hd).len + 1 := (hNoneData 0 cfg.P.hd).1
    by_cases hR : r = R + 1
    · subst hR
      simp only [lvlIdx', ↓reduceIte, cfg.P.hd, ↓reduceDIte, hlen0, updRound']
      exact ⟨le_refl _, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
    · have hOld := tr.hUpdBand r hr1 (by omega)
      have hidx_le : tr.lvlIdx r 0 ≤ (tr.H 0 cfg.P.hd).len := by
        rw [← tr.hLvlEnd 0 cfg.P.hd]
        exact tr.hLvlMono 0 cfg.P.hd r R hr1 (by omega) (le_refl R)
      simp only [lvlIdx', hR, ↓reduceIte, updRound',
        show tr.lvlIdx r 0 ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
      refine ⟨hOld.1, fun hlt => ?_⟩
      by_cases heq : tr.lvlIdx r 0 = (tr.H 0 cfg.P.hd).len
      · simp [heq]; omega
      · have hlt0 : tr.lvlIdx r 0 < (tr.H 0 cfg.P.hd).len := by omega
        simpa [show tr.lvlIdx r 0 ≠ (tr.H 0 cfg.P.hd).len by omega] using hOld.2 hlt0
  · intro τ hτ
    have hlen0 : (H1 0 cfg.P.hd).len = (tr.H 0 cfg.P.hd).len + 1 := (hNoneData 0 cfg.P.hd).1
    rw [hlen0] at hτ
    by_cases htop : τ = (tr.H 0 cfg.P.hd).len + 1
    · subst htop
      simp only [updRound', ↓reduceIte, snapC', snapI2E', timeOfRound']
      have hG_end : (H1 0 cfg.P.hd).D.G ((tr.H 0 cfg.P.hd).len + 1) = ch1.G 0 := by
        rw [← hlen0]; exact (H1 0 cfg.P.hd).hEndG
      refine ⟨hG_end.trans (by simp [ChainState.toTreeChain]), fun e' he' => ?_⟩
      have he'_ch1 : e' ∈ (ch1.G 0).E := by rw [← hG_end]; exact he'
      have hℓ_end := (H1 0 cfg.P.hd).hEndℓ e' he'_ch1
      rw [← hlen0, hℓ_end, TreeChain.chainLen, hℓ1]
    · have hτ_le : τ ≤ (tr.H 0 cfg.P.hd).len := by omega
      have huR : tr.updRound τ ≤ R := (tr.hUpdBound τ hτ_le).2
      have hOld := tr.hLvl0Match τ hτ_le
      have hPref0 := (hNoneData 0 cfg.P.hd).2.1 τ hτ_le
      simp only [updRound', htop, ↓reduceIte, snapC', snapI2E', timeOfRound',
        show tr.updRound τ ≠ R + 1 by omega]
      refine ⟨hPref0.1.trans hOld.1, fun e' he' => ?_⟩
      rw [hPref0.2.2.1]; exact hOld.2 e' (hPref0.1 ▸ he')
  · have hData := lvl0NoIns_unrebuilt tr hFresh hExtG hTB hFresh' hG0ℓ1.1
      hi2e_old hYesInsExt (H1 0 cfg.P.hd) (hNoneData 0 cfg.P.hd).1
      (hNoneData 0 cfg.P.hd).2.1 ((hNoneData 0 cfg.P.hd).2.2.1 rfl)
    simpa [hREnd, snapI2E', timeOfRound', updRound'] using hData

/-- Case 2 of `alg2HiddenTrace_update_preLoop`: some level `iStar < P.d` was rebuilt. -/
private lemma alg2HiddenTrace_update_preLoop_some (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    {extG' : MGraph} {e2i' i2e' : ℕ → ℕ} {nf' : ℕ} {U_int : List Update}
    (hTB : translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1)) =
      (extG', e2i', i2e', nf', U_int))
    (hExtG' : extG' = (D.G t).applyBatch (D.U (t + 1)))
    (hG1eq : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)))
    (hi2e_old : ∀ e' < st.nextFresh, i2e' e' = st.intToExt e')
    (hYesInsExt : ∀ e ∈ extG'.E, (∃ u ∈ D.U (t + 1), u.Inserts e) → st.nextFresh ≤ e2i' e)
    (hInv1 : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1)
    (hn1Last : ((algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.G cfg.P.d).n ≤ nLast)
    (hFresh' : FreshInv extG'
      ((algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.G 0)
      e2i' i2e' nf')
    (hShEq : ∀ i, st.chain.shiftCount i =
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.shiftCount i)
    (H1 : ∀ k < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1 k)
    (hCore1 : ChainCoreRel cfg.T cfg.TP cfg.P
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1 H1)
    {iStar : ℕ}
    (hSome : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
      (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
        (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.rebuildCount =
          some iStar)
    (hSomeData : iStar < cfg.P.d ∧
      (∀ k (hk : k < cfg.P.d), k < iStar →
        (H1 k hk).len = (tr.H k hk).len + 1 ∧
        (∀ s ≤ (tr.H k hk).len,
          (H1 k hk).D.G s = (tr.H k hk).D.G s ∧ (H1 k hk).D.U s = (tr.H k hk).D.U s ∧
          (H1 k hk).D.ℓ s = (tr.H k hk).D.ℓ s ∧ (H1 k hk).D.g s = (tr.H k hk).D.g s) ∧
        (k = 0 → (H1 k hk).D.U ((tr.H k hk).len + 1) = U_int) ∧
        (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
          (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.bran k =
            st.chain.bran k ∧
        (H1 k hk).s₀ = (tr.H k hk).s₀ ∧
        (∀ s ≤ (tr.H k hk).len, (H1 k hk).restarts s = (tr.H k hk).restarts s)) ∧
      (∀ k (hk : k < cfg.P.d), iStar ≤ k →
        (H1 k hk).len = 0 ∧
        (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
          (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1.bran k = 0)) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext (t + 1)
      { st with
        chain := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
          (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
        branD := 0
        passes := fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j
        extG := extG'
        extToInt := e2i'
        intToExt := i2e'
        nextFresh := nf'
        extℓ := D.ℓ (t + 1)
        extg := D.g (t + 1) }) := by
  let g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
  let ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
  have hReb := rebuildCount_of_updateLoop_some cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int st.chain U_int hSome
  have hiStarLt : iStar < cfg.P.d := hSomeData.1
  have hExtEq : extG' = D.G (t + 1) := by rw [hExtG', hG1eq]
  have hFrD1 : FreshInv (D.G (t + 1)) (ch1.G 0) e2i' i2e' nf' := hExtEq ▸ hFresh'
  have hℓ1 : ch1.ℓ = fun e' => D.ℓ (t + 1) (i2e' e') := hG0ℓ1.2.1
  have hSH1 := chainState_snapHoldsAt nLast hV hInv1 hFrD1 hℓ1 hn1 hn1Last
  have hℓ_nn : ∀ e' ∈ (ch1.G 0).E, 0 ≤ D.ℓ (t + 1) (i2e' e') := fun e' he' =>
    (hHist.2.1 (t + 1) ht1).2 _ (hFrD1.hRight e' he').2 |>.le
  have hw_nn : ∀ e' ∈ (ch1.G 0).E, 0 ≤ w_ext (t + 1) (i2e' e') := fun e' he' =>
    (hHS1.2.2.2.2 _ (hFrD1.hRight e' he').2).1.le
  have hNewStr_ok := chain_validStretch_hstr hV hSH1.1 hSH1.2.1 hSH1.2.2.1 hSH1.2.2.2.1
    hSH1.2.2.2.2 hℓ_nn hw_nn
  let gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  let R := (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round
  let W' : ℕ → ℝ := fun r => if r = R + 1 then (D.G (t + 1)).norm1 (w_ext (t + 1)) else tr.W_game r
  have hW_le : ∀ r ≤ R, tr.W_game r = W' r := fun r hr => by
    simp [W', Nat.ne_of_lt (lt_of_le_of_lt hr (Nat.lt_succ_self R))]
  let iFin : Fin (cfg.P.d + 1) := ⟨iStar, Nat.lt_succ_of_lt hiStarLt⟩
  let newStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ := fun i' j' =>
    if _hi : i'.val < cfg.P.d then
      hstrAt ch1.toTreeChain (fun e' => w_ext (t + 1) (i2e' e')) i'.val j'.val
    else 0
  let m₁ : Game.Move cfg.P.d cfg.P.k := .roundStep .roundCompleting .doNothing (fun _ _ => 0)
  let m₂ : Game.Move cfg.P.d cfg.P.k := .advRebuild iFin newStr
  have hPh : gSt.phase = .stage34 := tr.hPhase
  have hm1_v : Game.ValidStep cfg.gameParams W' gSt m₁ := by simp [Game.ValidStep, hPh, m₁]
  have hm1_s : Game.StrategyStep cfg.gameParams gSt
      (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁ := by
    simp [Game.StrategyStep, hPh, m₁]
    exact rfl
  have hm2_v : Game.ValidStep cfg.gameParams W' (Game.stepState W' cfg.P.hk gSt m₁) m₂ := by
    have hgr : gSt.round = R := rfl
    simp only [Game.ValidStep, Game.stepState, m₁, m₂, W', hgr, ↓reduceIte]
    exact ⟨weightValid_norm1_of_hiddenStableAt hV.hα hm1 hHS1, fun i' _ => hNewStr_ok i'⟩
  have hm2_s : Game.StrategyStep cfg.gameParams (Game.stepState W' cfg.P.hk gSt m₁)
      (Game.stepPasses cfg.P.hk gSt
        (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁) m₂ := by
    simp [Game.StrategyStep, Game.stepState, m₁]
  have hTwo := game_append_two_steps cfg.gameParams hW_le tr.hv tr.hf m₁ m₂
    hm1_v hm1_s hm2_v hm2_s
  let moves' := tr.moves ++ [m₁, m₂]
  let gSt' := Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length
  have hgSt' : gSt' =
      { round := R + 1
        phase := .stage34
        bran := fun i' => if iFin ≤ i' then ⟨0, cfg.P.hk⟩ else gSt.bran i'
        repT := fun i' => if iFin ≤ i' then R + 1 else gSt.repT i'
        str := fun i' => if iFin ≤ i' then newStr i' else gSt.str i' } :=
    hTwo.2.2.1.trans (by simp only [Game.stepState, m₁, m₂]; rfl)
  have hPas' : Game.passesAt W' cfg.P.hk tr.initStr moves' moves'.length =
      fun j => if iFin ≤ j then 0
        else Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length j :=
    hTwo.2.2.2.trans (by simp only [Game.stepPasses, m₁, m₂]; rfl)
  have hREnd : (Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length).round = R + 1 := by
    change gSt'.round = R + 1; simp [hgSt']
  let timeOfRound' : ℕ → ℕ := fun r => if r = R + 1 then t + 1 else tr.timeOfRound r
  let snapC' : ℕ → TreeChain := fun r => if r = R + 1 then ch1.toTreeChain else tr.snapC r
  let snapE2I' : ℕ → ℕ → ℕ := fun r => if r = R + 1 then e2i' else tr.snapE2I r
  let snapI2E' : ℕ → ℕ → ℕ := fun r => if r = R + 1 then i2e' else tr.snapI2E r
  let snapNF' : ℕ → ℕ := fun r => if r = R + 1 then nf' else tr.snapNF r
  let reinit' : Fin (cfg.P.d + 1) → ℕ := fun i' => if iStar ≤ i'.val then R + 1 else tr.reinit i'
  let lvlIdx' : ℕ → ℕ → ℕ := fun r k =>
    if r = R + 1 then (if hk : k < cfg.P.d then (H1 k hk).len else 0) else tr.lvlIdx r k
  let updRound' : ℕ → ℕ := fun τ =>
    if 0 < iStar then (if τ = (tr.H 0 cfg.P.hd).len + 1 then R + 1 else tr.updRound τ)
    else R + 1
  refine ⟨⟨moves', by simp [moves'], tr.initStr, W', hTwo.1, hTwo.2.1, ?_, timeOfRound', ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, snapC', snapE2I', snapI2E', snapNF', ?_, ?_, ?_, ?_, ?_, ?_, reinit',
    ?_, ?_, ?_, ?_, H1, lvlIdx', ?_, ?_, ?_, ?_, ?_, fun k hk => by simpa using (hCore1 k hk).2,
    updRound', ?_, ?_, ?_, ?_, ?_⟩⟩
  · change gSt'.phase = .stage34; simp [hgSt']
  · intro r₁ r₂ hr₁₂ hr₂; rw [hREnd] at hr₂
    by_cases h2 : r₂ = R + 1
    · subst h2
      by_cases h1 : r₁ = R + 1
      · simp [h1]
      · simp only [timeOfRound', h1, ↓reduceIte]
        calc tr.timeOfRound r₁ ≤ tr.timeOfRound R := tr.hTimeMono r₁ R (by omega) (le_refl R)
          _ = t := tr.hTimeEnd
          _ ≤ t + 1 := Nat.le_succ t
    · simp only [timeOfRound', show r₁ ≠ R + 1 by omega, h2, ↓reduceIte]
      exact tr.hTimeMono r₁ r₂ hr₁₂ (by omega)
  · rw [hREnd]; simp [timeOfRound']
  · intro r hr; rw [hREnd] at hr
    by_cases hR : r = R + 1
    · simp [W', timeOfRound', hR]
    · simp only [W', timeOfRound', hR, ↓reduceIte]
      exact tr.hW_eq r (by omega)
  · intro i
    rw [shiftCount_append_round_adv tr.moves m₂ (Or.inr ⟨iFin, newStr, rfl⟩) i, tr.hShiftMatch i,
      ← hShEq i.val]
  · intro i
    have hrc : Game.rebuildCount moves' i =
        Game.rebuildCount tr.moves i + if iFin = i then 1 else 0 := by
      simp [Game.rebuildCount, moves', m₁, m₂, List.countP_append]
    rw [hrc, tr.hRebMatch i, hReb.2]
    by_cases hie : i.val = iStar
    · have : iFin = i := Fin.ext hie.symm
      simp [this, hie]
    · have hne : iFin ≠ i := fun h => hie (congrArg Fin.val h).symm
      simp [hne, hie]
  · intro i
    rw [hPas']
    by_cases hi : iStar ≤ i.val
    · have hfin : iFin ≤ i := hi
      simp [hfin, hi]
    · have hfin : ¬ (iFin ≤ i) := hi
      simp [hfin, hi, tr.hPassMatch i]
  · intro i
    change (gSt'.bran i).val = _
    rw [hgSt']
    by_cases hi_star : iStar ≤ i.val
    · have hfin : iFin ≤ i := hi_star
      by_cases hi : i.val < cfg.P.d
      · simp [hfin, hi, (hSomeData.2.2 i.val hi hi_star).2]
      · simp [hfin, hi]
    · have hfin : ¬ (iFin ≤ i) := hi_star
      have hi : i.val < cfg.P.d := lt_of_lt_of_le (Nat.lt_of_not_le hi_star) hiStarLt.le
      simp only [hfin, hi, ↓reduceIte, (hSomeData.2.1 i.val hi (Nat.lt_of_not_le hi_star)).2.2.2.1]
      simpa [hi] using tr.hBranMatch i
  · rw [hREnd]; simp [snapC', ch1, g_int, ℓ_int]
  · rw [hREnd]; simp [snapE2I']
  · rw [hREnd]; simp [snapI2E']
  · rw [hREnd]; simp [snapNF']
  · intro r hr; rw [hREnd] at hr
    by_cases hR : r = R + 1
    · subst hR
      simpa [snapC', snapE2I', snapI2E', snapNF', timeOfRound', ChainState.toTreeChain] using hFrD1
    · simp only [snapC', snapE2I', snapI2E', snapNF', timeOfRound', hR, ↓reduceIte]
      exact tr.hSnapFresh r (by omega)
  · intro r hr; rw [hREnd] at hr
    by_cases hR : r = R + 1
    · subst hR
      simpa [snapC', snapI2E', timeOfRound', ChainState.toTreeChain, ch1, g_int, ℓ_int] using hSH1
    · simp only [snapC', snapI2E', timeOfRound', hR, ↓reduceIte]
      exact tr.hSnapHolds r (by omega)
  · intro i
    change reinit' i ≤ gSt'.repT i
    rw [hgSt']
    by_cases hi : iStar ≤ i.val
    · have hfin : iFin ≤ i := hi
      simp [reinit', hi, hfin]
    · have hfin : ¬ (iFin ≤ i) := hi
      simp only [reinit', hi, hfin, ↓reduceIte]
      dsimp only [gSt]
      exact tr.hRebRep i
  · intro i
    change gSt'.repT ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ reinit' ⟨i.val + 1, _⟩
    rw [hgSt']
    by_cases hi1 : iStar ≤ i.val + 1
    · by_cases hi0 : iStar ≤ i.val
      · have hi0_le : iFin ≤ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := hi0
        simp [reinit', hi1, hi0_le]
      · have hnot0 : ¬ (iFin ≤ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := hi0
        simp only [reinit', hi1, hnot0, ↓reduceIte]
        dsimp only [gSt]
        exact le_trans (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
          (Nat.le_succ R)
    · have hnot0 : ¬ (iFin ≤ ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
        change ¬ (iStar ≤ i.val); omega
      simp only [reinit', hi1, hnot0, ↓reduceIte]
      dsimp only [gSt]
      exact tr.hRepRe i
  · intro i hi r hr1 hr2 b hb; rw [hREnd] at hr2
    by_cases hR : r = R + 1
    · subst hR
      simp only [snapC', ↓reduceIte, ChainState.toTreeChain, ↓reduceIte]
      rfl
    · have hnoti : ¬ (iStar ≤ i) := by
        intro hle
        have hre : reinit' ⟨i, Nat.lt_succ_of_le hi⟩ = R + 1 := by simp [reinit', hle]
        omega
      have hbs : b < iStar := lt_of_lt_of_le hb (Nat.le_of_lt (Nat.lt_of_not_le hnoti))
      have hre : reinit' ⟨i, Nat.lt_succ_of_le hi⟩ = tr.reinit ⟨i, Nat.lt_succ_of_le hi⟩ := by
        simp [reinit', hnoti]
      rw [hre] at hr1
      simp only [snapC', hR, ↓reduceIte]
      rw [tr.hSnapBran i hi r hr1 (by omega) b hb]
      exact (hSomeData.2.1 b (lt_of_lt_of_le hb hi) hbs).2.2.2.1.symm
  · intro i j
    change gSt'.str i j = if h : i.val < cfg.P.d then
        hstrAt (snapC' (gSt'.repT i))
          (fun e' => w_ext (timeOfRound' (gSt'.repT i)) (snapI2E' (gSt'.repT i) e'))
          i.val j.val
      else 0
    rw [hgSt']
    by_cases hi : iStar ≤ i.val
    · have hfin : iFin ≤ i := hi
      by_cases hid : i.val < cfg.P.d
      · simp [hfin, newStr, snapC', snapI2E', timeOfRound', hid]
      · simp [hfin, newStr, hid]
    · have hfin : ¬ (iFin ≤ i) := hi
      dsimp only [gSt]
      have hrep_le : (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i ≤ R :=
        (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length i).2
      have hneq : (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).repT i ≠ R + 1 := by
        omega
      simp only [hfin, ↓reduceIte, snapC', snapI2E', timeOfRound', hneq]
      exact tr.hStrMatch i j
  · intro i hi
    by_cases his : iStar ≤ i
    · simp [reinit', his, lvlIdx', hi, (hSomeData.2.2 i hi his).1]
    · have hne : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≠ R + 1 := by
        have := (tr.hRebRep ⟨i, Nat.lt_succ_of_le hi.le⟩).trans
          (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
        omega
      simp [reinit', his, lvlIdx', hne, tr.hLvlReinit i hi]
  · intro i hi; rw [hREnd]; simp [lvlIdx', hi]
  · intro i hi r₁ r₂ hr1 hr12 hr2; rw [hREnd] at hr2
    by_cases his : iStar ≤ i
    · have hr1_eq : r₁ = R + 1 := by simp [reinit', his] at hr1; omega
      have hr2_eq : r₂ = R + 1 := by omega
      simp [hr1_eq, hr2_eq]
    · have hr1' : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r₁ := by simpa [reinit', his] using hr1
      have hData := hSomeData.2.1 i hi (Nat.lt_of_not_le his)
      by_cases h2 : r₂ = R + 1
      · subst h2
        by_cases h1 : r₁ = R + 1
        · simp [h1]
        · simp only [lvlIdx', h1, ↓reduceIte, hi, ↓reduceDIte]
          calc tr.lvlIdx r₁ i ≤ tr.lvlIdx R i := tr.hLvlMono i hi r₁ R hr1' (by omega) (le_refl R)
            _ = (tr.H i hi).len := tr.hLvlEnd i hi
            _ ≤ (H1 i hi).len := by rw [hData.1]; exact Nat.le_succ _
      · simp only [lvlIdx', show r₁ ≠ R + 1 by omega, h2, ↓reduceIte]
        exact tr.hLvlMono i hi r₁ r₂ hr1' hr12 (by omega)
  · intro i hi
    have hi0 : i < cfg.P.d := Nat.lt_of_succ_lt hi
    by_cases hi1_star : iStar ≤ i + 1
    · have hlen1 : (H1 (i + 1) hi).len = 0 := (hSomeData.2.2 (i + 1) hi hi1_star).1
      refine ⟨by rw [hlen1]; exact Nat.zero_le _, fun r hr1 hr2 => ?_⟩
      rw [hREnd] at hr2
      have hr_eq : r = R + 1 := by simp [reinit', hi1_star] at hr1; omega
      subst hr_eq
      simp [lvlIdx', hi, hi0, hlen1]
    · have hi0_lt : i < iStar := by omega
      have hi1_lt : i + 1 < iStar := by omega
      have hOld := tr.hLvlSucc i hi
      have hlen1 := (hSomeData.2.1 (i + 1) hi hi1_lt).1
      have hlen0 := (hSomeData.2.1 i hi0 hi0_lt).1
      refine ⟨by omega, fun r hr1 hr2 => ?_⟩
      rw [hREnd] at hr2
      by_cases hR : r = R + 1
      · subst hR
        simp only [lvlIdx', hi, hi0, ↓reduceIte, ↓reduceDIte]
        exact Nat.add_sub_of_le (by omega)
      · have hr1' : tr.reinit ⟨i + 1, Nat.lt_succ_of_le hi.le⟩ ≤ r := by
          simpa [reinit', hi1_star] using hr1
        simp only [lvlIdx', hR, ↓reduceIte]
        have hdiff : (H1 i hi0).len - (H1 (i + 1) hi).len =
            (tr.H i hi0).len - (tr.H (i + 1) hi).len := by omega
        rw [hdiff]
        exact hOld.2 r hr1' (by omega)
  · intro i hi r hr1 hr2; rw [hREnd] at hr2
    by_cases his : iStar ≤ i
    · have hr_eq : r = R + 1 := by simp [reinit', his] at hr1; omega
      subst hr_eq
      simp only [snapC', lvlIdx', hi, ↓reduceIte, ↓reduceDIte, ChainState.toTreeChain]
      exact ⟨(H1 i hi).hEndG.symm, fun j _ => by rw [← (H1 i hi).hRun],
        fun _ j _ => by rw [← (H1 i hi).hRun]⟩
    · have hr1' : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ r := by simpa [reinit', his] using hr1
      have hD := hSomeData.2.1 i hi (Nat.lt_of_not_le his)
      have hData := lvlSnap_unrebuilt tr i hi (H1 i hi) hD.1 hD.2.1 hD.2.2.2.2.2 r hr1' hr2
      simp only [lvlIdx', hi, ↓reduceDIte]
      refine ⟨hData.1, hData.2.1, fun hre1 j hj => ?_⟩
      by_cases hi1s : iStar ≤ i + 1
      · have hr_eq : r = R + 1 := by simp [reinit', hi1s] at hre1; omega
        subst hr_eq
        exact hData.2.2 (le_trans (tr.hRebRep _)
          (le_trans (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
            (Nat.le_succ R))) j hj
      · have hre1' : tr.reinit ⟨i + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hi)⟩ ≤ r := by
          simpa [reinit', hi1s] using hre1
        exact hData.2.2 hre1' j hj
  · intro τ hτ
    by_cases h0pos : 0 < iStar
    · have hD0 := hSomeData.2.1 0 cfg.P.hd h0pos
      rw [hD0.1] at hτ
      by_cases htop : τ = (tr.H 0 cfg.P.hd).len + 1
      · simp only [updRound', h0pos, htop, ↓reduceIte, reinit', show ¬ iStar ≤ 0 by omega, hREnd]
        exact ⟨le_trans (tr.hRebRep ⟨0, Nat.succ_pos _⟩)
          (le_trans (Game.repT_bounds tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length _).2
            (Nat.le_succ R)), le_refl _⟩
      · have hB := tr.hUpdBound τ (by omega)
        simp only [updRound', h0pos, htop, ↓reduceIte, reinit', show ¬ iStar ≤ 0 by omega, hREnd]
        exact ⟨hB.1, Nat.le_succ_of_le hB.2⟩
    · have hi0 : iStar = 0 := by omega
      simp [updRound', reinit', hi0, hREnd]
  · intro τ₁ τ₂ h12 h2
    by_cases h0pos : 0 < iStar
    · have hD0 := hSomeData.2.1 0 cfg.P.hd h0pos
      rw [hD0.1] at h2
      by_cases htop : τ₂ = (tr.H 0 cfg.P.hd).len + 1
      · have h1_le : τ₁ ≤ (tr.H 0 cfg.P.hd).len := by omega
        simp only [updRound', h0pos, htop, ↓reduceIte, show τ₁ ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
        exact Nat.lt_succ_of_le (tr.hUpdBound τ₁ h1_le).2
      · simp only [updRound', h0pos, htop, ↓reduceIte, show τ₁ ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
        exact tr.hUpdMono τ₁ τ₂ h12 (by omega)
    · have hlen0 : (H1 0 cfg.P.hd).len = 0 := (hSomeData.2.2 0 cfg.P.hd (by omega)).1
      omega
  · intro r hr1 hr2; rw [hREnd] at hr2
    by_cases h0pos : 0 < iStar
    · have hD0 := hSomeData.2.1 0 cfg.P.hd h0pos
      have hr1' : tr.reinit ⟨0, Nat.succ_pos _⟩ ≤ r := by
        simpa [reinit', show ¬ iStar ≤ 0 by omega] using hr1
      by_cases hR : r = R + 1
      · subst hR
        simp only [lvlIdx', ↓reduceIte, cfg.P.hd, ↓reduceDIte, updRound', h0pos, hD0.1]
        exact ⟨le_refl _, fun hlt => absurd hlt (Nat.lt_irrefl _)⟩
      · have hOld := tr.hUpdBand r hr1' (by omega)
        have hidx_le : tr.lvlIdx r 0 ≤ (tr.H 0 cfg.P.hd).len := by
          rw [← tr.hLvlEnd 0 cfg.P.hd]
          exact tr.hLvlMono 0 cfg.P.hd r R hr1' (by omega) (le_refl R)
        simp only [lvlIdx', hR, ↓reduceIte, updRound', h0pos,
          show tr.lvlIdx r 0 ≠ (tr.H 0 cfg.P.hd).len + 1 by omega]
        refine ⟨hOld.1, fun hlt => ?_⟩
        rw [hD0.1] at hlt
        by_cases heq : tr.lvlIdx r 0 = (tr.H 0 cfg.P.hd).len
        · simp [heq]; omega
        · have hlt0 : tr.lvlIdx r 0 < (tr.H 0 cfg.P.hd).len := by omega
          simpa [show tr.lvlIdx r 0 ≠ (tr.H 0 cfg.P.hd).len by omega] using hOld.2 hlt0
    · have hi0 : iStar = 0 := by omega
      have hlen0 : (H1 0 cfg.P.hd).len = 0 := (hSomeData.2.2 0 cfg.P.hd (by omega)).1
      have hr_eq : r = R + 1 := by simp [reinit', hi0] at hr1; omega
      subst hr_eq
      simp [updRound', h0pos, lvlIdx', cfg.P.hd, hlen0]
  · intro τ hτ
    by_cases h0pos : 0 < iStar
    · have hD0 := hSomeData.2.1 0 cfg.P.hd h0pos
      rw [hD0.1] at hτ
      by_cases htop : τ = (tr.H 0 cfg.P.hd).len + 1
      · subst htop
        simp only [updRound', h0pos, ↓reduceIte, snapC', snapI2E', timeOfRound']
        have hG_end : (H1 0 cfg.P.hd).D.G ((tr.H 0 cfg.P.hd).len + 1) = ch1.G 0 := by
          rw [← hD0.1]; exact (H1 0 cfg.P.hd).hEndG
        refine ⟨hG_end.trans (by simp [ChainState.toTreeChain]), fun e' he' => ?_⟩
        have he'_ch1 : e' ∈ (ch1.G 0).E := by rw [← hG_end]; exact he'
        have hℓ_end := (H1 0 cfg.P.hd).hEndℓ e' he'_ch1
        rw [← hD0.1, hℓ_end, TreeChain.chainLen, hℓ1]
      · have hτ_le : τ ≤ (tr.H 0 cfg.P.hd).len := by omega
        have hOld := tr.hLvl0Match τ hτ_le
        have hPref0 := hD0.2.1 τ hτ_le
        have huR : tr.updRound τ ≤ R := (tr.hUpdBound τ hτ_le).2
        simp only [updRound', h0pos, htop, ↓reduceIte, snapC', snapI2E', timeOfRound',
          show tr.updRound τ ≠ R + 1 by omega]
        refine ⟨hPref0.1.trans hOld.1, fun e' he' => ?_⟩
        rw [hPref0.2.2.1]; exact hOld.2 e' (hPref0.1 ▸ he')
    · have hi0 : iStar = 0 := by omega
      have hlen0 : (H1 0 cfg.P.hd).len = 0 := (hSomeData.2.2 0 cfg.P.hd (by omega)).1
      have hτ0 : τ = 0 := by omega
      subst hτ0
      simp only [updRound', h0pos, ↓reduceIte, snapC', snapI2E', timeOfRound']
      have hG_end : (H1 0 cfg.P.hd).D.G 0 = ch1.G 0 := by
        have h := (H1 0 cfg.P.hd).hEndG
        rwa [hlen0] at h
      refine ⟨hG_end.trans (by simp [ChainState.toTreeChain]), fun e' he' => ?_⟩
      have he'_ch1 : e' ∈ (ch1.G 0).E := by rw [← hG_end]; exact he'
      have hℓ_end := (H1 0 cfg.P.hd).hEndℓ e' he'_ch1
      rw [hlen0] at hℓ_end
      rw [hℓ_end, TreeChain.chainLen, hℓ1]
  · by_cases h0pos : 0 < iStar
    · have hD0 := hSomeData.2.1 0 cfg.P.hd h0pos
      have hData := lvl0NoIns_unrebuilt tr hFresh hExtG hTB hFresh' hG0ℓ1.1
        hi2e_old hYesInsExt (H1 0 cfg.P.hd) hD0.1 hD0.2.1 (hD0.2.2.1 rfl)
      simpa [hREnd, snapI2E', timeOfRound', updRound', h0pos] using hData
    · have hi0 : iStar = 0 := by omega
      have hlen0 : (H1 0 cfg.P.hd).len = 0 := (hSomeData.2.2 0 cfg.P.hd (by omega)).1
      intro s τ hsτ hτ r_s r_τ hrs1 hrs2 _ hrτ1 hrτ2 _ _ e' _
      have hτ0 : τ = 0 := by omega
      have hs0 : s = 0 := by omega
      have hrs_eq : r_s = R + 1 := by simp [updRound', h0pos] at hrs1; omega
      have hrτ_eq : r_τ = R + 1 := by simp [updRound', h0pos] at hrτ1; omega
      subst hs0; subst hτ0; subst hrs_eq; subst hrτ_eq
      simp only [snapI2E', timeOfRound', ↓reduceIte]
      exact ⟨fun _ => ⟨trivial, fun δ _ h2 => absurd h2 (by omega), trivial⟩,
        fun _ => ⟨trivial, fun δ _ h2 => absurd h2 (by omega)⟩⟩

/-- Combined pre-loop trace bridge across `algorithm1_update` inside `algorithm2_update`,
parameterized by last-level vertex cap `nLast`. -/
lemma alg2HiddenTrace_update_preLoopAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (_hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G (t + 1)) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e')) :
    let (extG', e2i', i2e', nf', U_int) :=
      translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
    let (branD1, passes1) :=
      match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext (t + 1)
      { st with
        chain := ch1, branD := branD1, passes := passes1,
        extG := extG', extToInt := e2i', intToExt := i2e', nextFresh := nf',
        extℓ := D.ℓ (t + 1), extg := D.g (t + 1) }) := by
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
  have hTB_eq : translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1)) =
      (extG', e2i', i2e', nf', U_int) := rfl
  have hTB_all := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
  dsimp only at hTB_all
  change extG' = st.extG.applyBatch (D.U (t + 1)) ∧
    FreshInv extG' ((st.chain.G 0).applyBatch U_int) e2i' i2e' nf' ∧
    (st.chain.G 0).BatchIsValid U_int ∧ NoBatchReinsert (st.chain.G 0) U_int ∧
    U_int.length = (D.U (t + 1)).length ∧ st.nextFresh ≤ nf' ∧
    (∀ u' ∈ U_int, ∀ e', u'.Inserts e' → st.nextFresh ≤ e' ∧ e' < nf') ∧
    (∀ e' < st.nextFresh, i2e' e' = st.intToExt e') ∧
    (∀ e ∈ extG'.E, (∀ u ∈ D.U (t + 1), ¬ u.Inserts e) →
      e ∈ st.extG.E ∧ e2i' e = st.extToInt e ∧ ∀ u' ∈ U_int, ¬ u'.Inserts (st.extToInt e)) ∧
    (∀ e ∈ extG'.E, (∃ u ∈ D.U (t + 1), u.Inserts e) → st.nextFresh ≤ e2i' e) at hTB_all
  rcases hTB_all with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
  have hExtG'_D : extG' = (D.G t).applyBatch (D.U (t + 1)) := by rw [hExtG', hExtG]
  have hG1eq : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)) := hD.2
  have hExtEq : extG' = D.G (t + 1) := by rw [hExtG'_D, hG1eq]
  have hG0'Valid : ((st.chain.G 0).applyBatch U_int).IsValid :=
    (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
  have hG0'm : ((st.chain.G 0).applyBatch U_int).m ≤ cfg.P.M₀ := by
    rw [hFresh'.m_eq, hExtEq]; exact hm1
  have hG0'n : ((st.chain.G 0).applyBatch U_int).n ≤ cfg.N₀ := by
    rw [hFresh'.n_eq, hExtEq]; exact hn1
  let g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
  let ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
  have hℓ_intPos : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, 0 < ℓ_int e' :=
    fun e' he' => hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
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
      have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
      have he2i'_eq : e2i' (st.intToExt e') = e' := by
        rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
      have := hFresh.hLtFresh e' he'0
      omega
    have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 _ he_ext1 hNoIns_ext).2
    dsimp only [ℓ_int]
    rw [hi2e_eq, hℓ_same, hℓ, hExtℓ]; rfl
  have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U_int g_int ℓ_int
    hBatch_int hNR_int hG0'Valid hG0'm hG0'n hℓ_intPos hℓ_intStable
  dsimp only at hU
  rcases hU with ⟨hInv1, _, _, hShEq, _, _⟩
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
  have hFresh1 : FreshInv extG' (ch1.G 0) e2i' i2e' nf' := by rw [hG0ℓ1.1]; exact hFresh'
  let st0 : ChainState cfg.T cfg.P :=
    { st.chain with recUpdates := fun j =>
        if j = 0 then st.chain.recUpdates 0 + U_int.length else st.chain.recUpdates j }
  let HPre0 : ∀ k, k < 0 → LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ { st0 with ℓ := ℓ_int, g := g_int } k :=
    fun _ hk => absurd hk (Nat.not_lt_zero _)
  have hLoop := updateLoop_hidden_trace cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv tr.H
    (fun k hk => ⟨(tr.hLvlSucc k hk).1, tr.hLvlCore k hk⟩)
    ℓ_int g_int U_int cfg.P.d 0 st0 ((st.chain.G 0).applyBatch U_int) U_int
    ((st.chain.G 0).batchEnc U_int) (Nat.zero_add cfg.P.d)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) rfl (fun _ _ => rfl) rfl rfl rfl rfl
    (fun _ => ⟨rfl, rfl⟩) (fun h => absurd h (Nat.lt_irrefl 0))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ hj => absurd hj (Nat.not_lt_zero _))
    (fun _ => rfl) (fun h => absurd h (Nat.lt_irrefl 0)) rfl
    hBatch_int hG0'Valid
    (by
      have hm0r : (((st.chain.G 0).applyBatch U_int).m : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast hG0'm
      have hγ1 := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
      have hmul : (cfg.P.M₀ : ℝ) ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
        nlinarith [show (0 : ℝ) ≤ cfg.P.M₀ from Nat.cast_nonneg _]
      have hceil : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
          (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / cfg.P.k) ^ 0 ≤ (levelM cfg.TP cfg.P 0 : ℝ) := Nat.le_ceil _
      simp only [pow_zero, mul_one] at hceil
      linarith)
    (fun _ => ⟨hG0'm, hG0'n, applyBatch_V_subset _ _, hℓ_intPos⟩)
    (fun h => absurd h (Nat.lt_irrefl 0)) hℓ_intPos hℓ_intStable
    HPre0 (fun _ hk => absurd hk (Nat.not_lt_zero _))
    (fun h => absurd h (Nat.lt_irrefl 0))
    (fun _ hk => absurd hk (Nat.not_lt_zero _))
  obtain ⟨⟨H1, hCore1, hRebSome, hRebNone⟩⟩ := hLoop
  dsimp only [tb]
  have hLast1 : (ch1.G cfg.P.d).n ≤ nLast := hLastBound hInv1 (hExtEq ▸ hFresh1)
  cases hFRL : firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
  | none =>
    have hFRL' : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
        (updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int cfg.P.d 0 st0
          ((st.chain.G 0).applyBatch U_int) U_int ((st.chain.G 0).batchEnc U_int)).1.rebuildCount =
        none := by dsimp only [ch1, algorithm1_update] at hFRL; exact hFRL
    exact alg2HiddenTrace_update_preLoop_none nLast hV hHist ht1 hm1 hn1 hHS1 tr hFresh
      hExtG hTB_eq hExtG'_D hG1eq hi2e_old hYesInsExt hInv1 hLast1 hFresh1 hShEq H1 hCore1 hFRL
      (by simpa [algorithm1_update, ch1, g_int, ℓ_int] using hRebNone hFRL')
  | some iStar =>
    have hFRL' : firstRebuiltLevel cfg.P.d st.chain.rebuildCount
        (updateLoop cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int cfg.P.d 0 st0
          ((st.chain.G 0).applyBatch U_int) U_int ((st.chain.G 0).batchEnc U_int)).1.rebuildCount =
        some iStar := by dsimp only [ch1, algorithm1_update] at hFRL; exact hFRL
    exact alg2HiddenTrace_update_preLoop_some nLast hV hHist ht1 hm1 hn1 hHS1 tr hFresh hExtG
      hTB_eq hExtG'_D hG1eq hi2e_old hYesInsExt hInv1 hLast1 hFresh1 hShEq H1 hCore1 hFRL
      (by simpa [algorithm1_update, ch1, g_int, ℓ_int] using hRebSome iStar hFRL')

/-- Combined pre-loop trace bridge across `algorithm1_update` inside `algorithm2_update`. -/
lemma alg2HiddenTrace_update_preLoop {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e')) :
    let (extG', e2i', i2e', nf', U_int) :=
      translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int
      (fun e' => D.g (t + 1) (i2e' e')) (fun e' => D.ℓ (t + 1) (i2e' e'))).1
    let (branD1, passes1) :=
      match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext (t + 1)
      { st with
        chain := ch1, branD := branD1, passes := passes1,
        extG := extG', extToInt := e2i', intToExt := i2e', nextFresh := nf',
        extℓ := D.ℓ (t + 1), extg := D.g (t + 1) }) :=
  alg2HiddenTrace_update_preLoopAt cfg.N₀ hV hHist ht1 hisUpd hm1 hn1
    (fun hIc hFc => chainInv_last_le_N0 hV hn1 hIc hFc) hHS1 tr hInv hBud hFresh hExtG hExtℓ hℓ

end MinCostFlow.Chain
