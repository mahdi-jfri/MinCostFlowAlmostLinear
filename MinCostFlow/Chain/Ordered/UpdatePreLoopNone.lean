module

public import MinCostFlow.Chain.Ordered.UpdatePreLoopHelpers
public import MinCostFlow.Chain.Ordered.RenameFacts

/-!
# No-rebuild case of ordered `alg2HiddenTrace_update_preLoopAt`

Proves `U3.alg2HiddenTrace_update_preLoop_none`: when `firstRebuiltLevel = none` after
ordered `algorithm1_update`, advances `Alg2HiddenTraceAt` across `t → t + 1` by appending
`.roundStep .roundCompleting .doNothing (fun _ _ => 0)` and `.advDoNothing`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

namespace U3

lemma alg2HiddenTrace_update_preLoop_none (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
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
        (H1 k hk).D.ℓ s = (tr.H k hk).D.ℓ s ∧ (H1 k hk).D.g s = (tr.H k hk).D.g s ∧
        (H1 k hk).ord s = (tr.H k hk).ord s) ∧
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
  have hRebEq : ch1.rebuildCount = st.chain.rebuildCount :=
    rebuildCount_of_updateLoop_none cfg.T cfg.L cfg.TP cfg.P cfg.N₀ ℓ_int g_int st.chain U_int hNone
  have hG0ℓ1 := update_G0_ℓ_of_not_over cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
    (update_not_over_of_rebuildCount_eq cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
      (congrFun hRebEq 0))
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

end U3

end MinCostFlow.Chain.Ordered
