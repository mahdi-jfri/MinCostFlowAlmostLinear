module

public import MinCostFlow.Chain.Ordered.HiddenTraceHelpers
import MinCostFlow.Chain.Ordered.InitPreserves
import MinCostFlow.Chain.Ordered.RebuildSuffix

/-!
# Init and Detect trace transitions for Algorithm 2 with orders

This file proves the `Init` (`t = 0`) and `Detect` (`t → t + 1` with empty batch) transitions
for `Ordered.Alg2HiddenTraceAt` and `Ordered.Alg2HiddenTrace`, following
`MinCostFlow.Chain.HiddenTraceSteps`:

* `alg2HiddenTrace_initAt`, `alg2HiddenTrace_init`: builds the initial ordered hidden trace after
  `algorithm2_init`, including the level-order clause of `hLvlCore`.
* `alg2HiddenTrace_detectAt`, `alg2HiddenTrace_detect`: advances the ordered hidden trace across
  `algorithm2_detect`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

/-- **Init step**: construct `Ordered.Alg2HiddenTraceAt` at `t = 0` after `algorithm2_init`,
parameterized by last-level vertex cap `nLast`. -/
theorem alg2HiddenTrace_initAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (_hEdge : HistoryEdgeOnly D T)
    (hm0 : (D.G 0).m ≤ cfg.P.M₀) (hn0 : (D.G 0).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G 0) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    {c_ext w_ext : ℕ → ℕ → ℝ} (hHS0 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext 0) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext 0
      (algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0))) := by
  classical
  set st₀ := algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0)
  have hG0Valid := (hHist.2.1 0 (Nat.zero_le _)).1
  have hℓ0 := (hHist.2.1 0 (Nat.zero_le _)).2
  have hℓ0R := lenInRange_of_hiddenStableAt hHS0
  have hInit := initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk (D.G 0) (D.ℓ 0) (D.g 0) hG0Valid hm0 hn0 hℓ0R
  have hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st₀.chain := hInit.1
  have hG0eq : st₀.chain.G 0 = D.G 0 := hInit.2.2.1
  have hFresh : FreshInv (D.G 0) (st₀.chain.G 0) st₀.extToInt st₀.intToExt st₀.nextFresh := by
    change FreshInv (D.G 0) (st₀.chain.G 0) id id ((D.G 0).E.sup id + 1)
    rw [hG0eq]; exact freshInv_init (D.G 0)
  have hSH := chainState_snapHoldsAt nLast hV hInv hFresh rfl hn0 (hLastBound hInv hFresh)
  have hℓ0_nn : ∀ e ∈ (st₀.chain.G 0).E, 0 ≤ D.ℓ 0 (st₀.intToExt e) := fun e he => by
    rw [hG0eq] at he; exact (hℓ0 e he).le
  have hw0_nn : ∀ e ∈ (st₀.chain.G 0).E, 0 ≤ w_ext 0 (st₀.intToExt e) := fun e he => by
    rw [hG0eq] at he; exact (hHS0.2.2.2.2 e he).1.le
  have hInitStr := chain_validStretch_hstr hV hSH.1 hSH.2.1 hSH.2.2.1 hSH.2.2.2.1 hSH.2.2.2.2
    hℓ0_nn hw0_nn
  let initStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ := fun i j =>
    if _hi : i.val < cfg.P.d then
      hstrAt st₀.chain.toTreeChain (fun e' => w_ext 0 (st₀.intToExt e')) i.val j.val
    else 0
  let W₀ : ℕ → ℝ := fun _ => (D.G 0).norm1 (w_ext 0)
  have hWV : Game.WeightValid cfg.gameParams.Ψ (W₀ 1) :=
    weightValid_norm1_of_hiddenStableAt hV.hα hm0 hHS0
  let moves₀ : List (Game.Move cfg.P.d cfg.P.k) := [.advDoNothing]
  have hv₀ : Game.ValidPlayPrefix cfg.gameParams W₀ initStr moves₀ := by
    refine ⟨⟨fun i j => (hInitStr i).1 j, fun i => (hInitStr i).2⟩, fun s hs => ?_⟩
    have hs0 : s = 0 := Nat.lt_one_iff.mp hs; subst hs0
    simpa [Game.ValidStep, Game.stateAt, Game.initState, moves₀] using ⟨hWV, trivial⟩
  have hf₀ : Game.FollowsStrategyPrefix cfg.gameParams W₀ initStr moves₀ := fun s hs => by
    have hs0 : s = 0 := Nat.lt_one_iff.mp hs; subst hs0
    simp [Game.StrategyStep, Game.stateAt, Game.initState]
  have hRS := rebuildSuffix_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ hV.hTP hV.hLP hV.hT hV.hL
    hV.hγM₀ hV.hγk (D.ℓ 0) (D.g 0) cfg.P.d 0 (fun _ => D.G 0)
    (fun _ => cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P 0) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0) (sortedEnds (D.G 0)))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (zero_add cfg.P.d) hG0Valid (Finset.Subset.refl _) hn0
    (by
      have hm0r : ((D.G 0).m : ℝ) ≤ cfg.P.M₀ := by exact_mod_cast hm0
      have hγ1 := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
      have hmul : (cfg.P.M₀ : ℝ) ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := by
        nlinarith [show (0 : ℝ) ≤ cfg.P.M₀ from Nat.cast_nonneg _]
      have hceil : (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
          (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / cfg.P.k) ^ 0 ≤ (levelM cfg.TP cfg.P 0 : ℝ) := Nat.le_ceil _
      simp only [pow_zero, mul_one] at hceil
      linarith) (hℓ0R.toLevel _ _ _) ⟨sortedRotation (D.G 0), rfl⟩
  let res0 := rebuildSuffix cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.ℓ 0) (D.g 0) cfg.P.d 0
    (fun _ => D.G 0)
    (fun _ => cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P 0) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0) (sortedEnds (D.G 0)))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hChCon : ∀ k ≤ cfg.P.d,
      st₀.chain.toTreeChain.chainLen st₀.chain.ℓ k =
        (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k ∧
      st₀.chain.toTreeChain.chainGrad st₀.chain.g k =
        (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainGrad (D.g 0) k :=
    fun k hk => ⟨chainLen_congr_params rfl (D.ℓ 0) hk (fun _ _ => rfl) (fun _ _ => rfl),
      chainGrad_congr_params rfl (D.g 0) hk (fun _ _ => rfl) (fun _ _ => rfl)⟩
  let H₀ : ∀ i < cfg.P.d, LevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st₀.chain i := fun i hi =>
    have hsuf := hRS.2.2.1 i (Nat.zero_le i) hi
    zeroLevelHistory cfg.T cfg.TP cfg.P cfg.N₀ st₀.chain i hi hV.hTP hsuf.2.2.2.2.2.1
      hsuf.2.2.2.2.2.2.2.1
      (le_trans (Finset.card_le_card (hRS.1 0 (Nat.zero_le _) ▸ hsuf.2.2.2.2.2.2.1)) hn0)
      (fun e he => by rw [(hChCon i hi.le).1]; exact hsuf.2.2.2.2.2.2.2.2.1 e he)
      (exists_rotation_levelOrd_of_inv hInv hi)
      (by rw [(hChCon i hi.le).1, (hChCon i hi.le).2]; exact hsuf.2.2.2.2.2.2.2.2.2.1)
      hsuf.2.1 hsuf.2.2.2.2.1 hsuf.2.2.2.1 rfl
      (fun h0 => by subst h0; exact hsuf.2.2.1)
      (fun h1 => (hRS.2.2.1 (i + 1) (Nat.zero_le _) h1).2.2.1)
      (by rw [(hChCon i hi.le).1]; exact hsuf.2.2.2.2.2.2.2.2.2.2.2)
  have hEndG : Game.stateAt W₀ cfg.P.hk initStr moves₀ moves₀.length =
      { Game.initState cfg.P.d cfg.P.k cfg.P.hk initStr with phase := .stage34 } := by
    simp [moves₀, Game.stateAt, Game.stepState]
  have hChEq : st₀.chain = (algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0)).1 := rfl
  have hSc0 : ∀ i, st₀.chain.shiftCount i = 0 := by rw [hChEq]; exact hInit.2.2.2.2.2.1
  have hRc0 : ∀ i, st₀.chain.rebuildCount i = 0 := by rw [hChEq]; exact hInit.2.2.2.2.2.2.1
  have hGeq : ∀ j, st₀.chain.G j = res0.1 j := fun _ => rfl
  have hSceq : ∀ j, st₀.chain.scState j = res0.2.1 j := fun _ => rfl
  have hBreq : ∀ j, st₀.chain.bran j = res0.2.2.1 j := fun _ => rfl
  refine ⟨{
    moves := moves₀, hmne := by simp [moves₀], initStr := initStr, W_game := W₀,
    hv := hv₀, hf := hf₀, hPhase := by rw [hEndG],
    timeOfRound := fun _ => 0, hTimeMono := fun _ _ _ _ => le_refl 0, hTimeEnd := rfl,
    hW_eq := fun _ _ => rfl,
    hShiftMatch := fun i => by rw [hSc0]; simp [moves₀, Game.shiftCount],
    hRebMatch := fun i => by rw [hRc0]; simp [moves₀, Game.rebuildCount],
    hPassMatch := fun i => by
      simp [moves₀, Game.passesAt, Game.stepPasses, st₀, algorithm2_init],
    hBranMatch := fun i => by
      rw [hEndG]
      by_cases hi : i.val < cfg.P.d
      · have hsuf := hRS.2.2.1 i.val (Nat.zero_le _) hi
        change 0 = if i.val < cfg.P.d then st₀.chain.bran i.val else st₀.branD
        simp only [hi, ↓reduceIte]; rw [hBreq]; exact hsuf.1.symm
      · change 0 = if i.val < cfg.P.d then st₀.chain.bran i.val else st₀.branD
        simp only [hi, ↓reduceIte]; rfl
    snapC := fun _ => st₀.chain.toTreeChain,
    snapE2I := fun _ => st₀.extToInt, snapI2E := fun _ => st₀.intToExt, snapNF := fun _ => st₀.nextFresh,
    hSnapEndC := rfl, hSnapEndE2I := rfl, hSnapEndI2E := rfl, hSnapEndNF := rfl,
    hSnapFresh := fun _ _ => hFresh,
    hSnapHolds := fun _ _ => hSH,
    reinit := fun _ => 1,
    hRebRep := fun _ => by rw [hEndG]; exact le_refl 1,
    hRepRe := fun _ => by rw [hEndG]; exact le_refl 1,
    hSnapBran := fun _ _ _ _ _ _ _ => rfl,
    hStrMatch := fun i j => by rw [hEndG]; simp [initStr, Game.initState],
    H := H₀, lvlIdx := fun _ _ => 0,
    hLvlReinit := fun _ _ => rfl, hLvlEnd := fun _ _ => rfl,
    hLvlMono := fun _ _ _ _ _ _ _ => le_refl 0,
    hLvlSucc := fun k hk => ⟨le_refl 0, fun _ _ _ => rfl⟩,
    hLvlSnap := fun k hk _ _ _ => by
      have hsuf := hRS.2.2.1 k (Nat.zero_le _) hk
      have hSC_eq : st₀.chain.scState k =
          cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (st₀.chain.G k)
            (st₀.chain.toTreeChain.chainLen st₀.chain.ℓ k)
            (st₀.chain.toTreeChain.chainGrad st₀.chain.g k)
            (st₀.chain.levelOrd k) := by
        rw [hSceq k, hGeq k, (hChCon k hk.le).1, (hChCon k hk.le).2]
        dsimp only [res0]; exact hsuf.2.2.2.2.2.2.2.2.2.1
      refine ⟨rfl, fun j _ => ?_, fun _ j _ => ?_⟩
      · simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.runOrdAfterRestarts,
          SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil]
        change cfg.T.lsfs (st₀.chain.scState k) j = _
        rw [hSC_eq]
      · simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.runOrdAfterRestarts,
          SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil]
        change cfg.T.emb (st₀.chain.scState k) j = _
        rw [hSC_eq]
    hLvlCore := fun k hk => by
      have hsufk := hRS.2.2.1 k (Nat.zero_le _) (Nat.lt_of_succ_lt hk)
      refine ⟨le_refl 0, fun δ hδ => ?_, fun δ h1 h2 => by simp [H₀, zeroLevelHistory] at h2; omega,
        fun δ hδ e he => ?_, fun δ hδ => ?_⟩
      · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
        simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.coreInstanceOrdFrom, Nat.sub_self, Nat.zero_add,
          SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil]
        rw [hGeq (k + 1), hGeq k, hBreq k, (hChCon k (Nat.lt_of_succ_lt hk).le).1,
          (hChCon k (Nat.lt_of_succ_lt hk).le).2]
        dsimp only [res0]
        change res0.1 (k + 1) = cfg.T.S (cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (res0.1 k)
          ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k)
          ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainGrad (D.g 0) k)
          (chainLevelOrd cfg.T res0.1 res0.2.1 res0.2.2.1 k)) (res0.2.2.1 k)
        rw [← hsufk.2.2.2.2.2.2.2.2.2.1, hsufk.1]
        exact hsufk.2.2.2.2.2.2.2.2.2.2.1
      · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
        simp only [H₀, zeroLevelHistory, SparseCoreRestartTool.coreInstanceOrdFrom, Nat.sub_self, Nat.zero_add,
          SparseCoreRestartTool.runOrdAfterRestarts, SparseCoreRestartTool.runOrdAfterUpdate, List.foldl_nil]
        rw [hGeq k, hBreq k, (hChCon k (Nat.lt_of_succ_lt hk).le).1,
          (hChCon k (Nat.lt_of_succ_lt hk).le).2, (hChCon (k + 1) hk.le).1]
        have hAct_fold : (mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).activeLSF k =
            cfg.T.lsfs (res0.2.1 k) (res0.2.2.1 k) := by
          simp [TreeChain.activeLSF, mkPartialChain, Nat.lt_of_succ_lt hk]
        rw [TreeChain.chainLen, hAct_fold]
        dsimp only [res0]
        change coreLen (cfg.T.lsfs (res0.2.1 k) (res0.2.2.1 k))
            ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k) e =
          coreLen (cfg.T.lsfs (cfg.T.initOrd cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (res0.1 k)
            ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k)
            ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainGrad (D.g 0) k)
            (chainLevelOrd cfg.T res0.1 res0.2.1 res0.2.2.1 k)) (res0.2.2.1 k))
            ((mkPartialChain cfg.T cfg.P res0.1 res0.2.1 res0.2.2.1 (res0.1 cfg.P.d)).chainLen (D.ℓ 0) k) e
        rw [← hsufk.2.2.2.2.2.2.2.2.2.1]
      · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
        have hRunK := (H₀ k (Nat.lt_of_succ_lt hk)).hRun
        have hLenK : (H₀ k (Nat.lt_of_succ_lt hk)).len = 0 := rfl
        have hS0K : (H₀ k (Nat.lt_of_succ_lt hk)).s₀ = 0 := rfl
        have hLenK1 : (H₀ (k + 1) hk).len = 0 := rfl
        have hIdx0 : (H₀ k (Nat.lt_of_succ_lt hk)).s₀ +
            (((H₀ k (Nat.lt_of_succ_lt hk)).len - (H₀ (k + 1) hk).len) -
              (H₀ k (Nat.lt_of_succ_lt hk)).s₀ + 0) = (H₀ k (Nat.lt_of_succ_lt hk)).len := by
          rw [hS0K, hLenK, hLenK1]
        rw [hIdx0, ← hRunK]
        rfl
    updRound := fun _ => 1,
    hUpdBound := fun _ _ => by rw [hEndG]; exact ⟨le_refl 1, le_refl 1⟩,
    hUpdMono := fun τ₁ τ₂ h12 h2 => by simp [H₀, zeroLevelHistory] at h2; omega,
    hUpdBand := fun r hre _ => ⟨hre, fun hlt => by simp [H₀, zeroLevelHistory] at hlt⟩,
    hLvl0Match := fun _ _ => ⟨rfl, fun _ _ => rfl⟩,
    hLvl0NoIns := fun s τ _ hτ _ _ _ _ _ _ _ _ _ e _ => by
      simp [H₀, zeroLevelHistory] at hτ
      subst hτ
      exact ⟨fun _ => ⟨rfl, fun x hx1 hx2 => by omega, rfl⟩, fun _ => ⟨rfl, fun x hx1 hx2 => by omega⟩⟩ }⟩

/-- **Init step**: construct `Ordered.Alg2HiddenTrace` at `t = 0` after `algorithm2_init`. -/
theorem alg2HiddenTrace_init {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hm0 : (D.G 0).m ≤ cfg.P.M₀) (hn0 : (D.G 0).n ≤ cfg.N₀)
    {c_ext w_ext : ℕ → ℕ → ℝ} (hHS0 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext 0) :
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext 0
      (algorithm2_init cfg (D.G 0) (D.g 0) (D.ℓ 0))) :=
  alg2HiddenTrace_initAt cfg.N₀ hV hHist hEdge hm0 hn0
    (fun hIc hFc => chainInv_last_le_N0 hV hn0 hIc hFc) hHS0

/-- **Detect step**: advance `Ordered.Alg2HiddenTraceAt` from `t` to `t + 1` across
`algorithm2_detect`, parameterized by last-level vertex cap `nLast`. -/
theorem alg2HiddenTrace_detectAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (_hEdge : HistoryEdgeOnly D T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = false)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G (t + 1)) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    (hℓ : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e')) :
    Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext
      (t + 1) (algorithm2_detect cfg st).2) := by
  have hDetU := (hHist.2.2.1 (t + 1) (by omega) ht1 hisUpd).1
  have hDetℓ : D.ℓ (t + 1) = D.ℓ t := by
    simpa using (hHist.2.2.1 (t + 1) (by omega) ht1 hisUpd).2.2
  have hDG : D.G (t + 1) = D.G t := by
    have hV1 := (hHist.1 (t + 1) (by omega) ht1).2
    rw [hDetU] at hV1; exact hV1
  have hFresh1 : FreshInv (D.G (t + 1)) (st.chain.G 0) st.extToInt st.intToExt st.nextFresh := by
    rw [hDG, ← hExtG]; exact hFresh
  have hℓ1 : st.chain.ℓ = fun e' => D.ℓ (t + 1) (st.intToExt e') := by
    rw [hℓ]; ext e'; rw [hDetℓ]
  have hSH1 := chainState_snapHoldsAt nLast hV hInv hFresh1 hℓ1 hn1 (hLastBound hInv hFresh1)
  set gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  set R := gSt.round
  let W' : ℕ → ℝ := fun r => if r = R + 1 then (D.G (t + 1)).norm1 (w_ext (t + 1)) else tr.W_game r
  have hW_le : ∀ r ≤ R, tr.W_game r = W' r := fun r hr => by
    simp [W', Nat.ne_of_lt (lt_of_le_of_lt hr (Nat.lt_succ_self R))]
  have hv_congr := validPlayPrefix_W_congr tr.W_game W' hW_le tr.hv
  have hf_congr := followsStrategyPrefix_W_congr tr.W_game W' hW_le tr.hf
  have hsc : Game.stateAt W' cfg.P.hk tr.initStr tr.moves tr.moves.length = gSt :=
    (stateAt_W_congr tr.W_game W' cfg.P.hk tr.initStr tr.moves tr.moves.length hW_le).1.symm
  have hpc : Game.passesAt W' cfg.P.hk tr.initStr tr.moves tr.moves.length =
      Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length :=
    (stateAt_W_congr tr.W_game W' cfg.P.hk tr.initStr tr.moves tr.moves.length hW_le).2.symm
  let m₁ : Game.Move cfg.P.d cfg.P.k := .roundStep .roundCompleting .doNothing (fun _ _ => 0)
  let m₂ : Game.Move cfg.P.d cfg.P.k := .advDoNothing
  have hPh : gSt.phase = .stage34 := tr.hPhase
  have hm1_v : Game.ValidStep cfg.gameParams W' gSt m₁ := by simp [Game.ValidStep, hPh, m₁]
  have hm1_s : Game.StrategyStep cfg.gameParams gSt
      (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m₁ := by
    simp [Game.StrategyStep, hPh, m₁]; rfl
  have hv1 := validPlayPrefix_snoc hv_congr m₁
    ((congrArg (fun s => Game.ValidStep cfg.gameParams W' s m₁) hsc).mpr hm1_v)
  have hf1 := followsStrategyPrefix_snoc hf_congr m₁
    ((congrArg (fun p => Game.StrategyStep cfg.gameParams _ p m₁) hpc).mpr
      ((congrArg (fun s => Game.StrategyStep cfg.gameParams s _ m₁) hsc).mpr hm1_s))
  have hlen1 : (tr.moves ++ [m₁]).length = tr.moves.length + 1 := by simp
  have hget1 : (tr.moves ++ [m₁])[tr.moves.length]'(by simp) = m₁ := by simp
  have hgSt1 : Game.stateAt W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (tr.moves ++ [m₁]).length =
      { gSt with round := R + 1, phase := .stage2 } := by
    rw [hlen1, Game.stateAt_succ W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (by simp),
      stateAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
      hget1, hsc]
    simp [m₁, Game.stepState, gSt, R]
  have hm2_v : Game.ValidStep cfg.gameParams W' { gSt with round := R + 1, phase := .stage2 } m₂ := by
    simp only [Game.ValidStep, m₂, W', ↓reduceIte]
    exact ⟨weightValid_norm1_of_hiddenStableAt hV.hα hm1 hHS1, trivial⟩
  let moves' := (tr.moves ++ [m₁]) ++ [m₂]
  have hlen2 : moves'.length = (tr.moves ++ [m₁]).length + 1 := by simp [moves']
  have hget2 : moves'[(tr.moves ++ [m₁]).length]'(by simp [moves']) = m₂ := by simp [moves']
  have hv' := validPlayPrefix_snoc hv1 m₂
    ((congrArg (fun s => Game.ValidStep cfg.gameParams W' s m₂) hgSt1).mpr hm2_v)
  have hf' := followsStrategyPrefix_snoc hf1 m₂
    ((congrArg (fun s => Game.StrategyStep cfg.gameParams s _ m₂) hgSt1).mpr
      (by simp [Game.StrategyStep]))
  have hEnd : Game.stateAt W' cfg.P.hk tr.initStr moves' moves'.length =
      { gSt with round := R + 1, phase := .stage34 } := by
    rw [hlen2, Game.stateAt_succ W' cfg.P.hk tr.initStr moves' (by simp [moves']),
      stateAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      hget2, hgSt1]
    simp [m₂, Game.stepState]
  have hPassEnd : Game.passesAt W' cfg.P.hk tr.initStr moves' moves'.length =
      Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length := by
    rw [hlen2, Game.passesAt_succ W' cfg.P.hk tr.initStr moves' (by simp [moves']),
      passesAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      stateAt_append_left W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) [m₂] _ (le_refl _),
      hget2]
    have hp1 : Game.passesAt W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (tr.moves ++ [m₁]).length =
        Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length := by
      rw [hlen1, Game.passesAt_succ W' cfg.P.hk tr.initStr (tr.moves ++ [m₁]) (by simp),
        passesAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
        stateAt_append_left W' cfg.P.hk tr.initStr tr.moves [m₁] tr.moves.length (le_refl _),
        hget1]
      simp [m₁, Game.stepPasses, hpc]
    rw [hp1]; simp [m₂, Game.stepPasses]
  let lvlIdx' : ℕ → ℕ → ℕ := fun r i =>
    if r = R + 1 then (if hi : i < cfg.P.d then (tr.H i hi).len else 0) else tr.lvlIdx r i
  refine ⟨{
    moves := moves', hmne := by simp [moves'], initStr := tr.initStr, W_game := W',
    hv := hv', hf := hf', hPhase := by rw [hEnd],
    timeOfRound := fun r => if r = R + 1 then t + 1 else tr.timeOfRound r,
    hTimeMono := fun r₁ r₂ h12 h2 => by
      rw [hEnd] at h2; simp only at h2
      rcases eq_or_lt_of_le (show r₂ ≤ R + 1 from h2) with rfl | h2lt
      · by_cases h1 : r₁ = R + 1
        · subst h1; simp
        · simp only [↓reduceIte, h1]
          exact le_trans (tr.hTimeMono r₁ R (by omega) (le_refl _)) (by rw [tr.hTimeEnd]; omega)
      · have hr2R : r₂ ≤ R := by omega
        simp only [Nat.ne_of_lt (lt_of_le_of_lt (le_trans h12 hr2R) (Nat.lt_succ_self _)),
          Nat.ne_of_lt (lt_of_le_of_lt hr2R (Nat.lt_succ_self _)), ↓reduceIte]
        exact tr.hTimeMono r₁ r₂ h12 hr2R
    hTimeEnd := by rw [hEnd]; simp,
    hW_eq := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp [W']
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp [W', hr1, tr.hW_eq r hrR]
    hShiftMatch := fun i => by
      change Game.shiftCount moves' i = st.chain.shiftCount i.val
      simpa [moves', Game.shiftCount, m₁, m₂] using tr.hShiftMatch i,
    hRebMatch := fun i => by
      change Game.rebuildCount moves' i = st.chain.rebuildCount i.val
      simpa [moves', Game.rebuildCount, m₁, m₂] using tr.hRebMatch i,
    hPassMatch := fun i => by rw [hPassEnd]; exact tr.hPassMatch i,
    hBranMatch := fun i => by rw [hEnd]; exact tr.hBranMatch i,
    snapC := fun r => if r = R + 1 then st.chain.toTreeChain else tr.snapC r,
    snapE2I := fun r => if r = R + 1 then st.extToInt else tr.snapE2I r,
    snapI2E := fun r => if r = R + 1 then st.intToExt else tr.snapI2E r,
    snapNF := fun r => if r = R + 1 then st.nextFresh else tr.snapNF r,
    hSnapEndC := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndE2I := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndI2E := by rw [hEnd]; simp [algorithm2_detect],
    hSnapEndNF := by rw [hEnd]; simp [algorithm2_detect],
    hSnapFresh := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [↓reduceIte]; exact hFresh1
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapFresh r hrR
    hSnapHolds := fun r hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [↓reduceIte]; exact hSH1
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapHolds r hrR
    reinit := tr.reinit,
    hRebRep := fun i => by rw [hEnd]; exact tr.hRebRep i,
    hRepRe := fun i => by rw [hEnd]; exact tr.hRepRe i,
    hSnapBran := fun i hi r hre hr b hb => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp [algorithm2_detect, ChainState.toTreeChain]
      · have hrR : r ≤ (Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length).round := by
          change r ≤ R; omega
        simp only [hr1, ↓reduceIte]; exact tr.hSnapBran i hi r hre hrR b hb
    hStrMatch := fun i j => by
      rw [hEnd]
      have hne : gSt.repT i ≠ R + 1 :=
        Nat.ne_of_lt (lt_of_le_of_lt (Game.repT_bounds _ _ _ _ _ i).2 (Nat.lt_succ_self _))
      simp only [hne, ↓reduceIte]
      exact tr.hStrMatch i j
    H := tr.H, lvlIdx := lvlIdx',
    hLvlReinit := fun i hi => by
      have hreR : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ R :=
        le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2
      simp [lvlIdx', Nat.ne_of_lt (lt_of_le_of_lt hreR (Nat.lt_succ_self _)), tr.hLvlReinit i hi],
    hLvlEnd := fun i hi => by rw [hEnd]; simp [lvlIdx', hi],
    hLvlMono := fun i hi r₁ r₂ hre1 h12 hr2 => by
      rw [hEnd] at hr2; simp only at hr2
      by_cases hr2_1 : r₂ = R + 1
      · subst hr2_1
        by_cases hr1_1 : r₁ = R + 1
        · subst hr1_1; exact le_rfl
        · have hr1R : r₁ ≤ R := by omega
          simp only [lvlIdx', hr1_1, ↓reduceIte, hi, ↓reduceDIte]
          rw [← tr.hLvlEnd i hi]
          exact tr.hLvlMono i hi r₁ R hre1 hr1R (le_refl R)
      · have hr2R : r₂ ≤ R := by omega
        have hr1_1 : r₁ ≠ R + 1 := by omega
        simp only [lvlIdx', hr2_1, hr1_1, ↓reduceIte]
        exact tr.hLvlMono i hi r₁ r₂ hre1 h12 hr2R
    hLvlSucc := fun i hi => by
      refine ⟨(tr.hLvlSucc i hi).1, fun r hre hr => ?_⟩
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1
        simp only [lvlIdx', ↓reduceIte, hi, Nat.lt_of_succ_lt hi, ↓reduceDIte]
        exact Nat.add_sub_of_le (tr.hLvlSucc i hi).1
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact (tr.hLvlSucc i hi).2 r hre hrR
    hLvlSnap := fun i hi r hre hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1
        simp only [lvlIdx', ↓reduceIte, hi, ↓reduceDIte]
        have hreR : tr.reinit ⟨i, Nat.lt_succ_of_le hi.le⟩ ≤ R :=
          le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2
        have hSnapR := tr.hLvlSnap i hi R hreR (le_refl R)
        refine ⟨by rw [← tr.hLvlEnd i hi, ← tr.hSnapEndC]; exact hSnapR.1,
          fun j hj => by rw [← tr.hLvlEnd i hi, ← tr.hSnapEndC]; exact hSnapR.2.1 j hj,
          fun _ j _ => by
            dsimp only [algorithm2_detect, ChainState.toTreeChain]
            rw [← (tr.H i hi).hRun]⟩
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact tr.hLvlSnap i hi r hre hrR
    hLvlCore := tr.hLvlCore, updRound := tr.updRound,
    hUpdBound := fun τ hτ => ⟨(tr.hUpdBound τ hτ).1, by rw [hEnd]; exact le_trans (tr.hUpdBound τ hτ).2 (Nat.le_succ _)⟩,
    hUpdMono := tr.hUpdMono,
    hUpdBand := fun r hre hr => by
      rw [hEnd] at hr; simp only at hr
      by_cases hr1 : r = R + 1
      · subst hr1; simp only [lvlIdx', ↓reduceIte, cfg.P.hd, ↓reduceDIte]
        exact ⟨le_trans (tr.hUpdBound _ (le_refl _)).2 (Nat.le_succ _), fun h => absurd h (lt_irrefl _)⟩
      · have hrR : r ≤ R := by omega
        simp only [lvlIdx', hr1, ↓reduceIte]; exact tr.hUpdBand r hre hrR
    hLvl0Match := fun τ hτ => by
      have hne : tr.updRound τ ≠ R + 1 := Nat.ne_of_lt (lt_of_le_of_lt (tr.hUpdBound τ hτ).2 (Nat.lt_succ_self _))
      have hm := tr.hLvl0Match τ hτ
      simp only [hne, ↓reduceIte]
      exact ⟨hm.1, fun e he => by simpa [hne] using hm.2 e he⟩
    hLvl0NoIns := fun s τ hs hτ r_s r_τ hrs1 hrs2 hrs3 hrt1 hrt2 hrt3 hst_r e he => by
      rw [hEnd] at hrs2 hrt2; simp only at hrs2 hrt2
      by_cases hrt1_eq : r_τ = R + 1
      · subst hrt1_eq
        have hτ_len : τ = (tr.H 0 cfg.P.hd).len := by
          by_contra hne
          have hlt := lt_of_le_of_ne hτ hne
          have hbad := hrt3 hlt; have hb := (tr.hUpdBound (τ + 1) hlt).2
          change tr.updRound (τ + 1) ≤ R at hb; omega
        subst hτ_len
        by_cases hrs_eq : r_s = R + 1
        · subst hrs_eq
          exact ⟨fun _ => ⟨rfl, fun x hx1 hx2 => by omega, rfl⟩,
            fun _ => ⟨rfl, fun x hx1 hx2 => by omega⟩⟩
        · have hrsR : r_s ≤ R := by omega
          have hR_band := tr.hUpdBand R (le_trans (tr.hRebRep _) (Game.repT_bounds _ _ _ _ _ _).2) (le_refl R)
          rw [tr.hLvlEnd 0 cfg.P.hd] at hR_band
          have hbase := tr.hLvl0NoIns s (tr.H 0 cfg.P.hd).len hs (le_refl _) r_s R hrs1 hrsR hrs3
            hR_band.1 (le_refl R) (fun hlt => absurd hlt (lt_irrefl _)) hrsR e he
          have hI2E_eq : st.intToExt e = tr.snapI2E R e := by rw [← tr.hSnapEndI2E]
          have hExtendNI : ∀ a, D.NotInsertedBetween a (tr.timeOfRound r_s) t →
              D.NotInsertedBetween a (tr.timeOfRound r_s) (t + 1) := fun a hNI x hx1 hx2 u hu hIu => by
            rcases eq_or_lt_of_le hx2 with rfl | hxlt
            · rw [hDetU] at hu; cases hu
            · exact hNI x hx1 (by omega) u hu hIu
          simp only [↓reduceIte, hrs_eq, hI2E_eq]
          rw [tr.hTimeEnd] at hbase
          refine ⟨fun heqs => ?_, fun hNI => ?_⟩
          · have hb := hbase.1 heqs; refine ⟨hb.1, hExtendNI _ hb.2.1, ?_⟩; rw [hDetℓ, hb.2.2]
          · have hb := hbase.2 hNI; exact ⟨hb.1, hExtendNI _ hb.2⟩
      · have hrtR : r_τ ≤ R := by omega
        have hrsR : r_s ≤ R := by omega
        have hrs_ne : r_s ≠ R + 1 := by omega
        simp only [hrt1_eq, hrs_ne, ↓reduceIte]
        exact tr.hLvl0NoIns s τ hs hτ r_s r_τ hrs1 hrsR hrs3 hrt1 hrtR hrt3 hst_r e he }⟩

/-- **Detect step**: advance `Ordered.Alg2HiddenTrace` from `t` to `t + 1` across
`algorithm2_detect`. -/
theorem alg2HiddenTrace_detect {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = false)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS1 : D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext (t + 1))
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t)
    (hℓ : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e')) :
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext (t + 1) (algorithm2_detect cfg st).2) :=
  alg2HiddenTrace_detectAt cfg.N₀ hV hHist hEdge ht1 hisUpd hm1 hn1
    (fun hIc hFc => chainInv_last_le_N0 hV hn1 hIc hFc)
    hHS1 tr hInv hFresh hExtG hℓ

end MinCostFlow.Chain.Ordered
