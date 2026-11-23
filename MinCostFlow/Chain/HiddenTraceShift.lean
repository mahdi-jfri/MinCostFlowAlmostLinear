module

public import MinCostFlow.Chain.HiddenTraceShiftHelpers
public import MinCostFlow.Chain.HiddenTraceSteps

/-!
# Shift step preservation of `Alg2HiddenTrace`

This file proves `alg2HiddenTrace_shift`, showing that whenever `algorithm2_loop` fails
to achieve ratio `-κ α` and selects `i = findEligibleLevel ...`, the shift count at level `i`
remains within `gameShiftBound` and `Alg2HiddenTrace` advances across `algorithm1_shift`.
-/

@[expose] public section

namespace MinCostFlow.Chain

/-- **Shift step**: when `algorithm2_loopWith` fails ratio `-κ α` and picks `i := findEligibleLevel ...`,
prove `shiftCount i + 1 ≤ gameShiftBound ...` MUST hold and advance `Alg2HiddenTraceAt` across
one `algorithm1_shift` step, parameterized by last-level vertex cap `nLast`. -/
theorem alg2HiddenTrace_shiftAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ}
    {st : Alg2State cfg}
    (tr : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBudget : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (_hBranD : st.branD < cfg.P.k)
    (hn : (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ {ch' e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' →
      FreshInv (D.G t) (ch'.G 0) e2i i2e nf → (ch'.G cfg.P.d).n ≤ nLast)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hNotGood : ¬ (st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) /
        st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) ≤
      -(alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast * cfg.α)))
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
  classical
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast
  set gSt := Game.stateAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length
  set R := gSt.round
  have hVNH := hV.toNoHidden
  have hFrD : FreshInv (D.G t) (st.chain.G 0) st.extToInt st.intToExt st.nextFresh := hExtG ▸ hFresh
  have hℓD : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e') := by rw [hℓ, hExtℓ]
  have hgD : st.chain.g = fun e' => D.g t (st.intToExt e') := by rw [hg, hExtg]
  obtain ⟨ctx, hcd, hck, hcγl, hcγc, hcσ, hcσm, hct, hcC, hc0, hcRep⟩ :=
    tr.toRepQualityCtx hV hHS hInv
  have hTH := hInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hVNH.hT hVNH.hMWU
    hVNH.hEmb hV.hγM₀ hV.hγk
  have hPb := freshInv_pullback_hiddenAt (tr.hSnapFresh R (le_refl R))
    (tr.hTimeEnd ▸ hHS t (le_refl t))
  rw [tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E] at hPb
  have h0R := hc0 R (by rw [hct])
  have h0t := hc0 ctx.t (le_refl _)
  have hvp_t : IsValidPair (ctx.G0 ctx.t) (ctx.ℓ0 ctx.t)
      (fun e' => c_ext t (st.intToExt e')) (ctx.w ctx.t) := by
    rw [h0t.1, h0t.2.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E]
    exact hPb.2.1
  have hItem3 : (ctx.G0 ctx.t).inner st.chain.g (fun e' => c_ext t (st.intToExt e')) /
      (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) ≤ -cfg.α := by
    rw [h0t.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E, hgD]
    exact hPb.2.2.1
  have hRat : (ctx.G0 ctx.t).inner st.chain.g (algorithm1_findCycle st.chain).1 /
      (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) (algorithm1_findCycle st.chain).1 > -(κ * cfg.α) := by
    have hIn : st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) =
        (st.chain.G 0).inner st.chain.g (algorithm1_findCycle st.chain).1 := by
      rw [hg, hFresh.inner_lift]
    have hLn : st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) =
        (st.chain.G 0).lnorm st.chain.ℓ (algorithm1_findCycle st.chain).1 := by
      rw [hℓ, hFresh.lnorm_lift]
    have hGt_eq : ctx.G0 ctx.t = st.chain.G 0 := by rw [h0t.1, hct, tr.hSnapEndC]; rfl
    have hℓt_eq : ctx.ℓ0 ctx.t = st.chain.ℓ := by rw [h0t.2.1, hct, tr.hTimeEnd, tr.hSnapEndI2E, hℓD]
    rw [hGt_eq, hℓt_eq]
    rw [hIn, hLn] at hNotGood
    exact lt_of_not_ge hNotGood
  have hκ_eq : κ = kappaBound ctx.d ctx.γ_ℓ (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      (alg2SigmaGame cfg.σ_mwu cfg.N₀) := by rw [hcd, hcγl]; rfl
  have hRatK : (ctx.G0 ctx.t).inner st.chain.g (algorithm1_findCycle st.chain).1 /
      (ctx.G0 ctx.t).lnorm (ctx.ℓ0 ctx.t) (algorithm1_findCycle st.chain).1 >
      -(kappaBound ctx.d ctx.γ_ℓ (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
        (alg2SigmaGame cfg.σ_mwu cfg.N₀) * cfg.α) := by
    rwa [← hκ_eq]
  have hSG_nn : 0 ≤ alg2SigmaGame cfg.σ_mwu cfg.N₀ := le_max_left _ _
  have hBad := lemma_6_3 ctx st.chain (by rw [hcC, hct, tr.hSnapEndC]) rfl
    (by rw [h0t.2.1, hct, tr.hTimeEnd, tr.hSnapEndI2E, hℓD])
    (by rw [hcσ]; exact le_refl _)
    (le_trans zero_le_one (le_max_of_le_left (hV.hTP.1 cfg.P.k cfg.N₀ cfg.P.hk)))
    hSG_nn hV.hα hInv.hℓPos hTH.2.1 hTH.2.2 hvp_t hItem3 hRatK
  have hGameBad : Game.LossSumCond tr.W_game gSt ∨ Game.BadStretchCond cfg.gameParams.σ gSt := by
    rcases hBad with hBN | hBH
    · left
      unfold BadNormCond at hBN
      unfold Game.LossSumCond
      have hWR : tr.W_game gSt.round = (ctx.G0 ctx.t).norm1 (ctx.w ctx.t) := by
        have hF0 := (tr.hSnapFresh R (le_refl R)).norm1_pullback (w_ext t)
        rw [tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E] at hF0
        have hW_g : tr.W_game gSt.round = (D.G t).norm1 (w_ext t) := by
          have h := tr.hW_eq R (le_refl R)
          rwa [tr.hTimeEnd] at h
        rw [h0t.1, h0t.2.2, hct, tr.hTimeEnd, tr.hSnapEndC, tr.hSnapEndI2E, hF0, hW_g]
      have hSum : (∑ j : Fin (cfg.P.d + 1), tr.W_game (gSt.repT j)) =
          ∑ j ∈ Finset.range (ctx.d + 1), (ctx.G0 (ctx.repT j)).norm1 (ctx.w (ctx.repT j)) := by
        rw [hcd, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hrepR : gSt.repT j ≤ R := (Game.repT_bounds _ _ _ _ _ j).2
        have hj0 := hc0 (gSt.repT j) (by rw [hct]; exact hrepR)
        have hF := (tr.hSnapFresh (gSt.repT j) hrepR).norm1_pullback (w_ext (tr.timeOfRound (gSt.repT j)))
        rw [tr.hW_eq (gSt.repT j) hrepR, ← hF, ← hj0.1, ← hj0.2.2, ← (hcRep j).2]
      rw [hWR, hSum, ← hcd]
      exact hBN
    · right
      obtain ⟨j, hj, hj_gt⟩ := hBH
      rw [hcd] at hj
      refine ⟨⟨j, Nat.lt_succ_of_lt hj⟩, ?_⟩
      have hbr_eq : (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩).val = (ctx.C ctx.t).bran j := by
        have := tr.hBranMatch ⟨j, Nat.lt_succ_of_lt hj⟩
        simp only [hj, ↓reduceIte] at this
        rw [this, hcC, hct, tr.hSnapEndC]; rfl
      have hstr_eq := tr.hStrMatch ⟨j, Nat.lt_succ_of_lt hj⟩ (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩)
      simp only [hj, ↓reduceDIte] at hstr_eq
      change cfg.gameParams.σ < gSt.str ⟨j, Nat.lt_succ_of_lt hj⟩ (gSt.bran ⟨j, Nat.lt_succ_of_lt hj⟩)
      rw [hstr_eq, hbr_eq, ← (hcRep ⟨j, Nat.lt_succ_of_lt hj⟩).2]
      have hrepR : ctx.repT j ≤ ctx.t := by
        rw [(hcRep ⟨j, Nat.lt_succ_of_lt hj⟩).2, hct]; exact (Game.repT_bounds _ _ _ _ _ _).2
      have hrep0 := hc0 (ctx.repT j) hrepR
      change alg2SigmaGame cfg.σ_mwu cfg.N₀ <
        hstrAt (tr.snapC (ctx.repT j)) (fun e' => w_ext (tr.timeOfRound (ctx.repT j)) (tr.snapI2E (ctx.repT j) e'))
          j ((ctx.C ctx.t).bran j)
      rw [← hrep0.2.2, ← hcC]
      exact hj_gt
  set curB := if i.val < cfg.P.d then st.chain.bran i.val else st.branD
  set wrapped := (curB + 1) % cfg.P.k = 0
  set ch' := (algorithm1_shift cfg.T cfg.L cfg.P st.chain i.val).1
  set branD' := if i.val < cfg.P.d then 0 else (st.branD + 1) % cfg.P.k
  set passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
    if i < j then 0
    else if j = i then (if wrapped then st.passes i + 1 else st.passes i)
    else st.passes j
  have hShift := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hVNH.hT hV.hL hV.hγM₀ hV.hγk hInv hBudget i.val (Nat.le_of_lt_succ i.isLt)
  have hInv' : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' := hShift.1
  have hch'G0 : ch'.G 0 = st.chain.G 0 := hShift.2.2.1
  have hch'ℓ : ch'.ℓ = st.chain.ℓ := hShift.2.2.2.1
  have hch'g : ch'.g = st.chain.g := hShift.2.2.2.2.1
  have hch'SC : ch'.shiftCount =
      fun j => if j = i.val then st.chain.shiftCount i.val + 1 else st.chain.shiftCount j :=
    hShift.2.2.2.2.2.1
  have hch'RC : ch'.rebuildCount = st.chain.rebuildCount := hShift.2.2.2.2.2.2.1
  have hFr' : FreshInv (D.G t) (ch'.G 0) st.extToInt st.intToExt st.nextFresh := by
    rw [hch'G0]; exact hFrD
  have hℓD' : ch'.ℓ = fun e' => D.ℓ t (st.intToExt e') := by rw [hch'ℓ, hℓD]
  have hSH' := chainState_snapHoldsAt nLast hVNH hInv' hFr' hℓD' hn (hLastBound hInv' hFr')
  have hℓ_nn' : ∀ e' ∈ (ch'.G 0).E, 0 ≤ D.ℓ t (st.intToExt e') := fun e' he' => by
    have hℓ_pos := (hInv'.hℓPos e' he').le
    exact (congrFun hℓD' e') ▸ hℓ_pos
  have hw_nn' : ∀ e' ∈ (ch'.G 0).E, 0 ≤ w_ext t (st.intToExt e') := fun e' he' =>
    (hHS t (le_refl t)).2.2.2.2 (st.intToExt e') (hFr'.hRight e' he').2 |>.1.le
  have hNewStr_spec := chain_validStretch_hstr hVNH hSH'.1 hSH'.2.1 hSH'.2.2.1 hSH'.2.2.2.1 hSH'.2.2.2.2
    hℓ_nn' hw_nn'
  let rPick : Fin (cfg.P.d + 1) → ℕ := fun i' =>
    if i < i' then R
    else if i' = i ∧ wrapped then Game.argminRound tr.W_game (gSt.repT i) R
    else gSt.repT i'
  let newStr : Fin (cfg.P.d + 1) → Fin cfg.P.k → ℝ := fun i' j =>
    if _hi : i'.val < cfg.P.d then
      let r_i := rPick i'
      let C_i := if r_i = R then ch'.toTreeChain else tr.snapC r_i
      let i2e_i := if r_i = R then st.intToExt else tr.snapI2E r_i
      hstrAt C_i (fun e' => w_ext (tr.timeOfRound r_i) (i2e_i e')) i'.val j.val
    else 0
  have hrPick_le : ∀ i', rPick i' ≤ R := fun i' => by
    dsimp only [rPick]
    split_ifs
    · exact le_rfl
    · exact (Game.argminRound_bounds tr.W_game (Game.repT_bounds _ _ _ _ _ i).2).2
    · exact (Game.repT_bounds _ _ _ _ _ i').2
  have hTimeR : tr.timeOfRound R = t := tr.hTimeEnd
  have hNewStr_valid : ∀ i', (∀ j, 0 ≤ newStr i' j) ∧ Game.ValidStretch cfg.gameParams.σ (newStr i') := by
    intro i'
    by_cases hi' : i'.val < cfg.P.d
    · by_cases hrR : rPick i' = R
      · simpa [newStr, hi', hrR, hTimeR] using hNewStr_spec i'
      · have hr_lt : rPick i' < R := lt_of_le_of_ne (hrPick_le i') hrR
        have hSr := tr.hSnapHolds (rPick i') (le_of_lt hr_lt)
        have hFr := tr.hSnapFresh (rPick i') (le_of_lt hr_lt)
        have htr_le : tr.timeOfRound (rPick i') ≤ t :=
          le_trans (tr.hTimeMono _ R (le_of_lt hr_lt) (le_refl R)) (le_of_eq tr.hTimeEnd)
        have hHSr := hHS _ htr_le
        have hℓ_r : ∀ e' ∈ ((tr.snapC (rPick i')).G 0).E,
            0 ≤ D.ℓ (tr.timeOfRound (rPick i')) (tr.snapI2E (rPick i') e') := fun e' he' =>
          (hHSr.2.2.2.2 _ (hFr.hRight e' he').2).2.2.1.le
        have hw_r : ∀ e' ∈ ((tr.snapC (rPick i')).G 0).E,
            0 ≤ w_ext (tr.timeOfRound (rPick i')) (tr.snapI2E (rPick i') e') := fun e' he' =>
          (hHSr.2.2.2.2 _ (hFr.hRight e' he').2).1.le
        simpa [newStr, hi', hrR] using
          chain_validStretch_hstr hVNH hSr.1 hSr.2.1 hSr.2.2.1 hSr.2.2.2.1 hSr.2.2.2.2 hℓ_r hw_r i'
    · refine ⟨fun j => by simp [newStr, hi'],
        ⟨⟨0, cfg.P.hk⟩, by simp [newStr, hi', Alg2Config.gameParams, alg2SigmaGame]⟩⟩
  let m : Game.Move cfg.P.d cfg.P.k := .roundStep .roundContinuing (.shift i) newStr
  have hPh : gSt.phase = .stage34 := tr.hPhase
  have hm_v : Game.ValidStep cfg.gameParams tr.W_game gSt m := by
    simp only [Game.ValidStep, hPh, m]
    exact ⟨fun _ => hGameBad, fun i' _ => hNewStr_valid i', fun _ => hNewStr_valid i⟩
  have hEligS := findEligibleLevel_spec hElig
  let moves' := tr.moves ++ [m]
  have hv' := validPlayPrefix_snoc tr.hv m hm_v
  have hm_f : Game.StrategyStep cfg.gameParams gSt
      (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m := by
    simp only [Game.StrategyStep, hPh, m]
    exact ⟨i,
      (congrArg (fun x : ℕ => (x : ℝ) < 2 * cfg.gameParams.Ψ) (tr.hPassMatch i)).mpr hEligS.1,
      fun j hj => hEligS.2 j
        ((congrArg (fun x : ℕ => (x : ℝ) < 2 * cfg.gameParams.Ψ) (tr.hPassMatch j)).mp hj),
      rfl⟩
  have hf' := followsStrategyPrefix_snoc tr.hf m hm_f
  have hShiftLe : (st.chain.shiftCount i.val : ℝ) + 1 ≤
      gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val := by
    have h73 := Game.lemma_7_3_prefix cfg.gameParams hv' hf' i
    have hSC : Game.shiftCount moves' i = st.chain.shiftCount i.val + 1 := by
      rw [Game.shiftCount, show moves' = tr.moves ++ [m] from rfl, List.countP_append]
      change Game.shiftCount tr.moves i + _ = _
      rw [tr.hShiftMatch i]; simp [m]
    have hRC : ∀ i' : Fin (cfg.P.d + 1),
        Game.rebuildCount moves' i' = st.chain.rebuildCount i'.val := fun i' => by
      rw [Game.rebuildCount, show moves' = tr.moves ++ [m] from rfl, List.countP_append]
      change Game.rebuildCount tr.moves i' + _ = _
      rw [tr.hRebMatch i']; simp [m]
    have h73p : (Game.shiftCount moves' i : ℝ) ≤
        (10 * Ψ_g * (cfg.P.k : ℝ)) ^ (i.val + 1) +
          (Finset.Iic i).sum (fun i' => (Game.rebuildCount moves' i' : ℝ) *
            (10 * Ψ_g * (cfg.P.k : ℝ)) ^ (i.val + 1 - i'.val)) := h73
    have hSumEq : (Finset.Iic i).sum (fun i' => (Game.rebuildCount moves' i' : ℝ) *
          (10 * Ψ_g * (cfg.P.k : ℝ)) ^ (i.val + 1 - i'.val)) =
        (Finset.range (i.val + 1)).sum (fun j => (st.chain.rebuildCount j : ℝ) *
          (10 * Ψ_g * (cfg.P.k : ℝ)) ^ (i.val + 1 - j)) :=
      Finset.sum_bij (fun a _ => a.val)
        (fun a ha => Finset.mem_range.mpr (Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp (Finset.mem_Iic.mp ha))))
        (fun _ _ _ _ h => Fin.ext h)
        (fun b hb => ⟨⟨b, Nat.lt_of_lt_of_le (Finset.mem_range.mp hb) i.isLt⟩,
          Finset.mem_Iic.mpr (Fin.le_iff_val_le_val.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))), rfl⟩)
        (fun a _ => by rw [hRC a])
    rw [hSC, hSumEq] at h73p
    unfold gameShiftBound
    push_cast at h73p ⊢; exact h73p
  refine ⟨hShiftLe, ?_⟩
  have hlen' : moves'.length = tr.moves.length + 1 := by simp [moves']
  have hget' : moves'[tr.moves.length]'(by simp [moves']) = m := by simp [moves']
  have hEndSt : Game.stateAt tr.W_game cfg.P.hk tr.initStr moves' moves'.length =
      Game.stepState tr.W_game cfg.P.hk gSt m := by
    rw [hlen', Game.stateAt_succ tr.W_game cfg.P.hk tr.initStr moves' (by simp [moves']),
      stateAt_append_left tr.W_game cfg.P.hk tr.initStr tr.moves [m] tr.moves.length (le_refl _),
      hget']
  have hPassSt : Game.passesAt tr.W_game cfg.P.hk tr.initStr moves' moves'.length =
      Game.stepPasses cfg.P.hk gSt
        (Game.passesAt tr.W_game cfg.P.hk tr.initStr tr.moves tr.moves.length) m := by
    rw [hlen', Game.passesAt_succ tr.W_game cfg.P.hk tr.initStr moves' (by simp [moves']),
      passesAt_append_left tr.W_game cfg.P.hk tr.initStr tr.moves [m] tr.moves.length (le_refl _),
      stateAt_append_left tr.W_game cfg.P.hk tr.initStr tr.moves [m] tr.moves.length (le_refl _),
      hget']
  have hRoundEq : (Game.stateAt tr.W_game cfg.P.hk tr.initStr moves' moves'.length).round = R := by
    rw [hEndSt]; simp [m, Game.stepState, R]
  have hcurB_eq : curB = (gSt.bran i).val := (tr.hBranMatch i).symm
  have hWrapEq : wrapped ↔ (Game.nextBranch cfg.P.hk (gSt.bran i)).val = 0 := by
    simp [Game.nextBranch, hcurB_eq, wrapped]
  -- Unpack exact `H'` and structural fields for `ch'`
  have hShiftStruct := alg2HiddenTrace_shiftStruct_aux cfg hV hVNH st.chain ch' i rfl hInv hInv'
    tr.H hShift.2.2.2.1 hShift.2.2.2.2.1
  rcases hShiftStruct with ⟨H', hH'le, hH'gt, hG'le, hBr'lt, hBr'eq, hBr'gt, hSucc', hH'restLt⟩
  let reinit' : Fin (cfg.P.d + 1) → ℕ := fun j => if i < j then R else tr.reinit j
  let lvlIdx' : ℕ → ℕ → ℕ := fun r k =>
    if r = R then (if hk : k < cfg.P.d then (H' k hk).len else 0) else tr.lvlIdx r k
  have hre_bounds : ∀ j, reinit' j ≤ R := fun j => by
    dsimp only [reinit']; split_ifs
    · exact le_rfl
    · exact le_trans (tr.hRebRep j) (Game.repT_bounds _ _ _ _ _ j).2
  have hSnapEndC_R : tr.snapC R = st.chain.toTreeChain := tr.hSnapEndC
  have hSnapEndE2I_R : tr.snapE2I R = st.extToInt := tr.hSnapEndE2I
  have hSnapEndI2E_R : tr.snapI2E R = st.intToExt := tr.hSnapEndI2E
  have hSnapEndNF_R : tr.snapNF R = st.nextFresh := tr.hSnapEndNF
  refine ⟨{
    moves := moves', hmne := by simp [moves'], initStr := tr.initStr, W_game := tr.W_game,
    hv := hv', hf := hf', hPhase := by rw [hEndSt]; simp [m, Game.stepState],
    timeOfRound := tr.timeOfRound,
    hTimeMono := fun r₁ r₂ h12 h2 => by rw [hRoundEq] at h2; exact tr.hTimeMono r₁ r₂ h12 h2,
    hTimeEnd := by rw [hRoundEq]; exact tr.hTimeEnd,
    hW_eq := fun r hr => by rw [hRoundEq] at hr; exact tr.hW_eq r hr,
    hShiftMatch := fun j => by
      change Game.shiftCount moves' j = ch'.shiftCount j.val
      rw [hch'SC]
      have hsm := tr.hShiftMatch j
      rw [Game.shiftCount, show moves' = tr.moves ++ [m] from rfl, List.countP_append]
      change Game.shiftCount tr.moves j + _ = _
      rw [hsm]; simp only [m, List.countP_cons, List.countP_nil, beq_iff_eq]
      by_cases hji : j = i
      · subst hji; simp
      · have hne : j.val ≠ i.val := fun hv => hji (Fin.ext hv)
        have hij : ¬ i = j := fun hv => hji hv.symm
        simp [hne, hij]
    hRebMatch := fun j => by
      change Game.rebuildCount moves' j = ch'.rebuildCount j.val
      rw [hch'RC]
      have hrm := tr.hRebMatch j
      rw [Game.rebuildCount, show moves' = tr.moves ++ [m] from rfl, List.countP_append]
      change Game.rebuildCount tr.moves j + _ = _
      rw [hrm]; simp [m]
    hPassMatch := fun j => by
      rw [hPassSt]
      simp only [m, Game.stepPasses, tr.hPassMatch]
      have hWrapEq' : (Game.nextBranch cfg.P.hk (gSt.bran i)).val = 0 ↔
          ((if i.val < cfg.P.d then st.chain.bran i.val else st.branD) + 1) % cfg.P.k = 0 :=
        hWrapEq.symm
      by_cases h1 : i < j
      · simp only [h1, ↓reduceIte]
      · by_cases h2 : j = i
        · subst h2
          simp only [h1, ↓reduceIte, hWrapEq']
          dsimp only [curB]
        · simp only [h1, h2, ↓reduceIte]
    hBranMatch := fun j => by
      rw [hEndSt]
      simp only [m, Game.stepState]
      by_cases h1 : i < j
      · simp only [h1, ↓reduceIte]
        have hi_lt : i.val < cfg.P.d := lt_of_lt_of_le h1 (Nat.le_of_lt_succ j.isLt)
        by_cases hj : j.val < cfg.P.d
        · simp [hj, hBr'gt j.val h1 hj]
        · simp [hj, branD', hi_lt]
      · simp only [h1, ↓reduceIte]
        by_cases h2 : j = i
        · subst h2
          have hbr_j : (gSt.bran j).val =
              if j.val < cfg.P.d then st.chain.bran j.val else st.branD :=
            tr.hBranMatch j
          simp only [↓reduceIte, Game.nextBranch, hbr_j]
          by_cases hj : j.val < cfg.P.d
          · simp [hj, hBr'eq hj]
          · simp [hj, branD']
        · have hj_lt : j < i := lt_of_le_of_ne (Fin.not_lt.mp h1) h2
          have hjd : j.val < cfg.P.d := lt_of_lt_of_le hj_lt (Nat.le_of_lt_succ i.isLt)
          have hbr_j : (gSt.bran j).val =
              if j.val < cfg.P.d then st.chain.bran j.val else st.branD :=
            tr.hBranMatch j
          simp only [hjd, ↓reduceIte] at hbr_j ⊢
          simp [h2, hbr_j, hBr'lt j.val (Fin.lt_def.mp hj_lt)]
    snapC := fun r => if r = R then ch'.toTreeChain else tr.snapC r,
    snapE2I := tr.snapE2I, snapI2E := tr.snapI2E, snapNF := tr.snapNF,
    hSnapEndC := by rw [hRoundEq]; simp,
    hSnapEndE2I := by rw [hRoundEq]; exact tr.hSnapEndE2I,
    hSnapEndI2E := by rw [hRoundEq]; exact tr.hSnapEndI2E,
    hSnapEndNF := by rw [hRoundEq]; exact tr.hSnapEndNF,
    hSnapFresh := fun r hr => by
      rw [hRoundEq] at hr
      by_cases hrR : r = R
      · subst hrR
        simp only [↓reduceIte]
        rw [hTimeR, hSnapEndE2I_R, hSnapEndI2E_R, hSnapEndNF_R]
        exact hFr'
      · simp only [hrR, ↓reduceIte]; exact tr.hSnapFresh r hr
    hSnapHolds := fun r hr => by
      rw [hRoundEq] at hr
      by_cases hrR : r = R
      · subst hrR
        simp only [↓reduceIte, hTimeR, hSnapEndI2E_R]
        exact hSH'
      · simp only [hrR, ↓reduceIte]; exact tr.hSnapHolds r hr
    reinit := reinit',
    hRebRep := fun j => by
      rw [hEndSt]; simp only [m, Game.stepState, reinit']
      by_cases h1 : i < j
      · simp [h1]; exact le_rfl
      · by_cases h2 : j = i
        · subst h2
          simp only [h1, ↓reduceIte]
          by_cases hw : (Game.nextBranch cfg.P.hk (gSt.bran j)).val = 0
          · simp only [hw, ↓reduceIte]
            exact le_trans (tr.hRebRep j)
              (Game.argminRound_bounds tr.W_game (Game.repT_bounds _ _ _ _ _ j).2).1
          · simp only [hw, ↓reduceIte]; exact tr.hRebRep j
        · simp [h1, h2]; exact tr.hRebRep j
    hRepRe := fun j => by
      rw [hEndSt]; simp only [m, Game.stepState, reinit']
      let j₀ : Fin (cfg.P.d + 1) := ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩
      let j₁ : Fin (cfg.P.d + 1) := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have h01 : j₀ < j₁ := by simp [j₀, j₁, Fin.lt_def]
      by_cases hi0 : i < j₀
      · have hi1 : i < j₁ := lt_trans hi0 h01
        simp only [j₀, j₁, hi0, hi1, ↓reduceIte]; exact le_rfl
      · by_cases hj0i : j₀ = i
        · have hi1 : i < j₁ := by simpa [hj0i] using h01
          have hnot_ii : ¬ i < i := lt_irrefl i
          simp only [j₀, j₁, hj0i, hi1, ↓reduceIte, hnot_ii]
          split_ifs
          · exact (Game.argminRound_bounds tr.W_game (Game.repT_bounds _ _ _ _ _ i).2).2
          · exact (Game.repT_bounds _ _ _ _ _ i).2
        · have hji_lt : j₀ < i := lt_of_le_of_ne (Fin.not_lt.mp hi0) hj0i
          have hji_val : j.val < i.val := Fin.lt_def.mp hji_lt
          have hji : j₁ ≤ i :=
            Fin.le_iff_val_le_val.mpr (by change j.val + 1 ≤ i.val; omega)
          have hn1 : ¬ i < j₁ := Fin.not_lt.mpr hji
          simpa [j₀, j₁, hi0, hj0i, hn1] using tr.hRepRe j
    hSnapBran := fun k hk r hre hr b hb => by
      rw [hRoundEq] at hr
      by_cases hrR : r = R
      · subst hrR; simp [ChainState.toTreeChain]
      · have hlt_R : r < R := lt_of_le_of_ne hr hrR
        have hki : k ≤ i.val := by
          by_contra hgt
          have hi_lt : i < ⟨k, Nat.lt_succ_of_le hk⟩ := Fin.lt_def.mpr (by change i.val < k; omega)
          have := hre
          simp only [reinit', hi_lt, ↓reduceIte] at this
          omega
        have hbi : b < i.val := lt_of_lt_of_le hb hki
        simp only [hrR, ↓reduceIte]
        have hnot : ¬ i < ⟨k, Nat.lt_succ_of_le hk⟩ :=
          fun hlt => absurd (Fin.lt_def.mp hlt) (by change ¬ i.val < k; omega)
        have hr_re : tr.reinit ⟨k, Nat.lt_succ_of_le hk⟩ ≤ r := by
          simpa [reinit', hnot] using hre
        rw [tr.hSnapBran k hk r hr_re (le_of_lt hlt_R) b hb, hBr'lt b hbi]
    hStrMatch := fun j l => by
      rw [hEndSt]; simp only [m, Game.stepState]
      have hRR : R = gSt.round := rfl
      by_cases h1 : i < j
      · simp only [h1, ↓reduceIte]
        by_cases hj : j.val < cfg.P.d
        · have hrr : rPick j = R := by simp [rPick, h1]
          simp [newStr, hj, hrr, ← hRR, hSnapEndI2E_R]
        · simp [newStr, hj]
      · by_cases h2 : j = i
        · subst h2
          by_cases hw : (Game.nextBranch cfg.P.hk (gSt.bran j)).val = 0
          · have hwa : wrapped := hWrapEq.mpr hw
            simp only [h1, ↓reduceIte, hw]
            by_cases hj : j.val < cfg.P.d
            · have hrr : rPick j = Game.argminRound tr.W_game (gSt.repT j) R := by
                dsimp [rPick]; simp [hwa]
              by_cases harg : Game.argminRound tr.W_game (gSt.repT j) R = R
              · have harg_g : Game.argminRound tr.W_game (gSt.repT j) gSt.round = R := harg
                rw [harg] at hrr
                simp only [newStr, hj, ↓reduceDIte, hrr, ↓reduceIte, harg_g, hSnapEndI2E_R]
              · have harg_g : Game.argminRound tr.W_game (gSt.repT j) gSt.round ≠ R := harg
                simp only [newStr, hj, ↓reduceDIte, hrr, harg, harg_g, ↓reduceIte]
                rfl
            · simp [newStr, hj]
          · have hnwa : ¬ wrapped := fun h => hw (hWrapEq.mp h)
            simp only [h1, ↓reduceIte, hw]
            have hstr0 := tr.hStrMatch j l
            by_cases hj : j.val < cfg.P.d
            · simp only [hj, ↓reduceDIte] at hstr0 ⊢
              change gSt.str j l = hstrAt (tr.snapC (gSt.repT j))
                (fun e' => w_ext (tr.timeOfRound (gSt.repT j)) (tr.snapI2E (gSt.repT j) e')) j.val l.val at hstr0
              rw [hstr0]
              by_cases hrR : gSt.repT j = R
              · rw [hrR]; simp only [↓reduceIte, hTimeR, hSnapEndI2E_R, hSnapEndC_R]
                refine hstrAt_congr _ ?_ (fun m hm => ?_) (fun m hm => ?_) ?_
                · intro m hm; change st.chain.G m = ch'.G m; exact (hG'le m (by omega) (lt_of_le_of_lt hm hj)).1.symm
                · have hmd := lt_trans hm hj; have hm_lt : m < j.val := by omega
                  simp only [TreeChain.activeLSF, ChainState.toTreeChain, hmd, ↓reduceIte]
                  rw [(hG'le m hm.le hmd).2.1 hm_lt, hBr'lt m hm_lt]
                · have hmd := lt_trans hm hj; have hm_lt : m < j.val := by omega
                  simp only [TreeChain.activeEmb, ChainState.toTreeChain, hmd, ↓reduceIte]
                  rw [(hG'le m hm.le hmd).2.1 hm_lt, hBr'lt m hm_lt]
                · change cfg.T.lsfs (st.chain.scState j.val) l.val = cfg.T.lsfs (ch'.scState j.val) l.val
                  exact ((hG'le j.val (le_refl _) hj).2.2 l.val l.isLt).symm
              · simp only [hrR, ↓reduceIte]
            · simp only [hj, ↓reduceDIte] at hstr0 ⊢
              rw [hstr0]
        · simp only [h1, ↓reduceIte, h2]
          have hji : j < i := lt_of_le_of_ne (Fin.not_lt.mp h1) h2
          have hjd : j.val < cfg.P.d := lt_of_lt_of_le hji (Nat.le_of_lt_succ i.isLt)
          have hstr0 := tr.hStrMatch j l
          simp only [hjd, ↓reduceDIte] at hstr0 ⊢
          change gSt.str j l = hstrAt (tr.snapC (gSt.repT j))
            (fun e' => w_ext (tr.timeOfRound (gSt.repT j)) (tr.snapI2E (gSt.repT j) e')) j.val l.val at hstr0
          rw [hstr0]
          by_cases hrR : gSt.repT j = R
          · rw [hrR]; simp only [↓reduceIte, hTimeR, hSnapEndI2E_R, hSnapEndC_R]
            refine hstrAt_congr _ ?_ (fun m hm => ?_) (fun m hm => ?_) ?_
            · intro m hm; change st.chain.G m = ch'.G m; exact (hG'le m (by omega) (lt_of_le_of_lt hm hjd)).1.symm
            · have hmd := lt_trans hm hjd; have hm_lt : m < i.val := by omega
              simp only [TreeChain.activeLSF, ChainState.toTreeChain, hmd, ↓reduceIte]
              rw [(hG'le m hm_lt.le hmd).2.1 hm_lt, hBr'lt m hm_lt]
            · have hmd := lt_trans hm hjd; have hm_lt : m < i.val := by omega
              simp only [TreeChain.activeEmb, ChainState.toTreeChain, hmd, ↓reduceIte]
              rw [(hG'le m hm_lt.le hmd).2.1 hm_lt, hBr'lt m hm_lt]
            · change cfg.T.lsfs (st.chain.scState j.val) l.val = cfg.T.lsfs (ch'.scState j.val) l.val
              rw [(hG'le j.val hji.le hjd).2.1 (Fin.lt_def.mp hji)]
          · simp only [hrR, ↓reduceIte],
    H := H', lvlIdx := lvlIdx',
    hLvlReinit := fun k hk => by
      dsimp only [lvlIdx', reinit']
      by_cases hik : i < ⟨k, Nat.lt_succ_of_le hk.le⟩
      · have hik_nat : i.val < k := Fin.lt_def.mp hik
        simp [hik, hk, hH'gt k hk hik_nat]
      · have hki : k ≤ i.val := by
          by_contra hgt
          exact hik (Fin.lt_def.mpr (by change i.val < k; omega))
        have hr0 := tr.hLvlReinit k hk
        by_cases hreR : tr.reinit ⟨k, Nat.lt_succ_of_le hk.le⟩ = R
        · have hLE := tr.hLvlEnd k hk
          change tr.lvlIdx R k = (tr.H k hk).len at hLE
          simp only [hik, ↓reduceIte, hreR, hk, ↓reduceDIte]
          rw [(hH'le k hk hki).2.1, ← hLE, ← hreR]; exact hr0
        · simp [hik, hreR, hr0]
    hLvlEnd := fun k hk => by rw [hRoundEq]; simp [lvlIdx', hk],
    hLvlMono := fun k hk r₁ r₂ hre1 h12 hr2 => by
      rw [hRoundEq] at hr2
      by_cases hr1R : r₁ = R
      · subst hr1R
        have : r₂ = R := le_antisymm hr2 h12
        subst this; exact le_rfl
      · have hki : k ≤ i.val := by
          by_contra hgt
          have hik : i < ⟨k, Nat.lt_succ_of_le hk.le⟩ := Fin.lt_def.mpr (by change i.val < k; omega)
          simp only [reinit', hik, ↓reduceIte] at hre1
          omega
        have hnot : ¬ i < ⟨k, Nat.lt_succ_of_le hk.le⟩ :=
          fun hlt => absurd (Fin.lt_def.mp hlt) (by change ¬ i.val < k; omega)
        have hre1' : tr.reinit ⟨k, Nat.lt_succ_of_le hk.le⟩ ≤ r₁ := by
          simpa [reinit', hnot] using hre1
        by_cases hr2R : r₂ = R
        · subst hr2R; simp only [lvlIdx', hr1R, ↓reduceIte, hk, ↓reduceDIte]
          rw [(hH'le k hk hki).2.1, ← tr.hLvlEnd k hk]
          exact tr.hLvlMono k hk r₁ R hre1' h12 (le_refl R)
        · simp only [lvlIdx', hr1R, hr2R, ↓reduceIte]
          exact tr.hLvlMono k hk r₁ r₂ hre1' h12 hr2
    hLvlSucc := fun k hk => by
      have hk1 : k + 1 < cfg.P.d := hk
      have hk0 : k < cfg.P.d := Nat.lt_of_succ_lt hk
      by_cases hk1i : k + 1 ≤ i.val
      · have hki : k ≤ i.val := by omega
        rw [(hH'le k hk0 hki).2.1, (hH'le (k + 1) hk1 hk1i).2.1]
        refine ⟨(tr.hLvlSucc k hk).1, fun r hre hr => ?_⟩
        rw [hRoundEq] at hr
        by_cases hrR : r = R
        · subst hrR; simp only [lvlIdx', ↓reduceIte, hk1, hk0, ↓reduceDIte]
          rw [(hH'le k hk0 hki).2.1, (hH'le (k + 1) hk1 hk1i).2.1]
          exact Nat.add_sub_of_le (tr.hLvlSucc k hk).1
        · have hn : ¬ i < ⟨k + 1, Nat.lt_succ_of_le hk1.le⟩ :=
            fun hlt => absurd (Fin.lt_def.mp hlt) (by change ¬ i.val < k + 1; omega)
          have hre' : tr.reinit ⟨k + 1, Nat.lt_succ_of_le hk1.le⟩ ≤ r := by
            simpa [reinit', hn] using hre
          simp only [lvlIdx', hrR, ↓reduceIte]
          exact (tr.hLvlSucc k hk).2 r hre' hr
      · have hik1 : i < ⟨k + 1, Nat.lt_succ_of_le hk1.le⟩ := Fin.lt_def.mpr (by change i.val < k + 1; omega)
        have hik_nat : i.val < k + 1 := by omega
        rw [hH'gt (k + 1) hk1 hik_nat]
        refine ⟨Nat.zero_le _, fun r hre hr => ?_⟩
        rw [hRoundEq] at hr
        have hreR : r = R := by
          simp only [reinit', hik1, ↓reduceIte] at hre
          omega
        subst hreR; simp [lvlIdx', hk1, hk0, hH'gt (k + 1) hk1 hik_nat]
    hLvlSnap := fun k hk r hre hr => by
      rw [hRoundEq] at hr
      by_cases hrR : r = R
      · subst hrR
        simp only [lvlIdx', ↓reduceIte, hk]
        refine ⟨(H' k hk).hEndG.symm, fun j _ => ?_, fun _ j _ => ?_⟩
        · change ch'.toTreeChain.lsfs k j =
            cfg.T.lsfs (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
              (H' k hk).D (H' k hk).restarts (H' k hk).len) j
          rw [← (H' k hk).hRun]; rfl
        · change ch'.toTreeChain.emb k j =
            cfg.T.emb (cfg.T.runAfterRestarts cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
              (H' k hk).D (H' k hk).restarts (H' k hk).len) j
          rw [← (H' k hk).hRun]; rfl
      · have hki : k ≤ i.val := by
          by_contra hgt
          have hik : i < ⟨k, Nat.lt_succ_of_le hk.le⟩ := Fin.lt_def.mpr (by change i.val < k; omega)
          simp only [reinit', hik, ↓reduceIte] at hre; omega
        have hn : ¬ i < ⟨k, Nat.lt_succ_of_le hk.le⟩ :=
          fun hlt => absurd (Fin.lt_def.mp hlt) (by change ¬ i.val < k; omega)
        have hre' : tr.reinit ⟨k, Nat.lt_succ_of_le hk.le⟩ ≤ r := by simpa [reinit', hn] using hre
        have hs := tr.hLvlSnap k hk r hre' hr
        simp only [hrR, ↓reduceIte, lvlIdx']
        by_cases hlt : k < i.val
        · have hData := hH'le k hk hki
          rw [hData.1, (hData.2.2 hlt).1]
          refine ⟨hs.1, hs.2.1, fun hre1 j hj => ?_⟩
          have hik1 : ¬ i < ⟨k + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)⟩ :=
            fun hx => absurd (Fin.lt_def.mp hx) (by change ¬ i.val < k + 1; omega)
          exact hs.2.2 (by simpa [reinit', hik1] using hre1) j hj
        · have hkeq : k = i.val := by omega
          have hData := hH'le k hk hki
          have hSpecK := hVNH.hT cfg.P.k (H' k hk).len (levelM cfg.TP cfg.P k) cfg.N₀
            (H' k hk).D (H' k hk).restarts cfg.P.hk (H' k hk).hG0 (H' k hk).hD (H' k hk).hLen
            (H' k hk).hℓPos (H' k hk).hInitMBound (H' k hk).hInitNBound (H' k hk).hRestartsLt
            (by rw [(H' k hk).hUpd]; exact (H' k hk).hThresh)
          have hSpecOld := hVNH.hT cfg.P.k (tr.H k hk).len (levelM cfg.TP cfg.P k) cfg.N₀
            (tr.H k hk).D (tr.H k hk).restarts cfg.P.hk (tr.H k hk).hG0 (tr.H k hk).hD
            (tr.H k hk).hLen (tr.H k hk).hℓPos (tr.H k hk).hInitMBound (tr.H k hk).hInitNBound
            (tr.H k hk).hRestartsLt (by rw [(tr.H k hk).hUpd]; exact (tr.H k hk).hThresh)
          have hIdxLe : tr.lvlIdx r k ≤ (tr.H k hk).len := by
            rw [← tr.hLvlEnd k hk]; exact tr.hLvlMono k hk r R hre' hr (le_refl R)
          refine ⟨by rw [hData.1]; exact hs.1, fun j hj => ?_, fun hre1 => ?_⟩
          · rw [hs.2.1 j hj]
            rw [SparseCoreRestartTool.lsfs_runAfterRestarts_eq hSpecK.2.2.1 _
                (by rw [hData.2.1]; exact hIdxLe) j hj,
              SparseCoreRestartTool.lsfs_runAfterRestarts_eq hSpecOld.2.2.1 _ hIdxLe j hj]
            have hRunEq : cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  (H' k hk).D (H' k hk).restarts (tr.lvlIdx r k) =
                cfg.T.runAfterUpdate cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀
                  (tr.H k hk).D (tr.H k hk).restarts (tr.lvlIdx r k) := by
              rw [hData.1]
              refine cfg.T.runAfterUpdate_congr_lt cfg.P.k (levelM cfg.TP cfg.P k) cfg.N₀ (tr.lvlIdx r k) rfl rfl rfl
                (fun _ _ _ => ⟨rfl, rfl, rfl⟩) fun s hsLt => ?_
              have hs_lt_len : s < (tr.H k hk).len := lt_of_lt_of_le hsLt hIdxLe
              exact hH'restLt k hk hki s hs_lt_len
            rw [hRunEq]
          · exfalso
            have hik1 : i < ⟨k + 1, Nat.lt_succ_of_le (Nat.succ_le_of_lt hk)⟩ :=
              Fin.lt_def.mpr (by change i.val < k + 1; omega)
            simp only [reinit', hik1, ↓reduceIte] at hre1
            exact hrR (by omega)
    hLvlCore := fun k hk => by
      have hk1 : k + 1 < cfg.P.d := hk
      have hk0 : k < cfg.P.d := Nat.lt_of_succ_lt hk
      by_cases hk1i : k + 1 ≤ i.val
      · have hki : k ≤ i.val := by omega
        have hki_lt : k < i.val := by omega
        have hD0 := hH'le k hk0 hki
        have hD1 := hH'le (k + 1) hk1 hk1i
        have hC := tr.hLvlCore k hk
        dsimp only at hC ⊢
        rw [hD0.1, hD0.2.1, (hD0.2.2 hki_lt).1, (hD0.2.2 hki_lt).2,
          hD1.1, hD1.2.1, hBr'lt k hki_lt]
        exact hC
      · have hik_nat : i.val < k + 1 := by omega
        have h0 := hH'gt (k + 1) hk1 hik_nat
        have hEndG0 : (H' (k + 1) hk1).D.G 0 = ch'.G (k + 1) := by
          simpa [h0] using (H' (k + 1) hk1).hEndG
        have hEndℓ0 : ∀ e ∈ (ch'.G (k + 1)).E,
            (H' (k + 1) hk1).D.ℓ 0 e = ch'.toTreeChain.chainLen ch'.ℓ (k + 1) e := fun e he' => by
          simpa [h0] using (H' (k + 1) hk1).hEndℓ e he'
        dsimp only
        rw [h0, Nat.sub_zero]
        have hs0_le := (H' k hk0).hs₀
        have hoff_zero : (H' k hk0).s₀ + ((H' k hk0).len - (H' k hk0).s₀ + 0) = (H' k hk0).len := by omega
        refine ⟨hs0_le, fun δ hδ => ?_, fun δ h1 h2 => by omega, fun δ hδ e he => ?_⟩
        · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
          rw [hEndG0, hSucc' k hk1 hik_nat]
          simp only [SparseCoreRestartTool.coreInstanceFrom, hoff_zero]
          rw [← (H' k hk0).hRun]
        · have hδ0 : δ = 0 := Nat.le_zero.mp hδ; subst hδ0
          have he' : e ∈ (ch'.G (k + 1)).E := by rwa [← hEndG0]
          rw [hEndℓ0 e he']
          have he_k : e ∈ (ch'.G k).E := by
            have hB' := level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
              hV.hTP hVNH.hT hV.hγM₀ hV.hγk hInv'
            have hLSF := (hB' k hk0.le).2.2.2.2 hk0 (ch'.bran k) (hInv'.hBran k hk0)
            rw [hSucc' k hk1 hik_nat] at he'
            exact (Finset.mem_sdiff.mp (hLSF.2.1.2.1 he')).1
          simp only [SparseCoreRestartTool.coreInstanceFrom, hoff_zero]
          rw [← (H' k hk0).hRun]
          have hAct : ch'.toTreeChain.activeLSF k = cfg.T.lsfs (ch'.scState k) (ch'.bran k) := by
            simp [TreeChain.activeLSF, ChainState.toTreeChain, hk0]
          change coreLen (ch'.toTreeChain.activeLSF k) (ch'.toTreeChain.chainLen ch'.ℓ k) e =
            coreLen (cfg.T.lsfs (ch'.scState k) (ch'.bran k)) ((H' k hk0).D.ℓ (H' k hk0).len) e
          rw [hAct]
          unfold coreLen
          rw [(H' k hk0).hEndℓ e he_k]
    updRound := tr.updRound,
    hUpdBound := fun τ hτ => by
      rw [(hH'le 0 cfg.P.hd (Nat.zero_le _)).2.1] at hτ
      have := tr.hUpdBound τ hτ
      have hnot0 : ¬ i < ⟨0, Nat.succ_pos _⟩ := fun hlt => Nat.not_lt_zero i.val (Fin.lt_def.mp hlt)
      refine ⟨by simpa [reinit', hnot0] using this.1, by rw [hRoundEq]; exact this.2⟩
    hUpdMono := fun τ₁ τ₂ h12 h2 => by
      rw [(hH'le 0 cfg.P.hd (Nat.zero_le _)).2.1] at h2
      exact tr.hUpdMono τ₁ τ₂ h12 h2
    hUpdBand := fun r hre hr => by
      rw [hRoundEq] at hr
      have hnot0 : ¬ i < ⟨0, Nat.succ_pos _⟩ := fun hlt => Nat.not_lt_zero i.val (Fin.lt_def.mp hlt)
      have hre0 : tr.reinit ⟨0, Nat.succ_pos _⟩ ≤ r := by simpa [reinit', hnot0] using hre
      by_cases hrR : r = R
      · subst hrR
        have hb := tr.hUpdBand R hre0 (le_refl R)
        have hLE0 : tr.lvlIdx R 0 = (tr.H 0 cfg.P.hd).len := tr.hLvlEnd 0 cfg.P.hd
        simp only [lvlIdx', cfg.P.hd, ↓reduceDIte, (hH'le 0 cfg.P.hd (Nat.zero_le _)).2.1]
        simpa [hLE0] using hb
      · simp only [lvlIdx', hrR, ↓reduceIte, (hH'le 0 cfg.P.hd (Nat.zero_le _)).2.1]
        exact tr.hUpdBand r hre0 hr
    hLvl0Match := fun τ hτ => by
      rw [(hH'le 0 cfg.P.hd (Nat.zero_le _)).2.1] at hτ
      rw [(hH'le 0 cfg.P.hd (Nat.zero_le _)).1]
      have hm := tr.hLvl0Match τ hτ
      have hG0_R : (tr.snapC R).G 0 = ch'.toTreeChain.G 0 := by
        change (tr.snapC R).G 0 = ch'.G 0; rw [hSnapEndC_R]; exact hch'G0.symm
      by_cases hur : tr.updRound τ = R
      · simp only [hur, ↓reduceIte] at hm ⊢
        rw [← hG0_R]; exact hm
      · simp only [hur, ↓reduceIte]; exact hm
    hLvl0NoIns := fun s τ hs hτ r_s r_τ hrs1 hrs2 hrs3 hrt1 hrt2 hrt3 hst_r e he => by
      rw [hRoundEq] at hrs2 hrt2
      simp only [(hH'le 0 cfg.P.hd (Nat.zero_le _)).1, (hH'le 0 cfg.P.hd (Nat.zero_le _)).2] at *
      exact tr.hLvl0NoIns s τ hs hτ r_s r_τ hrs1 hrs2 hrs3 hrt1 hrt2 hrt3 hst_r e he }⟩

/-- **Shift step**: when `algorithm2_loop` fails ratio `-κ α` and picks `i := findEligibleLevel ...`,
prove `shiftCount i + 1 ≤ gameShiftBound ...` MUST hold and advance `Alg2HiddenTrace` across one
`algorithm1_shift` step. -/
theorem alg2HiddenTrace_shift {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ}
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBudget : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k)
    (hn : (D.G t).n ≤ cfg.N₀)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (hNotGood : ¬ (st.extG.inner st.extg (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) /
        st.extG.lnorm st.extℓ (liftEdgeFn st.extG st.extToInt (algorithm1_findCycle st.chain).1) ≤
      -(alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ * cfg.α)))
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
    Nonempty (Alg2HiddenTrace cfg D c_ext w_ext t st') :=
  alg2HiddenTrace_shiftAt cfg.N₀ hV tr hInv hBudget hFresh hExtG hExtℓ hExtg hℓ hg hBranD hn
    (fun hIc hFc => chainInv_last_le_N0 hV.toNoHidden hn hIc hFc) hHS hNotGood i hElig

end MinCostFlow.Chain