module

public import MinCostFlow.Chain.UpdatePreLoop
public import MinCostFlow.Chain.LevelConnected

/-!
# Lemma 6.5 (`lemma_6_5`): Hidden-strategy correspondence and loop termination

This file completes Section 6 (`jtree.tex` lines 745–797, pages 29–30) by proving:
1. `alg2HiddenTrace_loop`: well-founded recursion on `shiftRemainingBudget` showing that under
   `HiddenStableAt`, `algorithm2_loop` always returns `some Δ` with ratio `≤ -κ * α` and a valid
   updated `Alg2HiddenTrace`.
2. `alg2HiddenTrace_update`: full step preservation across `algorithm2_update`.
3. **`theorem lemma_6_5`**: full hidden-strategy correspondence (`Game.ValidPlayPrefix` +
   `Game.FollowsStrategyPrefix`), non-failure (`¬ minRatioFailFailedBefore`), and `-κ * α`
   quality guarantee for `algorithm2_ds`.
-/

@[expose] public section

namespace MinCostFlow.Chain

/-- Well-founded trace and quality proof for `algorithm2_loopWith` under `HiddenStableAt` on `0 .. t`,
parameterized by last-level vertex cap `nLast`. -/
lemma alg2HiddenTrace_loopAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.Valid)
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
    let res := algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
      st.extG st.extToInt st.extg st.extℓ st.chain st.branD st.passes lctOps
    ∃ Δ, res.2.2.2.2 = some Δ ∧
      (D.G t).inner (D.g t) Δ / (D.G t).lnorm (D.ℓ t) Δ ≤
        -(alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast * cfg.α) ∧
      Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast) cfg D c_ext w_ext t
        { st with chain := res.1, branD := res.2.1, passes := res.2.2.1 }) := by
  let fc := algorithm1_findCycle st.chain
  let Δ_ext := liftEdgeFn st.extG st.extToInt fc.1
  let κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast
  by_cases hGood : st.extG.inner st.extg Δ_ext / st.extG.lnorm st.extℓ Δ_ext ≤ -(κ * cfg.α)
  · have hUnfold : algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
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
    have hShift := alg2HiddenTrace_shiftAt nLast hV tr hInv hBud hFresh hExtG hExtℓ hExtg hℓ hg hBranD
      hn hLastBound hHS hGood i hElig
    dsimp only at hShift
    rcases hShift with ⟨hCap, ⟨tr'⟩⟩
    have hVNH := hV.toNoHidden
    have hShP := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
      hV.hTP hV.hLP hVNH.hT hV.hL hV.hγM₀ hV.hγk hInv hBud i.val (Nat.le_of_lt_succ i.isLt)
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
    have hStepEq : algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
        st.extG st.extToInt st.extg st.extℓ st.chain st.branD st.passes lctOps =
        algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
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
    have ih := alg2HiddenTrace_loopAt nLast hV hm hn hLastBound hHS st' lctOps' tr' hInv' hBud' hFresh'
      hExtG hExtℓ hExtg (by simpa [st', ch', hℓ'] using hℓ) (by simpa [st', ch', hg'] using hg)
      hBranD'
    simpa [hStepEq, st'] using ih
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step st.chain i hCap

/-- Well-founded trace and quality proof for `algorithm2_loop` under `HiddenStableAt` on `0 .. t`.
By `Game.passes_zero_lt` + `findEligibleLevel_none_iff` and `alg2HiddenTrace_shift`,
`algorithm2_loop` never fails (`optΔ ≠ none`), returns ratio `≤ -κ * α`, and preserves
`Alg2HiddenTrace`. -/
lemma alg2HiddenTrace_loop {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ}
    (hm : (D.G t).m ≤ cfg.P.M₀) (hn : (D.G t).n ≤ cfg.N₀)
    (hHS : ∀ s ≤ t, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    (st : Alg2State cfg) (lctOps : ℕ)
    (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t) (hExtg : st.extg = D.g t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hg : st.chain.g = fun e' => st.extg (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k) :
    let res := algorithm2_loop cfg st.extG st.extToInt st.extg st.extℓ
      st.chain st.branD st.passes lctOps
    ∃ Δ, res.2.2.2.2 = some Δ ∧
      (D.G t).inner (D.g t) Δ / (D.G t).lnorm (D.ℓ t) Δ ≤
        -(alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ * cfg.α) ∧
      Nonempty (Alg2HiddenTrace cfg D c_ext w_ext t
        { st with chain := res.1, branD := res.2.1, passes := res.2.2.1 }) :=
  alg2HiddenTrace_loopAt cfg.N₀ hV hm hn (fun hIc hFc => chainInv_last_le_N0 hV.toNoHidden hn hIc hFc)
    hHS st lctOps tr hInv hBud hFresh hExtG hExtℓ hExtg hℓ hg hBranD

/-- One full `algorithm2_updateWith` step preserves `Alg2HiddenTraceAt`, never fails (`optΔ = some Δ`),
and produces a direction `Δ` with ratio `≤ -κ * α`, parameterized by `nLast`. -/
lemma alg2HiddenTrace_updateAt (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
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
    let res := algorithm2_updateWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
      st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) η
    ∃ Δ, res.2 = some Δ ∧
      (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤
        -(alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast * cfg.α) ∧
      Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
        cfg D c_ext w_ext (t + 1) res.1) := by
  have hVNH := hV.toNoHidden
  have hPre := alg2HiddenTrace_update_preLoopAt nLast hVNH hHist ht1 hisUpd hm1 hn1 hLastBound
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
    hBatch_int hNR_int hG0'Valid hG0'm hG0'n hℓ_intPos hℓ_intStable
  dsimp only at hU
  rcases hU with ⟨hInv1, hBud1, _, _, _, _⟩
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
  let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let stPre : Alg2State cfg :=
    { st with
      chain := ch1, branD := bp1.1, passes := bp1.2,
      extG := extG', extToInt := e2i', intToExt := i2e', nextFresh := nf',
      extℓ := D.ℓ (t + 1), extg := D.g (t + 1),
      largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
      updateCount := st.updateCount + 1 }
  have hFresh1 : FreshInv stPre.extG (stPre.chain.G 0) stPre.extToInt stPre.intToExt stPre.nextFresh := by
    dsimp only [stPre, extG', e2i', i2e', nf', ch1]; rw [hG0ℓ1.1]; exact hFresh'
  have hBranD1 : stPre.branD < cfg.P.k := by
    dsimp only [stPre, bp1]
    cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount <;> [exact hBranD; exact cfg.P.hk]
  let trPre' : Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext (t + 1) stPre :=
    alg2HiddenTrace_congr trPre rfl rfl rfl rfl rfl rfl
  obtain ⟨Δ, hSome, hRatio, ⟨trEnd⟩⟩ := alg2HiddenTrace_loopAt nLast hV hm1 hn1 hLastBound hHS stPre
    (st.lctUpdateOps + (D.U (t + 1)).length) trPre' hInv1 hBud1 hFresh1 hExtEq rfl rfl
    (by simpa [stPre] using hG0ℓ1.2.1) (by simpa [stPre] using hG0ℓ1.2.2.1) hBranD1
  have hLoopUnfold : algorithm2_updateWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
      st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) η =
      (let res := algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
          extG' e2i' (D.g (t + 1)) (D.ℓ (t + 1))
          ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
       let inc := fun e => if e ∈ extG'.E then -(η / extG'.inner (D.g (t + 1)) Δ) * Δ e else 0
       ({ chain := res.1
          branD := res.2.1
          passes := res.2.2.1
          extG := extG'
          extToInt := e2i'
          intToExt := i2e'
          nextFresh := nf'
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
    change (match (algorithm2_loopWith cfg (alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast)
        extG' e2i' (D.g (t + 1)) (D.ℓ (t + 1))
        ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)).2.2.2.2 with
      | none => _ | some _ => _) = _
    rw [hSome]
    rfl
  refine ⟨Δ, ?_, hRatio, ?_⟩
  · rw [hLoopUnfold]
  · refine ⟨alg2HiddenTrace_congr trEnd ?_ ?_ ?_ ?_ ?_ ?_⟩ <;> · rw [hLoopUnfold]

/-- One full `algorithm2_update` step preserves `Alg2HiddenTrace`, never fails (`optΔ = some Δ`),
and produces a direction `Δ` with ratio `≤ -κ * α`. -/
lemma alg2HiddenTrace_update {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    {c_ext w_ext : ℕ → ℕ → ℝ} {t : ℕ} (ht1 : t + 1 ≤ T) (hisUpd : isUpdate (t + 1) = true)
    (hm1 : (D.G (t + 1)).m ≤ cfg.P.M₀) (hn1 : (D.G (t + 1)).n ≤ cfg.N₀)
    (hHS : ∀ s ≤ t + 1, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext s)
    {st : Alg2State cfg} (tr : Alg2HiddenTrace cfg D c_ext w_ext t st)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc)
    (hFresh : FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh)
    (hExtG : st.extG = D.G t) (hExtℓ : st.extℓ = D.ℓ t)
    (hℓ : st.chain.ℓ = fun e' => st.extℓ (st.intToExt e'))
    (hBranD : st.branD < cfg.P.k) (η : ℝ) :
    let res := algorithm2_update cfg st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) η
    ∃ Δ, res.2 = some Δ ∧
      (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤
        -(alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ * cfg.α) ∧
      Nonempty (Alg2HiddenTrace cfg D c_ext w_ext (t + 1) res.1) :=
  alg2HiddenTrace_updateAt cfg.N₀ hV hHist ht1 hisUpd hm1 hn1
    (fun hIc hFc => chainInv_last_le_N0 hV.toNoHidden hn1 hIc hFc) hHS tr hInv hBud hFresh hExtG hExtℓ hℓ
    hBranD η

/-- Parameterized **Lemma 6.5**: same hidden-strategy correspondence and `-κ * α` quality
guarantee for `algorithm2_dsWith cfg κ` at last-level vertex cap `nLast`. -/
theorem lemma_6_5_at (nLast : ℕ) {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hLastBound : ∀ t ≤ T, ∀ {ch e2i i2e nf}, ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      FreshInv (D.G t) (ch.G 0) e2i i2e nf → (ch.G cfg.P.d).n ≤ nLast)
    {c_ext w_ext : ℕ → ℕ → ℝ}
    (hHS : ∀ t ≤ T, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext t) :
    let κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast
    let ds := algorithm2_dsWith cfg κ
    (∀ t ≤ T, Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext t (minRatioFailState ds D η isUpdate t))) ∧
    (∀ t ≤ T, ¬ minRatioFailFailedBefore ds D η isUpdate t) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir ds D η isUpdate t = some Δ ∧
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤ -(κ * cfg.α)) := by
  dsimp only
  set κ := alg2KappaAt cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ nLast
  set ds := algorithm2_dsWith cfg κ
  have hVNH := hV.toNoHidden
  have hUncond := algorithm2_uncond_preserves_with (cfg := cfg) (η := η) κ hVNH hHist hmBound hnBound
  have hExtLG := alg2UncondInv_extℓ_extg_with (cfg := cfg) (η := η) κ hHist
  have hTraces : ∀ t ≤ T, Nonempty (Alg2HiddenTraceAt (alg2SigmaTotAt cfg.TP cfg.LP cfg.P cfg.N₀ nLast)
      cfg D c_ext w_ext t (minRatioFailState ds D η isUpdate t)) := by
    intro t
    induction t with
    | zero =>
      intro ht0
      simpa [minRatioFailState, ds, algorithm2_dsWith] using
        alg2HiddenTrace_initAt nLast hVNH hHist (hmBound 0 ht0) (hnBound 0 ht0)
          (hLastBound 0 ht0) (hHS 0 ht0)
    | succ t ih =>
      intro ht1
      have ht_le : t ≤ T := Nat.le_of_succ_le ht1
      obtain ⟨tr⟩ := ih ht_le
      obtain ⟨hExtℓ, _⟩ := hExtLG t ht_le
      have hUI := hUncond.1 t ht_le
      rcases hUI with ⟨hInv, hBud, _, _, hFresh, hExtG, _, hChℓ, _, _, _, _, hBranD, _, _⟩
      by_cases hupd : isUpdate (t + 1) = true
      · obtain ⟨_, _, _, ⟨tr1⟩⟩ := alg2HiddenTrace_updateAt nLast hV hHist ht1 hupd
          (hmBound (t + 1) ht1) (hnBound (t + 1) ht1) (hLastBound (t + 1) ht1)
          (fun s hs => hHS s (le_trans hs ht1)) tr hInv hBud hFresh hExtG hExtℓ hChℓ hBranD (η (t + 1))
        simpa [minRatioFailState, hupd, ds, algorithm2_dsWith] using ⟨tr1⟩
      · have hfalse : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
        have hChℓ_D : (minRatioFailState ds D η isUpdate t).chain.ℓ =
            fun e' => D.ℓ t ((minRatioFailState ds D η isUpdate t).intToExt e') := by
          rw [hChℓ]; ext e'; rw [hExtℓ]
        simpa [minRatioFailState, hupd, ds, algorithm2_dsWith] using
          alg2HiddenTrace_detectAt nLast hVNH hHist ht1 hfalse (hmBound (t + 1) ht1)
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
    obtain ⟨Δ, hSome, hRatio, _⟩ := alg2HiddenTrace_updateAt nLast hV hHist ht1 hupd
      (hmBound (t + 1) ht1) (hnBound (t + 1) ht1) (hLastBound (t + 1) ht1)
      (fun s hs => hHS s (le_trans hs ht1)) tr hInv hBud hFresh hExtG hExtℓ hChℓ hBranD (η (t + 1))
    have hCirc := hUncond.2.2.1 t ht1 hupd Δ hSome
    exact ⟨Δ, hSome, hCirc, hRatio⟩
  refine ⟨hTraces, fun t ht ⟨s, hs, hus, hnone⟩ => ?_, hOpt⟩
  obtain ⟨Δ, hSome, _, _⟩ := hOpt s (by omega) hus
  rw [hSome] at hnone
  simp at hnone

/-- **Lemma 6.5** (`jtree.tex` lines 745–797, pages 29–30, with the sign of `-κ * α` corrected):
under `cfg.Valid`, `MinRatioHistoryValid D isUpdate T`, `(D.G t).m ≤ cfg.P.M₀`,
`(D.G t).n ≤ cfg.N₀`, and `D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext t` for all `t ≤ T`:
1. Every stage `t ≤ T` maintains a full `Alg2HiddenTrace` (valid Game play following Algorithm 3
   plus synchronized per-level histories).
2. `algorithm2_ds` never fails (`¬ minRatioFailFailedBefore`).
3. Every update step `t + 1 ≤ T` returns `some Δ` satisfying `IsCirculation` and ratio
   `≤ -(alg2Kappa ... * cfg.α)`. -/
theorem lemma_6_5 {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    {c_ext w_ext : ℕ → ℕ → ℝ}
    (hHS : ∀ t ≤ T, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext t) :
    (∀ t ≤ T, Nonempty (Alg2HiddenTrace cfg D c_ext w_ext t
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate t))) ∧
    (∀ t ≤ T, ¬ minRatioFailFailedBefore (algorithm2_ds cfg) D η isUpdate t) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir (algorithm2_ds cfg) D η isUpdate t = some Δ ∧
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤
          -(alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ * cfg.α)) :=
  lemma_6_5_at cfg.N₀ hV hHist hmBound hnBound
    (fun t ht _ _ _ _ hIc hFc => chainInv_last_le_N0 hV.toNoHidden (hnBound t ht) hIc hFc) hHS

/-- Connectedness-based **Lemma 6.5** for `algorithm2_dsOwn`: when every external graph `D.G t`
is connected, the last-level vertex cap is `levelM cfg.TP cfg.P cfg.P.d + 1` and `algorithm2_dsOwn`
never fails and achieves ratio `≤ -(alg2KappaOwn ... * cfg.α)`. -/
theorem lemma_6_5_own {cfg : Alg2Config} (hV : cfg.Valid)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hConn : ∀ t ≤ T, ∀ u ∈ (D.G t).V, ∀ v ∈ (D.G t).V, (D.G t).Connected u v)
    {c_ext w_ext : ℕ → ℕ → ℝ}
    (hHS : ∀ t ≤ T, D.HiddenStableAt cfg.α cfg.Ψ c_ext w_ext t) :
    (∀ t ≤ T, Nonempty (Alg2HiddenTraceAt (alg2SigmaTotOwn cfg.TP cfg.LP cfg.P cfg.N₀)
      cfg D c_ext w_ext t (minRatioFailState (algorithm2_dsOwn cfg) D η isUpdate t))) ∧
    (∀ t ≤ T, ¬ minRatioFailFailedBefore (algorithm2_dsOwn cfg) D η isUpdate t) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir (algorithm2_dsOwn cfg) D η isUpdate t = some Δ ∧
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.G (t + 1)).inner (D.g (t + 1)) Δ / (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤
          -(alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ * cfg.α)) :=
  lemma_6_5_at (levelM cfg.TP cfg.P cfg.P.d + 1) hV hHist hmBound hnBound
    (fun t ht _ _ _ _ hIc hFc =>
      (chainInv_comp_bound_all_levels hV.hTP hV.toNoHidden.hT hV.hγM₀ hV.hγk hIc
        (hFc.connected (hConn t ht))).2)
    hHS

end MinCostFlow.Chain
