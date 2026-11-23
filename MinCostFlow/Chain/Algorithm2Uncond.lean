module

public import MinCostFlow.Chain.Algorithm2

/-!
# Unconditional invariant preservation for Algorithm 2 (without `HiddenStable`)

This file proves `algorithm2_loop_preserves` and `algorithm2_uncond_preserves`, establishing that
on **every** `MinRatioHistoryValid` instance (even without `HiddenStable`, using only
`SparseCoreRestartTool.IsSpecRestartNoHidden`), `algorithm2_ds` maintains `ChainInv`, `ChainBudgetInvWith`,
`FreshInv`, exact `Query` and `Detect` outputs, `IsCirculation` for returned vectors,
LCT operation counts, and the unconditional `Game.lemma_7_3_prefix` upper bound
`s_i ≤ gameShiftBound cfg.P Ψ_game r_i i` across all steps `t ≤ T`.
-/

@[expose] public section

namespace MinCostFlow.Chain

private lemma minRatioFailLast_le (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    minRatioFailLast A D η isUpdate t e ≤ t := by
  induction t with
  | zero => exact le_refl 0
  | succ k ihk =>
    unfold minRatioFailLast
    split_ifs <;> omega

/-- Structural property of `updateLoop`: either `rebuildCount` is unchanged, or a unique level
`iStar < P.d` has its rebuild count incremented by `1`. -/
lemma updateLoop_rebuildCount_cases (T : SparseCoreRestartTool) (L : LastLevelTool)
    (TP : SparseCoreParams) (P : ChainParams) (N₀ : ℕ) (ℓ' g' : ℕ → ℝ) :
    ∀ (rem idx : ℕ) (st : ChainState T P) (curG : MGraph) (curU : List Update) (curEnc : ℕ),
      idx + rem = P.d →
      let st' := (updateLoop T L TP P N₀ ℓ' g' rem idx st curG curU curEnc).1
      st'.rebuildCount = st.rebuildCount ∨
      ∃ iStar, idx ≤ iStar ∧ iStar < P.d ∧
        st'.rebuildCount = fun j => if j = iStar then st.rebuildCount iStar + 1 else st.rebuildCount j := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEnc _
    left
    dsimp only [updateLoop]
    split_ifs <;> rfl
  | succ rem' ih =>
    intro idx st curG curU curEnc hsum
    dsimp only [updateLoop]
    split_ifs with hTh
    · right
      refine ⟨idx, le_refl _, by omega, ?_⟩
      dsimp only [algorithm1_rebuild]
      split_ifs
      · rfl
      · omega
    · dsimp only
      rcases ih (idx + 1) _ _ _ _ (by omega) with heq | ⟨iStar, h1, h2, h3⟩
      · exact Or.inl heq
      · exact Or.inr ⟨iStar, Nat.le_of_succ_le h1, h2, h3⟩

lemma firstRebuiltLevel_eq_of_eq {d : ℕ} (reb : ℕ → ℕ) :
    firstRebuiltLevel d reb reb = none := by
  unfold firstRebuiltLevel
  rw [List.find?_eq_none]
  intro j _
  simp

lemma firstRebuiltLevel_eq_of_inc {d : ℕ} {iStar : ℕ} (hi : iStar < d) (reb : ℕ → ℕ) :
    firstRebuiltLevel d reb (fun j => if j = iStar then reb iStar + 1 else reb j) = some iStar := by
  unfold firstRebuiltLevel
  rw [List.find?_eq_some_iff_append]
  refine ⟨by simp, List.range iStar, List.range' (iStar + 1) (d - (iStar + 1)), ?_, ?_⟩
  · have hsplit : d = iStar + (d - iStar) := (Nat.add_sub_cancel' hi.le).symm
    conv_lhs => rw [hsplit]
    rw [List.range_add]
    have hd1 : d - iStar = 1 + (d - (iStar + 1)) := by omega
    rw [hd1, List.range_add, List.map_append, List.range_one, List.range'_eq_map_range]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, add_zero]
    congr 2
    rw [List.map_map]
    refine List.map_congr_left fun x _ => by simp [Function.comp_apply]; omega
  · intro b hb
    have hlt : b < iStar := List.mem_range.mp hb
    simp [Nat.ne_of_lt hlt]

lemma algorithm2_loopWith_preserves {cfg : Alg2Config} (hV : cfg.ValidNoHidden) (κ : ℝ)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) (overflow : ℝ)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow)
    (hShBound : ∀ i : Fin (cfg.P.d + 1),
      (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val)
    (hBranD : branD < cfg.P.k)
    (hFresh : FreshInv extG (ch.G 0) e2i i2e nf) :
    let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    let ch' := res.1
    let branD' := res.2.1
    let lctOps' := res.2.2.2.1
    let optΔ := res.2.2.2.2
    ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' ∧
    ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch' overflow ∧
    ch'.G 0 = ch.G 0 ∧
    ch'.ℓ = ch.ℓ ∧
    ch'.g = ch.g ∧
    ch'.rebuildCount = ch.rebuildCount ∧
    (∀ i : Fin (cfg.P.d + 1), ch.shiftCount i.val ≤ ch'.shiftCount i.val) ∧
    (∀ i : Fin (cfg.P.d + 1),
      (ch'.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch'.rebuildCount i.val) ∧
    branD' < cfg.P.k ∧
    lctOps' ≤ lctOps + 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), (ch'.shiftCount j - ch.shiftCount j)) ∧
    (∀ Δ, optΔ = some Δ → extG.IsCirculation Δ) := by
  have hvp0 : IsValidPair (ch.G 0) ch.ℓ (fun _ => 0) (fun _ => 0) :=
    ⟨fun _ _ => by simp [MGraph.demand], fun _ _ => by simp⟩
  have hFC := findCycle_spec_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hσ_mwu_mono hV.hTP hV.hLP hV.hT hV.hMWU hV.hEmb hV.hγM₀ hV.hγk hInv hvp0
  set fc := algorithm1_findCycle ch
  set offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  have hoff_le : offTree ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 := by
    have h1 : (offTree : ℝ) ≤ 1 + cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hFC.2.2.1
    have h2 : (offTree : ℝ) ≤ ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 : ℕ) : ℝ) := by
      push_cast
      linarith [Nat.le_ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2))]
    exact_mod_cast h2
  have hstepOps : 2 * (offTree + 1) ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) := by omega
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Δ_ext := liftEdgeFn extG e2i fc.1
  set lctOps' := lctOps + 2 * (offTree + 1)
  have hfc_eq : (walkEdges (algorithm1_findCycle ch).2.1 \ ch.toTreeChain.chainTree.E).card = offTree := rfl
  rw [algorithm2_loopWith]
  dsimp only
  by_cases hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α)
  · rw [dite_eq_left_iff.mpr fun h => absurd hGood h]
    refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_, ?_⟩
    · dsimp only
      simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
      rw [hfc_eq]
      omega
    · dsimp only
      rintro Δ hΔ
      injection hΔ with hΔ
      rw [← hΔ]
      exact hFresh.isCirculation_lift hFC.1
  · rw [dite_eq_right_iff.mpr fun h => absurd h hGood]
    cases hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none =>
      refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_,
        fun _ h => by simp at h⟩
      dsimp only
      simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
      rw [hfc_eq]
      omega
    | some i =>
      dsimp only
      by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val
      · rw [dite_eq_left_iff.mpr fun h => absurd hCap h]
        have hi_le : i.val ≤ cfg.P.d := Nat.lt_succ_iff.mp i.isLt
        have hS := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
          hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hBud i.val hi_le
        dsimp only at hS
        rcases hS with ⟨hInv1, hBud1, hG01, hℓ1, hg1, hSh1, hReb1, _, _⟩
        set ch1 := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        have hShBound1 : ∀ j : Fin (cfg.P.d + 1),
            (ch1.shiftCount j.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g ch1.rebuildCount j.val := by
          intro j
          rw [hSh1, hReb1]
          dsimp only
          by_cases hji : j.val = i.val
          · rw [ite_eq_left_iff.mpr fun h => absurd hji h, hji]
            push_cast
            exact hCap
          · rw [ite_eq_right_iff.mpr fun h => absurd h hji]
            exact hShBound j
        have hBranD1 : (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k) < cfg.P.k := by
          by_cases hi : i.val < cfg.P.d
          · rw [ite_eq_left_iff.mpr fun h => absurd hi h]; exact cfg.P.hk
          · rw [ite_eq_right_iff.mpr fun h => absurd h hi]; exact Nat.mod_lt _ cfg.P.hk
        have hFresh1 : FreshInv extG (ch1.G 0) e2i i2e nf := by
          rw [hG01]; exact hFresh
        have ih := algorithm2_loopWith_preserves hV κ extG e2i i2e nf g' ℓ' ch1
          (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
          (fun j => if i < j then 0
            else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j)
          lctOps' overflow hInv1 hBud1 hShBound1 hBranD1 hFresh1
        dsimp only at ih
        rcases ih with ⟨hInvF, hBudF, hG0F, hℓF, hgF, hRebF, hShLeF, hShBF, hBranDF, hOpsF, hCircF⟩
        dsimp only [lctOps'] at hInvF hBudF hG0F hℓF hgF hRebF hShLeF hShBF hBranDF hOpsF hCircF
        have hle_sh : ∀ j, ch.shiftCount j ≤ ch1.shiftCount j := fun j => by
          rw [hSh1]; dsimp only
          by_cases hji : j = i.val
          · rw [ite_eq_left_iff.mpr fun h => absurd hji h, hji]; omega
          · rw [ite_eq_right_iff.mpr fun h => absurd h hji]
        refine ⟨hInvF, hBudF, hG0F.trans hG01, hℓF.trans hℓ1, hgF.trans hg1, hRebF.trans hReb1,
          fun j => le_trans (hle_sh j.val) (hShLeF j),
          hShBF, hBranDF, ?_, hCircF⟩
        have hsum_tot :
            ∑ j ∈ Finset.range (cfg.P.d + 1),
              ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                (fun j => if i < j then 0
                  else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                  else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch.shiftCount j) =
            1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
              ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                (fun j => if i < j then 0
                  else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                  else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j) := by
          set chF := (algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
            (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
            (fun j => if i < j then 0
              else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
              else passes j) (lctOps + 2 * (offTree + 1))).1
          have hadd : ∀ j ∈ Finset.range (cfg.P.d + 1),
              chF.shiftCount j - ch.shiftCount j =
                (chF.shiftCount j - ch1.shiftCount j) + (ch1.shiftCount j - ch.shiftCount j) := by
            intro j hj
            have hle1 : ch.shiftCount j ≤ ch1.shiftCount j := hle_sh j
            have hle2 : ch1.shiftCount j ≤ chF.shiftCount j :=
              hShLeF ⟨j, Finset.mem_range.mp hj⟩
            omega
          rw [Finset.sum_congr rfl hadd, Finset.sum_add_distrib]
          have hs1 : ∑ j ∈ Finset.range (cfg.P.d + 1), (ch1.shiftCount j - ch.shiftCount j) = 1 := by
            have hmem : i.val ∈ Finset.range (cfg.P.d + 1) := Finset.mem_range.mpr i.isLt
            have hterm : ∀ j ∈ Finset.range (cfg.P.d + 1),
                (ch1.shiftCount j - ch.shiftCount j) = if j = i.val then 1 else 0 := by
              intro j _; rw [hSh1]; dsimp only
              by_cases hji : j = i.val
              · rw [ite_eq_left_iff.mpr fun h => absurd hji h, ite_eq_left_iff.mpr fun h => absurd hji h, hji]
                simp
              · rw [ite_eq_right_iff.mpr fun h => absurd h hji, ite_eq_right_iff.mpr fun h => absurd h hji]
                simp
            rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' _ _ (fun _ => 1),
              ite_eq_left_iff.mpr fun h => absurd hmem h]
          omega
        have hmult :
            2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
              (1 + (1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
                ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                  (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                  (fun j => if i < j then 0
                    else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                    else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j))) =
            2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) +
              2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
                (1 + ∑ j ∈ Finset.range (cfg.P.d + 1),
                  ((algorithm2_loopWith cfg κ extG e2i g' ℓ' ch1
                    (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
                    (fun j => if i < j then 0
                      else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
                      else passes j) (lctOps + 2 * (offTree + 1))).1.shiftCount j - ch1.shiftCount j)) := by
          ring
        rw [hsum_tot, hmult]
        linarith [hOpsF, hstepOps]
      · rw [dite_eq_right_iff.mpr fun h => absurd h hCap]
        refine ⟨hInv, hBud, rfl, rfl, rfl, rfl, fun _ => le_refl _, hShBound, hBranD, ?_,
          fun _ h => by simp at h⟩
        dsimp only
        simp only [Nat.sub_self, Finset.sum_const_zero, add_zero, mul_one]
        rw [hfc_eq]
        omega
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

lemma algorithm2_loop_preserves {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) (overflow : ℝ)
    (hInv : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch)
    (hBud : ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow)
    (hShBound : ∀ i : Fin (cfg.P.d + 1),
      (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val)
    (hBranD : branD < cfg.P.k)
    (hFresh : FreshInv extG (ch.G 0) e2i i2e nf) :
    let res := algorithm2_loop cfg extG e2i g' ℓ' ch branD passes lctOps
    let ch' := res.1
    let branD' := res.2.1
    let lctOps' := res.2.2.2.1
    let optΔ := res.2.2.2.2
    ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch' ∧
    ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch' overflow ∧
    ch'.G 0 = ch.G 0 ∧
    ch'.ℓ = ch.ℓ ∧
    ch'.g = ch.g ∧
    ch'.rebuildCount = ch.rebuildCount ∧
    (∀ i : Fin (cfg.P.d + 1), ch.shiftCount i.val ≤ ch'.shiftCount i.val) ∧
    (∀ i : Fin (cfg.P.d + 1),
      (ch'.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch'.rebuildCount i.val) ∧
    branD' < cfg.P.k ∧
    lctOps' ≤ lctOps + 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      (1 + ∑ j ∈ Finset.range (cfg.P.d + 1), (ch'.shiftCount j - ch.shiftCount j)) ∧
    (∀ Δ, optΔ = some Δ → extG.IsCirculation Δ) :=
  algorithm2_loopWith_preserves hV (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i i2e nf g' ℓ' ch branD passes lctOps overflow hInv hBud hShBound hBranD hFresh

private lemma algorithm2_updateWith_eq_of_loop {cfg : Alg2Config} (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
    let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let lp := algorithm2_loopWith cfg κ tb.1 tb.2.1 g' ℓ' ch1 bp1.1 bp1.2 (st.lctUpdateOps + U_ext.length)
    (lp.2.2.2.2 = none →
      algorithm2_updateWith cfg κ st U_ext g' ℓ' η =
        ({ st with
           chain := lp.1
           branD := lp.2.1
           passes := lp.2.2.1
           extG := tb.1
           extToInt := tb.2.1
           intToExt := tb.2.2.1
           nextFresh := tb.2.2.2.1
           extℓ := ℓ'
           extg := g'
           lctUpdateOps := lp.2.2.2.1
           largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2
           updateCount := st.updateCount + 1 }, none)) ∧
    (∀ Δ, lp.2.2.2.2 = some Δ →
      algorithm2_updateWith cfg κ st U_ext g' ℓ' η =
        (let inc : ℕ → ℝ := fun e => if e ∈ tb.1.E then -(η / tb.1.inner g' Δ) * Δ e else 0
         { chain := lp.1
           branD := lp.2.1
           passes := lp.2.2.1
           extG := tb.1
           extToInt := tb.2.1
           intToExt := tb.2.2.1
           nextFresh := tb.2.2.2.1
           extℓ := ℓ'
           extg := g'
           flow := fun e => st.flow e + inc e
           detectAccum := fun e => st.detectAccum e + |inc e|
           lctUpdateOps := lp.2.2.2.1
           lctDetectOps := st.lctDetectOps
           largeBatchEnc := st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2
           updateCount := st.updateCount + 1 }, some Δ)) := by
  refine ⟨?_, ?_⟩
  · intro hnone
    dsimp only [algorithm2_updateWith] at hnone ⊢
    split
    · rfl
    · next opt heq => exact absurd (hnone.symm.trans heq) (by simp)
  · intro Δ hsome
    dsimp only [algorithm2_updateWith] at hsome ⊢
    split
    · next heq => exact absurd (hsome.symm.trans heq) (by simp)
    · next Δ' heq =>
      have hΔ : Δ = Δ' := Option.some.inj (hsome.symm.trans heq)
      subst hΔ
      rfl

/-- Full unconditional invariant maintained by `algorithm2_dsWith cfg κ` on any valid history
up to stage `t`, independent of `HiddenStable`. -/
def Alg2UncondInvWith (κ : ℝ) (cfg : Alg2Config) (D : DynamicInstance) (η : ℕ → ℝ)
    (isUpdate : ℕ → Bool) (t : ℕ) (st : Alg2State cfg) : Prop :=
  ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st.chain ∧
  ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st.chain st.largeBatchEnc ∧
  0 ≤ st.largeBatchEnc ∧
  st.largeBatchEnc ≤ (Finset.Icc 1 t).sum (fun s =>
    if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) ∧
  FreshInv st.extG (st.chain.G 0) st.extToInt st.intToExt st.nextFresh ∧
  st.extG = D.G t ∧
  (∀ e ∈ (D.G t).E, st.extℓ e = D.ℓ t e ∧ st.extg e = D.g t e) ∧
  st.chain.ℓ = (fun e' => st.extℓ (st.intToExt e')) ∧
  st.chain.g = (fun e' => st.extg (st.intToExt e')) ∧
  (∀ e, st.flow e = minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate t e) ∧
  (∀ e, st.detectAccum e =
    ∑ s ∈ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t,
      |minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate s e|) ∧
  (∀ i : Fin (cfg.P.d + 1),
    (st.chain.shiftCount i.val : ℝ) ≤
      gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain.rebuildCount i.val) ∧
  st.branD < cfg.P.k ∧
  st.lctUpdateOps ≤ cfg.P.M₀ +
    (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) +
    2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
      ((Finset.range t).sum (fun s => if isUpdate (s + 1) then 1 else 0) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), st.chain.shiftCount i) ∧
  st.lctDetectOps ≤ (Finset.Icc 1 t).sum (fun s =>
    if isUpdate s = false then
      ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card + 1
    else 0)

/-- Full unconditional invariant maintained by `algorithm2_ds` on any valid history up to stage
`t`, independent of `HiddenStable`. -/
abbrev Alg2UncondInv (cfg : Alg2Config) (D : DynamicInstance) (η : ℕ → ℝ)
    (isUpdate : ℕ → Bool) (t : ℕ) (st : Alg2State cfg) : Prop :=
  Alg2UncondInvWith (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) cfg D η isUpdate t st

/-- `algorithm2_dsWith cfg κ` unconditionally preserves `Alg2UncondInvWith` across all steps
`t ≤ T` and satisfies the `Query`, `Detect`, and `IsCirculation` requirements. -/
theorem algorithm2_uncond_preserves_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    (∀ t ≤ T, Alg2UncondInvWith κ cfg D η isUpdate t
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t)) ∧
    (∀ t ≤ T, ∀ e ∈ (D.G t).E,
      (algorithm2_dsWith cfg κ).query (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t) e =
        minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∀ Δ, minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = some Δ →
        (D.G (t + 1)).IsCirculation Δ) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t)).1 =
        minRatioFailDetectSet (algorithm2_dsWith cfg κ) D η isUpdate cfg.ε t) := by
  have hMain : ∀ t ≤ T, Alg2UncondInvWith κ cfg D η isUpdate t
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t) := by
    intro t
    induction t with
    | zero =>
      intro ht
      have hG0 := (hHist.2.1 0 ht).1
      have hℓ0 := (hHist.2.1 0 ht).2
      have hm0 := hmBound 0 ht
      have hn0 := hnBound 0 ht
      have hInit := initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
        hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk (D.G 0) (D.ℓ 0) (D.g 0) hG0 hm0 hn0 hℓ0
      rcases hInit with ⟨hInv0, hBud0, hG0eq, hℓ0eq, hg0eq, hSh0, _, _, _, _⟩
      set ch0 := (algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0)).1
      have hFr0 : FreshInv (D.G 0) (ch0.G 0) id id ((D.G 0).E.sup id + 1) :=
        hG0eq.symm ▸ freshInv_init (D.G 0)
      have hℓ0_ch : ch0.ℓ = fun e' => D.ℓ 0 (id e') := hℓ0eq
      have hg0_ch : ch0.g = fun e' => D.g 0 (id e') := hg0eq
      have hShSum0 : ∑ x ∈ Finset.range (cfg.P.d + 1), ch0.shiftCount x = 0 :=
        Finset.sum_eq_zero fun x _ => hSh0 x
      have hU0_le : (D.G 0).m ≤ cfg.P.M₀ +
          (Finset.Icc 1 0).sum (fun s => if isUpdate s then (D.U s).length else 0) +
          2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
            ((Finset.range 0).sum (fun s => if isUpdate (s + 1) then 1 else 0) +
              ∑ x ∈ Finset.range (cfg.P.d + 1), ch0.shiftCount x) := by
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, hShSum0]
        simp; exact hm0
      dsimp only [minRatioFailState, algorithm2_dsWith, algorithm2_init]
      refine ⟨hInv0, hBud0.toWith, le_rfl, ?_, hFr0, rfl, fun _ _ => ⟨rfl, rfl⟩,
        hℓ0_ch, hg0_ch, fun e => ?_, fun e => ?_, fun i => ?_, cfg.P.hk, hU0_le, ?_⟩
      · rw [Finset.Icc_eq_empty (by omega)]; simp
      · simp [minRatioFailFlow, minRatioFailIncrement]
      · simp [minRatioFailLast, minRatioFailIncrement]
      · dsimp only
        have hsh_i : (ch0.shiftCount i.val : ℝ) = 0 := by exact_mod_cast hSh0 i.val
        change (ch0.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch0.rebuildCount i.val
        rw [hsh_i]
        unfold gameShiftBound
        have hΨ_pos : 0 ≤ alg2PsiGame cfg.Ψ cfg.P.M₀ :=
          le_trans zero_le_one (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀)
        have hΨg : 0 ≤ 10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ) := by positivity
        have h1 : 0 ≤ (10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (i.val + 1) := by positivity
        have h2 : 0 ≤ ∑ i' ∈ Finset.range (i.val + 1),
            ((algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ (D.G 0) (D.ℓ 0) (D.g 0)).1.rebuildCount i' : ℝ) *
              (10 * alg2PsiGame cfg.Ψ cfg.P.M₀ * (cfg.P.k : ℝ)) ^ (i.val + 1 - i') :=
          Finset.sum_nonneg fun _ _ => by positivity
        simpa using add_nonneg h1 h2
      · rw [Finset.Icc_eq_empty (by omega)]; simp
    | succ t ih =>
      intro ht
      have ht_le : t ≤ T := Nat.le_of_succ_le ht
      have hI := ih ht_le
      rcases hI with ⟨hInv, hBud, hLB0, hLBSum, hFresh, hExtG, hExtLG, hChℓ, hChg,
        hFlow, hDet, hShB, hBranD, hUpdOps, hDetOps⟩
      set st : Alg2State cfg := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
      by_cases hupd : isUpdate (t + 1) = true
      · have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
        have hG1Valid := (hHist.2.1 (t + 1) ht).1
        have hℓ1Pos := (hHist.2.1 (t + 1) ht).2
        have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
        have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
          st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
        dsimp only at hTB
        set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
        set extG' := tb.1
        set e2i' := tb.2.1
        set i2e' := tb.2.2.1
        set nf' := tb.2.2.2.1
        set U_int := tb.2.2.2.2
        rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, hLenEq, _, _, hi2e_old, _, hYesInsExt⟩
        have hG1eq_batch : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)) := hD.2
        have hExtEq : extG' = D.G (t + 1) := by
          rw [hExtG', hExtG, ← hG1eq_batch]
        have hG0'Valid : ((st.chain.G 0).applyBatch U_int).IsValid :=
          (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
        have hG0'm : ((st.chain.G 0).applyBatch U_int).m ≤ cfg.P.M₀ := by
          rw [hFresh'.m_eq, hExtEq]; exact hmBound (t + 1) ht
        have hG0'n : ((st.chain.G 0).applyBatch U_int).n ≤ cfg.N₀ := by
          rw [hFresh'.n_eq, hExtEq]; exact hnBound (t + 1) ht
        set ℓ_int : ℕ → ℝ := fun e' => D.ℓ (t + 1) (i2e' e')
        set g_int : ℕ → ℝ := fun e' => D.g (t + 1) (i2e' e')
        have hℓ_intPos : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, 0 < ℓ_int e' :=
          fun e' he' => hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
        have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch U_int).E, e' ∈ (st.chain.G 0).E →
            (∀ u' ∈ U_int, ¬ u'.Inserts e') → ℓ_int e' = st.chain.ℓ e' := by
          intro e' he' he'0 _
          have he'_lt : e' < st.nextFresh := hFresh.hLtFresh e' he'0
          have hi2e_eq : i2e' e' = st.intToExt e' := hi2e_old e' he'_lt
          obtain ⟨_, he_pre⟩ := hFresh.hRight e' he'0
          obtain ⟨_, he_ext'⟩ := hFresh'.hRight e' he'
          have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by rw [← hExtEq, ← hi2e_eq]; exact he_ext'
          have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
            intro s hs1 hs2 u hu hIns
            have hseq : s = t + 1 := by omega
            subst hseq
            have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
            have he2i'_eq : e2i' (st.intToExt e') = e' := by
              rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
            omega
          have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht _ he_ext1 hNoIns_ext).2
          dsimp only [ℓ_int]
          rw [hi2e_eq, hℓ_same, hChℓ]
          dsimp only [Nat.add_sub_cancel]
          exact (hExtLG _ (hExtG ▸ he_pre)).1.symm
        have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
          hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud U_int g_int ℓ_int
          hBatch_int hNR_int hG0'Valid hG0'm hG0'n hℓ_intPos hℓ_intStable
        dsimp only at hU
        rcases hU with ⟨hInv1, hBud1, _, hSh1, hReb1, _⟩
        set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
        have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int
        have hFresh1 : FreshInv extG' (ch1.G 0) e2i' i2e' nf' := by rw [hG0ℓ1.1]; exact hFresh'
        have hShB1 : ∀ i : Fin (cfg.P.d + 1),
            (ch1.shiftCount i.val : ℝ) ≤
              gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1.rebuildCount i.val := fun i =>
          le_trans (by rw [← hSh1 i.val]; exact hShB i)
            (gameShiftBound_mono_reb (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) hReb1 i.val)
        set bp1 :=
          match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
          | none => (st.branD, st.passes)
          | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
        have hBranD1_lt : bp1.1 < cfg.P.k := by
          dsimp only [bp1]
          cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount <;> [exact hBranD; exact cfg.P.hk]
        have hLP := algorithm2_loopWith_preserves hV κ extG' e2i' i2e' nf' (D.g (t + 1)) (D.ℓ (t + 1))
          ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
          (st.largeBatchEnc + largeBatchEncCap cfg.P U_int)
          hInv1 hBud1 hShB1 hBranD1_lt hFresh1
        dsimp only at hLP
        rcases hLP with ⟨hInvF, hBudF, hG0F, hℓF, hgF, _, hShLeF, hShBF, hBranDF, hOpsF, _⟩
        set lp := algorithm2_loopWith cfg κ extG' e2i' (D.g (t + 1)) (D.ℓ (t + 1)) ch1 bp1.1 bp1.2
          (st.lctUpdateOps + (D.U (t + 1)).length)
        have hUpdEq := algorithm2_updateWith_eq_of_loop κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))
        dsimp only at hUpdEq
        have hStNext : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
            (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1 := by
          rw [minRatioFailState, ite_eq_left_iff.mpr fun h => absurd hupd h]; rfl
        have hOptDir : minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = lp.2.2.2.2 := by
          dsimp only [minRatioFailOptDir]
          change (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).2 =
            lp.2.2.2.2
          cases hlp : lp.2.2.2.2 with
          | none => rw [hUpdEq.1 hlp]
          | some Δ => rw [hUpdEq.2 Δ hlp]
        have hℓ_eq_ch : lp.1.ℓ = fun e' => D.ℓ (t + 1) (i2e' e') := hℓF.trans hG0ℓ1.2.1
        have hg_eq_ch : lp.1.g = fun e' => D.g (t + 1) (i2e' e') := hgF.trans hG0ℓ1.2.2.1
        have hLB_sum : st.largeBatchEnc + largeBatchEncCap cfg.P U_int ≤
            (Finset.Icc 1 (t + 1)).sum fun s =>
              if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0 := by
          rw [Finset.sum_Icc_succ_top (Nat.succ_pos t), ite_eq_left_iff.mpr fun h => absurd hupd h]
          have hCapEq : largeBatchEncCap cfg.P U_int = largeBatchEncCap cfg.P (D.U (t + 1)) := by
            simp [largeBatchEncCap, hLenEq]
          rw [hCapEq]
          exact add_le_add hLBSum le_rfl
        have hSh_sum_le :
            ∑ j ∈ Finset.range (cfg.P.d + 1), (lp.1.shiftCount j - st.chain.shiftCount j) +
              ∑ i ∈ Finset.range (cfg.P.d + 1), st.chain.shiftCount i =
            ∑ i ∈ Finset.range (cfg.P.d + 1), lp.1.shiftCount i := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hle := le_trans (le_of_eq (hSh1 j)) (hShLeF ⟨j, Finset.mem_range.mp hj⟩)
          dsimp only at hle
          omega
        have hUpdOps' :
            lp.2.2.2.1 ≤ cfg.P.M₀ +
              (Finset.Icc 1 (t + 1)).sum (fun s => if isUpdate s then (D.U s).length else 0) +
              2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 2) *
                ((Finset.range (t + 1)).sum (fun s => if isUpdate (s + 1) then 1 else 0) +
                  ∑ i ∈ Finset.range (cfg.P.d + 1), lp.1.shiftCount i) := by
          have hUsum : (Finset.Icc 1 (t + 1)).sum (fun s => if isUpdate s then (D.U s).length else 0) =
              (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) +
                (D.U (t + 1)).length := by
            rw [Finset.sum_Icc_succ_top (Nat.succ_pos t), ite_eq_left_iff.mpr fun h => absurd hupd h]
          have hTsum : (Finset.range (t + 1)).sum (fun s => if isUpdate (s + 1) then 1 else 0) =
              (Finset.range t).sum (fun s => if isUpdate (s + 1) then 1 else 0) + 1 := by
            rw [Finset.sum_range_succ, ite_eq_left_iff.mpr fun h => absurd hupd h]
          have h1eq : ∑ j ∈ Finset.range (cfg.P.d + 1), (lp.1.shiftCount j - ch1.shiftCount j) =
              ∑ j ∈ Finset.range (cfg.P.d + 1), (lp.1.shiftCount j - st.chain.shiftCount j) :=
            Finset.sum_congr rfl fun j _ => by rw [← hSh1 j]
          rw [h1eq] at hOpsF
          rw [hUsum, hTsum, ← hSh_sum_le]
          nlinarith [hOpsF, hUpdOps]
        have hDetOps' :
            st.lctDetectOps ≤ (Finset.Icc 1 (t + 1)).sum (fun s =>
              if isUpdate s = false then
                ((algorithm2_dsWith cfg κ).detect
                  (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card + 1
              else 0) := by
          rw [Finset.sum_Icc_succ_top (Nat.succ_pos t)]
          have hfl : ¬ isUpdate (t + 1) = false := by simp [hupd]
          rw [ite_eq_right_iff.mpr fun h => absurd h hfl, add_zero]
          exact hDetOps
        have hFlow_succ : ∀ Δopt e,
            minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = Δopt →
            (match Δopt with
            | none => st.flow e
            | some Δ => st.flow e + (if e ∈ extG'.E then -(η (t + 1) / extG'.inner (D.g (t + 1)) Δ) * Δ e else 0)) =
              minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e := by
          intro Δopt e hEq
          rw [minRatioFailFlow, Finset.sum_range_succ]
          change _ = minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate t e +
            minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e
          rw [← hFlow e]
          cases hDopt : Δopt with
          | none =>
            rw [hDopt] at hEq
            simp [minRatioFailIncrement, hEq]
          | some Δ =>
            rw [hDopt] at hEq
            simp [minRatioFailIncrement, hEq, hupd, hExtEq]
        have hDet_succ : ∀ Δopt e,
            minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = Δopt →
            (match Δopt with
            | none => st.detectAccum e
            | some Δ => st.detectAccum e + |if e ∈ extG'.E then -(η (t + 1) / extG'.inner (D.g (t + 1)) Δ) * Δ e else 0|) =
              ∑ s ∈ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e) (t + 1),
                |minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate s e| := by
          intro Δopt e hEq
          have hLastEq : minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e =
              minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e := by
            simp [minRatioFailLast, hupd]
          rw [hLastEq]
          have hle_last := minRatioFailLast_le (algorithm2_dsWith cfg κ) D η isUpdate t e
          have hIoc_split : Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) (t + 1) =
              insert (t + 1) (Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t) := by
            ext s; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
          have hnotmem : t + 1 ∉ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t := by
            simp only [Finset.mem_Ioc]; omega
          rw [hIoc_split, Finset.sum_insert hnotmem, ← hDet e]
          conv_rhs => rw [add_comm]
          cases hDopt : Δopt with
          | none =>
            rw [hDopt] at hEq
            simp [minRatioFailIncrement, hEq]
          | some Δ =>
            rw [hDopt] at hEq
            simp [minRatioFailIncrement, hEq, hupd, hExtEq]
        rw [hStNext]
        cases hLpOpt : lp.2.2.2.2 with
        | none =>
          rw [hUpdEq.1 hLpOpt]
          exact ⟨hInvF, hBudF, add_nonneg hLB0 (largeBatchEncCap_nonneg _ _), hLB_sum,
            by rw [hG0F]; exact hFresh1, hExtEq, fun _ _ => ⟨rfl, rfl⟩,
            hℓ_eq_ch, hg_eq_ch,
            fun e => hFlow_succ none e (hOptDir.trans hLpOpt),
            fun e => hDet_succ none e (hOptDir.trans hLpOpt),
            hShBF, hBranDF, hUpdOps', hDetOps'⟩
        | some Δ =>
          rw [hUpdEq.2 Δ hLpOpt]
          exact ⟨hInvF, hBudF, add_nonneg hLB0 (largeBatchEncCap_nonneg _ _), hLB_sum,
            by rw [hG0F]; exact hFresh1, hExtEq, fun _ _ => ⟨rfl, rfl⟩,
            hℓ_eq_ch, hg_eq_ch,
            fun e => hFlow_succ (some Δ) e (hOptDir.trans hLpOpt),
            fun e => hDet_succ (some Δ) e (hOptDir.trans hLpOpt),
            hShBF, hBranDF, hUpdOps', hDetOps'⟩
      · have hdet : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
        have hUnch := hHist.2.2.1 (t + 1) (Nat.succ_pos t) ht hdet
        have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
        have hG1eq : D.G (t + 1) = D.G t := by rw [hD.2, hUnch.1]; rfl
        have hStNext : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
            ((algorithm2_dsWith cfg κ).detect st).2 := by
          simp [minRatioFailState, hdet, st]
        rw [hStNext]
        dsimp [algorithm2_dsWith, algorithm2_detect]
        set S := st.extG.E.filter fun e => cfg.ε ≤ st.extℓ e * st.detectAccum e
        refine ⟨hInv, hBud, hLB0, ?_, hFresh, by rw [hExtG, hG1eq], fun e he => ?_,
          hChℓ, hChg, fun e => ?_, fun e => ?_, hShB, hBranD, ?_, ?_⟩
        · dsimp only
          have hsum : (Finset.Icc 1 (t + 1)).sum (fun s => if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) =
              (Finset.Icc 1 t).sum (fun s => if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) := by
            rw [Finset.sum_Icc_succ_top (Nat.succ_pos t), hdet]; simp
          rw [hsum]; exact hLBSum
        · rw [hG1eq] at he; rw [hUnch.2.2, hUnch.2.1]; exact hExtLG e he
        · dsimp only
          have hinc0 : minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e = 0 := by
            simp only [minRatioFailIncrement, hdet, Bool.false_eq_true, false_and]
            cases minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t <;> simp
          rw [hFlow e]
          simp [minRatioFailFlow, Finset.sum_range_succ, hinc0]
        · dsimp only
          have hinc0 : minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e = 0 := by
            simp only [minRatioFailIncrement, hdet, Bool.false_eq_true, false_and]
            cases minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t <;> simp
          have hmem_iff : e ∈ S ↔ isUpdate (t + 1) = false ∧
              e ∈ ((algorithm2_dsWith cfg κ).detect st).1 := by
            simp [hdet, algorithm2_dsWith, algorithm2_detect, S]
          by_cases heS : e ∈ S
          · rw [ite_eq_left_iff.mpr fun h => absurd heS h]
            have hlast : minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e = t + 1 := by
              rw [minRatioFailLast, ite_eq_left_iff.mpr fun h => absurd (hmem_iff.mp heS) h]
            rw [hlast]; simp
          · rw [ite_eq_right_iff.mpr fun h => absurd h heS]
            have hlast : minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e =
                minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e := by
              rw [minRatioFailLast, ite_eq_right_iff.mpr fun h => absurd h (hmem_iff.not.mp heS)]
            rw [hlast]
            have hle_last := minRatioFailLast_le (algorithm2_dsWith cfg κ) D η isUpdate t e
            have hIoc_split : Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) (t + 1) =
                insert (t + 1) (Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t) := by
              ext s; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
            have hnotmem : t + 1 ∉ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t := by
              simp only [Finset.mem_Ioc]; omega
            rw [hIoc_split, Finset.sum_insert hnotmem, hinc0, abs_zero, zero_add, hDet e]
        · have h1 : (Finset.Icc 1 (t + 1)).sum (fun s => if isUpdate s then (D.U s).length else 0) =
              (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) := by
            rw [Finset.sum_Icc_one_succ, hdet]; simp
          have h2 : (Finset.range (t + 1)).sum (fun s => if isUpdate (s + 1) then 1 else 0) =
              (Finset.range t).sum (fun s => if isUpdate (s + 1) then 1 else 0) := by
            rw [Finset.sum_range_succ, hdet]; simp
          rw [h1, h2]; exact hUpdOps
        · rw [Finset.sum_Icc_one_succ, hdet]
          change st.lctDetectOps + S.card + 1 ≤
            (Finset.Icc 1 t).sum (fun s => if isUpdate s = false then
              ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card + 1 else 0) +
            (((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t)).1.card + 1)
          have hSc : ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t)).1.card =
              S.card := rfl
          omega
  refine ⟨hMain, ?_, ?_, ?_⟩
  · intro t ht e _
    exact (hMain t ht).2.2.2.2.2.2.2.2.2.1 e
  · intro t ht1 hupd Δ hΔ
    have hI := hMain t (Nat.le_of_succ_le ht1)
    rcases hI with ⟨hInv, hBud, _, _, hFresh, hExtG, hExtLG, hChℓ, _, _, _, hShB, hBranD, _, _⟩
    have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht1
    have hG1Valid := (hHist.2.1 (t + 1) ht1).1
    have hℓ1Pos := (hHist.2.1 (t + 1) ht1).2
    set st : Alg2State cfg := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    have hBatch_ext : st.extG.BatchIsValid (D.U (t + 1)) := by rw [hExtG]; exact hD.1
    have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
      st.extToInt st.intToExt st.nextFresh hFresh hBatch_ext
    dsimp only at hTB
    set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
    rcases hTB with ⟨hExtG', hFresh', hBatch_int, hNR_int, _, _, _, hi2e_old, _, hYesInsExt⟩
    have hG1eq_batch : D.G (t + 1) = (D.G t).applyBatch (D.U (t + 1)) := hD.2
    have hExtEq : tb.1 = D.G (t + 1) := by
      dsimp only [tb]; rw [hExtG', hExtG, ← hG1eq_batch]
    have hG0'Valid : ((st.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
      (hFresh'.isValid_iff).mpr (hExtEq ▸ hG1Valid)
    have hG0'm : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
      rw [hFresh'.m_eq, hExtEq]; exact hmBound (t + 1) ht1
    have hG0'n : ((st.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
      rw [hFresh'.n_eq, hExtEq]; exact hnBound (t + 1) ht1
    have hℓ_intPos : ∀ e' ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, 0 < D.ℓ (t + 1) (tb.2.2.1 e') :=
      fun e' he' => hℓ1Pos _ (hExtEq ▸ (hFresh'.hRight e' he').2)
    have hℓ_intStable : ∀ e' ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, e' ∈ (st.chain.G 0).E →
        (∀ u' ∈ tb.2.2.2.2, ¬ u'.Inserts e') → D.ℓ (t + 1) (tb.2.2.1 e') = st.chain.ℓ e' := by
      intro e' he' he'0 _
      have he'_lt : e' < st.nextFresh := hFresh.hLtFresh e' he'0
      have hi2e_eq : tb.2.2.1 e' = st.intToExt e' := hi2e_old e' he'_lt
      obtain ⟨_, he_pre⟩ := hFresh.hRight e' he'0
      obtain ⟨_, he_ext'⟩ := hFresh'.hRight e' he'
      have he_ext1 : st.intToExt e' ∈ (D.G (t + 1)).E := by rw [← hExtEq, ← hi2e_eq]; exact he_ext'
      have hNoIns_ext : D.NotInsertedBetween (st.intToExt e') t (t + 1) := by
        intro s hs1 hs2 u hu hIns
        have hseq : s = t + 1 := by omega
        subst hseq
        have hge := hYesInsExt (st.intToExt e') (hExtEq ▸ he_ext1) ⟨u, hu, hIns⟩
        have he2i'_eq : tb.2.1 (st.intToExt e') = e' := by
          rw [← hi2e_eq]; exact (hFresh'.hRight e' he').1
        dsimp only [tb] at hge he2i'_eq
        rw [he2i'_eq] at hge
        omega
      have hℓ_same := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 _ he_ext1 hNoIns_ext).2
      rw [hi2e_eq, hℓ_same, hChℓ]
      dsimp only [Nat.add_sub_cancel]
      exact (hExtLG _ (hExtG ▸ he_pre)).1.symm
    have hU := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
      hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud tb.2.2.2.2
      (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
      hBatch_int hNR_int hG0'Valid hG0'm hG0'n hℓ_intPos hℓ_intStable
    dsimp only at hU
    rcases hU with ⟨hInv1, hBud1, _, hSh1, hReb1, _⟩
    set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1
    have hG0ℓ1 := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
    have hFresh1 : FreshInv tb.1 (ch1.G 0) tb.2.1 tb.2.2.1 tb.2.2.2.1 := by
      rw [hG0ℓ1.1]; exact hFresh'
    have hShB1 : ∀ i : Fin (cfg.P.d + 1),
        (ch1.shiftCount i.val : ℝ) ≤
          gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1.rebuildCount i.val := fun i =>
      le_trans (by rw [← hSh1 i.val]; exact hShB i)
        (gameShiftBound_mono_reb (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) hReb1 i.val)
    set bp1 :=
      match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    have hBranD1_lt : bp1.1 < cfg.P.k := by
      dsimp only [bp1]
      cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount <;> [exact hBranD; exact cfg.P.hk]
    have hLP := algorithm2_loopWith_preserves hV κ tb.1 tb.2.1 tb.2.2.1 tb.2.2.2.1
      (D.g (t + 1)) (D.ℓ (t + 1)) ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
      (st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2)
      hInv1 hBud1 hShB1 hBranD1_lt hFresh1
    dsimp only at hLP
    have hCirc := hLP.2.2.2.2.2.2.2.2.2.2
    set lp2 := algorithm2_loopWith cfg κ tb.1 tb.2.1 (D.g (t + 1)) (D.ℓ (t + 1)) ch1 bp1.1 bp1.2
      (st.lctUpdateOps + (D.U (t + 1)).length)
    have hUpdEq2 := algorithm2_updateWith_eq_of_loop κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))
    dsimp only at hUpdEq2
    have hOpt : lp2.2.2.2.2 = some Δ := by
      dsimp only [minRatioFailOptDir] at hΔ
      change (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).2 =
        some Δ at hΔ
      cases hl : lp2.2.2.2.2 with
      | none =>
        rw [hUpdEq2.1 hl] at hΔ
        simp at hΔ
      | some x =>
        rw [hUpdEq2.2 x hl] at hΔ
        simp only [Option.some.injEq] at hΔ
        rw [← hΔ]
    rw [← hExtEq]
    exact hCirc Δ hOpt
  · intro t ht1 hdet
    have hI := hMain t (Nat.le_of_succ_le ht1)
    rcases hI with ⟨_, _, _, _, _, hExtG, hExtLG, _, _, _, hDet, _, _, _, _⟩
    have hUnch := hHist.2.2.1 (t + 1) (Nat.succ_pos t) ht1 hdet
    have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht1
    have hG1eq : D.G (t + 1) = D.G t := by rw [hD.2, hUnch.1]; rfl
    set st : Alg2State cfg := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    change st.extG.E.filter (fun e => cfg.ε ≤ st.extℓ e * st.detectAccum e) =
      minRatioFailDetectSet (algorithm2_dsWith cfg κ) D η isUpdate cfg.ε t
    unfold minRatioFailDetectSet
    rw [hExtG, ← hG1eq, hUnch.2.2]
    refine Finset.filter_congr fun e he => ?_
    have he' : e ∈ (D.G t).E := hG1eq ▸ he
    have hle_last := minRatioFailLast_le (algorithm2_dsWith cfg κ) D η isUpdate t e
    have hIoc_split : Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) (t + 1) =
        insert (t + 1) (Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t) := by
      ext s; simp only [Finset.mem_Ioc, Finset.mem_insert]; omega
    have hnotmem : t + 1 ∉ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) t := by
      simp only [Finset.mem_Ioc]; omega
    have hinc0 : minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) e = 0 := by
      simp only [minRatioFailIncrement, hdet, Bool.false_eq_true, false_and]
      cases minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t <;> simp
    rw [hIoc_split, Finset.sum_insert hnotmem, hinc0, abs_zero, zero_add, ← hDet e,
      (hExtLG e he').1]
    simp only [Nat.add_sub_cancel]

/-- Unconditional preservation of all Algorithm 2 invariants for `algorithm2_ds` across steps `0..T`. -/
theorem algorithm2_uncond_preserves {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    (∀ t ≤ T, Alg2UncondInv cfg D η isUpdate t
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate t)) ∧
    (∀ t ≤ T, ∀ e ∈ (D.G t).E,
      (algorithm2_ds cfg).query (minRatioFailState (algorithm2_ds cfg) D η isUpdate t) e =
        minRatioFailFlow (algorithm2_ds cfg) D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∀ Δ, minRatioFailOptDir (algorithm2_ds cfg) D η isUpdate t = some Δ →
        (D.G (t + 1)).IsCirculation Δ) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      ((algorithm2_ds cfg).detect (minRatioFailState (algorithm2_ds cfg) D η isUpdate t)).1 =
        minRatioFailDetectSet (algorithm2_ds cfg) D η isUpdate cfg.ε t) :=
  algorithm2_uncond_preserves_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hmBound hnBound

lemma algorithm2_loopWith_rec_props (cfg : Alg2Config) (κ : ℝ)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) :
    let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
    res.1.recUpdates = ch.recUpdates ∧
    ∀ {factor : ℝ}, 0 ≤ factor → ChainRecBound cfg.P factor ch → ChainRecBound cfg.P factor res.1 := by
  set fc := algorithm1_findCycle ch
  set offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Δ_ext := liftEdgeFn extG e2i fc.1
  set lctOps' := lctOps + 2 * (offTree + 1)
  rw [algorithm2_loopWith]
  dsimp only
  by_cases hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α)
  · rw [dite_eq_left_iff.mpr fun h => absurd hGood h]
    exact ⟨rfl, fun _ hR => hR⟩
  · rw [dite_eq_right_iff.mpr fun h => absurd h hGood]
    cases hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none => exact ⟨rfl, fun _ hR => hR⟩
    | some i =>
      dsimp only
      by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val
      · rw [dite_eq_left_iff.mpr fun h => absurd hCap h]
        set ch1 := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        have hShRecEq : ch1.recUpdates = ch.recUpdates := by
          dsimp only [ch1, algorithm1_shift]
          split_ifs <;> rfl
        have ih := algorithm2_loopWith_rec_props cfg κ extG e2i g' ℓ' ch1
          (if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k)
          (fun j => if i < j then 0
            else if j = i then (if ((if i.val < cfg.P.d then ch.bran i.val else branD) + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j)
          lctOps'
        dsimp only at ih
        refine ⟨ih.1.trans hShRecEq, fun hf hR => ih.2 hf ?_⟩
        exact shift_preserves_chainRecBound cfg.T cfg.L cfg.P hf hR (Nat.lt_succ_iff.mp i.isLt)
      · rw [dite_eq_right_iff.mpr fun h => absurd h hCap]
        exact ⟨rfl, fun _ hR => hR⟩
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

lemma algorithm2_loop_rec_props (cfg : Alg2Config)
    (extG : MGraph) (e2i : ℕ → ℕ) (g' ℓ' : ℕ → ℝ)
    (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
    (lctOps : ℕ) :
    let res := algorithm2_loop cfg extG e2i g' ℓ' ch branD passes lctOps
    res.1.recUpdates = ch.recUpdates ∧
    ∀ {factor : ℝ}, 0 ≤ factor → ChainRecBound cfg.P factor ch → ChainRecBound cfg.P factor res.1 :=
  algorithm2_loopWith_rec_props cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i g' ℓ' ch branD passes lctOps

/-- Across every stage `t ≤ T`, `recUpdates 0` equals the cumulative length of external updates
`∑ s ∈ Icc 1 t, if isUpdate s then (D.U s).length else 0` for `algorithm2_dsWith cfg κ`. -/
theorem algorithm2_uncond_recUpdates_zero_eq_with {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    (κ : ℝ) {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t ≤ T,
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t).chain.recUpdates 0 =
        (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) := by
  have hMain := (algorithm2_uncond_preserves_with (η := η) κ hV hHist hmBound hnBound).1
  intro t
  induction t with
  | zero =>
    intro _
    simp [minRatioFailState, algorithm2_dsWith, algorithm2_init, algorithm1_initialize]
  | succ t ih =>
    intro ht
    have ht_le : t ≤ T := Nat.le_of_succ_le ht
    have iht := ih ht_le
    set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
    by_cases hupd : isUpdate (t + 1) = true
    · obtain ⟨_, _, _, _, hFresh, hExtG, _⟩ := hMain t ht_le
      have hD := hHist.1 (t + 1) (Nat.succ_pos t) ht
      have hBatch : st.extG.BatchIsValid (D.U (t + 1)) := hExtG ▸ hD.1
      have hTB := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
        st.extToInt st.intToExt st.nextFresh hFresh hBatch
      set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      have hLenEq : tb.2.2.2.2.length = (D.U (t + 1)).length := hTB.2.2.2.2.1
      have hUpdEq := algorithm2_updateWith_eq_of_loop κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))
      dsimp only at hUpdEq
      set ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))).1
      set initBP := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
        | none => (st.branD, st.passes)
        | some iStar => (0, fun j => if iStar ≤ j.val then 0 else st.passes j)
      set lp := algorithm2_loopWith cfg κ tb.1 tb.2.1 (D.g (t + 1)) (D.ℓ (t + 1)) ch1
        initBP.1 initBP.2 (st.lctUpdateOps + (D.U (t + 1)).length)
      have hChainEq : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)).chain = lp.1 := by
        rw [minRatioFailState, ite_eq_left_iff.mpr fun h => absurd hupd h]
        dsimp only [algorithm2_dsWith]
        change (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1.chain = lp.1
        cases hOpt : lp.2.2.2.2 with
        | none => rw [hUpdEq.1 hOpt]
        | some Δ => rw [hUpdEq.2 Δ hOpt]
      have hLoopRec := (algorithm2_loopWith_rec_props cfg κ tb.1 tb.2.1 (D.g (t + 1)) (D.ℓ (t + 1))
        ch1 initBP.1 initBP.2 (st.lctUpdateOps + (D.U (t + 1)).length)).1
      have hG0ℓ := update_G0_ℓ cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
        (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
      rw [hChainEq, congrFun hLoopRec 0, hG0ℓ.2.2.2, hLenEq, iht,
        Finset.sum_Icc_succ_top (Nat.succ_pos t), ite_eq_left_iff.mpr fun h => absurd hupd h]
    · have hdet : isUpdate (t + 1) = false := Bool.eq_false_iff.mpr hupd
      have hChainEq : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)).chain = st.chain := by
        simp [minRatioFailState, hupd, algorithm2_dsWith, algorithm2_detect, st]
      rw [hChainEq, iht, Finset.sum_Icc_succ_top (Nat.succ_pos t), hdet]
      simp

/-- Across every stage `t ≤ T`, `recUpdates 0` equals the cumulative length of external updates
`∑ s ∈ Icc 1 t, if isUpdate s then (D.U s).length else 0`. -/
theorem algorithm2_uncond_recUpdates_zero_eq {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t ≤ T,
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate t).chain.recUpdates 0 =
        (Finset.Icc 1 t).sum (fun s => if isUpdate s then (D.U s).length else 0) :=
  algorithm2_uncond_recUpdates_zero_eq_with hV (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    hHist hmBound hnBound

end MinCostFlow.Chain
