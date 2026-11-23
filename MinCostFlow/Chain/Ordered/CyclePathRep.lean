module

public import MinCostFlow.Chain.Ordered.CyclePathRepFind
public import MinCostFlow.Chain.Ordered.UpdatePreLoopHelpers
public import MinCostFlow.Chain.Ordered.RenameFacts

/-!
# Spanning-Tree Path and Off-Tree Edge Representation for Ordered Algorithm 2

Proves `alg2_update_optDir_cycle_rep_with` and `alg2_update_optDir_cycle_rep` for ordered
Algorithm 2 (`MinCostFlow.Chain.Ordered`), packaging the spanning forest `stNext.extTree` and
`(offTreeEdges, treePaths)` decomposition at every successful `Update` step (`jtree.tex`
lines 17–19, page 15).
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

private lemma alg2_loopWith_some_eq {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    (extG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (g' ℓ' : ℕ → ℝ) :
    ∀ (B : ℕ) (ch : ChainState cfg.T cfg.P) (branD : ℕ) (passes : Fin (cfg.P.d + 1) → ℕ)
      (lctOps : ℕ) (overflow : ℝ),
      shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch ≤ B →
      ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ ch →
      ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ ch overflow →
      LenInRange (max 0 cfg.Ψ) (ch.G 0) ch.ℓ →
      (∀ i : Fin (cfg.P.d + 1),
        (ch.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val) →
      branD < cfg.P.k →
      FreshInv extG (ch.G 0) e2i i2e nf →
      ∀ Δ,
        (algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps).2.2.2.2 = some Δ →
        let res := algorithm2_loopWith cfg κ extG e2i g' ℓ' ch branD passes lctOps
        Δ = liftEdgeFn extG e2i (algorithm1_findCycle res.1).1 ∧
        ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ res.1 ∧
        FreshInv extG (res.1.G 0) e2i i2e nf := by
  intro B
  induction B with
  | zero =>
    intro ch branD passes lctOps overflow hB hInv hBud hℓR hSh hBD hFresh Δ hSome
    rw [algorithm2_loopWith.eq_1] at hSome ⊢
    dsimp only at hSome ⊢
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤
        -(κ * cfg.α)
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      exact ⟨(Option.some.inj hSome).symm, hInv, hFresh⟩
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none =>
        rw [hElig] at hSome
        dsimp only at hSome
        simp at hSome
      | some i =>
        rw [hElig] at hSome
        dsimp only at hSome ⊢
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          omega
        · rw [dite_eq_right_of_eq_false (eq_false hCap)] at hSome
          simp at hSome
  | succ B ihB =>
    intro ch branD passes lctOps overflow hB hInv hBud hℓR hSh hBD hFresh Δ hSome
    rw [algorithm2_loopWith.eq_1] at hSome ⊢
    dsimp only at hSome ⊢
    by_cases hGood : extG.inner g' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) /
        extG.lnorm ℓ' (liftEdgeFn extG e2i (algorithm1_findCycle ch).1) ≤
        -(κ * cfg.α)
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      exact ⟨(Option.some.inj hSome).symm, hInv, hFresh⟩
    · simp only [hGood, ↓reduceDIte] at hSome ⊢
      cases hElig : findEligibleLevel cfg.P.d (alg2PsiGame cfg.Ψ cfg.P.M₀) passes with
      | none =>
        rw [hElig] at hSome
        dsimp only at hSome
        simp at hSome
      | some i =>
        rw [hElig] at hSome
        dsimp only at hSome ⊢
        by_cases hCap : (ch.shiftCount i.val : ℝ) + 1 ≤
            gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch.rebuildCount i.val
        · rw [dite_eq_left_of_eq_true (eq_true hCap)] at hSome ⊢
          have hlt := shiftRemainingBudget_lt_of_step (L := cfg.L) ch i hCap
          have hShP := shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
            hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hℓR hBud i.val (Nat.le_of_lt_succ i.isLt)
          dsimp only at hShP
          rcases hShP with ⟨hInv', hBud', hG0', hℓ1, _, hShCount', _, _, _⟩
          have hShBound' : ∀ j : Fin (cfg.P.d + 1),
              ((algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.shiftCount j.val : ℝ) ≤
                gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀)
                  (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.rebuildCount j.val := by
            intro j
            have hShReb : (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.rebuildCount = ch.rebuildCount := by
              dsimp only [algorithm1_shift]; split_ifs <;> rfl
            rw [hShReb, congrFun hShCount' j.val]
            by_cases hji : j.val = i.val
            · simp [hji, hCap]
            · simp [hji]; exact hSh j
          let curB := if i.val < cfg.P.d then ch.bran i.val else branD
          let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
          let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
            if i < j then 0
            else if j = i then (if (curB + 1) % cfg.P.k = 0 then passes i + 1 else passes i)
            else passes j
          let lctOps' := lctOps + 2 * ((walkEdges (algorithm1_findCycle ch).2.1 \ ch.toTreeChain.chainTree.E).card + 1)
          have hBranD' : branD' < cfg.P.k := by
            dsimp only [branD']
            split_ifs
            · exact cfg.P.hk
            · exact Nat.mod_lt _ cfg.P.hk
          have hFresh' : FreshInv extG ((algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1.G 0) e2i i2e nf :=
            hG0'.symm ▸ hFresh
          exact ihB (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1 branD' passes' lctOps' overflow (by omega)
            hInv' hBud' (by rw [hG0', hℓ1]; exact hℓR) hShBound' hBranD' hFresh' Δ hSome
        · rw [dite_eq_right_of_eq_false (eq_false hCap)] at hSome
          simp at hSome

private lemma algorithm2_updateWith_spec_fields (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    let tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
    let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
      (fun e' => g' (tb.2.2.1 e')) (fun e' => ℓ' (tb.2.2.1 e'))).1
    let bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
      | none => (st.branD, st.passes)
      | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
    let ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    let G₀' := (st.chain.G 0).applyBatch tb.2.2.2.2
    let lp := algorithm2_loopWith cfg κ tb.1 (level0E2I ren G₀' tb.2.1) g' ℓ' ch1 bp1.1 bp1.2
      (st.lctUpdateOps + U_ext.length)
    let res := algorithm2_updateWith cfg κ st U_ext g' ℓ' η
    res.2 = lp.2.2.2.2 ∧
    res.1.chain = lp.1 ∧
    res.1.extG = tb.1 ∧
    res.1.extToInt = level0E2I ren G₀' tb.2.1 ∧
    res.1.intToExt = level0I2E ren G₀' tb.2.2.1 ∧
    res.1.nextFresh = level0NF ren G₀' tb.2.2.2.1 := by
  dsimp only [algorithm2_updateWith]
  split <;> exact ⟨by symm; assumption, rfl, rfl, rfl, rfl, rfl⟩

/-- **Theorem 5.1 cycle-representation theorem for ordered `algorithm2_dsWith cfg κ`**: at every
successful `Update` step `t + 1 ≤ T` (`minRatioFailOptDir = some Δ`), the state `stNext` after
step `t + 1` maintains a spanning forest `T_tree := stNext.extTree ⊆ D.G (t + 1)` together with
`offTreeEdges` (`≤ ⌈TP.γ_ℓ (M₀²)⌉ + 1`) and `treePaths` (`≤ 2 * (⌈TP.γ_ℓ (M₀²)⌉ + 1)`) summing
to `Δ`. -/
theorem alg2_update_optDir_cycle_rep_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t, t + 1 ≤ T → isUpdate (t + 1) = true → ∀ Δ,
      minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t = some Δ →
      let stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
      let T_tree := stNext.extTree
      (D.G (t + 1)).IsSubgraph T_tree ∧
      T_tree.IsForest ∧
      (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
        (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
      ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
        T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
      ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
        offTreeEdges.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 ∧
        (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
        treePaths.length ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1) ∧
        (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
        ∀ e : ℕ, Δ e =
          (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
          (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum := by
  have hUncond := algorithm2_uncond_preserves_with (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound
  have hExtLG := alg2UncondInv_extℓ_extg_with (cfg := cfg) (η := η) κ hHist hEdge
  intro t ht1 hupd Δ hSome
  have ht_le : t ≤ T := Nat.le_of_succ_le ht1
  have hUI := hUncond.1 t ht_le
  rcases hUI with ⟨hInv, hBud, _, _, hFresh, hExtG, _, hChℓ, _, _, _, hShB, hBranD, _, _⟩
  obtain ⟨hExtℓ, _⟩ := hExtLG t ht_le
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t
  have hBatch := hHist.1 (t + 1) (Nat.succ_pos t) ht1
  simp only [Nat.add_sub_cancel] at hBatch
  have htb := translateBatch_preserves (D.U (t + 1)) st.extG (st.chain.G 0)
    st.extToInt st.intToExt st.nextFresh hFresh (hExtG ▸ hBatch.1)
  set tb := translateBatch st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
  have hEdge_int : ∀ u' ∈ tb.2.2.2.2, IsEdgeUpdate u' :=
    translateBatch_isEdgeUpdate st.extG st.extToInt st.intToExt st.nextFresh (D.U (t + 1))
      (hEdge (t + 1) (Nat.succ_pos t) ht1)
  rcases htb with ⟨htbExt, htbFresh, htbBatch, htbNR, htbLen, htbNf, htbInsN, htbOld, htbNotIns, htbIns⟩
  have hExtG' : tb.1 = D.G (t + 1) := by rw [htbExt, hExtG, hBatch.2]
  have hExtValid : (D.G (t + 1)).IsValid := (hHist.2.1 (t + 1) ht1).1
  have hU_valid_int : ((st.chain.G 0).applyBatch tb.2.2.2.2).IsValid :=
    htbFresh.isValid_iff.mpr (hExtG'.symm ▸ hExtValid)
  have hU_m : ((st.chain.G 0).applyBatch tb.2.2.2.2).m ≤ cfg.P.M₀ := by
    rw [htbFresh.m_eq, hExtG']; exact hmBound (t + 1) ht1
  have hU_n : ((st.chain.G 0).applyBatch tb.2.2.2.2).n ≤ cfg.N₀ := by
    rw [htbFresh.n_eq, hExtG']; exact hnBound (t + 1) ht1
  have hChℓ_D : st.chain.ℓ = fun e' => D.ℓ t (st.intToExt e') := by
    rw [hChℓ]; ext e'; rw [hExtℓ]
  have hℓ'_pos : ∀ e ∈ (D.G (t + 1)).E, 0 < D.ℓ (t + 1) e := (hHist.2.1 (t + 1) ht1).2
  have hℓ'_stable : ∀ e ∈ ((st.chain.G 0).applyBatch tb.2.2.2.2).E, e ∈ (st.chain.G 0).E →
      (∀ u ∈ tb.2.2.2.2, ¬ u.Inserts e) →
      D.ℓ (t + 1) (tb.2.2.1 e) = st.chain.ℓ e := by
    intro e he1 he0 hnoU
    obtain ⟨heq, heExt⟩ := htbFresh.hRight e he1
    have hD_no : ∀ u ∈ D.U (t + 1), ¬ u.Inserts (tb.2.2.1 e) := by
      intro u hu huIns
      have he_old : e < st.nextFresh := hFresh.hLtFresh e he0
      have hge := htbIns (tb.2.2.1 e) (hExtG' ▸ heExt) ⟨u, hu, huIns⟩
      rw [heq] at hge
      omega
    have hNotBet : D.NotInsertedBetween (tb.2.2.1 e) t (t + 1) := fun s hs1 hs2 u hu huIns => by
      have hst : s = t + 1 := by omega
      subst hst
      exact hD_no u hu huIns
    have hℓ_eq := (hHist.2.2.2 (t + 1) (Nat.succ_pos t) ht1 (tb.2.2.1 e)
      (hExtG' ▸ heExt) hNotBet).2
    simp only [Nat.add_sub_cancel] at hℓ_eq
    rw [hℓ_eq, hChℓ_D]
    congr 1
    exact htbOld e (hFresh.hLtFresh e he0)
  have hℓ'_pos_int : LenInRange (max 0 cfg.Ψ) ((st.chain.G 0).applyBatch tb.2.2.2.2)
      (fun e => D.ℓ (t + 1) (tb.2.2.1 e)) := by
    intro e he
    exact hLen.lenInRange ht1 hℓ'_pos _ (hExtG' ▸ (htbFresh.hRight e he).2)
  have hUpd := update_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hNoReins hV.hγM₀ hV.hγk hInv hBud
    tb.2.2.2.2 (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
    htbBatch htbNR hEdge_int hU_valid_int hU_m hU_n hℓ'_pos_int hℓ'_stable
  set updRes := algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2
    (fun e' => D.g (t + 1) (tb.2.2.1 e')) (fun e' => D.ℓ (t + 1) (tb.2.2.1 e'))
  set ch1 := updRes.1
  have hRen := update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain
    (D.g (t + 1)) (D.ℓ (t + 1)) htbFresh
  dsimp only at hRen
  set ren := level0Rebuilt cfg.P.d st.chain.rebuildCount ch1.rebuildCount
  set G₀' := (st.chain.G 0).applyBatch tb.2.2.2.2
  have hFresh1 : FreshInv tb.1 (ch1.G 0) (level0E2I ren G₀' tb.2.1) (level0I2E ren G₀' tb.2.2.1)
      (level0NF ren G₀' tb.2.2.2.1) := hRen.1
  set bp1 := match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar => (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  have hBranD1 : bp1.1 < cfg.P.k := by
    dsimp only [bp1]
    cases firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount
    · exact hBranD
    · exact cfg.P.hk
  have hShB1 : ∀ j : Fin (cfg.P.d + 1),
      (ch1.shiftCount j.val : ℝ) ≤ gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1.rebuildCount j.val := by
    intro j
    have hEq := hUpd.2.2.2.1 j.val
    have hRebLe : ∀ i, st.chain.rebuildCount i ≤ ch1.rebuildCount i := hUpd.2.2.2.2.1
    have hMono := gameShiftBound_mono_reb (P := cfg.P) (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) hRebLe j.val
    exact le_trans (hEq ▸ hShB j) hMono
  have hSpecF := algorithm2_updateWith_spec_fields cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))
  have hOptEq : minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t =
      (algorithm2_loopWith cfg κ tb.1 (level0E2I ren G₀' tb.2.1) (D.g (t + 1)) (D.ℓ (t + 1)) ch1
        bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)).2.2.2.2 :=
    hSpecF.1
  rw [hOptEq] at hSome
  have hLoopSome := alg2_loopWith_some_eq κ hV
    tb.1 (level0E2I ren G₀' tb.2.1) (level0I2E ren G₀' tb.2.2.1) (level0NF ren G₀' tb.2.2.2.1)
    (D.g (t + 1)) (D.ℓ (t + 1))
    (shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch1)
    ch1 bp1.1 bp1.2 (st.lctUpdateOps + (D.U (t + 1)).length)
    (st.largeBatchEnc + largeBatchEncCap cfg.P tb.2.2.2.2)
    le_rfl hUpd.1 hUpd.2.1
    (update_lenInRange cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain tb.2.2.2.2 _ _ hℓ'_pos_int) hShB1 hBranD1 hFresh1 Δ hSome
  rcases hLoopSome with ⟨hΔeq, hInvEnd, hFreshEnd⟩
  have hStStep : minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1) =
      (algorithm2_updateWith cfg κ st (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1 := by
    rw [minRatioFailState.eq_2]
    simp only [hupd, ↓reduceIte]
    rfl
  set stNext := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (t + 1)
  have hSt_extG : stNext.extG = D.G (t + 1) := by
    rw [hStStep, hSpecF.2.2.1, hExtG']
  have hInvNext : ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ stNext.chain := by
    rw [hStStep, hSpecF.2.1]; exact hInvEnd
  have hFreshNext : FreshInv stNext.extG (stNext.chain.G 0) stNext.extToInt stNext.intToExt stNext.nextFresh := by
    rw [hStStep, hSpecF.2.1, hSpecF.2.2.1, hSpecF.2.2.2.1, hSpecF.2.2.2.2.1, hSpecF.2.2.2.2.2]
    exact hFreshEnd
  have hTHNext := ChainInv.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk hInvNext
  have hSubNext := stNext.chain.toTreeChain.forestsAreSubgraphs_of_holds hTHNext.1
  have hRep := findCycle_tree_path_rep hV stNext hInvNext hFreshNext
  have hΔNext : Δ = liftEdgeFn stNext.extG stNext.extToInt (algorithm1_findCycle stNext.chain).1 := by
    rw [hStStep, hSpecF.2.1, hSpecF.2.2.1, hSpecF.2.2.2.1]; exact hΔeq
  rw [← hΔNext] at hRep
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← hSt_extG]; exact extTree_isSubgraph stNext
  · exact extTree_isForest stNext (hSt_extG ▸ hExtValid) hFreshNext
      (stNext.chain.toTreeChain.chainTree_isForest hTHNext.1 hSubNext)
  · intro u hu v hv hconn
    rw [← hSt_extG] at hu hv hconn
    exact extTree_connected_of_connected stNext hFreshNext hTHNext.1 hSubNext hTHNext.2.1 hu hv hconn
  · intro hConn
    rw [← hSt_extG] at hConn ⊢
    exact extTree_isSpanningTreeOn stNext (hSt_extG ▸ hExtValid) hFreshNext hTHNext.1 hSubNext hTHNext.2.1 hConn
  · rcases hRep with ⟨offTreeEdges, treePaths, h1, h2, h3, h4, h5⟩
    exact ⟨offTreeEdges, treePaths, h1, fun x hx => hSt_extG ▸ h2 x hx, h3, h4, h5⟩

/-- **Theorem 5.1 cycle-representation theorem for ordered `algorithm2_ds`**: at every successful
`Update` step `t + 1 ≤ T` (`minRatioFailOptDir = some Δ`), the state `stNext` after step `t + 1`
maintains a spanning forest `T_tree := stNext.extTree ⊆ D.G (t + 1)` together with
`offTreeEdges` and `treePaths` summing to `Δ`. -/
theorem alg2_update_optDir_cycle_rep {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T) (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    ∀ t, t + 1 ≤ T → isUpdate (t + 1) = true → ∀ Δ,
      minRatioFailOptDir (algorithm2_ds cfg) D η isUpdate t = some Δ →
      let stNext := minRatioFailState (algorithm2_ds cfg) D η isUpdate (t + 1)
      let T_tree := stNext.extTree
      (D.G (t + 1)).IsSubgraph T_tree ∧
      T_tree.IsForest ∧
      (∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V,
        (D.G (t + 1)).Connected u v → T_tree.Connected u v) ∧
      ((∀ u ∈ (D.G (t + 1)).V, ∀ v ∈ (D.G (t + 1)).V, (D.G (t + 1)).Connected u v) →
        T_tree.IsSpanningTreeOn (D.G (t + 1)).V) ∧
      ∃ (offTreeEdges : List (ℕ × Bool)) (treePaths : List (ℕ × ℕ)),
        offTreeEdges.length ≤ Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1 ∧
        (∀ x ∈ offTreeEdges, x.1 ∈ (D.G (t + 1)).E \ T_tree.E) ∧
        treePaths.length ≤ 2 * (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) + 1) ∧
        (∀ p ∈ treePaths, T_tree.Connected p.1 p.2) ∧
        ∀ e : ℕ, Δ e =
          (offTreeEdges.map (fun x => walkFlow [x] e)).sum +
          (treePaths.map (fun p => walkFlow (T_tree.forestPath p.1 p.2) e)).sum :=
  alg2_update_optDir_cycle_rep_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hEdge hLen hmBound hnBound

end MinCostFlow.Chain.Ordered
