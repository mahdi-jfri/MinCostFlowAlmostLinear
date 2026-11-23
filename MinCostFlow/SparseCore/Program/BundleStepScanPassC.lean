module

public import MinCostFlow.SparseCore.Program.BundleStepScanProcs

/-!
# Verification of Pass C in Phase 2 (`BundleStepScanPassC`)

Verifies `bundleStepScanPassCStmt`: for a non-maximal root `v` whose ends `xs` are stored as
`EndListAt` at `listPtr`, appends a 3-word heap node `[b, packEndKey eCap v key, oldHead]` to
`btCurBunBase[s]` and increments `btCurTagBase[s]` for every active end in `xs` whose bundle `b`
has `inCand[b] = 1`. Leaves `BundleTableAfterScan` and all addresses outside
`[btCurBunBase, btCurTagBase + slotCap) ∪ [hCur, h')` unchanged, advances `hCur` by at most
`3 * xs.length`, and runs in `≤ 120 * xs.length + 50` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

public section

/-- Verifies `bundleStepScanPassCStmt` on one non-maximal root `v` with `EndListAt` `xs` at
`listPtr`, extending `SlotScanListAt` by `addScanEndsForList (tableDelEdges S₀ D) candSet v xs`. -/
lemma bundleStepScanPassC_runs {w slotCap vCap eCap tbl listPtr v hStart hCur : ℕ}
    {pProg : Program} {S₀ : BundleTableState slotCap} {D : Finset ℕ}
    {m : BundleTableMeta slotCap} {candSet : Fin slotCap → Finset ℕ}
    {touched : List ℕ} {scan₀ : Fin slotCap → List (ℕ × ℕ × ℕ)} {P : ℕ → Prop}
    {xs : List End} {st₀ : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hpk_w : vCap * (2 * eCap) < 2 ^ w)
    (htbl_w : tbl + bundleTableFixedSize slotCap eCap < 2 ^ w)
    (hblks_w : ∀ js : Fin slotCap, ∀ p c, m.slotBlocks js = some (p, c) →
      p + bundleSlotBlockSize c < 2 ^ w)
    (hlist_w : listPtr + 1 + xs.length < 2 ^ w)
    (hv_lt : v < vCap)
    (hxs_lt : ∀ x ∈ xs, x.1 < eCap)
    (hfoot_lt : ∀ a, bundleTableFoot eCap tbl m a → a < hStart)
    (hhStart_le : hStart ≤ hCur)
    (hlist_le : listPtr + 1 + xs.length ≤ hCur)
    (hlist_disj_cur : ∀ a, listPtr ≤ a → a < listPtr + 1 + xs.length →
      a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a)
    (hcnt_le : ∀ j : Fin slotCap, (scan₀ j).length ≤ hCur)
    (hh_sp : hCur + 3 * xs.length < 2 ^ w)
    (hzero : ZeroFrom st₀.mem hCur)
    (hlist : EndListAt st₀.mem listPtr xs)
    (hafter : BundleTableAfterScan slotCap vCap eCap tbl S₀ D m candSet touched st₀.mem)
    (hscan₀ : SlotScanListAt slotCap eCap tbl st₀.mem hStart hCur scan₀)
    (hPin₀ : ∀ j : Fin slotCap, ScanNodesIn st₀.mem P (st₀.mem (btCurBunBase tbl slotCap eCap + j.1)) (scan₀ j))
    (hPnew : ∀ a, hCur ≤ a → P a)
    (hr0 : st₀.regs 0 = tbl) (hr6 : st₀.regs 6 = hCur)
    (hr7 : st₀.regs 7 = btSlotPtrBase tbl) (hr8 : st₀.regs 8 = btEdgeSlotBase tbl slotCap)
    (hr9 : st₀.regs 9 = btEndBundleBase tbl slotCap eCap)
    (hr11 : st₀.regs 11 = btSlotCandHeadBase tbl slotCap eCap)
    (hr20 : st₀.regs 20 = v) (hr21 : st₀.regs 21 = listPtr) (hr22 : st₀.regs 22 = xs.length) :
    let S := tableDelEdges S₀ D
    ∃ st' c h',
      Runs w pProg ω bundleStepScanPassCStmt st₀ .normal st' c ∧
      (∀ r ≤ 22, r ≠ 6 → st'.regs r = st₀.regs r) ∧
      st'.regs 6 = h' ∧
      hCur ≤ h' ∧ h' ≤ hCur + 3 * xs.length ∧
      ZeroFrom st'.mem h' ∧
      SlotScanListAt slotCap eCap tbl st'.mem hStart h' (addScanEndsForList S candSet v xs scan₀) ∧
      (∀ j : Fin slotCap, ScanNodesIn st'.mem P (st'.mem (btCurBunBase tbl slotCap eCap + j.1))
        (addScanEndsForList S candSet v xs scan₀ j)) ∧
      (∀ j : Fin slotCap, (addScanEndsForList S candSet v xs scan₀ j).length ≤ h') ∧
      (∀ a, (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
        (a < hCur ∨ h' ≤ a) → st'.mem a = st₀.mem a) ∧
      c ≤ 120 * xs.length + 50 := by
  classical
  intro S
  have htbl_w' : tbl + (14 + 7 * slotCap + 8 * eCap) < 2 ^ w := htbl_w
  have hcurB_eq : btSlotCandHeadBase tbl slotCap eCap + slotCap = btCurBunBase tbl slotCap eCap := by
    unfold btSlotCandHeadBase btCurBunBase; omega
  have hcurT_eq : btCurBunBase tbl slotCap eCap + slotCap = btCurTagBase tbl slotCap eCap := by
    unfold btCurBunBase btCurTagBase; omega
  have hcur_lt_hStart : btCurTagBase tbl slotCap eCap + slotCap ≤ hStart := by
    have := hfoot_lt (btCurTagBase tbl slotCap eCap + slotCap - 1)
      (Or.inl ⟨by unfold btCurTagBase; omega, by unfold btCurTagBase bundleTableFixedSize; omega⟩)
    unfold btCurTagBase at this ⊢; omega
  have hcur_disj_core : ∀ a, btCurBunBase tbl slotCap eCap ≤ a →
      a < btCurTagBase tbl slotCap eCap + slotCap → ¬ bundleTableCoreFoot eCap tbl m a := by
    intro a ha1 ha2 hc
    rcases hc with ⟨_, hc2⟩ | ⟨j, p, cap, hm, hp1, hp2⟩
    · unfold btCurBunBase at ha1; unfold bundleTableCoreSize at hc2; omega
    · have hsj := hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
      cases hS : tableDelEdges S₀ D j with
      | none => rw [hS, hm] at hsj; exact False.elim hsj
      | some B =>
        rw [hS, hm] at hsj
        have hdj := hsj.2.2
        unfold btCurBunBase at ha1; unfold btCurTagBase at ha2; unfold bundleTableFixedSize at hdj
        omega
  have hv2e_le : v * (2 * eCap) ≤ vCap * (2 * eCap) := Nat.mul_le_mul_right _ (Nat.le_of_lt hv_lt)
  -- Header: r23 = slotCap, r24 = 2 * eCap, r25 = btCurBunBase, r26 = btCurTagBase, r27 = v * (2 * eCap)
  set r23 := Function.update st₀.regs 23 slotCap
  set r24 := Function.update r23 24 (2 * eCap)
  set r25 := Function.update r24 25 (btCurBunBase tbl slotCap eCap)
  set r26 := Function.update r25 26 (btCurTagBase tbl slotCap eCap)
  set r27 := Function.update r26 27 (v * (2 * eCap))
  set stH : State := { st₀ with regs := r27 }
  have ha23 : Runs w pProg ω (.assign 23 (.load (.reg 0))) st₀ .normal { st₀ with regs := r23 } 3 :=
    runs_assign_iff.mpr ⟨slotCap, by
      have hm0 : st₀.mem tbl = slotCap := by simpa [btOffSlotCap] using hafter.1
      simp [Expr.eval, hr0, hm0], rfl, rfl, rfl⟩
  have ha24 : Runs w pProg ω (.assign 24 (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.const 2)))))
      { st₀ with regs := r23 } .normal { st₀ with regs := r24 } 7 :=
    runs_assign_iff.mpr ⟨2 * eCap, by
      have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
      have htbl2 : tbl + 2 < 2 ^ w := by clear * - htbl_w'; omega
      have h2e_w : 2 * eCap < 2 ^ w := by clear * - htbl_w'; omega
      have hm2 : st₀.mem (tbl + 2) = eCap := hafter.2.2.1
      simp [Expr.eval, BinOp.eval, r23, hr0, h2_w, htbl2, hm2, h2e_w], rfl, rfl, rfl⟩
  have ha25 : Runs w pProg ω (.assign 25 (.bin .add (.reg 11) (.reg 23)))
      { st₀ with regs := r24 } .normal { st₀ with regs := r25 } 4 :=
    runs_assign_iff.mpr ⟨btCurBunBase tbl slotCap eCap, by
      have hcb_w : btCurBunBase tbl slotCap eCap < 2 ^ w := by
        unfold btCurBunBase; clear * - htbl_w'; omega
      simp [Expr.eval, BinOp.eval, r24, r23, hr11, hcurB_eq, hcb_w], rfl, rfl, rfl⟩
  have ha26 : Runs w pProg ω (.assign 26 (.bin .add (.reg 25) (.reg 23)))
      { st₀ with regs := r25 } .normal { st₀ with regs := r26 } 4 :=
    runs_assign_iff.mpr ⟨btCurTagBase tbl slotCap eCap, by
      have hct_w : btCurTagBase tbl slotCap eCap < 2 ^ w := by
        unfold btCurTagBase; clear * - htbl_w'; omega
      simp [Expr.eval, BinOp.eval, r25, r24, r23, hcurT_eq, hct_w], rfl, rfl, rfl⟩
  have ha27 : Runs w pProg ω (.assign 27 (.bin .mul (.reg 20) (.reg 24)))
      { st₀ with regs := r26 } .normal stH 4 :=
    runs_assign_iff.mpr ⟨v * (2 * eCap), by
      have hmul_w : v * (2 * eCap) < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, r26, r25, r24, r23, hr20, hmul_w], rfl, rfl, rfl⟩
  -- Loop over i ∈ [0, xs.length)
  let body : Stmt :=
    .assign 29 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 28))) ;;
    .assign 30 (.bin .div (.reg 29) (.const 2)) ;;
    .assign 31 (.load (.bin .add (.reg 8) (.reg 30))) ;;
    .cond (.reg 31)
      (.assign 32 (.bin .sub (.reg 31) (.const 1)) ;;
       .assign 33 (.load (.bin .add (.reg 7) (.reg 32))) ;;
       .assign 34 (.load (.reg 33)) ;;
       .assign 35 (.load (.bin .add (.reg 9) (.reg 29))) ;;
       .assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
         (.bin .mul (.const 4) (.reg 34))) (.reg 35))) ;;
       .cond (.reg 36)
         (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
          .store (.reg 6) (.reg 35) ;;
          .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
          .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
          .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
          .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
          .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
          .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
         .nop)
      .nop
  let Inv : ℕ → ℕ → State → Prop := fun i hNow st =>
    (∀ r ≤ 27, r ≠ 6 → st.regs r = stH.regs r) ∧
    st.regs 6 = hNow ∧ st.regs 28 = i ∧
    hCur ≤ hNow ∧ hNow ≤ hCur + 3 * i ∧
    ZeroFrom st.mem hNow ∧
    SlotScanListAt slotCap eCap tbl st.mem hStart hNow
      (addScanEndsForList S candSet v (xs.take i) scan₀) ∧
    (∀ j : Fin slotCap, ScanNodesIn st.mem P (st.mem (btCurBunBase tbl slotCap eCap + j.1))
      (addScanEndsForList S candSet v (xs.take i) scan₀ j)) ∧
    (∀ j : Fin slotCap, (addScanEndsForList S candSet v (xs.take i) scan₀ j).length ≤ hNow) ∧
    (∀ a, (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
      (a < hCur ∨ hNow ≤ a) → st.mem a = st₀.mem a)
  have hloop : ∀ d i (hd : i + d = xs.length) hNow st, Inv i hNow st →
      ∃ stEnd cEnd hEnd,
        Runs w pProg ω (.loop (.bin .lt (.reg 28) (.reg 22))
          (body ;; .assign 28 (.bin .add (.reg 28) (.const 1)))) st .normal stEnd cEnd ∧
        Inv xs.length hEnd stEnd ∧ cEnd ≤ 120 * d + 4 := by
    intro d
    induction d with
    | zero =>
      intro i hd hNow st hI
      have hi : i = xs.length := by omega
      subst hi
      have hcond0 : Expr.eval w st (.bin .lt (.reg 28) (.reg 22)) = some 0 := by
        have hr22' : st.regs 22 = xs.length := by
          rw [hI.1 22 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr22]
        simp [Expr.eval, BinOp.eval, hI.2.2.1, hr22', show 0 < 2 ^ w by omega]
      exact ⟨st, 4, hNow, runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩), hI, by omega⟩
    | succ d ih =>
      intro i hd hNow st hI
      have hi : i < xs.length := by omega
      rcases hI with ⟨hregs, hr6_i, hr28_i, hlo_i, hhi_i, hzf_i, hscan_i, hPin_i, hcnt_i, hfr_i⟩
      have h1_w : 1 < 2 ^ w := by clear * - hw16; omega
      have h2_w : 2 < 2 ^ w := by clear * - hw16; omega
      have h3_w : 3 < 2 ^ w := by clear * - hw16; omega
      have h4_w : 4 < 2 ^ w := by clear * - hw16; omega
      have hr_eq : ∀ r ≤ 27, r ≠ 6 → st.regs r = stH.regs r := hregs
      have hr7' : st.regs 7 = btSlotPtrBase tbl := by
        rw [hr_eq 7 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr7]
      have hr8' : st.regs 8 = btEdgeSlotBase tbl slotCap := by
        rw [hr_eq 8 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr8]
      have hr9' : st.regs 9 = btEndBundleBase tbl slotCap eCap := by
        rw [hr_eq 9 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr9]
      have hr21' : st.regs 21 = listPtr := by
        rw [hr_eq 21 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr21]
      have hr22' : st.regs 22 = xs.length := by
        rw [hr_eq 22 (by decide) (by decide)]; simp [stH, r27, r26, r25, r24, r23, hr22]
      have hr25' : st.regs 25 = btCurBunBase tbl slotCap eCap := by
        rw [hr_eq 25 (by decide) (by decide)]; simp [stH, r27, r26, r25]
      have hr26' : st.regs 26 = btCurTagBase tbl slotCap eCap := by
        rw [hr_eq 26 (by decide) (by decide)]; simp [stH, r27, r26]
      have hr27' : st.regs 27 = v * (2 * eCap) := by
        rw [hr_eq 27 (by decide) (by decide)]; simp [stH, r27]
      set x := xs[i]'hi
      have hx_e : x.1 < eCap := hxs_lt x (List.getElem_mem hi)
      have hkey_lt : endKey x < 2 * eCap := by
        rcases x with ⟨ee, side⟩; cases side <;> simp [endKey] at hx_e ⊢ <;> omega
      have hkey_div : endKey x / 2 = x.1 := by
        rcases x with ⟨ee, side⟩; cases side
        · simp [endKey]; omega
        · simp [endKey]
      have hmem_key : st.mem (listPtr + 1 + i) = endKey x := by
        rw [hfr_i (listPtr + 1 + i) (hlist_disj_cur _ (by omega) (by omega)) (Or.inl (by omega))]
        have h2 := hlist.2 i hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at h2
        exact h2
      have hmem_core : ∀ a, bundleTableCoreFoot eCap tbl m a → st.mem a = st₀.mem a := fun a ha =>
        hfr_i a (by
          by_contra hnot
          push Not at hnot
          exact hcur_disj_core a hnot.1 hnot.2 ha)
          (Or.inl (Nat.lt_of_lt_of_le (hfoot_lt a (bundleTableCoreFoot_subset_foot ha)) hhStart_le))
      have hmem_es : st.mem (btEdgeSlotBase tbl slotCap + x.1) = st₀.mem (btEdgeSlotBase tbl slotCap + x.1) :=
        hmem_core _ (btEdgeSlot_in_coreFoot hx_e)
      set es := st₀.mem (btEdgeSlotBase tbl slotCap + x.1)
      set r29 := Function.update st.regs 29 (endKey x)
      set r30 := Function.update r29 30 x.1
      set r31 := Function.update r30 31 es
      set st31 : State := { st with regs := r31 }
      have ha29 : Runs w pProg ω (.assign 29 (.load (.bin .add (.bin .add (.reg 21) (.const 1)) (.reg 28))))
          st .normal { st with regs := r29 } 7 :=
        runs_assign_iff.mpr ⟨endKey x, by
          simp [Expr.eval, BinOp.eval, hr21', hr28_i, h1_w, show listPtr + 1 < 2 ^ w by omega,
            show listPtr + 1 + i < 2 ^ w by omega, hmem_key], rfl, rfl, rfl⟩
      have ha30 : Runs w pProg ω (.assign 30 (.bin .div (.reg 29) (.const 2)))
          { st with regs := r29 } .normal { st with regs := r30 } 4 :=
        runs_assign_iff.mpr ⟨x.1, by
          simp [Expr.eval, BinOp.eval, r29, h2_w, hkey_div, show x.1 < 2 ^ w by clear * - htbl_w' hx_e; omega],
          rfl, rfl, rfl⟩
      have ha31 : Runs w pProg ω (.assign 31 (.load (.bin .add (.reg 8) (.reg 30))))
          { st with regs := r30 } .normal st31 5 :=
        runs_assign_iff.mpr ⟨es, by
          have hes_w : btEdgeSlotBase tbl slotCap + x.1 < 2 ^ w := by
            unfold btEdgeSlotBase; clear * - htbl_w' hx_e; omega
          simp [Expr.eval, BinOp.eval, r30, r29, hr8', hes_w, hmem_es, es], rfl, rfl, rfl⟩
      have htake_eq := addScanEndsForList_take_succ S candSet v xs scan₀ hi
      have hbody_step : ∃ stB cB hNext,
          Runs w pProg ω body st .normal stB cB ∧
          (∀ r ≤ 28, r ≠ 6 → stB.regs r = st.regs r) ∧
          stB.regs 6 = hNext ∧ hNow ≤ hNext ∧ hNext ≤ hNow + 3 ∧
          ZeroFrom stB.mem hNext ∧
          SlotScanListAt slotCap eCap tbl stB.mem hStart hNext
            (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀) ∧
          (∀ j : Fin slotCap, ScanNodesIn stB.mem P (stB.mem (btCurBunBase tbl slotCap eCap + j.1))
            (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j)) ∧
          (∀ j : Fin slotCap, (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j).length ≤ hNext) ∧
          (∀ a, (a < btCurBunBase tbl slotCap eCap ∨ btCurTagBase tbl slotCap eCap + slotCap ≤ a) →
            (a < hCur ∨ hNext ≤ a) → stB.mem a = st₀.mem a) ∧
          cB ≤ 111 := by
        by_cases hes0 : es = 0
        · -- Not in any active slot
          have hno_slot : ∀ (j : Fin slotCap) (B : BundleState), S j = some B → x.1 ∉ B.edges := by
            intro j B hSj hxB
            have h1 := (hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x.1 hx_e).1 j B hSj hxB
            change es = j.1 + 1 at h1; omega
          have hscan_eq : addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ =
              addScanEndsForList S candSet v (xs.take i) scan₀ := by
            rw [htake_eq]; funext j; cases hSj : S j with
            | none => rfl
            | some B =>
              have hne : (xs[i]'hi).1 ∉ B.edges := hno_slot j B hSj
              dsimp only; simp [hne]
          have hcond : Runs w pProg ω
              (.cond (.reg 31)
                (.assign 32 (.bin .sub (.reg 31) (.const 1)) ;;
                 .assign 33 (.load (.bin .add (.reg 7) (.reg 32))) ;;
                 .assign 34 (.load (.reg 33)) ;;
                 .assign 35 (.load (.bin .add (.reg 9) (.reg 29))) ;;
                 .assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
                   (.bin .mul (.const 4) (.reg 34))) (.reg 35))) ;;
                 .cond (.reg 36)
                   (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
                    .store (.reg 6) (.reg 35) ;;
                    .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
                    .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
                    .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
                    .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
                    .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
                    .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                   .nop)
                .nop) st31 .normal st31 3 := by
            refine runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st31, r31, hes0], ?_, by simp [Expr.size]⟩
            simp only [↓reduceIte]
            exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
          refine ⟨st31, _, hNow,
            bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30 (bundle_runs_seq_normal ha31 hcond)),
            fun r hr _ => by simp [st31, r31, r30, r29, show r ≠ 31 by omega, show r ≠ 30 by omega, show r ≠ 29 by omega],
            by simp [st31, r31, r30, r29, hr6_i], le_refl _, by omega, hzf_i,
            hscan_eq ▸ hscan_i, hscan_eq ▸ hPin_i, hscan_eq ▸ hcnt_i, hfr_i, by omega⟩
        · -- Active edge in some unique slot j₀
          have hex : ∃ (j₀ : Fin slotCap) (B₀ : BundleState), S j₀ = some B₀ ∧ x.1 ∈ B₀.edges := by
            by_contra hno; push Not at hno
            exact hes0 ((hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x.1 hx_e).2 hno)
          obtain ⟨j₀, B₀, hSj₀, hxB₀⟩ := hex
          have hes_eq : es = j₀.1 + 1 := (hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.1 x.1 hx_e).1 j₀ B₀ hSj₀ hxB₀
          have hslotj := hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j₀
          have hSj₀' : tableDelEdges S₀ D j₀ = some B₀ := hSj₀
          rw [hSj₀'] at hslotj
          cases hm₀ : m.slotBlocks j₀ with
          | none => rw [hm₀] at hslotj; exact False.elim hslotj
          | some pb =>
            rcases pb with ⟨p, bunCap⟩
            rw [hm₀] at hslotj
            obtain ⟨hp_mem, hcandRep, _⟩ := hslotj
            obtain ⟨nB, hV, hnB, _, hbo_lt, _, hcap_m, _, _, _, _, _, _, hinC_m, _, _, _⟩ := hcandRep
            have hp_w := hblks_w j₀ p bunCap hm₀
            set b := B₀.bundleOf x
            have hb_lt : b < nB := hbo_lt x ((mem_edgeEnds _ _).mpr hxB₀)
            have hmem_p : st.mem (btSlotPtrBase tbl + j₀.1) = p :=
              (hmem_core _ (btSlotPtr_in_coreFoot j₀.2)).trans hp_mem
            have hmem_cap : st.mem p = bunCap :=
              (hmem_core _ (Or.inr ⟨j₀, p, bunCap, hm₀, le_refl _, by unfold bundleSlotBlockSize; omega⟩)).trans hcap_m
            have hmem_b : st.mem (btEndBundleBase tbl slotCap eCap + endKey x) = b :=
              (hmem_core _ (btEndBundle_in_coreFoot hkey_lt)).trans
                (hafter.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j₀ B₀ hSj₀ x ((mem_edgeEnds _ _).mpr hxB₀))
            have hmem_inC : st.mem (bsInCandBase p bunCap + b) = if b ∈ candSet j₀ then 1 else 0 :=
              (hmem_core _ (Or.inr ⟨j₀, p, bunCap, hm₀, by unfold bsInCandBase; omega,
                by unfold bsInCandBase bundleSlotBlockSize; omega⟩)).trans (hinC_m b (by omega))
            set inC := if b ∈ candSet j₀ then 1 else 0
            set r32 := Function.update r31 32 j₀.1
            set r33 := Function.update r32 33 p
            set r34 := Function.update r33 34 bunCap
            set r35 := Function.update r34 35 b
            set r36 := Function.update r35 36 inC
            set st36 : State := { st with regs := r36 }
            have hj0_lt : j₀.1 < slotCap := j₀.2
            have ha32 : Runs w pProg ω (.assign 32 (.bin .sub (.reg 31) (.const 1)))
                st31 .normal { st with regs := r32 } 4 :=
              runs_assign_iff.mpr ⟨j₀.1, by
                have hj_w : j₀.1 < 2 ^ w := by clear * - htbl_w' hj0_lt; omega
                simp [Expr.eval, BinOp.eval, st31, r31, hes_eq, h1_w, hj_w], rfl, rfl, rfl⟩
            have ha33 : Runs w pProg ω (.assign 33 (.load (.bin .add (.reg 7) (.reg 32))))
                { st with regs := r32 } .normal { st with regs := r33 } 5 :=
              runs_assign_iff.mpr ⟨p, by
                have hsp_w : btSlotPtrBase tbl + j₀.1 < 2 ^ w := by
                  unfold btSlotPtrBase; clear * - htbl_w' hj0_lt; omega
                simp [Expr.eval, BinOp.eval, r32, r31, r30, r29, hr7', hsp_w, hmem_p], rfl, rfl, rfl⟩
            have ha34 : Runs w pProg ω (.assign 34 (.load (.reg 33)))
                { st with regs := r33 } .normal { st with regs := r34 } 3 :=
              runs_assign_iff.mpr ⟨bunCap, by simp [Expr.eval, r33, hmem_cap], rfl, rfl, rfl⟩
            have ha35 : Runs w pProg ω (.assign 35 (.load (.bin .add (.reg 9) (.reg 29))))
                { st with regs := r34 } .normal { st with regs := r35 } 5 :=
              runs_assign_iff.mpr ⟨b, by
                have heb_w : btEndBundleBase tbl slotCap eCap + endKey x < 2 ^ w := by
                  unfold btEndBundleBase; clear * - htbl_w' hkey_lt; omega
                simp [Expr.eval, BinOp.eval, r34, r33, r32, r31, r30, r29, hr9', heb_w, hmem_b], rfl, rfl, rfl⟩
            have ha36 : Runs w pProg ω (.assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
                (.bin .mul (.const 4) (.reg 34))) (.reg 35))))
                { st with regs := r35 } .normal st36 11 :=
              runs_assign_iff.mpr ⟨inC, by
                unfold bundleSlotBlockSize at hp_w
                have hm_inC' : st.mem (p + 3 + 4 * bunCap + b) = inC := hmem_inC
                simp [Expr.eval, BinOp.eval, r35, r34, r33, h3_w, h4_w,
                  show p + 3 < 2 ^ w by omega, show 4 * bunCap < 2 ^ w by omega,
                  show p + 3 + 4 * bunCap < 2 ^ w by omega, show p + 3 + 4 * bunCap + b < 2 ^ w by omega,
                  hm_inC'], rfl, rfl, rfl⟩
            have hdisj_oth : ∀ j : Fin slotCap, j ≠ j₀ → ∀ B, S j = some B → x.1 ∉ B.edges :=
              fun j hne B hSj hxB => Finset.disjoint_left.mp
                (hafter.2.2.2.2.2.2.2.2.2.2.2.2.1 j j₀ hne B B₀ hSj hSj₀) hxB hxB₀
            by_cases hbc : b ∈ candSet j₀
            · -- Record node at hNow, hNow + 1, hNow + 2 and update curBun[j₀], curTag[j₀]
              have hinC1 : inC = 1 := ite_eq_left hbc
              set oldHead := st.mem (btCurBunBase tbl slotCap eCap + j₀.1)
              set oldCnt := st.mem (btCurTagBase tbl slotCap eCap + j₀.1)
              have hcb_j_w : btCurBunBase tbl slotCap eCap + j₀.1 < 2 ^ w := by
                unfold btCurBunBase; clear * - htbl_w' hj0_lt; omega
              have hct_j_w : btCurTagBase tbl slotCap eCap + j₀.1 < 2 ^ w := by
                unfold btCurTagBase; clear * - htbl_w' hj0_lt; omega
              have hpk_val_w : v * (2 * eCap) + endKey x < 2 ^ w := by
                have : (v + 1) * (2 * eCap) ≤ vCap * (2 * eCap) := Nat.mul_le_mul_right _ hv_lt
                have : v * (2 * eCap) + 2 * eCap = (v + 1) * (2 * eCap) := by ring
                omega
              have hcnt_eq : oldCnt = (addScanEndsForList S candSet v (xs.take i) scan₀ j₀).length :=
                (hscan_i j₀).2
              have hcnt_w : oldCnt + 1 < 2 ^ w := by
                have := hcnt_i j₀; omega
              set r37a := Function.update r36 37 oldHead
              set m1 := Function.update st.mem hNow b
              set m2 := Function.update m1 (hNow + 1) (packEndKey eCap v (endKey x))
              set m3 := Function.update m2 (hNow + 2) oldHead
              set m4 := Function.update m3 (btCurBunBase tbl slotCap eCap + j₀.1) hNow
              set r6' := Function.update r37a 6 (hNow + 3)
              set r37b := Function.update r6' 37 oldCnt
              set m5 := Function.update m4 (btCurTagBase tbl slotCap eCap + j₀.1) (oldCnt + 1)
              set stDone : State := { mem := m5, regs := r37b, pos := st.pos }
              have hm4_ct : m4 (btCurTagBase tbl slotCap eCap + j₀.1) = oldCnt := by
                have hne1 : btCurTagBase tbl slotCap eCap + j₀.1 ≠ btCurBunBase tbl slotCap eCap + j₀.1 := by
                  unfold btCurBunBase btCurTagBase; omega
                have hne2 : btCurTagBase tbl slotCap eCap + j₀.1 ≠ hNow + 2 := by
                  have := j₀.2; omega
                have hne3 : btCurTagBase tbl slotCap eCap + j₀.1 ≠ hNow + 1 := by
                  have := j₀.2; omega
                have hne4 : btCurTagBase tbl slotCap eCap + j₀.1 ≠ hNow := by
                  have := j₀.2; omega
                dsimp only [m4, m3, m2, m1]
                rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
                  Function.update_of_ne hne3, Function.update_of_ne hne4]
              have ha37a : Runs w pProg ω (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))))
                  st36 .normal { st36 with regs := r37a } 5 :=
                runs_assign_iff.mpr ⟨oldHead, by
                  simp [Expr.eval, BinOp.eval, st36, r36, r35, r34, r33, r32, r31, r30, r29, hr25', hcb_j_w, oldHead],
                  rfl, rfl, rfl⟩
              have hs0 : Runs w pProg ω (.store (.reg 6) (.reg 35))
                  { st36 with regs := r37a } .normal { st36 with mem := m1, regs := r37a } 3 :=
                runs_store_iff.mpr ⟨hNow, b,
                  by simp [Expr.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i],
                  by simp [Expr.eval, r37a, r36, r35], rfl, rfl, rfl⟩
              have hs1 : Runs w pProg ω (.store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)))
                  { st36 with mem := m1, regs := r37a } .normal { st36 with mem := m2, regs := r37a } 7 :=
                runs_store_iff.mpr ⟨hNow + 1, packEndKey eCap v (endKey x),
                  by simp [Expr.eval, BinOp.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i, h1_w,
                    show hNow + 1 < 2 ^ w by omega],
                  by simp [Expr.eval, BinOp.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr27',
                    packEndKey, hpk_val_w], rfl, rfl, rfl⟩
              have hs2 : Runs w pProg ω (.store (.bin .add (.reg 6) (.const 2)) (.reg 37))
                  { st36 with mem := m2, regs := r37a } .normal { st36 with mem := m3, regs := r37a } 5 :=
                runs_store_iff.mpr ⟨hNow + 2, oldHead,
                  by simp [Expr.eval, BinOp.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i, h2_w,
                    show hNow + 2 < 2 ^ w by omega],
                  by simp [Expr.eval, r37a], rfl, rfl, rfl⟩
              have hs3 : Runs w pProg ω (.store (.bin .add (.reg 25) (.reg 32)) (.reg 6))
                  { st36 with mem := m3, regs := r37a } .normal { st36 with mem := m4, regs := r37a } 5 :=
                runs_store_iff.mpr ⟨btCurBunBase tbl slotCap eCap + j₀.1, hNow,
                  by simp [Expr.eval, BinOp.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr25', hcb_j_w],
                  by simp [Expr.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i], rfl, rfl, rfl⟩
              have ha6 : Runs w pProg ω (.assign 6 (.bin .add (.reg 6) (.const 3)))
                  { st36 with mem := m4, regs := r37a } .normal { st36 with mem := m4, regs := r6' } 4 :=
                runs_assign_iff.mpr ⟨hNow + 3, by
                  simp [Expr.eval, BinOp.eval, r37a, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i, h3_w,
                    show hNow + 3 < 2 ^ w by omega], rfl, rfl, rfl⟩
              have ha37b : Runs w pProg ω (.assign 37 (.load (.bin .add (.reg 26) (.reg 32))))
                  { st36 with mem := m4, regs := r6' } .normal { st36 with mem := m4, regs := r37b } 5 :=
                runs_assign_iff.mpr ⟨oldCnt, by
                  simp [Expr.eval, BinOp.eval, r6', r37a, r36, r35, r34, r33, r32, r31, r30, r29,
                    hr26', hct_j_w, hm4_ct], rfl, rfl, rfl⟩
              have hs4 : Runs w pProg ω (.store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                  { st36 with mem := m4, regs := r37b } .normal stDone 7 :=
                runs_store_iff.mpr ⟨btCurTagBase tbl slotCap eCap + j₀.1, oldCnt + 1,
                  by simp [Expr.eval, BinOp.eval, r37b, r6', r37a, r36, r35, r34, r33, r32, r31, r30, r29,
                    hr26', hct_j_w],
                  by simp [Expr.eval, BinOp.eval, r37b, h1_w, hcnt_w], rfl, rfl, rfl⟩
              have hinner := bundle_runs_seq_normal ha37a (bundle_runs_seq_normal hs0
                (bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2
                  (bundle_runs_seq_normal hs3 (bundle_runs_seq_normal ha6
                    (bundle_runs_seq_normal ha37b hs4))))))
              have hcond36 : Runs w pProg ω (.cond (.reg 36)
                  (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
                   .store (.reg 6) (.reg 35) ;;
                   .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
                   .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
                   .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
                   .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
                   .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
                   .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                  .nop) st36 .normal stDone (1 + (5 + (3 + (7 + (5 + (5 + (4 + (5 + 7 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
                runs_cond_iff.mpr ⟨1, _, by simp [Expr.eval, st36, r36, hinC1],
                  by simpa only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] using hinner, by simp [Expr.size]⟩
              have houter := bundle_runs_seq_normal ha32 (bundle_runs_seq_normal ha33
                (bundle_runs_seq_normal ha34 (bundle_runs_seq_normal ha35
                  (bundle_runs_seq_normal ha36 hcond36))))
              have hcond31 : Runs w pProg ω (.cond (.reg 31)
                  (.assign 32 (.bin .sub (.reg 31) (.const 1)) ;;
                   .assign 33 (.load (.bin .add (.reg 7) (.reg 32))) ;;
                   .assign 34 (.load (.reg 33)) ;;
                   .assign 35 (.load (.bin .add (.reg 9) (.reg 29))) ;;
                   .assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
                     (.bin .mul (.const 4) (.reg 34))) (.reg 35))) ;;
                   .cond (.reg 36)
                     (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
                      .store (.reg 6) (.reg 35) ;;
                      .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
                      .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
                      .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
                      .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
                      .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
                      .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                     .nop)
                  .nop) st31 .normal stDone _ :=
                runs_cond_iff.mpr ⟨j₀.1 + 1, _, by simp [Expr.eval, st31, r31, hes_eq],
                  by simpa only [Nat.succ_ne_zero, ↓reduceIte] using houter, rfl⟩
              have hrunB := bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30
                (bundle_runs_seq_normal ha31 hcond31))
              have hm5_eq : ∀ a, a ≠ hNow → a ≠ hNow + 1 → a ≠ hNow + 2 →
                  a ≠ btCurBunBase tbl slotCap eCap + j₀.1 →
                  a ≠ btCurTagBase tbl slotCap eCap + j₀.1 → m5 a = st.mem a := by
                intro a h1 h2 h3 h4 h5; simp [m5, m4, m3, m2, m1, h1, h2, h3, h4, h5]
              have hcurB_lt_hStart : btCurBunBase tbl slotCap eCap + slotCap ≤ hStart := by
                unfold btCurBunBase; unfold btCurTagBase at hcur_lt_hStart; omega
              have hheap_eq : ∀ a, hStart ≤ a → a < hNow → m5 a = st.mem a := fun a ha1 ha2 =>
                hm5_eq a (by omega) (by omega) (by omega)
                  (by have := j₀.2; omega) (by have := j₀.2; omega)
              have hscan_next : SlotScanListAt slotCap eCap tbl m5 hStart (hNow + 3)
                  (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀) ∧
                  ∀ j : Fin slotCap, ScanNodesIn m5 P (m5 (btCurBunBase tbl slotCap eCap + j.1))
                    (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j) := by
                have hall : ∀ j : Fin slotCap,
                    (ScanNodesAt eCap m5 hStart (hNow + 3) (m5 (btCurBunBase tbl slotCap eCap + j.1))
                      (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j) ∧
                     m5 (btCurTagBase tbl slotCap eCap + j.1) =
                      (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j).length) ∧
                    ScanNodesIn m5 P (m5 (btCurBunBase tbl slotCap eCap + j.1))
                      (addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ j) := by
                  intro j
                  rw [htake_eq]
                  by_cases hjj : j = j₀
                  · subst hjj
                    have hxB₀' : (xs[i]'hi).1 ∈ B₀.edges := hxB₀
                    have hbc' : B₀.bundleOf (xs[i]'hi) ∈ candSet j := hbc
                    simp only [hSj₀, hxB₀', hbc', and_self, ↓reduceIte]
                    have hcb_m5 : m5 (btCurBunBase tbl slotCap eCap + j.1) = hNow := by
                      have hne : btCurBunBase tbl slotCap eCap + j.1 ≠ btCurTagBase tbl slotCap eCap + j.1 := by
                        unfold btCurBunBase btCurTagBase; omega
                      dsimp only [m5, m4]
                      rw [Function.update_of_ne hne, Function.update_self]
                    have hct_m5 : m5 (btCurTagBase tbl slotCap eCap + j.1) = oldCnt + 1 := by
                      simp [m5]
                    have hm5_0 : m5 hNow = b := by
                      have := j.2
                      simp [m5, m4, m3, m2, m1,
                        show hNow ≠ btCurTagBase tbl slotCap eCap + j.1 by omega,
                        show hNow ≠ btCurBunBase tbl slotCap eCap + j.1 by omega]
                    have hm5_1 : m5 (hNow + 1) = packEndKey eCap v (endKey x) := by
                      have := j.2
                      simp [m5, m4, m3, m2,
                        show hNow + 1 ≠ btCurTagBase tbl slotCap eCap + j.1 by omega,
                        show hNow + 1 ≠ btCurBunBase tbl slotCap eCap + j.1 by omega]
                    have hm5_2 : m5 (hNow + 2) = oldHead := by
                      have := j.2
                      simp [m5, m4, m3,
                        show hNow + 2 ≠ btCurTagBase tbl slotCap eCap + j.1 by omega,
                        show hNow + 2 ≠ btCurBunBase tbl slotCap eCap + j.1 by omega]
                    obtain ⟨hsn', hpin'⟩ := scanNodesAt_mono_of_in (hi' := hNow + 3) (hscan_i j).1 (hPin_i j) (by omega)
                      (fun a ha1 ha2 _ => hheap_eq a ha1 ha2) (fun _ _ _ hp => hp)
                    refine ⟨⟨?_, by rw [hct_m5, hcnt_eq]; rfl⟩, ?_⟩
                    · rw [hcb_m5]
                      refine ⟨by omega, by omega, hm5_0, hm5_1, ?_⟩
                      rw [hm5_2]; exact hsn'
                    · rw [hcb_m5]
                      refine ⟨hPnew hNow (by omega), hPnew (hNow + 1) (by omega), hPnew (hNow + 2) (by omega), ?_⟩
                      rw [hm5_2]; exact hpin'
                  · have hcb_m5 : m5 (btCurBunBase tbl slotCap eCap + j.1) =
                        st.mem (btCurBunBase tbl slotCap eCap + j.1) := by
                      have hne1 : btCurBunBase tbl slotCap eCap + j.1 ≠ btCurBunBase tbl slotCap eCap + j₀.1 := by
                        intro h; exact hjj (Fin.ext (by omega))
                      have hne2 : btCurBunBase tbl slotCap eCap + j.1 ≠ btCurTagBase tbl slotCap eCap + j₀.1 := by
                        unfold btCurBunBase btCurTagBase; have := j.2; omega
                      exact hm5_eq _
                        (by have := j.2; omega) (by have := j.2; omega) (by have := j.2; omega)
                        hne1 hne2
                    have hct_m5 : m5 (btCurTagBase tbl slotCap eCap + j.1) =
                        st.mem (btCurTagBase tbl slotCap eCap + j.1) := by
                      have hne1 : btCurTagBase tbl slotCap eCap + j.1 ≠ btCurBunBase tbl slotCap eCap + j₀.1 := by
                        unfold btCurBunBase btCurTagBase; have := j₀.2; omega
                      have hne2 : btCurTagBase tbl slotCap eCap + j.1 ≠ btCurTagBase tbl slotCap eCap + j₀.1 := by
                        intro h; exact hjj (Fin.ext (by omega))
                      exact hm5_eq _ (by have := j.2; omega) (by have := j.2; omega) (by have := j.2; omega)
                        hne1 hne2
                    have hno : ∀ B, S j = some B → ¬ ((xs[i]'hi).1 ∈ B.edges ∧ B.bundleOf (xs[i]'hi) ∈ candSet j) :=
                      fun B hSj hc => hdisj_oth j hjj B hSj hc.1
                    obtain ⟨hsn', hpin'⟩ := scanNodesAt_mono_of_in (hi' := hNow + 3) (hscan_i j).1 (hPin_i j) (by omega)
                      (fun a ha1 ha2 _ => hheap_eq a ha1 ha2) (fun _ _ _ hp => hp)
                    dsimp only
                    cases hSj : S j with
                    | none =>
                      simp only [hcb_m5, hct_m5]
                      exact ⟨⟨hsn', (hscan_i j).2⟩, hpin'⟩
                    | some B =>
                      simp only [hno B hSj, ↓reduceIte, hcb_m5, hct_m5]
                      exact ⟨⟨hsn', (hscan_i j).2⟩, hpin'⟩
                exact ⟨fun j => (hall j).1, fun j => (hall j).2⟩
              refine ⟨stDone, _, hNow + 3, hrunB,
                fun r hr hne6 => by
                  simp [stDone, r37b, r6', r37a, r36, r35, r34, r33, r32, r31, r30, r29, hne6,
                    show r ≠ 37 by omega, show r ≠ 36 by omega, show r ≠ 35 by omega, show r ≠ 34 by omega,
                    show r ≠ 33 by omega, show r ≠ 32 by omega, show r ≠ 31 by omega, show r ≠ 30 by omega,
                    show r ≠ 29 by omega],
                by simp [stDone, r37b, r6'], by omega, by omega,
                fun a ha => (hm5_eq a (by omega) (by omega) (by omega)
                  (by have := j₀.2; omega) (by have := j₀.2; omega)).trans (hzf_i a (by omega)),
                hscan_next.1, hscan_next.2,
                fun j => by
                  rw [htake_eq]; have h1 := hcnt_i j
                  cases hSj : S j with
                  | none => simp only [hSj]; omega
                  | some B => simp only [hSj]; split_ifs <;> simp <;> omega,
                fun a hnc hnh =>
                  (hm5_eq a (by omega) (by omega) (by omega)
                    (by unfold btCurBunBase btCurTagBase at hnc; unfold btCurBunBase; have := j₀.2; omega)
                    (by unfold btCurBunBase btCurTagBase at hnc; unfold btCurTagBase; have := j₀.2; omega)).trans
                  (hfr_i a hnc (by omega)),
                by simp only [Expr.size]; omega⟩
            · -- b ∉ candSet j₀: skip
              have hinC0 : inC = 0 := ite_eq_right hbc
              have hscan_eq : addScanEndsForList S candSet v (xs.take (i + 1)) scan₀ =
                  addScanEndsForList S candSet v (xs.take i) scan₀ := by
                rw [htake_eq]; funext j
                by_cases hjj : j = j₀
                · subst hjj
                  have hnb : B₀.bundleOf (xs[i]'hi) ∉ candSet j := hbc
                  simp [hSj₀, hnb]
                · cases hSj : S j with
                  | none => rfl
                  | some B =>
                    have hne : (xs[i]'hi).1 ∉ B.edges := hdisj_oth j hjj B hSj
                    dsimp only; simp [hne]
              have hnop36 : Runs w pProg ω .nop st36 .normal st36 1 :=
                runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩
              have hcond36 : Runs w pProg ω (.cond (.reg 36)
                  (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
                   .store (.reg 6) (.reg 35) ;;
                   .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
                   .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
                   .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
                   .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
                   .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
                   .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                  .nop) st36 .normal st36 3 :=
                runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, st36, r36, hinC0],
                  by simpa only [↓reduceIte] using hnop36, by simp [Expr.size]⟩
              have houter := bundle_runs_seq_normal ha32 (bundle_runs_seq_normal ha33
                (bundle_runs_seq_normal ha34 (bundle_runs_seq_normal ha35
                  (bundle_runs_seq_normal ha36 hcond36))))
              have hcond31 : Runs w pProg ω (.cond (.reg 31)
                  (.assign 32 (.bin .sub (.reg 31) (.const 1)) ;;
                   .assign 33 (.load (.bin .add (.reg 7) (.reg 32))) ;;
                   .assign 34 (.load (.reg 33)) ;;
                   .assign 35 (.load (.bin .add (.reg 9) (.reg 29))) ;;
                   .assign 36 (.load (.bin .add (.bin .add (.bin .add (.reg 33) (.const 3))
                     (.bin .mul (.const 4) (.reg 34))) (.reg 35))) ;;
                   .cond (.reg 36)
                     (.assign 37 (.load (.bin .add (.reg 25) (.reg 32))) ;;
                      .store (.reg 6) (.reg 35) ;;
                      .store (.bin .add (.reg 6) (.const 1)) (.bin .add (.reg 27) (.reg 29)) ;;
                      .store (.bin .add (.reg 6) (.const 2)) (.reg 37) ;;
                      .store (.bin .add (.reg 25) (.reg 32)) (.reg 6) ;;
                      .assign 6 (.bin .add (.reg 6) (.const 3)) ;;
                      .assign 37 (.load (.bin .add (.reg 26) (.reg 32))) ;;
                      .store (.bin .add (.reg 26) (.reg 32)) (.bin .add (.reg 37) (.const 1)))
                     .nop)
                  .nop) st31 .normal st36 _ :=
                runs_cond_iff.mpr ⟨j₀.1 + 1, _, by simp [Expr.eval, st31, r31, hes_eq],
                  by simpa only [Nat.succ_ne_zero, ↓reduceIte] using houter, rfl⟩
              have hrunB := bundle_runs_seq_normal ha29 (bundle_runs_seq_normal ha30
                (bundle_runs_seq_normal ha31 hcond31))
              refine ⟨st36, _, hNow, hrunB,
                fun r hr _ => by
                  simp [st36, r36, r35, r34, r33, r32, r31, r30, r29,
                    show r ≠ 36 by omega, show r ≠ 35 by omega, show r ≠ 34 by omega, show r ≠ 33 by omega,
                    show r ≠ 32 by omega, show r ≠ 31 by omega, show r ≠ 30 by omega, show r ≠ 29 by omega],
                by simp [st36, r36, r35, r34, r33, r32, r31, r30, r29, hr6_i], le_refl _, by omega,
                hzf_i, hscan_eq ▸ hscan_i, hscan_eq ▸ hPin_i, hscan_eq ▸ hcnt_i, hfr_i, by simp only [Expr.size]; omega⟩
      obtain ⟨stB, cB, hNext, hrunB, hregsB, hr6B, hloB, hhiB, hzfB, hscanB, hPinB, hcntB, hfrB, hcB⟩ := hbody_step
      set stInc : State := { stB with regs := Function.update stB.regs 28 (i + 1) }
      have hinc : Runs w pProg ω (.assign 28 (.bin .add (.reg 28) (.const 1))) stB .normal stInc 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp [Expr.eval, BinOp.eval, hregsB 28 (by decide) (by decide), hr28_i, h1_w,
            show i + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
      have hInvNext : Inv (i + 1) hNext stInc :=
        ⟨fun r hr hne6 => by
            simp only [stInc, Function.update_of_ne (show r ≠ 28 by omega)]
            exact (hregsB r (by omega) hne6).trans (hregs r hr hne6),
          by simp [stInc, hr6B], by simp [stInc], by omega, by omega, hzfB, hscanB, hPinB, hcntB, hfrB⟩
      obtain ⟨stEnd, cEnd, hEnd, hrest, hIEnd, hcEnd⟩ := ih (i + 1) (by omega) hNext stInc hInvNext
      have hcond1 : Expr.eval w st (.bin .lt (.reg 28) (.reg 22)) = some 1 := by
        simp [Expr.eval, BinOp.eval, hr28_i, hr22', hi, h1_w]
      have hrunLoop := runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, stInc, cB + 4 + 1, cEnd, hcond1,
        by decide, bundle_runs_seq_normal hrunB hinc, hrest, rfl⟩))
      refine ⟨stEnd, _, hEnd, hrunLoop, hIEnd, ?_⟩
      simp only [Expr.size] at *
      omega
  set st0L : State := { stH with regs := Function.update stH.regs 28 0 }
  have ha28 : Runs w pProg ω (.assign 28 (.const 0)) stH .normal st0L 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hInv0 : Inv 0 hCur st0L :=
    ⟨fun r hr _ => by simp [st0L, show r ≠ 28 by omega],
      by simp [st0L, stH, r27, r26, r25, r24, r23, hr6], by simp [st0L],
      le_refl _, by omega, hzero, by simpa [addScanEndsForList_nil] using hscan₀,
      by simpa [addScanEndsForList_nil] using hPin₀,
      by simpa [addScanEndsForList_nil] using hcnt_le, fun _ _ _ => rfl⟩
  obtain ⟨stEnd, cEnd, hEnd, hrunL, hIEnd, hcEnd⟩ := hloop xs.length 0 (by omega) hCur st0L hInv0
  have hrunAll := bundle_runs_seq_normal ha23 (bundle_runs_seq_normal ha24
    (bundle_runs_seq_normal ha25 (bundle_runs_seq_normal ha26
      (bundle_runs_seq_normal ha27 (bundle_runs_seq_normal ha28 hrunL)))))
  rcases hIEnd with ⟨hregsE, hr6E, _, hloE, hhiE, hzfE, hscanE, hPinE, hcntE, hfrE⟩
  rw [List.take_length] at hscanE hPinE hcntE
  exact ⟨stEnd, _, hEnd, hrunAll,
    fun r hr hne6 => by
      rw [hregsE r (by omega) hne6]
      simp [stH, r27, r26, r25, r24, r23, show r ≠ 27 by omega, show r ≠ 26 by omega,
        show r ≠ 25 by omega, show r ≠ 24 by omega, show r ≠ 23 by omega],
    hr6E, hloE, hhiE, hzfE, hscanE, hPinE, hcntE, hfrE, by omega⟩

end

end MinCostFlow.SparseCore.Program
