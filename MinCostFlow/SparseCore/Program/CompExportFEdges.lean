module

public import MinCostFlow.SparseCore.Program.CompExportBase
import WordRAM.Tactic

/-!
# Branch Forest-Edge Export Loop (`CompExportFEdges`)

Implements and verifies `compExpFEdgesStmt` for `op 6` (`compExportBranchProc`):
iterates `ec = 0 .. numEdgeful - 1` and emits all triples `(e, F.tail e, F.head e)` of
`(S j).RF.F.E` contiguously at `fEPtr` in `O(numEdgeful + F.m)` time.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Inner loop of `compExpFEdgesStmt`: emits all `mF` edge triples `(e, F.tail e, F.head e)` of
one edgeful component's forest `dgF` starting at `r3 + 3 * r4`, advancing `r4`. -/
def compExpFEdgesInnerStmt : Stmt :=
  .loop (.bin .lt (.reg 17) (.reg 11))
    (.assign 18 (.load (.bin .add (.reg 14) (.reg 17))) ;;
     .assign 19 (.load (.bin .add (.reg 15) (.reg 18))) ;;
     .assign 19 (.load (.bin .add (.reg 13) (.reg 19))) ;;
     .assign 20 (.load (.bin .add (.reg 16) (.reg 18))) ;;
     .assign 20 (.load (.bin .add (.reg 13) (.reg 20))) ;;
     .store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 18) ;;
     .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 19) ;;
     .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20) ;;
     .assign 4 (.bin .add (.reg 4) (.const 1)) ;;
     .assign 17 (.bin .add (.reg 17) (.const 1)))

/-- Iterate `ec = 0 .. numEdgeful - 1` and emit all triples `(e, F.tail e, F.head e)` of
`(S j).RF.F.E` starting at `r3 = fEPtr`, accumulating `r4 = fCount` (`(S j).RF.F.m`).
Inputs: `r0 = b`, `r1 = j`, `r2 = k`, `r3 = fEPtr`. Preserves `r0..r3`; writes `r4 = (S j).RF.F.m`.
Uses scratch registers `5..20`. -/
def compExpFEdgesStmt : Stmt :=
  .assign 4 (.const 0) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffNumEdgeful))) ;;
  .assign 6 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr))) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 8 (.const 0) ;;
  .loop (.bin .lt (.reg 8) (.reg 5))
    (.assign 9 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 8) (.reg 2)) (.reg 1)))) ;;
     .assign 10 (.load (.bin .add (.reg 9) (.const lsfOffDgFPtr))) ;;
     .assign 11 (.load (.bin .add (.reg 10) (.const dgMOff))) ;;
     .assign 12 (.load (.bin .add (.reg 10) (.const dgECapOff))) ;;
     .assign 13 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 7))) ;;
     .assign 14 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7))) (.reg 12)) ;;
     .assign 15 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
       (.bin .mul (.const 3) (.reg 12))) ;;
     .assign 16 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
       (.bin .mul (.const 4) (.reg 12))) ;;
     .assign 17 (.const 0) ;;
     compExpFEdgesInnerStmt ;;
     .assign 8 (.bin .add (.reg 8) (.const 1)))

lemma compExpFEdgesStmt_noRand : compExpFEdgesStmt.NoRand := by
  simp [compExpFEdgesStmt, compExpFEdgesInnerStmt, Stmt.NoRand]

set_option maxHeartbeats 800000 in
private lemma compExpFEdgesInner_runs {w dgFPtr vCap eCapF fEPtr baseCnt : ℕ}
    {p : Program} {F : MGraph} {eL : List ℕ} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hdgF : DynGraphAt st.mem dgFPtr vCap eCapF F)
    (heL_len : eL.length = F.m) (heL_nd : eL.Nodup) (heL_mem : ∀ e, e ∈ eL ↔ e ∈ F.E)
    (heL_at : ListAt st.mem (dgEListBase dgFPtr vCap eCapF) eL)
    (hdisj : dgFPtr + dynGraphSize vCap eCapF ≤ fEPtr)
    (hcnt_w : fEPtr + 3 * (baseCnt + F.m) < 2 ^ w)
    (hr3 : st.regs 3 = fEPtr) (hr4 : st.regs 4 = baseCnt)
    (hr11 : st.regs 11 = F.m) (hr13 : st.regs 13 = dgIntToExtBase dgFPtr vCap)
    (hr14 : st.regs 14 = dgEListBase dgFPtr vCap eCapF)
    (hr15 : st.regs 15 = dgETailSlotBase dgFPtr vCap eCapF)
    (hr16 : st.regs 16 = dgEHeadSlotBase dgFPtr vCap eCapF)
    (hr17 : st.regs 17 = 0) :
    ∃ st' c,
      Runs w p ω compExpFEdgesInnerStmt st .normal st' c ∧
      (∀ r < 17, r ≠ 4 → st'.regs r = st.regs r) ∧
      st'.regs 4 = baseCnt + F.m ∧
      (∀ i (hi : i < F.m),
        let e := eL[i]'(heL_len.symm ▸ hi)
        st'.mem (fEPtr + 3 * (baseCnt + i)) = e ∧
        st'.mem (fEPtr + 3 * (baseCnt + i) + 1) = F.tail e ∧
        st'.mem (fEPtr + 3 * (baseCnt + i) + 2) = F.head e) ∧
      (∀ a, a < fEPtr + 3 * baseCnt ∨ fEPtr + 3 * (baseCnt + F.m) ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 80 * F.m + 5 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hloop : ∀ rem i (s : State) (hi : i ≤ F.m), F.m - i = rem →
      (∀ r < 17, r ≠ 4 → s.regs r = st.regs r) →
      s.regs 4 = baseCnt + i → s.regs 17 = i →
      (∀ q (hq : q < i),
        let e := eL[q]'(heL_len.symm ▸ (by omega))
        s.mem (fEPtr + 3 * (baseCnt + q)) = e ∧
        s.mem (fEPtr + 3 * (baseCnt + q) + 1) = F.tail e ∧
        s.mem (fEPtr + 3 * (baseCnt + q) + 2) = F.head e) →
      (∀ a, a < fEPtr + 3 * baseCnt ∨ fEPtr + 3 * (baseCnt + i) ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω compExpFEdgesInnerStmt s .normal st' c ∧
        (∀ r < 17, r ≠ 4 → st'.regs r = st.regs r) ∧
        st'.regs 4 = baseCnt + F.m ∧
        (∀ q (hq : q < F.m),
          let e := eL[q]'(heL_len.symm ▸ hq)
          st'.mem (fEPtr + 3 * (baseCnt + q)) = e ∧
          st'.mem (fEPtr + 3 * (baseCnt + q) + 1) = F.tail e ∧
          st'.mem (fEPtr + 3 * (baseCnt + q) + 2) = F.head e) ∧
        (∀ a, a < fEPtr + 3 * baseCnt ∨ fEPtr + 3 * (baseCnt + F.m) ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 80 * rem + 5 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr_o hr4_s hr17_s hdone hfr
      have hi_eq : i = F.m := by omega
      subst hi_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr17_s,
        hr_o 11 (by omega) (by omega), hr11], rfl, rfl, by simp [Expr.size]⟩),
        hr_o, hr4_s, hdone, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr_o hr4_s hr17_s hdone hfr
      have hi_lt : i < F.m := by omega
      have hi_eL : i < eL.length := by omega
      set e := eL[i]'hi_eL
      have heF : e ∈ F.E := (heL_mem e).mp (List.getElem_mem hi_eL)
      have he_lt : e < eCapF := hdgF.2.2.1 e heF
      have he_ends := hdgF.1 e heF
      have ht_slot_eq : st.mem (dgETailSlotBase dgFPtr vCap eCapF + e) =
          st.mem (dgExtToIntBase dgFPtr vCap + F.tail e) :=
        (hdgF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heF).1
      have hh_slot_eq : st.mem (dgEHeadSlotBase dgFPtr vCap eCapF + e) =
          st.mem (dgExtToIntBase dgFPtr vCap + F.head e) :=
        (hdgF.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e heF).2
      set sT := st.mem (dgExtToIntBase dgFPtr vCap + F.tail e)
      set sH := st.mem (dgExtToIntBase dgFPtr vCap + F.head e)
      have hsT_lt : sT < vCap := hdgF.2.1 sT (hdgF.2.2.2.2.2.2.2.2.2.1 _ he_ends.1).1
      have hsH_lt : sH < vCap := hdgF.2.1 sH (hdgF.2.2.2.2.2.2.2.2.2.1 _ he_ends.2).1
      have hi2eT : st.mem (dgIntToExtBase dgFPtr vCap + sT) = F.tail e :=
        (hdgF.2.2.2.2.2.2.2.2.2.1 _ he_ends.1).2
      have hi2eH : st.mem (dgIntToExtBase dgFPtr vCap + sH) = F.head e :=
        (hdgF.2.2.2.2.2.2.2.2.2.1 _ he_ends.2).2
      have hFm_le : F.m ≤ eCapF := by
        have hsub : F.E ⊆ Finset.range eCapF := fun x hx => Finset.mem_range.mpr (hdgF.2.2.1 x hx)
        simpa [MGraph.m] using Finset.card_le_card hsub
      have hs_below : ∀ a < dgFPtr + dynGraphSize vCap eCapF, s.mem a = st.mem a :=
        fun a ha => hfr a (Or.inl (by omega))
      have hdg_lt : dgFPtr + dynGraphSize vCap eCapF < 2 ^ w := by omega
      have ha_eL : dgEListBase dgFPtr vCap eCapF + i < dgFPtr + dynGraphSize vCap eCapF := by
        dsimp only [dgEListBase, dynGraphSize]; omega
      have ha_ts : dgETailSlotBase dgFPtr vCap eCapF + e < dgFPtr + dynGraphSize vCap eCapF := by
        dsimp only [dgETailSlotBase, dynGraphSize]; omega
      have ha_hs : dgEHeadSlotBase dgFPtr vCap eCapF + e < dgFPtr + dynGraphSize vCap eCapF := by
        dsimp only [dgEHeadSlotBase, dynGraphSize]; omega
      have ha_iT : dgIntToExtBase dgFPtr vCap + sT < dgFPtr + dynGraphSize vCap eCapF := by
        dsimp only [dgIntToExtBase, dynGraphSize]; omega
      have ha_iH : dgIntToExtBase dgFPtr vCap + sH < dgFPtr + dynGraphSize vCap eCapF := by
        dsimp only [dgIntToExtBase, dynGraphSize]; omega
      set idx := baseCnt + i
      let a1 : State := { s with regs := Function.update s.regs 18 e }
      let a2 : State := { a1 with regs := Function.update a1.regs 19 sT }
      let a3 : State := { a2 with regs := Function.update a2.regs 19 (F.tail e) }
      let a4 : State := { a3 with regs := Function.update a3.regs 20 sH }
      let a5 : State := { a4 with regs := Function.update a4.regs 20 (F.head e) }
      let m1 := Function.update s.mem (fEPtr + 3 * idx) e
      let m2 := Function.update m1 (fEPtr + 3 * idx + 1) (F.tail e)
      let m3 := Function.update m2 (fEPtr + 3 * idx + 2) (F.head e)
      let b1 : State := { a5 with mem := m1 }
      let b2 : State := { b1 with mem := m2 }
      let b3 : State := { b2 with mem := m3 }
      let b4 : State := { b3 with regs := Function.update b3.regs 4 (idx + 1) }
      let b5 : State := { b4 with regs := Function.update b4.regs 17 (i + 1) }
      have h3idx : 3 * idx < 2 ^ w := by omega
      have hidx0 : fEPtr + 3 * idx < 2 ^ w := by omega
      have hidx1 : fEPtr + 3 * idx + 1 < 2 ^ w := by omega
      have hidx2 : fEPtr + 3 * idx + 2 < 2 ^ w := by omega
      have ha1 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 14) (.reg 17)))) s .normal a1 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_o 14 (by omega) (by omega), hr14, hr17_s,
            show dgEListBase dgFPtr vCap eCapF + i < 2 ^ w by omega])
          ((hs_below _ ha_eL).trans (heL_at i hi_eL)), rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 15) (.reg 18)))) a1 .normal a2 5 :=
        runs_assign_iff.mpr ⟨sT, Expr.eval_load_of_eq (by
          simp [a1, Expr.eval, BinOp.eval, hr_o 15 (by omega) (by omega), hr15,
            show dgETailSlotBase dgFPtr vCap eCapF + e < 2 ^ w by omega])
          ((hs_below _ ha_ts).trans ht_slot_eq), rfl, rfl, by simp [Expr.size]⟩
      have ha3 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 13) (.reg 19)))) a2 .normal a3 5 :=
        runs_assign_iff.mpr ⟨F.tail e, Expr.eval_load_of_eq (by
          simp [a2, a1, Expr.eval, BinOp.eval, hr_o 13 (by omega) (by omega), hr13,
            show dgIntToExtBase dgFPtr vCap + sT < 2 ^ w by omega])
          ((hs_below _ ha_iT).trans hi2eT), rfl, rfl, by simp [Expr.size]⟩
      have ha4 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 16) (.reg 18)))) a3 .normal a4 5 :=
        runs_assign_iff.mpr ⟨sH, Expr.eval_load_of_eq (by
          simp [a3, a2, a1, Expr.eval, BinOp.eval, hr_o 16 (by omega) (by omega), hr16,
            show dgEHeadSlotBase dgFPtr vCap eCapF + e < 2 ^ w by omega])
          ((hs_below _ ha_hs).trans hh_slot_eq), rfl, rfl, by simp [Expr.size]⟩
      have ha5 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 13) (.reg 20)))) a4 .normal a5 5 :=
        runs_assign_iff.mpr ⟨F.head e, Expr.eval_load_of_eq (by
          simp [a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 13 (by omega) (by omega), hr13,
            show dgIntToExtBase dgFPtr vCap + sH < 2 ^ w by omega])
          ((hs_below _ ha_iH).trans hi2eH), rfl, rfl, by simp [Expr.size]⟩
      have hb1 : Runs w p ω (.store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 18)) a5 .normal b1 7 :=
        runs_store_iff.mpr ⟨fEPtr + 3 * idx, e,
          by simp [a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw3, h3idx, hidx0, idx],
          by simp [a5, a4, a3, a2, a1, Expr.eval], by simp [b1, a5, a4, a3, a2, a1, m1], rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 19)) b1 .normal b2 9 :=
        runs_store_iff.mpr ⟨fEPtr + 3 * idx + 1, F.tail e,
          by simp [b1, a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw1, hw3, h3idx, hidx0, hidx1, idx],
          by simp [b1, a5, a4, a3, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20)) b2 .normal b3 9 :=
        runs_store_iff.mpr ⟨fEPtr + 3 * idx + 2, F.head e,
          by simp [b2, b1, a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw2, hw3, h3idx, hidx0, hidx2, idx],
          by simp [b2, b1, a5, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
      have hb4 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) b3 .normal b4 4 :=
        runs_assign_iff.mpr ⟨idx + 1, by simp [b3, b2, b1, a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr4_s, hw1,
          show idx + 1 < 2 ^ w by omega, idx], rfl, rfl, by simp [Expr.size]⟩
      have hb5 : Runs w p ω (.assign 17 (.bin .add (.reg 17) (.const 1))) b4 .normal b5 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [b4, b3, b2, b1, a5, a4, a3, a2, a1, Expr.eval, BinOp.eval, hr17_s, hw1,
          show i + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal b5 67 :=
        runs_seq_iff.mpr (Or.inr ⟨a1, 5, _, ha1, runs_seq_iff.mpr (Or.inr ⟨a2, 5, _, ha2,
          runs_seq_iff.mpr (Or.inr ⟨a3, 5, _, ha3, runs_seq_iff.mpr (Or.inr ⟨a4, 5, _, ha4,
          runs_seq_iff.mpr (Or.inr ⟨a5, 5, _, ha5, runs_seq_iff.mpr (Or.inr ⟨b1, 7, _, hb1,
          runs_seq_iff.mpr (Or.inr ⟨b2, 9, _, hb2, runs_seq_iff.mpr (Or.inr ⟨b3, 9, _, hb3,
          runs_seq_iff.mpr (Or.inr ⟨b4, 4, 4, hb4, hb5, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
      obtain ⟨st', cRest, hrest, hr'_o, hr'_4, hdone', hfr', hcRest⟩ :=
        ih (i + 1) b5 (by omega) (by omega)
          (fun r hr hne4 => by simp [b5, b4, b3, b2, b1, a5, a4, a3, a2, a1, hne4,
            show r ≠ 17 by omega, show r ≠ 18 by omega, show r ≠ 19 by omega, show r ≠ 20 by omega, hr_o r hr hne4])
          (by simp [b5, b4, idx]; omega) (by simp [b5])
          (fun q hq => by
            dsimp only [b5, b4, b3, m3, m2, m1]
            by_cases hqi : q = i
            · subst hqi; simp [idx, e, Function.update_of_ne (by omega : fEPtr + 3 * idx ≠ fEPtr + 3 * idx + 2),
                Function.update_of_ne (by omega : fEPtr + 3 * idx ≠ fEPtr + 3 * idx + 1),
                Function.update_of_ne (by omega : fEPtr + 3 * idx + 1 ≠ fEPtr + 3 * idx + 2)]
            · have hqlt : q < i := by omega
              rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                  Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
              exact hdone q hqlt)
          (fun a ha => by
            dsimp only [b5, b4, b3, m3, m2, m1]
            rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact hfr a (by omega))
      have hfull : Runs w p ω compExpFEdgesInnerStmt s .normal st' (67 + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, b5, 67, cRest,
          by simp [Expr.eval, BinOp.eval, hr17_s, hr_o 11 (by omega) (by omega), hr11, hi_lt, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 67 + cRest + 4, hfull, hr'_o, hr'_4, hdone', hfr', by omega⟩
  exact hloop F.m 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ _ => rfl) hr4 hr17
    (fun _ h => by omega) (fun _ _ => rfl)

set_option maxHeartbeats 800000 in
open Classical in
/-- Verification of `compExpFEdgesStmt`: emits all `(S j).RF.F.m` edge triples of `(S j).RF.F.E`
contiguously at `fEPtr`, sets `reg 4 = (S j).RF.F.m`, preserves memory outside
`[fEPtr, fEPtr + 3 * (S j).RF.F.m)`, and runs in `≤ 85 * (S j).RF.F.m + 95 * x.numEdgeful + 35`
steps. -/
theorem compExpFEdges_runs {W : LSFWindowImpl} {w k b fEPtr : ℕ}
    {p : Program} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {st : State} {ω : ℕ → Bool} (j : Fin k)
    (hw16 : 16 ≤ 2 ^ w)
    (hrep : CompLSFRepAt W k b S x st.mem)
    (hend_le : x.endAddr ≤ fEPtr)
    (hbuf_w : fEPtr + 3 * x.m0Total < 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = j.1) (hr2 : st.regs 2 = k) (hr3 : st.regs 3 = fEPtr) :
    ∃ st' c, ∃ eF : List (ℕ × ℕ × ℕ),
      Runs w p ω compExpFEdgesStmt st .normal st' c ∧
      (∀ r < 4, st'.regs r = st.regs r) ∧
      st'.regs 4 = (S j).RF.F.m ∧
      eF.length = (S j).RF.F.m ∧
      (eF.map Prod.fst).Nodup ∧
      (∀ t ∈ eF, t.1 ∈ (S j).RF.F.E ∧ t.2.1 = (S j).RF.F.tail t.1 ∧ t.2.2 = (S j).RF.F.head t.1) ∧
      (∀ e ∈ (S j).RF.F.E, ∃ t ∈ eF, t.1 = e) ∧
      (∀ i (hi : i < eF.length),
        st'.mem (fEPtr + 3 * i) = eF[i].1 ∧
        st'.mem (fEPtr + 3 * i + 1) = eF[i].2.1 ∧
        st'.mem (fEPtr + 3 * i + 2) = eF[i].2.2) ∧
      (∀ a, a < fEPtr ∨ fEPtr + 3 * (S j).RF.F.m ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 85 * (S j).RF.F.m + 95 * x.numEdgeful + 35 := by
  obtain ⟨hk, _, _, _, _, _, _, _, hnumEf, hTE, hhdr, ⟨ℓ₀, hBr⟩, hm0Tot, hT,
    hCompMeta, hEfMeta, _, _, _, _, _, _, hWins, _⟩ := hrep
  have hIj := (hBr j).1
  have hS_G0 := (hBr j).2.1
  have ⟨hFE_eq, hF_ends, hF_disj, hFm_le⟩ := compLSF_F_eq_edgeful hIj
  have hFm_le_m0 : (S j).RF.F.m ≤ x.m0Total := by rw [← hm0Tot, ← hS_G0]; exact hFm_le
  have hefComp_inj : Function.Injective x.edgefulComp := fun ec₁ ec₂ heq => by
    have h1 := (hEfMeta ec₁).2; have h2 := (hEfMeta ec₂).2; rw [heq] at h1; exact Fin.ext (h1.symm.trans h2)
  have hbij_ef : ∀ C, C ∈ edgefulComps (S j).G₀ ↔ ∃ ec : Fin x.numEdgeful, x.compOf (x.edgefulComp ec) = C := fun C => by
    simp only [edgefulComps, Finset.mem_filter, hS_G0]
    constructor
    · rintro ⟨hC, hpos⟩
      obtain ⟨c, rfl⟩ := (hT.hBij.2 C).mp hC
      obtain ⟨ec, _, _, hcomp⟩ := (hCompMeta c).2.2.2 hpos
      exact ⟨ec, congrArg x.compOf hcomp⟩
    · rintro ⟨ec, rfl⟩
      exact ⟨hT.compOf_mem _, (hEfMeta ec).1⟩
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hb_off : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  -- Extract canonical `eL` for each edgeful component `ec` from its `dgF`
  have heL_ex : ∀ ec : Fin x.numEdgeful,
      let C := x.compOf (x.edgefulComp ec)
      let hWin := x.winHandle ec j
      let xWin := x.winConc ec j
      let dgFPtr := lsfDgFPtr hWin xWin.vCap xWin.eCap xWin.tM
      let F := ((S j).compSt C).RF.F
      ∃ eL : List ℕ, eL.length = F.m ∧ eL.Nodup ∧ (∀ e, e ∈ eL ↔ e ∈ F.E) ∧
        ListAt st.mem (dgEListBase dgFPtr xWin.vCap (fECap xWin.eCap xWin.n0)) eL := fun ec => by
    have hdgF := (hWins ec j).2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨eL, h1, h2, h3, h4, _⟩ := hdgF.2.2.2.2.2.2.2.2.2.2.2.2.1
    exact ⟨eL, h1, h2, h3, h4⟩
  let ecEList : Fin x.numEdgeful → List ℕ := fun ec => (heL_ex ec).choose
  let ecTriples : Fin x.numEdgeful → List (ℕ × ℕ × ℕ) := fun ec =>
    let F := ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F
    (ecEList ec).map fun e => (e, F.tail e, F.head e)
  let ecTriplesNat : ℕ → List (ℕ × ℕ × ℕ) := fun q =>
    if hq : q < x.numEdgeful then ecTriples ⟨q, hq⟩ else []
  let prefTriples : ℕ → List (ℕ × ℕ × ℕ) := fun idx =>
    ((List.range idx).map ecTriplesNat).flatten
  have hpref0 : prefTriples 0 = [] := rfl
  have hpref_succ : ∀ idx (hidx : idx < x.numEdgeful),
      prefTriples (idx + 1) = prefTriples idx ++ ecTriples ⟨idx, hidx⟩ := fun idx hidx => by
    simp [prefTriples, List.range_succ, List.map_append, List.flatten_append, ecTriplesNat, hidx]
  have hecF_len : ∀ ec : Fin x.numEdgeful,
      (ecTriples ec).length = ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.m := fun ec => by
    simp only [ecTriples, ecEList, List.length_map, (heL_ex ec).choose_spec.1]
  have hecF_mem : ∀ ec : Fin x.numEdgeful, ∀ t ∈ ecTriples ec,
      t.1 ∈ ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.E ∧
      t.2.1 = ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.tail t.1 ∧
      t.2.2 = ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.head t.1 := by
    intro ec t ht
    simp only [ecTriples, List.mem_map] at ht
    obtain ⟨e, heL, rfl⟩ := ht
    exact ⟨((heL_ex ec).choose_spec.2.2.1 e).mp heL, rfl, rfl⟩
  have hpref_nd : ∀ idx ≤ x.numEdgeful, ((prefTriples idx).map Prod.fst).Nodup := by
    intro idx
    induction idx with
    | zero => intro _; simp [hpref0]
    | succ idx ih =>
      intro hle
      have hlt : idx < x.numEdgeful := by omega
      rw [hpref_succ idx hlt, List.map_append, List.nodup_append]
      refine ⟨ih (by omega), ?_, ?_⟩
      · simpa [ecTriples, List.map_map, Function.comp_def] using (heL_ex ⟨idx, hlt⟩).choose_spec.2.1
      · intro a ha1 b' hb2 heq
        subst heq
        simp only [List.mem_map, prefTriples, List.mem_flatten, List.mem_range] at ha1
        obtain ⟨t1, ⟨L, ⟨q, hq, rfl⟩, ht1L⟩, rfl⟩ := ha1
        have hq_lt : q < x.numEdgeful := by omega
        simp only [ecTriplesNat, hq_lt, ↓reduceDIte] at ht1L
        have h1 := (hecF_mem ⟨q, hq_lt⟩ t1 ht1L).1
        simp only [List.mem_map] at hb2
        obtain ⟨t2, ht2, ht2eq⟩ := hb2
        have h2 := ht2eq ▸ (hecF_mem ⟨idx, hlt⟩ t2 ht2).1
        have hcne : x.compOf (x.edgefulComp ⟨q, hq_lt⟩) ≠ x.compOf (x.edgefulComp ⟨idx, hlt⟩) := fun h => by
          have := hefComp_inj (hT.hBij.1 h); simp only [Fin.mk.injEq] at this; omega
        exact Finset.disjoint_left.mp (hF_disj _ ((hbij_ef _).mpr ⟨⟨q, hq_lt⟩, rfl⟩)
          _ ((hbij_ef _).mpr ⟨⟨idx, hlt⟩, rfl⟩) hcne) h1 h2
  have hpref_sub : ∀ idx ≤ x.numEdgeful, ∀ t ∈ prefTriples idx,
      t.1 ∈ (S j).RF.F.E ∧ t.2.1 = (S j).RF.F.tail t.1 ∧ t.2.2 = (S j).RF.F.head t.1 := by
    intro idx hle t ht
    simp only [prefTriples, List.mem_flatten, List.mem_map, List.mem_range] at ht
    obtain ⟨L, ⟨q, hq, rfl⟩, htL⟩ := ht
    have hq_lt : q < x.numEdgeful := by omega
    simp only [ecTriplesNat, hq_lt, ↓reduceDIte] at htL
    have ⟨hfE, htl, hhd⟩ := hecF_mem ⟨q, hq_lt⟩ t htL
    have hC_ef : x.compOf (x.edgefulComp ⟨q, hq_lt⟩) ∈ edgefulComps (S j).G₀ := (hbij_ef _).mpr ⟨⟨q, hq_lt⟩, rfl⟩
    have hFE_mem : t.1 ∈ (S j).RF.F.E := hFE_eq ▸ Finset.mem_biUnion.mpr ⟨_, hC_ef, hfE⟩
    have hends := hF_ends _ hC_ef t.1 hfE
    exact ⟨hFE_mem, htl.trans hends.1.symm, hhd.trans hends.2.symm⟩
  have hfull_cov : ∀ e ∈ (S j).RF.F.E, ∃ t ∈ prefTriples x.numEdgeful, t.1 = e := by
    intro e he
    obtain ⟨C, hCef, hfC⟩ := Finset.mem_biUnion.mp (hFE_eq ▸ he)
    obtain ⟨ec, rfl⟩ := (hbij_ef C).mp hCef
    have hfL : e ∈ ecEList ec := ((heL_ex ec).choose_spec.2.2.1 e).mpr hfC
    refine ⟨(e, ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.tail e,
      ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F.head e), ?_, rfl⟩
    simp only [prefTriples, List.mem_flatten, List.mem_map, List.mem_range]
    refine ⟨ecTriples ec, ⟨ec.1, ec.2, by simp [ecTriplesNat, ec.2]⟩, ?_⟩
    exact List.mem_map.mpr ⟨e, hfL, rfl⟩
  have hfull_len : (prefTriples x.numEdgeful).length = (S j).RF.F.m := by
    have h1 := List.toFinset_card_of_nodup (hpref_nd x.numEdgeful (le_refl _))
    rw [List.length_map] at h1
    rw [← h1]
    congr 1; ext e
    simp only [List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨t, ht, rfl⟩; exact (hpref_sub x.numEdgeful (le_refl _) t ht).1
    · intro he; exact hfull_cov e he
  have hpref_mono : ∀ idx ≤ x.numEdgeful, (prefTriples idx).length ≤ (S j).RF.F.m := by
    intro idx hle
    rw [← hfull_len]
    have hsub_len : ∀ a b, a ≤ b → (prefTriples a).length ≤ (prefTriples b).length := by
      intro a b hab
      induction hab with
      | refl => exact le_refl _
      | @step m hm ih =>
        simp only [prefTriples, List.range_succ, List.map_append, List.flatten_append, List.length_append] at ih ⊢
        omega
    exact hsub_len idx x.numEdgeful hle
  -- Prefix (5 assigns)
  let s1 : State := { st with regs := Function.update st.regs 4 0 }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 x.numEdgeful }
  let s3 : State := { s2 with regs := Function.update s2.regs 6 (compHandlesBase b x.vCap x.eCap x.L_w) }
  let s4 : State := { s3 with regs := Function.update s3.regs 7 x.vCap }
  let s5 : State := { s4 with regs := Function.update s4.regs 8 0 }
  have hp1 : Runs w p ω (.assign 4 (.const 0)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffNumEdgeful)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨x.numEdgeful, Expr.eval_load_of_eq (by
      have := hb_off compOffNumEdgeful (by decide); simp [s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 0) (.const compOffHandlesPtr)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨compHandlesBase b x.vCap x.eCap x.L_w, Expr.eval_load_of_eq (by
      have := hb_off compOffHandlesPtr (by decide); simp [s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 0) (.const compOffVCap)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq (by
      have := hb_off compOffVCap (by decide); simp [s3, s2, s1, Expr.eval, BinOp.eval, hr0, this.1, this.2])
      hhdr.1, rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 8 (.const 0)) s4 .normal s5 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Outer loop induction
  let outerStmt : Stmt :=
    .loop (.bin .lt (.reg 8) (.reg 5))
      (.assign 9 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 8) (.reg 2)) (.reg 1)))) ;;
       .assign 10 (.load (.bin .add (.reg 9) (.const lsfOffDgFPtr))) ;;
       .assign 11 (.load (.bin .add (.reg 10) (.const dgMOff))) ;;
       .assign 12 (.load (.bin .add (.reg 10) (.const dgECapOff))) ;;
       .assign 13 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 7))) ;;
       .assign 14 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7))) (.reg 12)) ;;
       .assign 15 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
         (.bin .mul (.const 3) (.reg 12))) ;;
       .assign 16 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
         (.bin .mul (.const 4) (.reg 12))) ;;
       .assign 17 (.const 0) ;;
       compExpFEdgesInnerStmt ;;
       .assign 8 (.bin .add (.reg 8) (.const 1)))
  have houter : ∀ rem idx (s : State), idx ≤ x.numEdgeful → x.numEdgeful - idx = rem →
      (∀ r < 4, s.regs r = st.regs r) →
      s.regs 4 = (prefTriples idx).length →
      s.regs 5 = x.numEdgeful → s.regs 6 = compHandlesBase b x.vCap x.eCap x.L_w →
      s.regs 7 = x.vCap → s.regs 8 = idx →
      (∀ q (hq : q < (prefTriples idx).length),
        s.mem (fEPtr + 3 * q) = (prefTriples idx)[q].1 ∧
        s.mem (fEPtr + 3 * q + 1) = (prefTriples idx)[q].2.1 ∧
        s.mem (fEPtr + 3 * q + 2) = (prefTriples idx)[q].2.2) →
      (∀ a, a < fEPtr ∨ fEPtr + 3 * (prefTriples idx).length ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω outerStmt s .normal st' c ∧
        (∀ r < 4, st'.regs r = st.regs r) ∧
        st'.regs 4 = (S j).RF.F.m ∧
        (∀ q (hq : q < (prefTriples x.numEdgeful).length),
          st'.mem (fEPtr + 3 * q) = (prefTriples x.numEdgeful)[q].1 ∧
          st'.mem (fEPtr + 3 * q + 1) = (prefTriples x.numEdgeful)[q].2.1 ∧
          st'.mem (fEPtr + 3 * q + 2) = (prefTriples x.numEdgeful)[q].2.2) ∧
        (∀ a, a < fEPtr ∨ fEPtr + 3 * (S j).RF.F.m ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 85 * ((S j).RF.F.m - (prefTriples idx).length) + 95 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro idx s hle hrem hr_lt hr4 hr5 hr6 hr7 hr8 hdone hfr
      have hidx_eq : idx = x.numEdgeful := by omega
      subst hidx_eq
      rw [hfull_len] at hr4 hfr
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr8, hr5], rfl, rfl, by simp [Expr.size]⟩),
        hr_lt, hr4, hdone, hfr, by omega⟩
    | succ rem ih =>
      intro idx s hle hrem hr_lt hr4 hr5 hr6 hr7 hr8 hdone hfr
      have hidx_lt : idx < x.numEdgeful := by omega
      let ec : Fin x.numEdgeful := ⟨idx, hidx_lt⟩
      obtain ⟨hslot, hWrep, hvW, _, _, hWge, hWle⟩ := hWins ec j
      set hWin := x.winHandle ec j
      set xWin := x.winConc ec j
      set dgFPtr := lsfDgFPtr hWin xWin.vCap xWin.eCap xWin.tM
      set eCapF := fECap xWin.eCap xWin.n0
      set F := ((S j).compSt (x.compOf (x.edgefulComp ec))).RF.F
      have hdgF_st := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hHdr := hWrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have hdgF_end : dgFPtr + dynGraphSize xWin.vCap eCapF ≤ x.endAddr := by
        have h1 : dgFPtr + dynGraphSize xWin.vCap eCapF ≤ xWin.endAddr hWin := by
          dsimp only [dgFPtr, eCapF, LSFConcrete.endAddr, lsfEndAddr, lsfStaticSize, lsfDgFPtr,
            lsfTBlockPtr, lsfDgGPtr]; omega
        omega
      have hs_below : ∀ a < x.endAddr, s.mem a = st.mem a := fun a ha => hfr a (Or.inl (by omega))
      have hdgF_s : DynGraphAt s.mem dgFPtr xWin.vCap eCapF F :=
        dynGraphAt_of_agree hdgF_st fun a ha1 ha2 => hs_below a (by omega)
      have heL_spec := (heL_ex ec).choose_spec
      have heL_at_s : ListAt s.mem (dgEListBase dgFPtr xWin.vCap eCapF) (ecEList ec) := fun i hi => by
        have hFm_le_ec : F.m ≤ eCapF := by
          have hsub : F.E ⊆ Finset.range eCapF := fun e he => Finset.mem_range.mpr (hdgF_st.2.2.1 e he)
          simpa [MGraph.m] using Finset.card_le_card hsub
        have ha_lt : dgEListBase dgFPtr xWin.vCap eCapF + i < x.endAddr := by
          have := heL_spec.1; dsimp only [F] at hFm_le_ec; dsimp only [ecEList] at hi
          dsimp only [dgEListBase, dynGraphSize] at hdgF_end ⊢; omega
        exact (hs_below _ ha_lt).trans (heL_spec.2.2.2 i hi)
      have hslot_lt : compHandlesBase b x.vCap x.eCap x.L_w + (idx * k + j.1) < x.endAddr := by
        have h1 : idx * k + j.1 < x.m0Total * k := by
          have : idx + 1 ≤ x.m0Total := by omega
          have := Nat.mul_le_mul_right k this
          rw [Nat.add_mul, Nat.one_mul] at this; have := j.2; omega
        dsimp only [compTablesEnd] at hTE; omega
      have hWin_hdr_lt : hWin + lsfHdrSize ≤ x.endAddr := by
        have : hWin + lsfHdrSize ≤ dgFPtr + dynGraphSize xWin.vCap eCapF := by
          dsimp only [dgFPtr, lsfDgFPtr, lsfTBlockPtr, lsfDgGPtr, lsfHdrSize]; omega
        omega
      have hdgF_ltw : dgFPtr + dynGraphSize xWin.vCap eCapF < 2 ^ w := by omega
      have hslot_w : compHandlesBase b x.vCap x.eCap x.L_w + (idx * k + j.1) < 2 ^ w := by omega
      have hidxk_w : idx * k < 2 ^ w := by omega
      have hidxkj_w : idx * k + j.1 < 2 ^ w := by omega
      let b1 : State := { s with regs := Function.update s.regs 9 hWin }
      let b2 : State := { b1 with regs := Function.update b1.regs 10 dgFPtr }
      let b3 : State := { b2 with regs := Function.update b2.regs 11 F.m }
      let b4 : State := { b3 with regs := Function.update b3.regs 12 eCapF }
      let b5 : State := { b4 with regs := Function.update b4.regs 13 (dgIntToExtBase dgFPtr xWin.vCap) }
      let b6 : State := { b5 with regs := Function.update b5.regs 14 (dgEListBase dgFPtr xWin.vCap eCapF) }
      let b7 : State := { b6 with regs := Function.update b6.regs 15 (dgETailSlotBase dgFPtr xWin.vCap eCapF) }
      let b8 : State := { b7 with regs := Function.update b7.regs 16 (dgEHeadSlotBase dgFPtr xWin.vCap eCapF) }
      let b9 : State := { b8 with regs := Function.update b8.regs 17 0 }
      have hb1 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 6) (.bin .add (.bin .mul (.reg 8) (.reg 2)) (.reg 1))))) s .normal b1 9 :=
        runs_assign_iff.mpr ⟨hWin, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr6, hr8, hr_lt 2 (by omega), hr2, hr_lt 1 (by omega), hr1, hidxk_w, hidxkj_w, hslot_w])
          ((hs_below _ hslot_lt).trans hslot), rfl, rfl, by simp [Expr.size]⟩
      have hb2 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 9) (.const lsfOffDgFPtr)))) b1 .normal b2 5 :=
        runs_assign_iff.mpr ⟨dgFPtr, Expr.eval_load_of_eq (by
          simp [b1, Expr.eval, BinOp.eval, show lsfOffDgFPtr < 2 ^ w by dsimp only [lsfOffDgFPtr]; omega,
            show hWin + lsfOffDgFPtr < 2 ^ w by dsimp only [lsfOffDgFPtr, lsfHdrSize] at hWin_hdr_lt ⊢; omega])
          ((hs_below _ (by dsimp only [lsfOffDgFPtr, lsfHdrSize] at hWin_hdr_lt ⊢; omega)).trans hHdr.2.2.2.2.2.2.1),
          rfl, rfl, by simp [Expr.size]⟩
      have hb3 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 10) (.const dgMOff)))) b2 .normal b3 5 :=
        runs_assign_iff.mpr ⟨F.m, Expr.eval_load_of_eq (x := dgFPtr + dgMOff) (by
          simp [b2, Expr.eval, BinOp.eval, show dgMOff < 2 ^ w by dsimp only [dgMOff]; omega,
            show dgFPtr + dgMOff < 2 ^ w by dsimp only [dgMOff, dynGraphSize] at hdgF_ltw ⊢; omega])
          ((hs_below _ (by dsimp only [dgMOff, dynGraphSize] at hdgF_end ⊢; omega)).trans hdgF_st.2.2.2.2.2.2.1),
          rfl, rfl, by simp [Expr.size]⟩
      have hb4 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 10) (.const dgECapOff)))) b3 .normal b4 5 :=
        runs_assign_iff.mpr ⟨eCapF, Expr.eval_load_of_eq (x := dgFPtr + dgECapOff) (by
          simp [b3, b2, Expr.eval, BinOp.eval, show dgECapOff < 2 ^ w by dsimp only [dgECapOff]; omega,
            show dgFPtr + dgECapOff < 2 ^ w by dsimp only [dgECapOff, dynGraphSize] at hdgF_ltw ⊢; omega])
          ((hs_below _ (by dsimp only [dgECapOff, dynGraphSize] at hdgF_end ⊢; omega)).trans hdgF_st.2.2.2.2.1),
          rfl, rfl, by simp [Expr.size]⟩
      have hdg4_w : dgFPtr + 4 < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have h4v_w : 4 * xWin.vCap < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have h7v_w : 7 * xWin.vCap < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have h47_w : dgFPtr + 4 + 7 * xWin.vCap < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have h3ec_w : 3 * eCapF < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have h4ec_w : 4 * eCapF < 2 ^ w := by dsimp only [dynGraphSize] at hdgF_ltw; omega
      have hr7_w : s.regs 7 = xWin.vCap := hr7.trans hvW.symm
      have hb5 : Runs w p ω (.assign 13 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 4) (.reg 7)))) b4 .normal b5 8 :=
        runs_assign_iff.mpr ⟨dgIntToExtBase dgFPtr xWin.vCap, by
          simp [b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7_w, hw4, hdg4_w, h4v_w,
            show dgFPtr + 4 + 4 * xWin.vCap < 2 ^ w by dsimp only [dynGraphSize] at hdgF_ltw; omega, dgIntToExtBase],
          rfl, rfl, by simp [Expr.size]⟩
      have hb6 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7))) (.reg 12))) b5 .normal b6 10 :=
        runs_assign_iff.mpr ⟨dgEListBase dgFPtr xWin.vCap eCapF, by
          simp [b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7_w, hw4, hw7, hdg4_w, h7v_w, h47_w,
            show dgFPtr + 4 + 7 * xWin.vCap + eCapF < 2 ^ w by dsimp only [dynGraphSize] at hdgF_ltw; omega, dgEListBase],
          rfl, rfl, by simp [Expr.size]⟩
      have hb7 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
          (.bin .mul (.const 3) (.reg 12)))) b6 .normal b7 12 :=
        runs_assign_iff.mpr ⟨dgETailSlotBase dgFPtr xWin.vCap eCapF, by
          simp [b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7_w, hw3, hw4, hw7, hdg4_w, h7v_w, h47_w, h3ec_w,
            show dgFPtr + 4 + 7 * xWin.vCap + 3 * eCapF < 2 ^ w by dsimp only [dynGraphSize] at hdgF_ltw; omega, dgETailSlotBase],
          rfl, rfl, by simp [Expr.size]⟩
      have hb8 : Runs w p ω (.assign 16 (.bin .add (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 7)))
          (.bin .mul (.const 4) (.reg 12)))) b7 .normal b8 12 :=
        runs_assign_iff.mpr ⟨dgEHeadSlotBase dgFPtr xWin.vCap eCapF, by
          simp [b7, b6, b5, b4, b3, b2, b1, Expr.eval, BinOp.eval, hr7_w, hw4, hw7, hdg4_w, h7v_w, h47_w, h4ec_w,
            show dgFPtr + 4 + 7 * xWin.vCap + 4 * eCapF < 2 ^ w by dsimp only [dynGraphSize] at hdgF_ltw; omega, dgEHeadSlotBase],
          rfl, rfl, by simp [Expr.size]⟩
      have hb9 : Runs w p ω (.assign 17 (.const 0)) b8 .normal b9 2 :=
        runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have hnext_len : (prefTriples (idx + 1)).length = (prefTriples idx).length + F.m := by
        rw [hpref_succ idx hidx_lt, List.length_append, hecF_len ec]
      have hnext_le : (prefTriples idx).length + F.m ≤ (S j).RF.F.m := by
        rw [← hnext_len]; exact hpref_mono (idx + 1) (by omega)
      obtain ⟨b10, cIn, hb10, hb10_r, hb10_4, hb10_done, hb10_fr, hcIn⟩ :=
        compExpFEdgesInner_runs (fEPtr := fEPtr) (baseCnt := (prefTriples idx).length) (p := p) (ω := ω) (st := b9)
          hw16 hdgF_s heL_spec.1 heL_spec.2.1 heL_spec.2.2.1 heL_at_s (by omega) (by omega)
          (by simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr_lt 3 (by omega), hr3])
          (by simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr4])
          (by simp [b9, b8, b7, b6, b5, b4, b3])
          (by simp [b9, b8, b7, b6, b5]) (by simp [b9, b8, b7, b6])
          (by simp [b9, b8, b7]) (by simp [b9, b8]) (by simp [b9])
      let b11 : State := { b10 with regs := Function.update b10.regs 8 (idx + 1) }
      have hb11 : Runs w p ω (.assign 8 (.bin .add (.reg 8) (.const 1))) b10 .normal b11 4 :=
        runs_assign_iff.mpr ⟨idx + 1, by
          have hr8_b10 : b10.regs 8 = idx := by rw [hb10_r 8 (by omega) (by omega)]; simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr8]
          simp [Expr.eval, BinOp.eval, hr8_b10, hw1, show idx + 1 < 2 ^ w by omega], rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal b11 (82 + cIn) :=
        runs_seq_iff.mpr (Or.inr ⟨b1, 9, _, hb1, runs_seq_iff.mpr (Or.inr ⟨b2, 5, _, hb2,
          runs_seq_iff.mpr (Or.inr ⟨b3, 5, _, hb3, runs_seq_iff.mpr (Or.inr ⟨b4, 5, _, hb4,
          runs_seq_iff.mpr (Or.inr ⟨b5, 8, _, hb5, runs_seq_iff.mpr (Or.inr ⟨b6, 10, _, hb6,
          runs_seq_iff.mpr (Or.inr ⟨b7, 12, _, hb7, runs_seq_iff.mpr (Or.inr ⟨b8, 12, _, hb8,
          runs_seq_iff.mpr (Or.inr ⟨b9, 2, _, hb9, runs_seq_iff.mpr (Or.inr ⟨b10, cIn, 4, hb10, hb11, rfl⟩),
          rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
      obtain ⟨st', cRest, hrest, hr'_lt, hr'_4, hdone', hfr', hcRest⟩ :=
        ih (idx + 1) b11 (by omega) (by omega)
          (fun r hr => by rw [show b11.regs r = b10.regs r by simp [b11, show r ≠ 8 by omega],
            hb10_r r (by omega) (by omega)]; simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, show r ≠ 9 by omega,
            show r ≠ 10 by omega, show r ≠ 11 by omega, show r ≠ 12 by omega, show r ≠ 13 by omega,
            show r ≠ 14 by omega, show r ≠ 15 by omega, show r ≠ 16 by omega, show r ≠ 17 by omega, hr_lt r hr])
          (by simp [b11, hb10_4, hnext_len])
          (by rw [show b11.regs 5 = b10.regs 5 by simp [b11], hb10_r 5 (by omega) (by omega)]; simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr5])
          (by rw [show b11.regs 6 = b10.regs 6 by simp [b11], hb10_r 6 (by omega) (by omega)]; simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr6])
          (by rw [show b11.regs 7 = b10.regs 7 by simp [b11], hb10_r 7 (by omega) (by omega)]; simp [b9, b8, b7, b6, b5, b4, b3, b2, b1, hr7])
          (by simp [b11])
          (fun q hq => by
            dsimp only [b11]
            by_cases hq1 : q < (prefTriples idx).length
            · have hfrq0 := hb10_fr (fEPtr + 3 * q) (Or.inl (by omega))
              have hfrq1 := hb10_fr (fEPtr + 3 * q + 1) (Or.inl (by omega))
              have hfrq2 := hb10_fr (fEPtr + 3 * q + 2) (Or.inl (by omega))
              have hget : (prefTriples (idx + 1))[q]'hq = (prefTriples idx)[q]'hq1 := by
                simp only [hpref_succ idx hidx_lt]; exact List.getElem_append_left hq1
              rw [hget, hfrq0, hfrq1, hfrq2]
              exact hdone q hq1
            · have hq2 : q - (prefTriples idx).length < F.m := by omega
              have hget : (prefTriples (idx + 1))[q]'hq = (ecTriples ec)[q - (prefTriples idx).length]'(by rw [hecF_len ec]; exact hq2) := by
                simp only [hpref_succ idx hidx_lt]; exact List.getElem_append_right (by omega)
              rw [hget]
              have hidx_eq : fEPtr + 3 * q = fEPtr + 3 * ((prefTriples idx).length + (q - (prefTriples idx).length)) := by omega
              have hstep_m := hb10_done (q - (prefTriples idx).length) hq2
              rw [hidx_eq]; simpa [ecTriples] using hstep_m)
          (fun a ha => by
            dsimp only [b11]
            rw [hnext_len] at ha
            have ha1 : a < fEPtr + 3 * (prefTriples idx).length ∨ fEPtr + 3 * ((prefTriples idx).length + F.m) ≤ a := by
              rcases ha with h | h
              · exact Or.inl (by omega)
              · exact Or.inr (by omega)
            rw [hb10_fr a ha1]
            refine hfr a ?_
            rcases ha with h | h
            · exact Or.inl h
            · exact Or.inr (by omega))
      have hfull : Runs w p ω outerStmt s .normal st' (82 + cIn + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, b11, 82 + cIn, cRest,
          by simp [Expr.eval, BinOp.eval, hr8, hr5, hidx_lt, hw0], by decide,
          by simpa using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 82 + cIn + cRest + 4, hfull, hr'_lt, hr'_4, hdone', hfr', by omega⟩
  obtain ⟨st', cOut, hout, hr'_lt, hr'_4, hdone', hfr', hcOut⟩ :=
    houter x.numEdgeful 0 s5 (Nat.zero_le _) (Nat.sub_zero _)
      (fun r hr => by simp [s5, s4, s3, s2, s1, show r ≠ 4 by omega, show r ≠ 5 by omega,
        show r ≠ 6 by omega, show r ≠ 7 by omega, show r ≠ 8 by omega])
      (by simp [s5, s4, s3, s2, s1, hpref0]) (by simp [s5, s4, s3, s2])
      (by simp [s5, s4, s3]) (by simp [s5, s4]) (by simp [s5])
      (fun _ h => by simp [hpref0] at h) (fun _ _ => rfl)
  have hrun : Runs w p ω compExpFEdgesStmt st .normal st' (24 + cOut) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, hp1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hp2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hp3, runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, hp4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 2, cOut, hp5, hout, rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  exact ⟨st', 24 + cOut, prefTriples x.numEdgeful, hrun, hr'_lt, hr'_4, hfull_len,
    hpref_nd x.numEdgeful (le_refl _), hpref_sub x.numEdgeful (le_refl _), hfull_cov, hdone', hfr',
    by simp only [hpref0, List.length_nil, Nat.sub_zero] at hcOut; omega⟩

end

end MinCostFlow.SparseCore.Program
