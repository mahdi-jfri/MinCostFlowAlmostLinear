module

public import MinCostFlow.SparseCore.Program.CompExportBase
import WordRAM.Tactic

/-!
# Branch Tree-Edge Export Inner Loop (`CompExportGraphsInner`)

Implements and verifies `compExpTEdgesInnerStmt` / `compExpTEdgesInner_runs` for one edgeful
component `ec`: scans `tOrigList` and emits `(f, G_c.tail f, G_c.head f)` whenever
`dgEPres[f] ≠ 0` and `isIns[f] = 0`, in `≤ 95 * tM + 5` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-- Inner loop of `compExpTEdgesStmt` for one edgeful component `ec`: scans `r18 = 0 .. r13 - 1`
(`tOrigList`), emitting `(f, G.tail f, G.head f)` whenever `dgEPres[f] ≠ 0` and `isIns[f] = 0`. -/
def compExpTEdgesInnerStmt : Stmt :=
  .loop (.bin .lt (.reg 18) (.reg 13))
    (.assign 19 (.load (.bin .add (.reg 14) (.reg 18))) ;;
     .assign 20 (.load (.bin .add (.reg 15) (.reg 19))) ;;
     .cond (.reg 20)
       (.assign 20 (.load (.bin .add (.reg 9) (.reg 19))) ;;
        .cond (.reg 20)
          .nop
          (.assign 20 (.load (.bin .add (.reg 16) (.reg 19))) ;;
           .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
           .store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 19) ;;
           .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 20) ;;
           .assign 20 (.load (.bin .add (.reg 17) (.reg 19))) ;;
           .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
           .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20) ;;
           .assign 4 (.bin .add (.reg 4) (.const 1))))
       .nop ;;
     .assign 18 (.bin .add (.reg 18) (.const 1)))

set_option maxHeartbeats 600000 in
open Classical in
/-- Inner-loop verification for one edgeful component's `tOrigList` scan. -/
theorem compExpTEdgesInner_runs {w tEPtr baseCnt vCap eCap isInsPtr dgGPtr origIdPtr tM : ℕ}
    {p : Program} {G_c T_c : MGraph} {insSet : Finset ℕ} {tOrigList : List ℕ}
    {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hlist_len : tOrigList.length = tM)
    (_hlist_nd : tOrigList.Nodup)
    (hlist_mem : ∀ f, f ∈ tOrigList ↔ f ∈ T_c.E)
    (hlist_lt : ∀ f ∈ T_c.E, f < eCap)
    (hlist_at : ListAt st.mem origIdPtr tOrigList)
    (hdgG : DynGraphAt st.mem dgGPtr vCap eCap G_c)
    (hins : ∀ e < eCap, st.mem (isInsPtr + e) = if e ∈ insSet then 1 else 0)
    (horig_le : origIdPtr + tM ≤ tEPtr)
    (hdgG_le : dgGPtr + dynGraphSize vCap eCap ≤ tEPtr)
    (hins_le : isInsPtr + eCap ≤ tEPtr)
    (hbuf_w : tEPtr + 3 * (baseCnt + tM) < 2 ^ w)
    (hr3 : st.regs 3 = tEPtr) (hr4 : st.regs 4 = baseCnt)
    (hr9 : st.regs 9 = isInsPtr)
    (hr12 : st.regs 12 = dgIntToExtBase dgGPtr vCap)
    (hr13 : st.regs 13 = tM) (hr14 : st.regs 14 = origIdPtr)
    (hr15 : st.regs 15 = dgEPresBase dgGPtr vCap)
    (hr16 : st.regs 16 = dgETailSlotBase dgGPtr vCap eCap)
    (hr17 : st.regs 17 = dgEHeadSlotBase dgGPtr vCap eCap)
    (hr18 : st.regs 18 = 0) :
    let kept := tOrigList.filter fun f => decide (f ∈ G_c.E ∧ f ∉ insSet)
    let eL := kept.map fun f => (f, G_c.tail f, G_c.head f)
    ∃ st' c,
      Runs w p ω compExpTEdgesInnerStmt st .normal st' c ∧
      (∀ r < 18, r ≠ 4 → st'.regs r = st.regs r) ∧
      st'.regs 4 = baseCnt + eL.length ∧
      (∀ q (hq : q < eL.length),
        st'.mem (tEPtr + 3 * (baseCnt + q)) = eL[q].1 ∧
        st'.mem (tEPtr + 3 * (baseCnt + q) + 1) = eL[q].2.1 ∧
        st'.mem (tEPtr + 3 * (baseCnt + q) + 2) = eL[q].2.2) ∧
      (∀ a, a < tEPtr + 3 * baseCnt ∨ tEPtr + 3 * (baseCnt + eL.length) ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 95 * tM + 5 := by
  intro kept eL
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hdg_sz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  have hloop : ∀ rem i (s : State) (hi : i ≤ tM), tM - i = rem →
      let pref := (tOrigList.take i).filter fun f => decide (f ∈ G_c.E ∧ f ∉ insSet)
      let pL := pref.map fun f => (f, G_c.tail f, G_c.head f)
      (∀ r < 18, r ≠ 4 → s.regs r = st.regs r) →
      s.regs 4 = baseCnt + pL.length →
      s.regs 18 = i →
      (∀ q (hq : q < pL.length),
        s.mem (tEPtr + 3 * (baseCnt + q)) = pL[q].1 ∧
        s.mem (tEPtr + 3 * (baseCnt + q) + 1) = pL[q].2.1 ∧
        s.mem (tEPtr + 3 * (baseCnt + q) + 2) = pL[q].2.2) →
      (∀ a, a < tEPtr + 3 * baseCnt ∨ tEPtr + 3 * (baseCnt + pL.length) ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω compExpTEdgesInnerStmt s .normal st' c ∧
        (∀ r < 18, r ≠ 4 → st'.regs r = st.regs r) ∧
        st'.regs 4 = baseCnt + eL.length ∧
        (∀ q (hq : q < eL.length),
          st'.mem (tEPtr + 3 * (baseCnt + q)) = eL[q].1 ∧
          st'.mem (tEPtr + 3 * (baseCnt + q) + 1) = eL[q].2.1 ∧
          st'.mem (tEPtr + 3 * (baseCnt + q) + 2) = eL[q].2.2) ∧
        (∀ a, a < tEPtr + 3 * baseCnt ∨ tEPtr + 3 * (baseCnt + eL.length) ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 95 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem pref pL hr_o hr4_s hr18_s hdone hfr
      have hi_eq : i = tM := by omega
      subst hi_eq
      have hp_eq : pL = eL := by simp [pL, pref, eL, kept, ← hlist_len]
      rw [hp_eq] at hr4_s hdone hfr
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr18_s, hr_o 13 (by omega) (by omega), hr13],
        rfl, rfl, by simp [Expr.size]⟩), hr_o, hr4_s, hdone, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem pref pL hr_o hr4_s hr18_s hdone hfr
      have hi_lt : i < tM := by omega
      have hi_len : i < tOrigList.length := by omega
      set f := tOrigList[i]'hi_len
      have hfT : f ∈ T_c.E := (hlist_mem f).mp (List.getElem_mem hi_len)
      have hflt : f < eCap := hlist_lt f hfT
      have hp_le_i : pL.length ≤ i := by
        simpa [pL] using le_trans (List.length_filter_le _ _) (by simp [hi_len.le])
      have hs_below : ∀ a < tEPtr, s.mem a = st.mem a := fun a ha => hfr a (Or.inl (by omega))
      have hs_f : s.mem (origIdPtr + i) = f := (hs_below _ (by omega)).trans (hlist_at i hi_len)
      set presV := if f ∈ G_c.E then 1 else 0
      have hpres_lt : dgEPresBase dgGPtr vCap + f < tEPtr := by
        dsimp only [dgEPresBase] at *; omega
      have hs_pres : s.mem (dgEPresBase dgGPtr vCap + f) = presV :=
        (hs_below _ hpres_lt).trans (hdgG.2.2.2.2.2.2.2.2.2.2.2.1 f hflt)
      let a1 : State := { s with regs := Function.update s.regs 19 f }
      let a2 : State := { a1 with regs := Function.update a1.regs 20 presV }
      have ha1 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 14) (.reg 18)))) s .normal a1 5 :=
        runs_assign_iff.mpr ⟨f, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_o 14 (by omega) (by omega), hr14, hr18_s,
            show origIdPtr + i < 2 ^ w by omega]) hs_f, rfl, rfl, by simp [Expr.size]⟩
      have ha2 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 15) (.reg 19)))) a1 .normal a2 5 :=
        runs_assign_iff.mpr ⟨presV, Expr.eval_load_of_eq (by
          simp [a1, Expr.eval, BinOp.eval, hr_o 15 (by omega) (by omega), hr15,
            show dgEPresBase dgGPtr vCap + f < 2 ^ w by omega]) hs_pres, rfl, rfl, by simp [Expr.size]⟩
      have htake_succ : tOrigList.take (i + 1) = tOrigList.take i ++ [f] := List.take_succ_eq_append_getElem hi_len
      set pref' := (tOrigList.take (i + 1)).filter fun g => decide (g ∈ G_c.E ∧ g ∉ insSet)
      set pL' := pref'.map fun g => (g, G_c.tail g, G_c.head g)
      set idx := baseCnt + pL.length
      have hcond : ∃ a3 cC,
          Runs w p ω
            (.cond (.reg 20)
              (.assign 20 (.load (.bin .add (.reg 9) (.reg 19))) ;;
               .cond (.reg 20)
                 .nop
                 (.assign 20 (.load (.bin .add (.reg 16) (.reg 19))) ;;
                  .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
                  .store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 19) ;;
                  .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 20) ;;
                  .assign 20 (.load (.bin .add (.reg 17) (.reg 19))) ;;
                  .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
                  .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20) ;;
                  .assign 4 (.bin .add (.reg 4) (.const 1))))
              .nop) a2 .normal a3 cC ∧
          (∀ r < 18, r ≠ 4 → a3.regs r = st.regs r) ∧
          a3.regs 4 = baseCnt + pL'.length ∧
          a3.regs 18 = i ∧
          (∀ q (hq : q < pL'.length),
            a3.mem (tEPtr + 3 * (baseCnt + q)) = pL'[q].1 ∧
            a3.mem (tEPtr + 3 * (baseCnt + q) + 1) = pL'[q].2.1 ∧
            a3.mem (tEPtr + 3 * (baseCnt + q) + 2) = pL'[q].2.2) ∧
          (∀ a, a < tEPtr + 3 * baseCnt ∨ tEPtr + 3 * (baseCnt + pL'.length) ≤ a → a3.mem a = st.mem a) ∧
          cC ≤ 70 := by
        by_cases hfG : f ∈ G_c.E
        · have hpres1 : presV = 1 := if_pos hfG
          set insV := if f ∈ insSet then 1 else 0
          have hs_ins : s.mem (isInsPtr + f) = insV := (hs_below _ (by omega)).trans (hins f hflt)
          let b1 : State := { a2 with regs := Function.update a2.regs 20 insV }
          have hb1 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 9) (.reg 19)))) a2 .normal b1 5 :=
            runs_assign_iff.mpr ⟨insV, Expr.eval_load_of_eq (by
              simp [a2, a1, Expr.eval, BinOp.eval, hr_o 9 (by omega) (by omega), hr9,
                show isInsPtr + f < 2 ^ w by omega]) hs_ins, rfl, rfl, by simp [Expr.size]⟩
          by_cases hfI : f ∈ insSet
          · have hins1 : insV = 1 := if_pos hfI
            have hpL'_eq : pL' = pL := by simp [pL', pref', htake_succ, List.filter_append, hfI, pL, pref]
            let emitStmt : Stmt :=
              .assign 20 (.load (.bin .add (.reg 16) (.reg 19))) ;;
              .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
              .store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 19) ;;
              .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 20) ;;
              .assign 20 (.load (.bin .add (.reg 17) (.reg 19))) ;;
              .assign 20 (.load (.bin .add (.reg 12) (.reg 20))) ;;
              .store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20) ;;
              .assign 4 (.bin .add (.reg 4) (.const 1))
            have hinner : Runs w p ω (.cond (.reg 20) .nop emitStmt) b1 .normal b1 3 :=
              runs_cond_iff.mpr ⟨1, 1, by simp [b1, Expr.eval, hins1],
                by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
            have hbr : Runs w p ω (.assign 20 (.load (.bin .add (.reg 9) (.reg 19))) ;;
                .cond (.reg 20) .nop emitStmt) a2 .normal b1 9 :=
              runs_seq_iff.mpr (Or.inr ⟨b1, 5, 3, hb1, hinner, rfl⟩)
            refine ⟨b1, 11, runs_cond_iff.mpr ⟨1, 9, by simp [a2, Expr.eval, hpres1], by simpa [emitStmt] using hbr, by simp [Expr.size]⟩,
              fun r hr hne4 => by simp [b1, a2, a1, show r ≠ 20 by omega, show r ≠ 19 by omega, hr_o r hr hne4],
              by simp [b1, a2, a1, hr4_s, hpL'_eq, idx], by simp [b1, a2, a1, hr18_s],
              by rw [hpL'_eq]; exact hdone, by rw [hpL'_eq]; exact hfr, by omega⟩
          · have hins0 : insV = 0 := if_neg hfI
            have hpL'_eq : pL' = pL ++ [(f, G_c.tail f, G_c.head f)] := by
              simp [pL', pref', htake_succ, List.filter_append, hfG, hfI, pL, pref]
            have hpL'_len : pL'.length = pL.length + 1 := by simp [hpL'_eq]
            set sT := st.mem (dgETailSlotBase dgGPtr vCap eCap + f)
            set sH := st.mem (dgEHeadSlotBase dgGPtr vCap eCap + f)
            have htV : G_c.tail f ∈ G_c.V := (hdgG.1 f hfG).1
            have hhV : G_c.head f ∈ G_c.V := (hdgG.1 f hfG).2
            have hsT_eq : sT = st.mem (dgExtToIntBase dgGPtr vCap + G_c.tail f) :=
              (hdgG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfG).1
            have hsH_eq : sH = st.mem (dgExtToIntBase dgGPtr vCap + G_c.head f) :=
              (hdgG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hfG).2
            have hsT_lt : sT < vCap := hdgG.2.1 _ (hsT_eq ▸ (hdgG.2.2.2.2.2.2.2.2.2.1 _ htV).1)
            have hsH_lt : sH < vCap := hdgG.2.1 _ (hsH_eq ▸ (hdgG.2.2.2.2.2.2.2.2.2.1 _ hhV).1)
            have hu_eq : st.mem (dgIntToExtBase dgGPtr vCap + sT) = G_c.tail f := by
              rw [hsT_eq]; exact (hdgG.2.2.2.2.2.2.2.2.2.1 _ htV).2
            have hv_eq : st.mem (dgIntToExtBase dgGPtr vCap + sH) = G_c.head f := by
              rw [hsH_eq]; exact (hdgG.2.2.2.2.2.2.2.2.2.1 _ hhV).2
            have hsT_a : dgETailSlotBase dgGPtr vCap eCap + f < tEPtr := by dsimp only [dgETailSlotBase]; omega
            have hsH_a : dgEHeadSlotBase dgGPtr vCap eCap + f < tEPtr := by dsimp only [dgEHeadSlotBase]; omega
            have hiT_a : dgIntToExtBase dgGPtr vCap + sT < tEPtr := by dsimp only [dgIntToExtBase]; omega
            have hiH_a : dgIntToExtBase dgGPtr vCap + sH < tEPtr := by dsimp only [dgIntToExtBase]; omega
            let c1 : State := { b1 with regs := Function.update b1.regs 20 sT }
            let c2 : State := { c1 with regs := Function.update c1.regs 20 (G_c.tail f) }
            let m1 := Function.update s.mem (tEPtr + 3 * idx) f
            let m2 := Function.update m1 (tEPtr + 3 * idx + 1) (G_c.tail f)
            let c3 : State := { c2 with mem := m1 }
            let c4 : State := { c3 with mem := m2 }
            let c5 : State := { c4 with regs := Function.update c4.regs 20 sH }
            let c6 : State := { c5 with regs := Function.update c5.regs 20 (G_c.head f) }
            let m3 := Function.update m2 (tEPtr + 3 * idx + 2) (G_c.head f)
            let c7 : State := { c6 with mem := m3 }
            let c8 : State := { c7 with regs := Function.update c7.regs 4 (idx + 1) }
            have hc1 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 16) (.reg 19)))) b1 .normal c1 5 :=
              runs_assign_iff.mpr ⟨sT, Expr.eval_load_of_eq (by
                simp [b1, a2, a1, Expr.eval, BinOp.eval, hr_o 16 (by omega) (by omega), hr16,
                  show dgETailSlotBase dgGPtr vCap eCap + f < 2 ^ w by omega])
                (hs_below _ hsT_a), rfl, rfl, by simp [Expr.size]⟩
            have hc2 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 12) (.reg 20)))) c1 .normal c2 5 :=
              runs_assign_iff.mpr ⟨G_c.tail f, Expr.eval_load_of_eq (by
                simp [c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 12 (by omega) (by omega), hr12,
                  show dgIntToExtBase dgGPtr vCap + sT < 2 ^ w by omega])
                ((hs_below _ hiT_a).trans hu_eq), rfl, rfl, by simp [Expr.size]⟩
            have hc3 : Runs w p ω (.store (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.reg 19)) c2 .normal c3 7 :=
              runs_store_iff.mpr ⟨tEPtr + 3 * idx, f, by
                simp [c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw3,
                  show 3 * idx < 2 ^ w by omega, show tEPtr + 3 * idx < 2 ^ w by omega, idx],
                by simp [c2, c1, b1, a2, a1, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
            have hc4 : Runs w p ω (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 1)) (.reg 20)) c3 .normal c4 9 :=
              runs_store_iff.mpr ⟨tEPtr + 3 * idx + 1, G_c.tail f, by
                simp [c3, c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw3, hw1,
                  show 3 * idx < 2 ^ w by omega, show tEPtr + 3 * idx < 2 ^ w by omega,
                  show tEPtr + 3 * idx + 1 < 2 ^ w by omega, idx],
                by simp [c3, c2, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
            have hc5 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 17) (.reg 19)))) c4 .normal c5 5 :=
              runs_assign_iff.mpr ⟨sH, Expr.eval_load_of_eq (x := dgEHeadSlotBase dgGPtr vCap eCap + f) (by
                simp [c4, c3, c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 17 (by omega) (by omega), hr17,
                  show dgEHeadSlotBase dgGPtr vCap eCap + f < 2 ^ w by omega])
                (by dsimp only [c4, c3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact hs_below _ hsH_a),
                rfl, rfl, by simp [Expr.size]⟩
            have hc6 : Runs w p ω (.assign 20 (.load (.bin .add (.reg 12) (.reg 20)))) c5 .normal c6 5 :=
              runs_assign_iff.mpr ⟨G_c.head f, Expr.eval_load_of_eq (x := dgIntToExtBase dgGPtr vCap + sH) (by
                simp [c5, c4, c3, c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 12 (by omega) (by omega), hr12,
                  show dgIntToExtBase dgGPtr vCap + sH < 2 ^ w by omega])
                (by dsimp only [c5, c4, c3, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]; exact (hs_below _ hiH_a).trans hv_eq),
                rfl, rfl, by simp [Expr.size]⟩
            have hc7 : Runs w p ω (.store (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 3) (.reg 4))) (.const 2)) (.reg 20)) c6 .normal c7 9 :=
              runs_store_iff.mpr ⟨tEPtr + 3 * idx + 2, G_c.head f, by
                simp [c6, c5, c4, c3, c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr_o 3 (by omega) (by omega), hr3, hr4_s, hw3, hw2,
                  show 3 * idx < 2 ^ w by omega, show tEPtr + 3 * idx < 2 ^ w by omega,
                  show tEPtr + 3 * idx + 2 < 2 ^ w by omega, idx],
                by simp [c6, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
            have hc8 : Runs w p ω (.assign 4 (.bin .add (.reg 4) (.const 1))) c7 .normal c8 4 :=
              runs_assign_iff.mpr ⟨idx + 1, by
                simp [c7, c6, c5, c4, c3, c2, c1, b1, a2, a1, Expr.eval, BinOp.eval, hr4_s, hw1,
                  show idx + 1 < 2 ^ w by omega, idx], rfl, rfl, by simp [Expr.size]⟩
            have helse : Runs w p ω _ b1 .normal c8 56 :=
              runs_seq_iff.mpr (Or.inr ⟨c1, 5, _, hc1, runs_seq_iff.mpr (Or.inr ⟨c2, 5, _, hc2,
                runs_seq_iff.mpr (Or.inr ⟨c3, 7, _, hc3, runs_seq_iff.mpr (Or.inr ⟨c4, 9, _, hc4,
                runs_seq_iff.mpr (Or.inr ⟨c5, 5, _, hc5, runs_seq_iff.mpr (Or.inr ⟨c6, 5, _, hc6,
                runs_seq_iff.mpr (Or.inr ⟨c7, 9, 4, hc7, hc8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
            have hinner : Runs w p ω (.cond (.reg 20) .nop _) b1 .normal c8 58 :=
              runs_cond_iff.mpr ⟨0, 56, by simp [b1, Expr.eval, hins0], by simpa using helse, by simp [Expr.size]⟩
            have hbr : Runs w p ω _ a2 .normal c8 64 :=
              runs_seq_iff.mpr (Or.inr ⟨b1, 5, 58, hb1, hinner, rfl⟩)
            refine ⟨c8, 66, runs_cond_iff.mpr ⟨1, 64, by simp [a2, Expr.eval, hpres1], by simpa using hbr, by simp [Expr.size]⟩,
              fun r hr hne4 => by simp [c8, c7, c6, c5, c4, c3, c2, c1, b1, a2, a1, hne4,
                show r ≠ 20 by omega, show r ≠ 19 by omega, hr_o r hr hne4],
              by simp [c8, idx, hpL'_len]; omega,
              by simp [c8, c7, c6, c5, c4, c3, c2, c1, b1, a2, a1, hr18_s],
              fun q hq => by
                dsimp only [c8, c7, m3, m2, m1]
                by_cases hql : q < pL.length
                · have hget : pL'[q]'hq = pL[q]'hql := by simp [hpL'_eq, List.getElem_append_left hql]
                  rw [hget]
                  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega),
                      Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                  exact hdone q hql
                · have hqe : q = pL.length := by omega
                  subst hqe
                  have hget : pL'[pL.length]'hq = (f, G_c.tail f, G_c.head f) := by simp [hpL'_eq]
                  rw [hget]
                  simp [idx]
              , fun a ha => by
                dsimp only [c8, c7, m3, m2, m1]
                rw [hpL'_len] at ha
                rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
                exact hfr a (by omega), by omega⟩
        · have hpres0 : presV = 0 := if_neg hfG
          have hpL'_eq : pL' = pL := by simp [pL', pref', htake_succ, List.filter_append, hfG, pL, pref]
          refine ⟨a2, 3, runs_cond_iff.mpr ⟨0, 1, by simp [a2, Expr.eval, hpres0],
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
            fun r hr hne4 => by simp [a2, a1, show r ≠ 20 by omega, show r ≠ 19 by omega, hr_o r hr hne4],
            by simp [a2, a1, hr4_s, hpL'_eq, idx], by simp [a2, a1, hr18_s],
            by rw [hpL'_eq]; exact hdone, by rw [hpL'_eq]; exact hfr, by omega⟩
      obtain ⟨a3, cC, ha3, ha3_o, ha3_4, ha3_18, ha3_done, ha3_fr, hcC⟩ := hcond
      let a4 : State := { a3 with regs := Function.update a3.regs 18 (i + 1) }
      have ha4 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.const 1))) a3 .normal a4 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, ha3_18, hw1, show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal a4 (17 + cC) :=
        runs_seq_iff.mpr (Or.inr ⟨a1, 5, 11 + cC, ha1,
          runs_seq_iff.mpr (Or.inr ⟨a2, 5, 5 + cC, ha2,
          runs_seq_iff.mpr (Or.inr ⟨a3, cC, 4, ha3, ha4, by omega⟩), by omega⟩), by omega⟩)
      obtain ⟨st', cRest, hrest, hr'_o, hr'_4, hdone', hfr', hcRest⟩ :=
        ih (i + 1) a4 (by omega) (by omega)
          (fun r hr hne4 => by simp [a4, show r ≠ 18 by omega, ha3_o r hr hne4])
          (by simpa [a4, pL', pref'] using ha3_4) (by simp [a4]) ha3_done ha3_fr
      have hfull : Runs w p ω compExpTEdgesInnerStmt s .normal st' (17 + cC + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, a4, 17 + cC, cRest,
          by simp [Expr.eval, BinOp.eval, hr18_s, hr_o 13 (by omega) (by omega), hr13, hi_lt, hw0], by decide,
          by simpa [compExpTEdgesInnerStmt] using hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 17 + cC + cRest + 4, hfull, hr'_o, hr'_4, hdone', hfr', by omega⟩
  obtain ⟨st', c, h1, h2, h3, h4, h5, h6⟩ :=
    hloop tM 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ _ => rfl) (by simpa using hr4) hr18
      (fun _ h => by simp at h) (fun _ _ => rfl)
  exact ⟨st', c, h1, h2, h3, h4, h5, by omega⟩

end

end MinCostFlow.SparseCore.Program
