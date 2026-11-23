module

public import MinCostFlow.SparseCore.Program.CompBatchStepLift
import WordRAM.Tactic

/-!
# Vertex-Split Step Primitives (`CompBatchStepSplitBase`)

Defines `compCopyNonCrossSliceStmt`, `compStepSplitPrefStmt`, `compStepSplitBuildStmt`,
`compStepSplitDispStmt`, and `compStepSplitProc`, and verifies:
* `compCopyNonCrossSlice_runs`: filters an input edge slice in `O(len + 1)` time, copying only
  non-cross edges (`mem (isCrossBase + e) = 0`) into the output buffer.
* `compStepSplitPref_runs`: 15-statement prefix decoding `[tag, v, v', kt, kh]`, resolving `cv`,
  storing `vComp[v'] := cv` and `mem[splitPtr] := v'`, and populating registers `6..18`.
* `compStepSplitBuild_runs`: constructs the 1-update projected split batch
  `[1, tag, v, v', kt', kh'] ++ Lt' ++ Lh'` in `updBuf` by filtering out cross-edges from `Lt` and
  `Lh` (works uniformly for both Tag 2 and Tag 3 with zero ghost-list reads).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Procedures -/

/-- Copy elements `e` from `[reg rSrc, reg rSrc + reg rLen)` to `[reg rDst, ...)` whose cross-edge
flag `mem (reg rCrBase + e)` is `0`, putting the copied count into `reg rCnt` and advancing
`reg rDst` by that count. Uses scratch registers `rIdx`, `rElem`, `rFlag`. -/
def compCopyNonCrossSliceStmt (rSrc rDst rLen rCrBase rCnt rIdx rElem rFlag : ℕ) : Stmt :=
  .assign rCnt (.const 0) ;;
  .assign rIdx (.const 0) ;;
  .loop (.bin .lt (.reg rIdx) (.reg rLen))
    (.assign rElem (.load (.bin .add (.reg rSrc) (.reg rIdx))) ;;
     .assign rFlag (.load (.bin .add (.reg rCrBase) (.reg rElem))) ;;
     .cond (.reg rFlag)
       .nop
       (.store (.reg rDst) (.reg rElem) ;;
        .assign rDst (.bin .add (.reg rDst) (.const 1)) ;;
        .assign rCnt (.bin .add (.reg rCnt) (.const 1))) ;;
     .assign rIdx (.bin .add (.reg rIdx) (.const 1)))

lemma compCopyNonCrossSliceStmt_noRand (rSrc rDst rLen rCrBase rCnt rIdx rElem rFlag : ℕ) :
    (compCopyNonCrossSliceStmt rSrc rDst rLen rCrBase rCnt rIdx rElem rFlag).NoRand := by
  simp [compCopyNonCrossSliceStmt, Stmt.NoRand]

/-- Common 15-statement prefix of `compStepSplitProc`: decodes `[tag, v, v', kt, kh]`, resolves
`cv := vComp[v]`, writes `vComp[v'] := cv` and `mem[splitPtr] := v'`, and populates registers
`6..18`. Assumes `args = [b, uPtr, heap, cntBase, updBuf, splitPtr]` in `reg 0..5`. -/
def compStepSplitPrefStmt : Stmt :=
  .assign 6 (.load (.reg 1)) ;;
  .assign 7 (.load (.bin .add (.reg 1) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 1) (.const 2))) ;;
  .assign 9 (.load (.bin .add (.reg 1) (.const 3))) ;;
  .assign 10 (.load (.bin .add (.reg 1) (.const 4))) ;;
  .assign 11 (.load (.bin .add (.reg 0) (.const compOffVCompPtr))) ;;
  .assign 12 (.load (.bin .add (.reg 11) (.reg 7))) ;;
  .store (.bin .add (.reg 11) (.reg 8)) (.reg 12) ;;
  .store (.reg 5) (.reg 8) ;;
  .assign 13 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))) ;;
  .assign 14 (.bin .add (.reg 2) (.const 1)) ;;
  .assign 15 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr))) ;;
  .assign 16 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr))) ;;
  .assign 17 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 18 (.load (.bin .add (.reg 0) (.const compOffECap)))

/-- Builds `[1, tag, v, v', kt', kh'] ++ Lt' ++ Lh'` in `updBuf` (`reg 4`) by filtering out
cross-edges (`isCross[e] ≠ 0`) from `Lt` and `Lh`, and puts `1 + 5 + kt' + kh'` into `reg 23`.
Writes only registers `19..27` and memory `[updBuf, updBuf + 1 + 5 + kt' + kh')`. -/
def compStepSplitBuildStmt (_bApp : ℕ) : Stmt :=
  .store (.reg 4) (.const 1) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 6) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 7) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.reg 8) ;;
  .assign 24 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr))) ;;
  .assign 19 (.bin .add (.reg 1) (.const 5)) ;;
  .assign 20 (.bin .add (.reg 4) (.const 6)) ;;
  compCopyNonCrossSliceStmt 19 20 9 24 21 25 26 27 ;;
  .assign 19 (.bin .add (.reg 19) (.reg 9)) ;;
  compCopyNonCrossSliceStmt 19 20 10 24 22 25 26 27 ;;
  .store (.bin .add (.reg 4) (.const 4)) (.reg 21) ;;
  .store (.bin .add (.reg 4) (.const 5)) (.reg 22) ;;
  .assign 23 (.bin .add (.bin .add (.const 6) (.reg 21)) (.reg 22))

/-- Conditional projected-split dispatch for component in `reg 12`. -/
def compStepSplitDispStmt (bApp bDisp : ℕ) : Stmt :=
  .assign 19 (.load (.bin .add (.reg 15) (.reg 12))) ;;
  .cond (.reg 19)
    (compStepSplitBuildStmt bApp ;;
     .assign 24 (.load (.bin .add (.reg 16) (.reg 12))) ;;
     .call 20 bDisp [.reg 0, .reg 24, .reg 4, .reg 23, .reg 3])
    .nop

/-- `args = [b, uPtr, heap, cntBase, updBuf, splitPtr]`: processes an encoded `.split v v' St Sh`
at `uPtr` (tag 2 or 3), records `v'` at `splitPtr`, and returns `uPtr + 5 + kt + kh`. -/
def compStepSplitProc (bApp bMark bDisp : ℕ) : Stmt :=
  compStepSplitPrefStmt ;;
  .call 20 bMark [.reg 13, .reg 14, .reg 2, .reg 12] ;;
  compStepSplitDispStmt bApp bDisp ;;
  .ret (.bin .add (.bin .add (.bin .add (.reg 1) (.const 5)) (.reg 9)) (.reg 10))

lemma compStepSplitProc_noRand (bApp bMark bDisp : ℕ) :
    (compStepSplitProc bApp bMark bDisp).NoRand := by
  simp [compStepSplitProc, compStepSplitPrefStmt, compStepSplitDispStmt, compStepSplitBuildStmt,
    compCopyNonCrossSliceStmt_noRand, Stmt.NoRand]

/-! ## 2. Filtered-slice copy verification (`compCopyNonCrossSlice_runs`) -/

set_option maxHeartbeats 800000 in
/-- Executes `compCopyNonCrossSliceStmt`, copying `L' = L.filter (fun e => decide (st.mem (crBase + e) = 0))`
into `[dst, dst + L'.length)`, setting `rDst := dst + L'.length` and `rCnt := L'.length`, and
touching no other memory or registers outside `{rDst, rCnt, rIdx, rElem, rFlag}`. -/
lemma compCopyNonCrossSlice_runs {w rSrc rDst rLen rCrBase rCnt rIdx rElem rFlag
    src dst crBase eCap : ℕ} {L : List ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hnd : [rSrc, rDst, rLen, rCrBase, rCnt, rIdx, rElem, rFlag].Nodup)
    (hw16 : 16 ≤ 2 ^ w)
    (hsrc_w : src + L.length < 2 ^ w) (hdst_w : dst + L.length < 2 ^ w)
    (hcr_w : crBase + eCap < 2 ^ w)
    (hsrc_disj : src + L.length ≤ dst ∨ dst + L.length ≤ src)
    (hcr_disj : crBase + eCap ≤ dst ∨ dst + L.length ≤ crBase)
    (hL_at : ListAt st.mem src L) (hL_lt : ∀ e ∈ L, e < eCap)
    (hrSrc : st.regs rSrc = src) (hrDst : st.regs rDst = dst)
    (hrLen : st.regs rLen = L.length) (hrCrBase : st.regs rCrBase = crBase) :
    let L' := L.filter fun e => decide (st.mem (crBase + e) = 0)
    ∃ st' c,
      Runs w p ω (compCopyNonCrossSliceStmt rSrc rDst rLen rCrBase rCnt rIdx rElem rFlag)
        st .normal st' c ∧
      (∀ r, r ≠ rDst → r ≠ rCnt → r ≠ rIdx → r ≠ rElem → r ≠ rFlag → st'.regs r = st.regs r) ∧
      st'.regs rDst = dst + L'.length ∧
      st'.regs rCnt = L'.length ∧
      ListAt st'.mem dst L' ∧
      (∀ a, a < dst ∨ dst + L'.length ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 40 * L.length + 12 := by
  intro L'
  have hw0 : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  rcases hnd with ⟨⟨hSD, hSL, hSCr, hSC, hSI, hSE, hSF⟩,
    ⟨hDL, hDCr, hDC, hDI, hDE, hDF⟩,
    ⟨hLCr, hLC, hLI, hLE, hLF⟩,
    ⟨hCrC, hCrI, hCrE, hCrF⟩,
    ⟨hCI, hCE, hCF⟩, ⟨hIE, hIF⟩, ⟨hEF, _⟩⟩
  let st1 : State := { st with regs := Function.update st.regs rCnt 0 }
  let st2 : State := { st1 with regs := Function.update st1.regs rIdx 0 }
  have hinit1 : Runs w p ω (.assign rCnt (.const 0)) st .normal st1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  have hinit2 : Runs w p ω (.assign rIdx (.const 0)) st1 .normal st2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  let pred : ℕ → Bool := fun e => decide (st.mem (crBase + e) = 0)
  have hloop : ∀ rem i (pref : List ℕ) (s : State), i ≤ L.length → L.length - i = rem →
      pref = (L.take i).filter pred →
      s.regs rSrc = src → s.regs rDst = dst + pref.length → s.regs rLen = L.length →
      s.regs rCrBase = crBase → s.regs rCnt = pref.length → s.regs rIdx = i →
      (∀ r, r ≠ rDst → r ≠ rCnt → r ≠ rIdx → r ≠ rElem → r ≠ rFlag → s.regs r = st.regs r) →
      ListAt s.mem dst pref →
      (∀ a, a < dst ∨ dst + pref.length ≤ a → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω (.loop (.bin .lt (.reg rIdx) (.reg rLen))
          (.assign rElem (.load (.bin .add (.reg rSrc) (.reg rIdx))) ;;
           .assign rFlag (.load (.bin .add (.reg rCrBase) (.reg rElem))) ;;
           .cond (.reg rFlag)
             .nop
             (.store (.reg rDst) (.reg rElem) ;;
              .assign rDst (.bin .add (.reg rDst) (.const 1)) ;;
              .assign rCnt (.bin .add (.reg rCnt) (.const 1))) ;;
           .assign rIdx (.bin .add (.reg rIdx) (.const 1)))) s .normal st' c ∧
        (∀ r, r ≠ rDst → r ≠ rCnt → r ≠ rIdx → r ≠ rElem → r ≠ rFlag → st'.regs r = st.regs r) ∧
        st'.regs rDst = dst + L'.length ∧
        st'.regs rCnt = L'.length ∧
        ListAt st'.mem dst L' ∧
        (∀ a, a < dst ∨ dst + L'.length ≤ a → st'.mem a = st.mem a) ∧
        c ≤ 40 * rem + 6 := by
    intro rem
    induction rem with
    | zero =>
      intro i pref s hi hrem hpref_def hS hD hL hCr hC hI hregs hLA hfr
      have hieq : i = L.length := by omega
      subst hieq
      have hpref : pref = L' := by rw [hpref_def]; simp [L', pred]
      rw [hpref] at hD hC hLA hfr
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hI, hL],
        rfl, rfl, by simp [Expr.size]⟩), hregs, hD, hC, hLA, hfr, by omega⟩
    | succ rem ih =>
      intro i pref s hi hrem hpref_def hS hD hL hCr hC hI hregs hLA hfr
      have hilt : i < L.length := by omega
      have hpref_le : pref.length ≤ i := by
        rw [hpref_def]
        exact le_trans (List.length_filter_le _ _) (List.length_take_le _ _)
      obtain ⟨e, he_eq⟩ : ∃ e, L[i]'hilt = e := ⟨L[i]'hilt, rfl⟩
      have he_lt : e < eCap := hL_lt e (he_eq ▸ List.getElem_mem hilt)
      have hsrc_out : src + i < dst ∨ dst + pref.length ≤ src + i :=
        hsrc_disj.imp (fun h => by omega) (fun h => by omega)
      have hcr_out : crBase + e < dst ∨ dst + pref.length ≤ crBase + e :=
        hcr_disj.imp (fun h => by omega) (fun h => by omega)
      have hsrc_eq : s.mem (src + i) = e := (hfr (src + i) hsrc_out).trans ((hL_at i hilt).trans he_eq)
      have hcr_eq : s.mem (crBase + e) = st.mem (crBase + e) := hfr (crBase + e) hcr_out
      let s1 : State := { s with regs := Function.update s.regs rElem e }
      let s2 : State := { s1 with regs := Function.update s1.regs rFlag (st.mem (crBase + e)) }
      have hs1 : Runs w p ω (.assign rElem (.load (.bin .add (.reg rSrc) (.reg rIdx)))) s .normal s1 5 :=
        runs_assign_iff.mpr ⟨e,
          Expr.eval_load_of_eq (by simp [Expr.eval, BinOp.eval, hS, hI, show src + i < 2 ^ w by omega]) hsrc_eq,
          rfl, rfl, by simp [Expr.size]⟩
      have hs2 : Runs w p ω (.assign rFlag (.load (.bin .add (.reg rCrBase) (.reg rElem)))) s1 .normal s2 5 :=
        runs_assign_iff.mpr ⟨st.mem (crBase + e),
          Expr.eval_load_of_eq (by simp [s1, Expr.eval, BinOp.eval, Function.update_of_ne hCrE, hCr,
            show crBase + e < 2 ^ w by omega]) hcr_eq,
          rfl, rfl, by simp [Expr.size]⟩
      have hcond : ∃ s3 cCond,
          Runs w p ω (.cond (.reg rFlag) .nop
            (.store (.reg rDst) (.reg rElem) ;;
             .assign rDst (.bin .add (.reg rDst) (.const 1)) ;;
             .assign rCnt (.bin .add (.reg rCnt) (.const 1)))) s2 .normal s3 cCond ∧
          cCond ≤ 16 ∧
          (∀ r, r ≠ rDst → r ≠ rCnt → r ≠ rIdx → r ≠ rElem → r ≠ rFlag → s3.regs r = st.regs r) ∧
          s3.regs rIdx = i ∧
          s3.regs rDst = dst + ((L.take (i + 1)).filter pred).length ∧
          s3.regs rCnt = ((L.take (i + 1)).filter pred).length ∧
          ListAt s3.mem dst ((L.take (i + 1)).filter pred) ∧
          (∀ a, a < dst ∨ dst + ((L.take (i + 1)).filter pred).length ≤ a → s3.mem a = st.mem a) := by
        have hpref_succ : (L.take (i + 1)).filter pred =
            if st.mem (crBase + e) = 0 then pref ++ [e] else pref := by
          rw [List.take_succ_eq_append_getElem hilt, he_eq, List.filter_append, List.filter_cons,
            List.filter_nil, ← hpref_def]
          by_cases hfl : st.mem (crBase + e) = 0 <;> simp [pred, hfl]
        by_cases hfl : st.mem (crBase + e) = 0
        · rw [hpref_succ, ite_eq_left hfl]
          let t1 : State := { s2 with mem := Function.update s2.mem (dst + pref.length) e }
          let t2 : State := { t1 with regs := Function.update t1.regs rDst (dst + pref.length + 1) }
          let t3 : State := { t2 with regs := Function.update t2.regs rCnt (pref.length + 1) }
          have ht1 : Runs w p ω (.store (.reg rDst) (.reg rElem)) s2 .normal t1 3 :=
            runs_store_iff.mpr ⟨dst + pref.length, e,
              by simp [s2, s1, Expr.eval, Function.update_of_ne hDF, Function.update_of_ne hDE, hD],
              by simp [s2, s1, Expr.eval, Function.update_of_ne hEF], rfl, rfl, by simp [Expr.size]⟩
          have ht2 : Runs w p ω (.assign rDst (.bin .add (.reg rDst) (.const 1))) t1 .normal t2 4 :=
            runs_assign_iff.mpr ⟨dst + pref.length + 1,
              by simp [t1, s2, s1, Expr.eval, BinOp.eval, Function.update_of_ne hDF, Function.update_of_ne hDE,
                hD, hw1, show dst + pref.length + 1 < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have ht3 : Runs w p ω (.assign rCnt (.bin .add (.reg rCnt) (.const 1))) t2 .normal t3 4 :=
            runs_assign_iff.mpr ⟨pref.length + 1,
              by simp [t2, t1, s2, s1, Expr.eval, BinOp.eval, Function.update_of_ne (Ne.symm hDC),
                Function.update_of_ne hCF, Function.update_of_ne hCE, hC, hw1, show pref.length + 1 < 2 ^ w by omega],
              rfl, rfl, by simp [Expr.size]⟩
          have hbr : Runs w p ω _ s2 .normal t3 13 :=
            runs_seq_iff.mpr (Or.inr ⟨t1, 3, 9, ht1, runs_seq_iff.mpr (Or.inr ⟨t2, 4, 4, ht2, ht3, rfl⟩), rfl⟩)
          refine ⟨t3, 15, runs_cond_iff.mpr ⟨0, 13, by simp [s2, Expr.eval, hfl], by simpa using hbr, by simp [Expr.size]⟩,
            by omega,
            fun r h1 h2 h3 h4 h5 => by
              simp [t3, t2, t1, s2, s1, Function.update_of_ne h2, Function.update_of_ne h1,
                Function.update_of_ne h5, Function.update_of_ne h4, hregs r h1 h2 h3 h4 h5],
            by simp [t3, t2, t1, s2, s1, Function.update_of_ne (Ne.symm hCI), Function.update_of_ne (Ne.symm hDI),
              Function.update_of_ne hIF, Function.update_of_ne hIE, hI],
            by simp [t3, t2, Function.update_of_ne hDC]; omega,
            by simp [t3],
            fun k hk => by
              simp only [List.length_append, List.length_singleton] at hk
              dsimp only [t3, t2, t1, s2, s1]
              by_cases hkp : k < pref.length
              · rw [Function.update_of_ne (by omega), List.getElem_append_left hkp]; exact hLA k hkp
              · have hkeq : k = pref.length := by omega
                subst hkeq
                rw [Function.update_self, List.getElem_append_right (le_refl _)]
                simp,
            fun a ha => by
              simp only [List.length_append, List.length_singleton] at ha
              dsimp only [t3, t2, t1, s2, s1]
              rw [Function.update_of_ne (by omega)]
              exact hfr a (by omega)⟩
        · rw [hpref_succ, ite_eq_right hfl]
          refine ⟨s2, 3, runs_cond_iff.mpr ⟨st.mem (crBase + e), 1, by simp [s2, Expr.eval],
            by simpa [hfl] using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩,
            by omega,
            fun r h1 h2 h3 h4 h5 => by
              simp [s2, s1, Function.update_of_ne h5, Function.update_of_ne h4, hregs r h1 h2 h3 h4 h5],
            by simp [s2, s1, Function.update_of_ne hIF, Function.update_of_ne hIE, hI],
            by simp [s2, s1, Function.update_of_ne hDF, Function.update_of_ne hDE, hD],
            by simp [s2, s1, Function.update_of_ne hCF, Function.update_of_ne hCE, hC],
            hLA, hfr⟩
      obtain ⟨s3, cCond, hrunC, hcCond, hr3, hI3, hD3, hC3, hLA3, hfr3⟩ := hcond
      let s4 : State := { s3 with regs := Function.update s3.regs rIdx (i + 1) }
      have hs4 : Runs w p ω (.assign rIdx (.bin .add (.reg rIdx) (.const 1))) s3 .normal s4 4 :=
        runs_assign_iff.mpr ⟨i + 1, by simp [Expr.eval, BinOp.eval, hI3, hw1, show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal s4 (5 + 5 + cCond + 4 + 3) :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hs1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2,
            runs_seq_iff.mpr (Or.inr ⟨s3, cCond, 4, hrunC, hs4, rfl⟩), rfl⟩), by omega⟩)
      have hr4 : ∀ r, r ≠ rDst → r ≠ rCnt → r ≠ rIdx → r ≠ rElem → r ≠ rFlag → s4.regs r = st.regs r :=
        fun r h1 h2 h3 h4 h5 => by simp [s4, Function.update_of_ne h3, hr3 r h1 h2 h3 h4 h5]
      obtain ⟨st', c', hrun', hr', hD', hC', hLA', hfr', hc'⟩ :=
        ih (i + 1) ((L.take (i + 1)).filter pred) s4 (by omega) (by omega) rfl
          (by rw [hr4 rSrc hSD hSC hSI hSE hSF, hrSrc])
          (by simp [s4, Function.update_of_ne hDI, hD3])
          (by rw [hr4 rLen (Ne.symm hDL) hLC hLI hLE hLF, hrLen])
          (by rw [hr4 rCrBase (Ne.symm hDCr) hCrC hCrI hCrE hCrF, hrCrBase])
          (by simp [s4, Function.update_of_ne hCI, hC3])
          (by simp [s4]) hr4 hLA3 hfr3
      refine ⟨st', 3 + (5 + 5 + cCond + 4 + 3) + c' + 1,
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s4, _, c',
          by simp [Expr.eval, BinOp.eval, hI, hL, hilt, hw1], by decide, hbody, hrun', by simp [Expr.size]⟩)),
        hr', hD', hC', hLA', hfr', by omega⟩
  obtain ⟨st', c', hrun', hr', hD', hC', hLA', hfr', hc'⟩ :=
    hloop L.length 0 [] st2 (Nat.zero_le _) (Nat.sub_zero _) rfl
      (by simp [st2, st1, Function.update_of_ne hSI, Function.update_of_ne hSC, hrSrc])
      (by simp [st2, st1, Function.update_of_ne hDI, Function.update_of_ne hDC, hrDst])
      (by simp [st2, st1, Function.update_of_ne hLI, Function.update_of_ne hLC, hrLen])
      (by simp [st2, st1, Function.update_of_ne hCrI, Function.update_of_ne hCrC, hrCrBase])
      (by simp [st2, st1, Function.update_of_ne hCI])
      (by simp [st2])
      (fun r _ h2 h3 _ _ => by simp [st2, st1, Function.update_of_ne h3, Function.update_of_ne h2])
      (fun _ hi => by simp at hi) (fun _ _ => rfl)
  exact ⟨st', 2 + 2 + c' + 2,
    runs_seq_iff.mpr (Or.inr ⟨st1, 2, _, hinit1, runs_seq_iff.mpr (Or.inr ⟨st2, 2, c', hinit2, hrun', rfl⟩), by omega⟩),
    hr', hD', hC', hLA', hfr', by omega⟩

/-! ## 3. Prefix verification (`compStepSplitPref_runs`) -/

set_option maxHeartbeats 600000 in
/-- Executes `compStepSplitPrefStmt`, decoding `[tag, v, v', kt, kh]`, writing `vComp[v'] := cv`
and `mem[splitPtr] := v'`, and populating registers `6..18`. -/
lemma compStepSplitPref_runs {w k b uPtr heap cntBase updBuf splitPtr tag v v' kt kh : ℕ}
    {p : Program} {x : CompLSFMeta k} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hend_le_sp : x.endAddr ≤ splitPtr) (hsp_w : splitPtr < 2 ^ w)
    (hheap_w : heap + 1 < 2 ^ w) (hu_w : uPtr + 5 < 2 ^ w)
    (hhdr : compHeaderAt mem b x)
    (hu_in : mem uPtr = tag ∧ mem (uPtr + 1) = v ∧ mem (uPtr + 2) = v' ∧
      mem (uPtr + 3) = kt ∧ mem (uPtr + 4) = kh)
    (hv_lt : v < x.vCap) (hv'_lt : v' < x.vCap) {cv : Fin x.numComps}
    (hvc_m : mem (compVCompBase b + v) = cv.1) :
    let st0 := startState [b, uPtr, heap, cntBase, updBuf, splitPtr] mem pos
    let m1 := Function.update mem (compVCompBase b + v') cv.1
    let m2 := Function.update m1 splitPtr v'
    let regsP :=
      Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update
        st0.regs 6 tag) 7 v) 8 v') 9 kt) 10 kh) 11 (compVCompBase b)) 12 cv.1)
        13 (compTouchMarkBase b x.vCap x.eCap)) 14 (heap + 1))
        15 (compEdgefulBase b x.vCap)) 16 (compEdgefulIdxBase b x.vCap))
        17 x.vCap) 18 x.eCap
    ∃ cP, Runs w p ω compStepSplitPrefStmt st0 .normal { st0 with regs := regsP, mem := m2 } cP ∧
      cP ≤ 100 := by
  intro st0 m1 m2 regsP
  have hend_w : x.endAddr < 2 ^ w := lt_of_le_of_lt hend_le_sp hsp_w
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := lt_of_le_of_lt hTE hend_w
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hte_w ⊢; omega
  have h_off_w : ∀ off < compHdrSize, b + off < 2 ^ w := fun off hoff => by omega
  have hne_hdr : ∀ off < compHdrSize, b + off ≠ compVCompBase b + v' ∧ b + off ≠ splitPtr := fun off hoff => by
    have h1 : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    dsimp only [compVCompBase, compHdrSize] at h1 hoff ⊢; exact ⟨by omega, by omega⟩
  have hvc_v_w : compVCompBase b + v < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hvc_v'_w : compVCompBase b + v' < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compVCompBase, compHdrSize] at hte_w ⊢; omega
  have hm2_fr : ∀ z, z ≠ compVCompBase b + v' → z ≠ splitPtr → m2 z = mem z := fun z h1 h2 => by
    simp [m2, m1, Function.update_of_ne h2, Function.update_of_ne h1]
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw9 : 9 < 2 ^ w := by omega
  have hw10 : 10 < 2 ^ w := by omega
  have hw11 : 11 < 2 ^ w := by omega
  have hw19 : 19 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have hh_0 : mem b = x.vCap := by simpa [compOffVCap] using hhdr.1
  have hh_1 : mem (b + 1) = x.eCap := by simpa [compOffECap] using hhdr.2.1
  have hh_9 : mem (b + 9) = compVCompBase b := by simpa [compOffVCompPtr] using hhdr.2.2.2.2.2.2.2.2.2.1
  have hh_10 : mem (b + 10) = compEdgefulBase b x.vCap := by simpa [compOffEdgefulPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hh_11 : mem (b + 11) = compEdgefulIdxBase b x.vCap := by simpa [compOffEdgefulIdxPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have hh_19 : mem (b + 19) = compTouchMarkBase b x.vCap x.eCap := by simpa [compOffTouchMarkPtr] using hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let st1 : State := { st0 with regs := Function.update st0.regs 6 tag }
  let st2 : State := { st1 with regs := Function.update st1.regs 7 v }
  let st3 : State := { st2 with regs := Function.update st2.regs 8 v' }
  let st4 : State := { st3 with regs := Function.update st3.regs 9 kt }
  let st5 : State := { st4 with regs := Function.update st4.regs 10 kh }
  let st6 : State := { st5 with regs := Function.update st5.regs 11 (compVCompBase b) }
  let st7 : State := { st6 with regs := Function.update st6.regs 12 cv.1 }
  let st8 : State := { st7 with mem := m1 }
  let st9 : State := { st8 with mem := m2 }
  let st10 : State := { st9 with regs := Function.update st9.regs 13 (compTouchMarkBase b x.vCap x.eCap) }
  let st11 : State := { st10 with regs := Function.update st10.regs 14 (heap + 1) }
  let st12 : State := { st11 with regs := Function.update st11.regs 15 (compEdgefulBase b x.vCap) }
  let st13 : State := { st12 with regs := Function.update st12.regs 16 (compEdgefulIdxBase b x.vCap) }
  let st14 : State := { st13 with regs := Function.update st13.regs 17 x.vCap }
  have s1 : Runs w p ω (.assign 6 (.load (.reg 1))) st0 .normal st1 3 := by
    rw [runs_assign_iff]; refine ⟨tag, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st0, startState, Expr.eval, hu_in.1]
  have s2 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 1) (.const 1)))) st1 .normal st2 5 := by
    rw [runs_assign_iff]; refine ⟨v, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st1, st0, startState, Expr.eval, BinOp.eval, hw0, show uPtr + 1 < 2 ^ w by omega, hu_in.2.1]
  have s3 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 1) (.const 2)))) st2 .normal st3 5 := by
    rw [runs_assign_iff]; refine ⟨v', ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st2, st1, st0, startState, Expr.eval, BinOp.eval, hw2, show uPtr + 2 < 2 ^ w by omega, hu_in.2.2.1]
  have s4 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 1) (.const 3)))) st3 .normal st4 5 := by
    rw [runs_assign_iff]; refine ⟨kt, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, hw3, show uPtr + 3 < 2 ^ w by omega, hu_in.2.2.2.1]
  have s5 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 1) (.const 4)))) st4 .normal st5 5 := by
    rw [runs_assign_iff]; refine ⟨kh, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, hw4, show uPtr + 4 < 2 ^ w by omega, hu_in.2.2.2.2]
  have s6 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 0) (.const compOffVCompPtr)))) st5 .normal st6 5 := by
    rw [runs_assign_iff]; refine ⟨compVCompBase b, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, compOffVCompPtr, hw9, h_off_w 9 (by decide), hh_9]
  have s7 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 11) (.reg 7)))) st6 .normal st7 5 := by
    rw [runs_assign_iff]; refine ⟨cv.1, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, hvc_v_w, hvc_m]
  have s8 : Runs w p ω (.store (.bin .add (.reg 11) (.reg 8)) (.reg 12)) st7 .normal st8 5 := by
    rw [runs_store_iff]; refine ⟨compVCompBase b + v', cv.1, ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [st7, st6, st5, st4, st3, Expr.eval, BinOp.eval, hvc_v'_w]
    · simp [st7, Expr.eval]
  have s9 : Runs w p ω (.store (.reg 5) (.reg 8)) st8 .normal st9 3 := by
    rw [runs_store_iff]; refine ⟨splitPtr, v', ?_, ?_, rfl, rfl, by simp [Expr.size]⟩
    · simp [st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval]
    · simp [st8, st7, st6, st5, st4, st3, Expr.eval]
  have s10 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr)))) st9 .normal st10 5 := by
    rw [runs_assign_iff]; refine ⟨compTouchMarkBase b x.vCap x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h19 := hne_hdr 19 (by decide)
    simp [st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval,
      compOffTouchMarkPtr, hw19, h_off_w 19 (by decide), hm2_fr _ h19.1 h19.2, hh_19]
  have s11 : Runs w p ω (.assign 14 (.bin .add (.reg 2) (.const 1))) st10 .normal st11 4 := by
    rw [runs_assign_iff]; refine ⟨heap + 1, ?_, rfl, rfl, by simp [Expr.size]⟩
    simp [st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval, hw0, hheap_w]
  have s12 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const compOffEdgefulPtr)))) st11 .normal st12 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgefulBase b x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h10 := hne_hdr 10 (by decide)
    simp [st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval,
      compOffEdgefulPtr, hw10, h_off_w 10 (by decide), hm2_fr _ h10.1 h10.2, hh_10]
  have s13 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 0) (.const compOffEdgefulIdxPtr)))) st12 .normal st13 5 := by
    rw [runs_assign_iff]; refine ⟨compEdgefulIdxBase b x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h11 := hne_hdr 11 (by decide)
    simp [st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState, Expr.eval, BinOp.eval,
      compOffEdgefulIdxPtr, hw11, h_off_w 11 (by decide), hm2_fr _ h11.1 h11.2, hh_11]
  have s14 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 0) (.const compOffVCap)))) st13 .normal st14 5 := by
    rw [runs_assign_iff]; refine ⟨x.vCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h0 := hne_hdr 0 (by decide)
    simp [st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState,
      Expr.eval, BinOp.eval, compOffVCap, show b < 2 ^ w by omega, hm2_fr _ (by simpa using h0.1) (by simpa using h0.2), hh_0]
  have s15 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 0) (.const compOffECap)))) st14 .normal
      { st0 with regs := regsP, mem := m2 } 5 := by
    rw [runs_assign_iff]; refine ⟨x.eCap, ?_, rfl, rfl, by simp [Expr.size]⟩
    have h1 := hne_hdr 1 (by decide)
    simp [st14, st13, st12, st11, st10, st9, st8, st7, st6, st5, st4, st3, st2, st1, st0, startState,
      Expr.eval, BinOp.eval, compOffECap, hw0, h_off_w 1 (by decide), hm2_fr _ h1.1 h1.2, hh_1]
  refine ⟨84, ?_, by omega⟩
  exact runs_seq_iff.mpr (Or.inr ⟨_, _, _, s1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s2,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s3,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s4,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s5,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s6,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s7,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s8,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s9,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s10,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s11,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s12,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s13,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, s14, s15, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)

/-! ## 4. Projected split-buffer builder (`compStepSplitBuild_runs`) -/

set_option maxHeartbeats 1200000 in
/-- Executes `compStepSplitBuildStmt bApp`, writing `[1, tag, v, v', kt', kh'] ++ Lt' ++ Lh'` at
`updBuf`, where `Lt'` and `Lh'` filter out cross-edges (`st.mem (isCrossBase + e) ≠ 0`). Leaves
`1 + 5 + kt' + kh'` in `reg 23`, preserves `reg 0..18`, and touches only `[updBuf, updBuf + 1 + len')`. -/
lemma compStepSplitBuild_runs {w k b bApp uPtr updBuf tag v v' : ℕ} {Lt Lh : List ℕ}
    {p : Program} {x : CompLSFMeta k} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hr0 : st.regs 0 = b) (hr1 : st.regs 1 = uPtr) (hr4 : st.regs 4 = updBuf)
    (hr6 : st.regs 6 = tag) (hr7 : st.regs 7 = v) (hr8 : st.regs 8 = v')
    (hr9 : st.regs 9 = Lt.length) (hr10 : st.regs 10 = Lh.length)
    (hTE : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k ≤ x.endAddr)
    (hend_le_buf : x.endAddr ≤ updBuf)
    (hu_disj : uPtr + (5 + Lt.length + Lh.length) ≤ updBuf)
    (hbuf_w : updBuf + 6 + Lt.length + Lh.length < 2 ^ w)
    (hLt_at : ListAt st.mem (uPtr + 5) Lt)
    (hLh_at : ListAt st.mem (uPtr + 5 + Lt.length) Lh)
    (hLt_lt : ∀ e ∈ Lt, e < x.eCap)
    (hLh_lt : ∀ e ∈ Lh, e < x.eCap)
    (hcr_ptr : st.mem (b + compOffIsCrossPtr) = compIsCrossBase b x.vCap x.eCap) :
    let crBase := compIsCrossBase b x.vCap x.eCap
    let Lt' := Lt.filter fun e => decide (st.mem (crBase + e) = 0)
    let Lh' := Lh.filter fun e => decide (st.mem (crBase + e) = 0)
    let len' := 5 + Lt'.length + Lh'.length
    ∃ st' c,
      Runs w p ω (compStepSplitBuildStmt bApp) st .normal st' c ∧
      (∀ r < 19, st'.regs r = st.regs r) ∧
      st'.regs 23 = 1 + len' ∧
      st'.mem updBuf = 1 ∧
      ListAt st'.mem (updBuf + 1) ([tag, v, v', Lt'.length, Lh'.length] ++ Lt' ++ Lh') ∧
      (∀ a, a < updBuf ∨ updBuf + 1 + len' ≤ a → st'.mem a = st.mem a) ∧
      c ≤ 40 * (5 + Lt.length + Lh.length) + 120 := by
  intro crBase Lt' Lh' len'
  have hLt'_le : Lt'.length ≤ Lt.length := List.length_filter_le _ _
  have hLh'_le : Lh'.length ≤ Lh.length := List.length_filter_le _ _
  have hw0 : w ≠ 0 := by intro h; subst h; simp at hw16
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw5 : 5 < 2 ^ w := by omega
  have hw6 : 6 < 2 ^ w := by omega
  have hte_w : compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k < 2 ^ w := by omega
  have hb_hdr_w : b + compHdrSize < 2 ^ w := by
    dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hte_w ⊢; omega
  have hw16' : 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have hb16 : b + 16 < 2 ^ w := by dsimp only [compHdrSize] at hb_hdr_w; omega
  have hcr_end_le : crBase + x.eCap ≤ x.endAddr := by
    have : crBase + x.eCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [crBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize, compTablesEnd,
        compHandlesBase, compStaticSize]; omega
    omega
  have hcr_end_w : crBase + x.eCap < 2 ^ w := by omega
  let m1 := Function.update st.mem updBuf 1
  let m2 := Function.update m1 (updBuf + 1) tag
  let m3 := Function.update m2 (updBuf + 2) v
  let m4 := Function.update m3 (updBuf + 3) v'
  let s1 : State := { st with mem := m1 }
  let s2 : State := { s1 with mem := m2 }
  let s3 : State := { s2 with mem := m3 }
  let s4 : State := { s3 with mem := m4 }
  let s5 : State := { s4 with regs := Function.update s4.regs 24 crBase }
  let s6 : State := { s5 with regs := Function.update s5.regs 19 (uPtr + 5) }
  let s7 : State := { s6 with regs := Function.update s6.regs 20 (updBuf + 6) }
  have hm4_fr : ∀ a, a < updBuf ∨ updBuf + 4 ≤ a → m4 a = st.mem a := fun a ha => by
    simp [m4, m3, m2, m1, Function.update_of_ne (show a ≠ updBuf + 3 by omega),
      Function.update_of_ne (show a ≠ updBuf + 2 by omega),
      Function.update_of_ne (show a ≠ updBuf + 1 by omega),
      Function.update_of_ne (show a ≠ updBuf by omega)]
  have hs1 : Runs w p ω (.store (.reg 4) (.const 1)) st .normal s1 3 :=
    runs_store_iff.mpr ⟨updBuf, 1, by simp [Expr.eval, hr4], by simp [Expr.eval, hw0], rfl, rfl, by simp [Expr.size]⟩
  have hs2 : Runs w p ω (.store (.bin .add (.reg 4) (.const 1)) (.reg 6)) s1 .normal s2 5 :=
    runs_store_iff.mpr ⟨updBuf + 1, tag, by simp [s1, Expr.eval, BinOp.eval, hr4, hw0, show updBuf + 1 < 2 ^ w by omega],
      by simp [s1, Expr.eval, hr6], rfl, rfl, by simp [Expr.size]⟩
  have hs3 : Runs w p ω (.store (.bin .add (.reg 4) (.const 2)) (.reg 7)) s2 .normal s3 5 :=
    runs_store_iff.mpr ⟨updBuf + 2, v, by simp [s2, s1, Expr.eval, BinOp.eval, hr4, hw2, show updBuf + 2 < 2 ^ w by omega],
      by simp [s2, s1, Expr.eval, hr7], rfl, rfl, by simp [Expr.size]⟩
  have hs4 : Runs w p ω (.store (.bin .add (.reg 4) (.const 3)) (.reg 8)) s3 .normal s4 5 :=
    runs_store_iff.mpr ⟨updBuf + 3, v', by simp [s3, s2, s1, Expr.eval, BinOp.eval, hr4, hw3, show updBuf + 3 < 2 ^ w by omega],
      by simp [s3, s2, s1, Expr.eval, hr8], rfl, rfl, by simp [Expr.size]⟩
  have hs5 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 0) (.const compOffIsCrossPtr)))) s4 .normal s5 5 := by
    rw [runs_assign_iff]; refine ⟨crBase, ?_, rfl, rfl, by simp [Expr.size]⟩
    have hlt_buf : b + 16 < updBuf := by
      have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
        dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
      dsimp only [compHdrSize] at this; omega
    have hcr_ptr' : st.mem (b + 16) = crBase := hcr_ptr
    simp [s4, s3, s2, s1, Expr.eval, BinOp.eval, hr0, compOffIsCrossPtr, hw16', hb16,
      hm4_fr _ (Or.inl hlt_buf), hcr_ptr']
  have hs6 : Runs w p ω (.assign 19 (.bin .add (.reg 1) (.const 5))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨uPtr + 5, by simp [s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr1, hw5, show uPtr + 5 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hs7 : Runs w p ω (.assign 20 (.bin .add (.reg 4) (.const 6))) s6 .normal s7 4 :=
    runs_assign_iff.mpr ⟨updBuf + 6, by simp [s6, s5, s4, s3, s2, s1, Expr.eval, BinOp.eval, hr4, hw6, show updBuf + 6 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hLt_s7 : ListAt s7.mem (uPtr + 5) Lt := fun i hi =>
    (hm4_fr (uPtr + 5 + i) (Or.inl (by omega))).trans (hLt_at i hi)
  have hcr_s7 : ∀ e < x.eCap, s7.mem (crBase + e) = st.mem (crBase + e) := fun e he =>
    hm4_fr (crBase + e) (Or.inl (by omega))
  obtain ⟨s8, c1, hs8, hr8_eq, hD8, hC8, hLA8, hfr8, hc1⟩ :=
    compCopyNonCrossSlice_runs (rSrc := 19) (rDst := 20) (rLen := 9) (rCrBase := 24)
      (rCnt := 21) (rIdx := 25) (rElem := 26) (rFlag := 27)
      (src := uPtr + 5) (dst := updBuf + 6) (crBase := crBase) (eCap := x.eCap) (L := Lt)
      (st := s7) (ω := ω) (by decide) hw16 (by omega) (by omega) hcr_end_w
      (Or.inl (by omega)) (Or.inl (by omega)) hLt_s7 hLt_lt
      (by simp [s7, s6]) (by simp [s7]) (by simp [s7, s6, s5, s4, s3, s2, s1, hr9]) (by simp [s7, s6, s5])
  have hLt'_eq : (Lt.filter fun e => decide (s7.mem (crBase + e) = 0)) = Lt' :=
    List.filter_congr fun e he => by rw [hcr_s7 e (hLt_lt e he)]
  rw [hLt'_eq] at hD8 hC8 hLA8 hfr8
  let s9 : State := { s8 with regs := Function.update s8.regs 19 (uPtr + 5 + Lt.length) }
  have hs9 : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.reg 9))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨uPtr + 5 + Lt.length,
      by simp [Expr.eval, BinOp.eval, hr8_eq 19 (by omega) (by omega) (by omega) (by omega) (by omega),
        hr8_eq 9 (by omega) (by omega) (by omega) (by omega) (by omega), s7, s6, s5, s4, s3, s2, s1, hr9,
        show uPtr + 5 + Lt.length < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hLh_s9 : ListAt s9.mem (uPtr + 5 + Lt.length) Lh := fun i hi =>
    (hfr8 (uPtr + 5 + Lt.length + i) (Or.inl (by omega))).trans
      ((hm4_fr (uPtr + 5 + Lt.length + i) (Or.inl (by omega))).trans (hLh_at i hi))
  have hcr_s9 : ∀ e < x.eCap, s9.mem (crBase + e) = st.mem (crBase + e) := fun e he =>
    (hfr8 (crBase + e) (Or.inl (by omega))).trans (hcr_s7 e he)
  obtain ⟨s10, c2, hs10, hr10_eq, _, hC10, hLA10, hfr10, hc2⟩ :=
    compCopyNonCrossSlice_runs (rSrc := 19) (rDst := 20) (rLen := 10) (rCrBase := 24)
      (rCnt := 22) (rIdx := 25) (rElem := 26) (rFlag := 27)
      (src := uPtr + 5 + Lt.length) (dst := updBuf + 6 + Lt'.length) (crBase := crBase) (eCap := x.eCap)
      (L := Lh) (st := s9) (ω := ω) (by decide) hw16 (by omega) (by omega) hcr_end_w
      (Or.inl (by omega)) (Or.inl (by omega)) hLh_s9 hLh_lt
      (by simp [s9]) (by simp [s9, hD8])
      (by simp [s9, hr8_eq 10 (by omega) (by omega) (by omega) (by omega) (by omega), s7, s6, s5, s4, s3, s2, s1, hr10])
      (by simp [s9, hr8_eq 24 (by omega) (by omega) (by omega) (by omega) (by omega), s7, s6, s5])
  have hLh'_eq : (Lh.filter fun e => decide (s9.mem (crBase + e) = 0)) = Lh' :=
    List.filter_congr fun e he => by rw [hcr_s9 e (hLh_lt e he)]
  rw [hLh'_eq] at hC10 hLA10 hfr10
  have hr10_lt19 : ∀ r < 19, s10.regs r = st.regs r := fun r hr => by
    rw [hr10_eq r (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp [s9, show r ≠ 19 by omega, hr8_eq r (by omega) (by omega) (by omega) (by omega) (by omega),
      s7, s6, s5, s4, s3, s2, s1, show r ≠ 20 by omega, show r ≠ 24 by omega]
  have hr10_21 : s10.regs 21 = Lt'.length := by
    rw [hr10_eq 21 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp [s9, hC8]
  let m5 := Function.update s10.mem (updBuf + 4) Lt'.length
  let m6 := Function.update m5 (updBuf + 5) Lh'.length
  let s11 : State := { s10 with mem := m5 }
  let s12 : State := { s11 with mem := m6 }
  let s13 : State := { s12 with regs := Function.update s12.regs 23 (1 + len') }
  have hs11 : Runs w p ω (.store (.bin .add (.reg 4) (.const 4)) (.reg 21)) s10 .normal s11 5 :=
    runs_store_iff.mpr ⟨updBuf + 4, Lt'.length,
      by simp [Expr.eval, BinOp.eval, hr10_lt19 4 (by omega), hr4, hw4, show updBuf + 4 < 2 ^ w by omega],
      by simp [Expr.eval, hr10_21], rfl, rfl, by simp [Expr.size]⟩
  have hs12 : Runs w p ω (.store (.bin .add (.reg 4) (.const 5)) (.reg 22)) s11 .normal s12 5 :=
    runs_store_iff.mpr ⟨updBuf + 5, Lh'.length,
      by simp [s11, Expr.eval, BinOp.eval, hr10_lt19 4 (by omega), hr4, hw5, show updBuf + 5 < 2 ^ w by omega],
      by simp [s11, Expr.eval, hC10], rfl, rfl, by simp [Expr.size]⟩
  have hs13 : Runs w p ω (.assign 23 (.bin .add (.bin .add (.const 6) (.reg 21)) (.reg 22))) s12 .normal s13 6 :=
    runs_assign_iff.mpr ⟨1 + len',
      by simp [s12, s11, Expr.eval, BinOp.eval, hr10_21, hC10, hw6,
        show 6 + Lt'.length < 2 ^ w by omega, show 6 + Lt'.length + Lh'.length < 2 ^ w by omega, len']; omega,
      rfl, rfl, by simp [Expr.size]⟩
  have hrun_full : Runs w p ω (compStepSplitBuildStmt bApp) st .normal s13 (51 + c1 + c2 + 12) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 3, _, hs1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hs2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, hs3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, hs4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, hs5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 4, _, hs6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 4, _, hs7,
      runs_seq_iff.mpr (Or.inr ⟨s8, c1, _, hs8,
      runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, hs9,
      runs_seq_iff.mpr (Or.inr ⟨s10, c2, _, hs10,
      runs_seq_iff.mpr (Or.inr ⟨s11, 5, _, hs11,
      runs_seq_iff.mpr (Or.inr ⟨s12, 5, 6, hs12, hs13, rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  have hm6_ge6 : ∀ z ≥ updBuf + 6, m6 z = s10.mem z := fun z hz => by
    simp [m6, m5, Function.update_of_ne (show z ≠ updBuf + 5 by omega),
      Function.update_of_ne (show z ≠ updBuf + 4 by omega)]
  have hm6_lt4 : ∀ z < updBuf + 4, m6 z = m4 z := fun z hz => by
    simp [m6, m5, Function.update_of_ne (show z ≠ updBuf + 5 by omega),
      Function.update_of_ne (show z ≠ updBuf + 4 by omega)]
    exact (hfr10 z (Or.inl (by omega))).trans (hfr8 z (Or.inl (by omega)))
  refine ⟨s13, 51 + c1 + c2 + 12, hrun_full,
    fun r hr => by simp [s13, s12, s11, show r ≠ 23 by omega, hr10_lt19 r hr],
    by simp [s13],
    by change m6 updBuf = 1; rw [hm6_lt4 updBuf (by omega)]
       simp [m4, m3, m2, m1, Function.update_of_ne (show updBuf ≠ updBuf + 3 by omega),
         Function.update_of_ne (show updBuf ≠ updBuf + 2 by omega),
         Function.update_of_ne (show updBuf ≠ updBuf + 1 by omega)],
    fun i hi => by
      change m6 (updBuf + 1 + i) = _
      by_cases h0 : i = 0
      · subst h0; rw [hm6_lt4 (updBuf + 1) (by omega)]
        simp [m4, m3, m2, Function.update_of_ne (show updBuf + 1 ≠ updBuf + 3 by omega),
          Function.update_of_ne (show updBuf + 1 ≠ updBuf + 2 by omega)]
      · by_cases h1 : i = 1
        · subst h1; rw [hm6_lt4 (updBuf + 1 + 1) (by omega)]
          simp [m4, m3, show updBuf + 1 + 1 = updBuf + 2 by omega,
            Function.update_of_ne (show updBuf + 2 ≠ updBuf + 3 by omega)]
        · by_cases h2 : i = 2
          · subst h2; rw [hm6_lt4 (updBuf + 1 + 2) (by omega)]
            simp [m4, show updBuf + 1 + 2 = updBuf + 3 by omega]
          · by_cases h3 : i = 3
            · subst h3
              simp [m6, m5, show updBuf + 1 + 3 = updBuf + 4 by omega,
                Function.update_of_ne (show updBuf + 4 ≠ updBuf + 5 by omega)]
            · by_cases h4 : i = 4
              · subst h4; simp [m6, show updBuf + 1 + 4 = updBuf + 5 by omega]
              · by_cases h5 : i < 5 + Lt'.length
                · rw [hm6_ge6 _ (by omega), hfr10 _ (Or.inl (by omega)),
                    show updBuf + 1 + i = updBuf + 6 + (i - 5) by omega, hLA8 (i - 5) (by omega)]
                  rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
                  simp
                · rw [hm6_ge6 _ (by omega),
                    show updBuf + 1 + i = updBuf + 6 + Lt'.length + (i - (5 + Lt'.length)) by omega,
                    hLA10 (i - (5 + Lt'.length)) (by simp at hi; omega)]
                  rw [List.getElem_append_right (by simp; omega)]
                  congr 1; simp; omega,
    fun a ha => by
      change m6 a = st.mem a
      simp [m6, m5, Function.update_of_ne (show a ≠ updBuf + 5 by dsimp only [len'] at ha; omega),
        Function.update_of_ne (show a ≠ updBuf + 4 by dsimp only [len'] at ha; omega)]
      exact (hfr10 a (by dsimp only [len'] at ha; omega)).trans
        ((hfr8 a (by dsimp only [len'] at ha; omega)).trans (hm4_fr a (by dsimp only [len'] at ha; omega))),
    by omega⟩

end

end MinCostFlow.SparseCore.Program
