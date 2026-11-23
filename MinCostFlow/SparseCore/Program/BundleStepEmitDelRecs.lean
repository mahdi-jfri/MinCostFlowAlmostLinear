module

public import MinCostFlow.SparseCore.Program.BundleStepEmitPop

/-!
# Phase 3 deletion-record emission (`BundleStepEmitDelRecs`)

Verifies Step 3C (`bundleStepEmitDelRecsStmt`): using `r23 = scannedEnds` computed by
`bundleStepEmitBuildCSRStmt`, reserves the output batch buffer
`[batchPtr, batchPtr + 1 + 2 * delCnt + 6 * scannedEnds)`, and emits `[1, e]` deletion records
yielding `BatchBodyAt` matching `B₀.graph.applyBatch (dels.map .delete)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.DynSpanner
open MinCostFlow.DynSpanner.Program

public section

theorem bundleStepEmitDelRecs_runs {w delArr hCur scannedEnds : ℕ}
    {pProg : Program} {ω : ℕ → Bool}
    {B₀ : BundleState} {dels : List ℕ} {st₀ : State}
    (hw16 : 16 ≤ 2 ^ w)
    (hdel_w : delArr + dels.length < 2 ^ w)
    (hdel_at : ListAt st₀.mem delArr dels)
    (hzero : ZeroFrom st₀.mem hCur)
    (hh_w : hCur + 1 + 2 * dels.length + 6 * scannedEnds < 2 ^ w)
    (hdel_disj_h : delArr + dels.length ≤ hCur ∨
      hCur + 1 + 2 * dels.length + 6 * scannedEnds ≤ delArr)
    (hr4 : st₀.regs 4 = hCur)
    (hr16 : st₀.regs 16 = delArr) (hr17 : st₀.regs 17 = dels.length)
    (hr23 : st₀.regs 23 = scannedEnds) :
    let hB : BundleState := { B₀ with edges := B₀.edges \ dels.toFinset }
    ∃ stEnd cEnd,
      Runs w pProg ω bundleStepEmitDelRecsStmt st₀ .normal stEnd cEnd ∧
      (∀ r ≤ 19, r ≠ 4 → stEnd.regs r = st₀.regs r) ∧
      stEnd.regs 4 = hCur + 1 + 2 * dels.length + 6 * scannedEnds ∧
      stEnd.regs 20 = hCur ∧ stEnd.regs 21 = 1 + 2 * dels.length ∧
      stEnd.regs 22 = dels.length ∧
      BatchBodyAt stEnd.mem (hCur + 1) B₀.graph (dels.map Update.delete) (2 * dels.length) ∧
      B₀.graph.applyBatch (dels.map Update.delete) = hB.graph ∧
      ZeroFrom stEnd.mem (hCur + 1 + 2 * dels.length + 6 * scannedEnds) ∧
      (∀ a, (a < hCur + 1 ∨ hCur + 1 + 2 * dels.length ≤ a) → stEnd.mem a = st₀.mem a) ∧
      cEnd ≤ 45 * dels.length + 35 := by
  intro hB
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h6_w : 6 < 2 ^ w := by omega
  -- Step 1: reserve `batchPtr` and init `r21 := 1`, `r22 := 0`
  let r20 := Function.update st₀.regs 20 hCur
  let r4n := Function.update r20 4 (hCur + 1 + 2 * dels.length + 6 * scannedEnds)
  let r21 := Function.update r4n 21 1
  let r22 := Function.update r21 22 0
  let stB : State := { st₀ with regs := r22 }
  have ha20 : Runs w pProg ω (.assign 20 (.reg 4)) st₀ .normal { st₀ with regs := r20 } 2 :=
    runs_assign_iff.mpr ⟨hCur, by simp [Expr.eval, hr4], rfl, rfl, rfl⟩
  have ha4n : Runs w pProg ω (.assign 4 (.bin .add (.bin .add (.bin .add (.reg 20) (.const 1))
      (.bin .mul (.const 2) (.reg 17))) (.bin .mul (.const 6) (.reg 23))))
      { st₀ with regs := r20 } .normal { st₀ with regs := r4n } 12 :=
    runs_assign_iff.mpr ⟨hCur + 1 + 2 * dels.length + 6 * scannedEnds, by
      simp [Expr.eval, BinOp.eval, r20, hr17, hr23, h1_w, h2_w, h6_w,
        show hCur + 1 < 2 ^ w by omega, show 2 * dels.length < 2 ^ w by omega,
        show hCur + 1 + 2 * dels.length < 2 ^ w by omega,
        show 6 * scannedEnds < 2 ^ w by omega, hh_w],
      rfl, rfl, by simp [Expr.size]⟩
  have ha21 : Runs w pProg ω (.assign 21 (.const 1)) { st₀ with regs := r4n } .normal { st₀ with regs := r21 } 2 :=
    runs_assign_iff.mpr ⟨1, by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
  have ha22 : Runs w pProg ω (.assign 22 (.const 0)) { st₀ with regs := r21 } .normal stB 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, h0_w], rfl, rfl, rfl⟩
  -- Step 2: emit `[1, e]` records for `e ∈ dels`
  let emitBody : Stmt :=
    .assign 25 (.load (.bin .add (.reg 16) (.reg 24))) ;;
    .store (.bin .add (.reg 20) (.reg 21)) (.const 1) ;;
    .store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25) ;;
    .assign 21 (.bin .add (.reg 21) (.const 2)) ;;
    .assign 22 (.bin .add (.reg 22) (.const 1))
  let emitInv : ℕ → Unit → State → Prop := fun j _ st =>
    (∀ r ≤ 23, r ≠ 21 → r ≠ 22 → st.regs r = stB.regs r) ∧
    st.regs 21 = 1 + 2 * j ∧ st.regs 22 = j ∧ st.regs 24 = j ∧
    BatchBodyAt st.mem (hCur + 1) B₀.graph ((dels.take j).map Update.delete) (2 * j) ∧
    (∀ a, (a < hCur + 1 ∨ hCur + 1 + 2 * j ≤ a) → st.mem a = st₀.mem a)
  obtain ⟨stEnd, cEmit, _, hrunEmit, ⟨hregsEnd, hr21End, hr22End, _, hbatEnd, hfrEnd⟩, hcEmit⟩ :=
    runs_forRange_pot (w := w) (p := pProg) (ω := ω) (r := 24) (lo := .const 0) (hi := .reg 17)
      (body := emitBody) (fun _ _ => 0) emitInv (fun _ => 29) dels.length (by omega) (fun _ => by omega)
      (st₀ := stB) (a₀ := ())
      (by refine ⟨by simp [Expr.eval, h0_w], ⟨fun r hr _ _ => by simp [show r ≠ 24 by omega],
            by simp [stB, r22, r21], by simp [stB, r22], by simp,
            by simp [BatchBodyAt], fun _ _ => rfl⟩, rfl⟩)
      (fun _ _ _ _ hI => hI.2.2.2.1)
      (fun _ _ st _ hI => by
        have h17 : st.regs 17 = dels.length := by
          rw [hI.1 17 (by decide) (by decide) (by decide)]; simp [stB, r22, r21, r4n, r20, hr17]
        simp [Expr.eval, h17])
      (fun j _ st hj ⟨hregE, hr21E, hr22E, hr24E, hbatE, hfrE⟩ => by
        set e := dels[j]'hj
        have hval_e : st.mem (delArr + j) = e := by
          rw [hfrE (delArr + j) (by clear * - hdel_disj_h hj; omega)]; exact hdel_at j hj
        let r25 := Function.update st.regs 25 e
        let m1 := Function.update st.mem (hCur + (1 + 2 * j)) 1
        let m2 := Function.update m1 (hCur + (1 + 2 * j) + 1) e
        let r21' := Function.update r25 21 (1 + 2 * j + 2)
        let r22' := Function.update r21' 22 (j + 1)
        let st1 : State := { mem := m2, regs := r22', pos := st.pos }
        have hr16E : st.regs 16 = delArr := by
          rw [hregE 16 (by decide) (by decide) (by decide)]; simp [stB, r22, r21, r4n, r20, hr16]
        have hr20E : st.regs 20 = hCur := by
          rw [hregE 20 (by decide) (by decide) (by decide)]; simp [stB, r22, r21, r4n, r20]
        have hs1 : Runs w pProg ω (.assign 25 (.load (.bin .add (.reg 16) (.reg 24)))) st .normal { st with regs := r25 } 5 :=
          runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, hr16E, hr24E, show delArr + j < 2 ^ w by omega, hval_e], rfl, rfl, rfl⟩
        have hs2 : Runs w pProg ω (.store (.bin .add (.reg 20) (.reg 21)) (.const 1))
            { st with regs := r25 } .normal { mem := m1, regs := r25, pos := st.pos } 5 :=
          runs_store_iff.mpr ⟨hCur + (1 + 2 * j), 1,
            by simp [Expr.eval, BinOp.eval, r25, hr20E, hr21E, show hCur + (1 + 2 * j) < 2 ^ w by omega],
            by simp [Expr.eval, h1_w], rfl, rfl, rfl⟩
        have hs3 : Runs w pProg ω (.store (.bin .add (.bin .add (.reg 20) (.reg 21)) (.const 1)) (.reg 25))
            { mem := m1, regs := r25, pos := st.pos } .normal { mem := m2, regs := r25, pos := st.pos } 7 :=
          runs_store_iff.mpr ⟨hCur + (1 + 2 * j) + 1, e,
            by simp [Expr.eval, BinOp.eval, r25, hr20E, hr21E, h1_w, show hCur + (1 + 2 * j) < 2 ^ w by omega,
              show hCur + (1 + 2 * j) + 1 < 2 ^ w by omega],
            by simp [Expr.eval, r25], rfl, rfl, by simp [Expr.size]⟩
        have hs4 : Runs w pProg ω (.assign 21 (.bin .add (.reg 21) (.const 2)))
            { mem := m2, regs := r25, pos := st.pos } .normal { mem := m2, regs := r21', pos := st.pos } 4 :=
          runs_assign_iff.mpr ⟨1 + 2 * j + 2, by simp [Expr.eval, BinOp.eval, r25, hr21E, h2_w, show 1 + 2 * j + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have hs5 : Runs w pProg ω (.assign 22 (.bin .add (.reg 22) (.const 1)))
            { mem := m2, regs := r21', pos := st.pos } .normal st1 4 :=
          runs_assign_iff.mpr ⟨j + 1, by simp [Expr.eval, BinOp.eval, r21', r25, hr22E, h1_w, show j + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
        have hbody_run : Runs w pProg ω emitBody st .normal st1 29 :=
          bundle_runs_seq_normal hs1 (bundle_runs_seq_normal hs2 (bundle_runs_seq_normal hs3
            (bundle_runs_seq_normal hs4 hs5)))
        refine ⟨st1, 29, (), hbody_run, by simp [st1, r22', r21', r25, hr24E], ?_, rfl, by omega⟩
        refine ⟨fun r hr h21 h22 => by
            simp [st1, r22', r21', r25, show r ≠ 24 by omega, h22, h21, show r ≠ 25 by omega, hregE r hr h21 h22],
          by simp [st1, r22', r21']; omega, by simp [st1, r22'], by simp, ?_, ?_⟩
        · rw [List.take_succ_eq_append_getElem hj, List.map_append, List.map_singleton,
            show 2 * (j + 1) = 2 * j + 2 by omega]
          refine bundle_batchBodyAt_snoc (batchBodyAt_agree hbatE fun x hx1 hx2 => by
            dsimp only [st1, m2, m1]; rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)])
            ⟨rfl, fun i hi => by
              simp only [List.length_cons, List.length_nil] at hi
              interval_cases i
              · dsimp only [st1, m2, m1]
                rw [Function.update_of_ne (by omega), show hCur + 1 + 2 * j + 0 = hCur + (1 + 2 * j) by omega,
                  Function.update_self]; rfl
              · dsimp only [st1, m2]
                rw [show hCur + 1 + 2 * j + 1 = hCur + (1 + 2 * j) + 1 by omega, Function.update_self]; rfl⟩
        · intro a ha; dsimp only [st1, m2, m1]
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfrE a (by omega))
  rw [List.take_length] at hbatEnd
  have hrcEmit : rangeCost (fun _ => 29) 0 dels.length = 29 * dels.length := by
    induction dels.length with
    | zero => simp [rangeCost]
    | succ m ih => rw [rangeCost_zero_eq_range, List.range_succ, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton, ← rangeCost_zero_eq_range, ih]; ring
  simp only [Expr.size] at hcEmit; rw [hrcEmit] at hcEmit
  refine ⟨stEnd, _,
    bundle_runs_seq_normal ha20 (bundle_runs_seq_normal ha4n (bundle_runs_seq_normal ha21
      (bundle_runs_seq_normal ha22 hrunEmit))),
    fun r hr h4 => by
      rw [hregsEnd r (by omega) (by omega) (by omega)]
      simp [stB, r22, r21, r4n, r20, h4, show r ≠ 20 by omega, show r ≠ 21 by omega, show r ≠ 22 by omega],
    by rw [hregsEnd 4 (by decide) (by decide) (by decide)]; simp [stB, r22, r21, r4n],
    by rw [hregsEnd 20 (by decide) (by decide) (by decide)]; simp [stB, r22, r21, r4n, r20],
    hr21End, hr22End, hbatEnd, applyBatch_deletes_eq B₀ dels,
    fun a ha => (hfrEnd a (Or.inr (by omega))).trans (hzero a (by omega)),
    hfrEnd, by omega⟩

end

end MinCostFlow.SparseCore.Program
