module

public import MinCostFlow.SparseCore.Program.CompBatchLoop
public import MinCostFlow.SparseCore.Program.CompBatchPack
import WordRAM.Tactic

/-!
# Batch-Update Procedure (`op 0`) for Per-Component Dynamic LSF (`CompBatchProcs`)

Defines and verifies `compBatchUpdateProc` (`op 0` of `compLSFDS`):
given `[b, batchPtr, heap]`, sequentially executes every update in `U` via `compBatchLoopStmt`,
clears `touchMark` back to zero, zeroes any unused prefix of `[heap + 1 + numTouched, heap + 1 + 2 * |U|)`,
and calls `compPackChangesProc` to pack all `k` per-branch `Read.LSFChangeAt` records and zero all
scratch buffers.

`compLSFDS_op0` establishes `CompLSFRepAt`, `CompBatchPost` (satisfying both P10's `LSFChangeAt` /
`LSFChange.Exact` and P2/P9's `CompForestCutsValid`), `DSRep.Respects`, and the exact amortized
cost bound `compBatchLsfMul * k * sumTouchedLsfBatchCost + compBatchUpdMul * k * (|U| + 1)`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Batch-update procedure (`op 0`) -/

/-- `op 0` (`args = [b, batchPtr, heap]`): executes an encoded `BatchAt` batch `U` sequentially,
writes `[numTouched, c_0, ..., c_{r-1}, chgPtr_0, ..., chgPtr_{k-1}]` plus packed `LSFChangeAt`
records at `[heap, outEnd)`, clears `touchMark` and all scratch buffers, and returns `outEnd`. -/
def compBatchUpdateProc (bZero bIns bDel bSplit bPack : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const compOffK))) ;;
  .assign 4 (.load (.bin .add (.reg 0) (.const compOffVCap))) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))) ;;
  .assign 6 (.load (.reg 1)) ;;
  .assign 7 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 6)))
    (.bin .mul (.reg 3) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 4))))) ;;
  .assign 8 (.bin .add (.bin .add (.reg 7) (.reg 3))
    (.bin .mul (.const 2) (.bin .mul (.reg 3) (.reg 4)))) ;;
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;
  .store (.reg 2) (.const 0) ;;
  .assign 10 (.const 0) ;;
  .assign 11 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 12 (.const 0) ;;
  compBatchLoopStmt bIns bDel bSplit ;;
  .assign 13 (.load (.reg 2)) ;;
  .assign 14 (.const 0) ;;
  .loop (.bin .lt (.reg 14) (.reg 13))
    (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))) ;;
     .store (.bin .add (.reg 5) (.reg 15)) (.const 0) ;;
     .assign 14 (.bin .add (.reg 14) (.const 1))) ;;
  .call 15 bZero
    [.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13),
     .bin .sub (.bin .mul (.const 2) (.reg 6)) (.reg 13)] ;;
  .call 15 bPack [.reg 0, .reg 2, .reg 13, .reg 7, .reg 8, .reg 12] ;;
  .ret (.reg 15)

lemma compBatchUpdateProc_noRand (bZero bIns bDel bSplit bPack : ℕ) :
    (compBatchUpdateProc bZero bIns bDel bSplit bPack).NoRand := by
  simp [compBatchUpdateProc, compBatchLoopStmt, Stmt.NoRand]

/-! ## 2. Helpers: unmark loop and `compZeroRangeProc` call -/

lemma compBatchZeroRange_call {w bZero ptr len : ℕ} {p : Program} {mem : ℕ → ℕ} {pos : ℕ}
    {ω : ℕ → Bool} (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hw16 : 16 ≤ 2 ^ w) (hbd : ptr + len < 2 ^ w) :
    ∃ o st' c, Runs w p ω compZeroRangeProc (startState [ptr, len] mem pos) o st' c ∧
      o.value = 0 ∧ (∀ i < len, st'.mem (ptr + i) = 0) ∧
      (∀ a, a < ptr ∨ ptr + len ≤ a → st'.mem a = mem a) ∧ c ≤ 20 * len + 15 := by
  obtain ⟨body, hbody, o, st', c, hrun, ⟨p', l', harg, hval, hpost, hfr⟩, hcost⟩ :=
    compZeroRange_meetsContract hpZero [ptr, len] mem pos ω (by simp; omega) ⟨ptr, len, rfl, hw16, hbd⟩
  have hb : body = compZeroRangeProc := Option.some.inj (hbody.symm.trans hpZero)
  have ⟨hp, hl⟩ : ptr = p' ∧ len = l' := by simpa using harg
  subst hb hp hl
  exact ⟨o, st', c, hrun, hval, hpost, hfr, by dsimp only [compZeroRangeContract] at hcost; exact hcost⟩

/-- Verification of the unmark loop: zeroes `touchMark[c]` for every `c ∈ touched` while preserving
every cell outside `[tmBase, tmBase + vCap)`. -/
lemma compUnmarkLoop_runs {w heap tmBase vCap : ℕ} {touched : List ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hw16 : 16 ≤ 2 ^ w)
    (htm_w : tmBase + vCap < 2 ^ w) (hheap_w : heap + 1 + touched.length < 2 ^ w)
    (hdisj : tmBase + vCap ≤ heap)
    (hlt : ∀ c ∈ touched, c < vCap)
    (hr2 : st.regs 2 = heap) (hr5 : st.regs 5 = tmBase)
    (hr13 : st.regs 13 = touched.length) (hr14 : st.regs 14 = 0)
    (hls : ListAt st.mem (heap + 1) touched) :
    ∃ st' c,
      Runs w p ω
        (.loop (.bin .lt (.reg 14) (.reg 13))
          (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))) ;;
           .store (.bin .add (.reg 5) (.reg 15)) (.const 0) ;;
           .assign 14 (.bin .add (.reg 14) (.const 1))))
        st .normal st' c ∧
      (∀ r < 14, st'.regs r = st.regs r) ∧
      (∀ c ∈ touched, st'.mem (tmBase + c) = 0) ∧
      (∀ a, (∀ c ∈ touched, a ≠ tmBase + c) → st'.mem a = st.mem a) ∧
      c ≤ 26 * touched.length + 10 := by
  have hw0 : w ≠ 0 := by intro h; subst h; omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hloop : ∀ rem i (s : State) (hi : i ≤ touched.length), touched.length - i = rem →
      (∀ r < 14, s.regs r = st.regs r) → s.regs 14 = i →
      (∀ j (hj : j < i), s.mem (tmBase + touched[j]'(by omega)) = 0) →
      (∀ a, (∀ j (hj : j < i), a ≠ tmBase + touched[j]'(by omega)) → s.mem a = st.mem a) →
      ∃ st' c,
        Runs w p ω
          (.loop (.bin .lt (.reg 14) (.reg 13))
            (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))) ;;
             .store (.bin .add (.reg 5) (.reg 15)) (.const 0) ;;
             .assign 14 (.bin .add (.reg 14) (.const 1))))
          s .normal st' c ∧
        (∀ r < 14, st'.regs r = st.regs r) ∧
        (∀ j (hj : j < touched.length), st'.mem (tmBase + touched[j]) = 0) ∧
        (∀ a, (∀ j (hj : j < touched.length), a ≠ tmBase + touched[j]) → st'.mem a = st.mem a) ∧
        c ≤ 26 * rem + 4 := by
    intro rem
    induction rem with
    | zero =>
      intro i s hi hrem hr_lt hr14_s hzero hfr
      have hi_eq : i = touched.length := by omega
      subst hi_eq
      exact ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hr14_s, hr_lt 13 (by omega), hr13, hw0],
        rfl, rfl, by simp [Expr.size]⟩), hr_lt, hzero, hfr, by omega⟩
    | succ rem ih =>
      intro i s hi hrem hr_lt hr14_s hzero hfr
      have hi_lt : i < touched.length := by omega
      set c_i := touched[i]
      have hci_lt : c_i < vCap := hlt c_i (List.getElem_mem hi_lt)
      have hs_ci : s.mem (heap + 1 + i) = c_i := by
        rw [hfr (heap + 1 + i) fun j hj => by
          have := hlt _ (List.getElem_mem (show j < touched.length by omega)); omega]
        exact hls i hi_lt
      let s1 : State := { s with regs := Function.update s.regs 15 c_i }
      let s2 : State := { s1 with mem := Function.update s1.mem (tmBase + c_i) 0 }
      let s3 : State := { s2 with regs := Function.update s2.regs 14 (i + 1) }
      have h1 : Runs w p ω (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))))
          s .normal s1 7 :=
        runs_assign_iff.mpr ⟨c_i, Expr.eval_load_of_eq (by
          simp [Expr.eval, BinOp.eval, hr_lt 2 (by omega), hr2, hr14_s, hw1,
            show heap + 1 < 2 ^ w by omega, show heap + 1 + i < 2 ^ w by omega]) hs_ci,
          rfl, rfl, by simp [Expr.size]⟩
      have h2 : Runs w p ω (.store (.bin .add (.reg 5) (.reg 15)) (.const 0)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨tmBase + c_i, 0, by
          simp [s1, Expr.eval, BinOp.eval, hr_lt 5 (by omega), hr5, show tmBase + c_i < 2 ^ w by omega],
          by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
      have h3 : Runs w p ω (.assign 14 (.bin .add (.reg 14) (.const 1))) s2 .normal s3 4 :=
        runs_assign_iff.mpr ⟨i + 1, by
          simp [s2, s1, Expr.eval, BinOp.eval, hr14_s, hw1, show i + 1 < 2 ^ w by omega],
          rfl, rfl, by simp [Expr.size]⟩
      have hbody : Runs w p ω _ s .normal s3 18 :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 7, _, h1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, h2, h3, rfl⟩), rfl⟩)
      obtain ⟨st', cRest, hrest, hr', hzero', hfr', hcRest⟩ :=
        ih (i + 1) s3 (by omega) (by omega)
          (fun r hr => by simp [s3, s2, s1, show r ≠ 14 by omega, show r ≠ 15 by omega, hr_lt r hr])
          (by simp [s3])
          (fun j hj => by
            dsimp only [s3, s2, s1]
            by_cases hji : j = i
            · subst hji; simp [c_i]
            · by_cases heq : tmBase + touched[j] = tmBase + c_i
              · rw [heq, Function.update_self]
              · rw [Function.update_of_ne heq]; exact hzero j (by omega))
          (fun a ha => by
            dsimp only [s3, s2, s1]
            rw [Function.update_of_ne (show a ≠ tmBase + c_i from ha i (by omega))]
            exact hfr a fun j hj => ha j (by omega))
      have hfull : Runs w p ω
          (.loop (.bin .lt (.reg 14) (.reg 13))
            (.assign 15 (.load (.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 14))) ;;
             .store (.bin .add (.reg 5) (.reg 15)) (.const 0) ;;
             .assign 14 (.bin .add (.reg 14) (.const 1)))) s .normal st' (18 + cRest + 4) :=
        runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, 18, cRest,
          by simp [Expr.eval, BinOp.eval, hr14_s, hr_lt 13 (by omega), hr13, hi_lt, hw0],
          by decide, hbody, hrest, by simp [Expr.size]; omega⟩))
      exact ⟨st', 18 + cRest + 4, hfull, hr', hzero', hfr', by omega⟩
  obtain ⟨st', c, hrun, hr', hzero, hfr, hc⟩ :=
    hloop touched.length 0 st (Nat.zero_le _) (Nat.sub_zero _) (fun _ _ => rfl) hr14
      (fun _ h => by omega) (fun _ _ => rfl)
  refine ⟨st', c, hrun, hr', fun x hx => ?_, fun a ha => hfr a fun j hj => ha _ (List.getElem_mem hj), by omega⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  exact hzero j hj

/-! ## 3. Full `op 0` verification (`compLSFDS_op0`) -/

set_option maxHeartbeats 1200000 in
open Classical in
/-- Full verification of `compBatchUpdateProc` (`op 0` of `compLSFDS`). -/
theorem compLSFDS_op0 {W : LSFWindowImpl}
    {w k b bZero bLogAdd bPreLog bLsf bCons bErase bApp bMark bDisp bIns bDel bSplit bPack : ℕ}
    {G₀ : MGraph} {S : CompLSFFamily k} {x : CompLSFMeta k}
    {args : List ℕ} {mem : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool} {p : Program}
    (hpZero : p.procs[bZero]? = some compZeroRangeProc)
    (hpLogAdd : p.procs[bLogAdd]? = some (compLogAddOrigRootProc
      (lsfBaseBat W.Q_AN bLsf + 0) (lsfBaseDg bLsf + 7 + dgIdxDeleteEdge) (lsfBaseBat W.Q_AN bLsf + 1)))
    (hpPreLog : p.procs[bPreLog]? = some (compPreLogProc bLogAdd))
    (hpLsf : p.HasAt bLsf (lsfModuleProcs W.Q_AN W.c_AN W.K_AN bLsf W.h))
    (hpCons : p.procs[bCons]? = some ghostConsProc)
    (hpErase : p.procs[bErase]? = some ghostEraseProc)
    (hpApp : p.procs[bApp]? = some ghostAppendProc)
    (hpMark : p.procs[bMark]? = some compMarkTouchProc)
    (hpDisp : p.procs[bDisp]? = some (compDispatchOneProc bZero bPreLog (bLsf + lsfIdxBatch)))
    (hpIns : p.procs[bIns]? = some (compStepInsertProc bCons bMark bDisp))
    (hpDel : p.procs[bDel]? = some (compStepDeleteProc bErase bMark bDisp))
    (hpSplit : p.procs[bSplit]? = some (compStepSplitProc bApp bMark bDisp))
    (hpPack : p.procs[bPack]? = some (compPackChangesProc bZero))
    (hrep : CompLSFRepAt W k b S x mem)
    (hpre : (compLSFDS W w k G₀).pre 0 S args mem)
    (hargs : ∀ a ∈ args, a < 2 ^ w)
    (hhead : args.head? = some b)
    (hdisj : ∀ a, compFoot b x a → a < heapArg args)
    (hz : ZeroFrom mem (heapArg args))
    (hsp : heapArg args + (compLSFDS W w k G₀).space 0 S args mem < 2 ^ w) :
    ∃ o st' c,
      Runs w p ω (compBatchUpdateProc bZero bIns bDel bSplit bPack)
        (startState args mem pos) o st' c ∧
      ∃ S' x',
        CompLSFRepAt W k b S' x' st'.mem ∧
        (compLSFDS W w k G₀).post 0 S args mem S' st'.mem ∧
        (compLSFRep W k).Respects (compFoot b x) (heapArg args)
          ((compLSFDS W w k G₀).space 0 S args mem) mem o.value b x' st'.mem ∧
        c + compPhi b x' st'.mem ≤ (compLSFDS W w k G₀).cost 0 S args mem + compPhi b x mem := by
  rcases hpre with ⟨hk, b', batchPtr, heap, totalWords, U, rfl, hw16, hBAt, hBVal, hBCaps,
    hBWords, hBHeap, hBOut⟩
  simp only [List.head?_cons, Option.some.injEq] at hhead; subst b'
  have hheap_eq : heapArg [b, batchPtr, heap] = heap := rfl
  rw [hheap_eq] at hdisj hz hsp ⊢
  have hrep_orig := hrep
  obtain ⟨hk', _, _, _, hLw, _, _, hnumC, _, hTE, hhdr, ⟨ℓ₀, hBr⟩, _, hT, _, _, _, _, _, _, _, _, hWins, _⟩ := hrep
  have hend_heap : x.endAddr ≤ heap := by
    have hb_lt_end : b < x.endAddr := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize] at hTE; omega
    have hlt := hdisj (x.endAddr - 1) ⟨by omega, by omega⟩
    omega
  have hmem_vCap : mem (b + compOffVCap) = x.vCap := hhdr.1
  have hmem_eCap : mem (b + compOffECap) = x.eCap := hhdr.2.1
  have hmem_k : mem (b + compOffK) = k := hhdr.2.2.1
  have hmem_Lw : mem (b + compOffLW) = x.L_w := hhdr.2.2.2.1
  have hmem_tmPtr : mem (b + compOffTouchMarkPtr) = compTouchMarkBase b x.vCap x.eCap :=
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmem_end : mem (b + compOffEndAddr) = x.endAddr :=
    hhdr.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hmem_vCap, hmem_eCap] at hBCaps
  rw [hmem_end] at hBOut
  have htw_eq : batchMemLen mem batchPtr = totalWords := batchMemLen_eq hBAt
  have hnumU_m : mem batchPtr = U.length := hBAt.2.1
  have htw_ge1 : 1 ≤ totalWords := by have := hBAt.1; omega
  have hsp_eq : (compLSFDS W w k G₀).space 0 S [b, batchPtr, heap] mem =
      7 + 3 * U.length + totalWords + 2 * x.eCap + k * (4 + 4 * x.vCap) := by
    simp only [compLSFDS, compBatchSpace, List.getD_cons_zero, List.getD_cons_succ,
      hmem_vCap, hmem_eCap, htw_eq, hnumU_m]
  have hsp_lt : heap + (7 + 3 * U.length + totalWords + 2 * x.eCap + k * (4 + 4 * x.vCap)) < 2 ^ w := by
    rwa [hsp_eq] at hsp
  set numU := U.length
  set tmBase := compTouchMarkBase b x.vCap x.eCap
  set cntBase := heap + 1 + 2 * numU + k * (3 + 2 * x.vCap)
  set splitBase := cntBase + k + 2 * (k * x.vCap)
  set updBuf := splitBase + numU
  have hcnt_eq : cntBase + k + 2 * (k * x.vCap) = heap + 1 + 2 * numU + k * (4 + 4 * x.vCap) := by
    dsimp only [cntBase]; ring
  have hupd_eq : updBuf = heap + 1 + 3 * numU + k * (4 + 4 * x.vCap) := by
    dsimp only [updBuf, splitBase]; omega
  have htm_le_end : tmBase + x.vCap ≤ x.endAddr := by
    have : tmBase + x.vCap ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [tmBase, compTablesEnd, compHandlesBase, compStaticSize, compTouchMarkBase,
        compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
        compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
    omega
  have hb_hdr_lt : b + compHdrSize ≤ x.endAddr := by
    have : b + compHdrSize ≤ compTablesEnd b x.vCap x.eCap x.L_w x.m0Total k := by
      dsimp only [compTablesEnd, compHandlesBase, compStaticSize, compHdrSize]; omega
    omega
  have hw0' : (0 : ℕ) < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hbp_w : batchPtr < 2 ^ w := by omega
  have hb_off_w : ∀ off < compHdrSize, off < 2 ^ w ∧ b + off < 2 ^ w := fun off hoff => by
    dsimp only [compHdrSize] at hb_hdr_lt hoff; omega
  -- Step 1: Prefix (11 statements; `mem[heap] := 0` leaves `mem` identically equal since `ZeroFrom mem heap`)
  set st0 := startState [b, batchPtr, heap] mem pos
  let r1 := Function.update st0.regs 3 k
  let r2 := Function.update r1 4 x.vCap
  let r3 := Function.update r2 5 tmBase
  let r4 := Function.update r3 6 numU
  let r5 := Function.update r4 7 cntBase
  let r6 := Function.update r5 8 splitBase
  let r7 := Function.update r6 9 updBuf
  let r8 := Function.update r7 10 0
  let r9 := Function.update r8 11 (batchPtr + 1)
  let r10 := Function.update r9 12 0
  have hupd_mem_eq : Function.update mem heap 0 = mem := by
    funext a; by_cases ha : a = heap
    · subst ha; rw [Function.update_self, hz a (le_refl _)]
    · simp [ha]
  let stP : State := { st0 with regs := r10 }
  have hp1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const compOffK))))
      st0 .normal { st0 with regs := r1 } 5 :=
    runs_assign_iff.mpr ⟨k, Expr.eval_load_of_eq (by
      have := hb_off_w compOffK (by decide); simp [st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_k,
      rfl, rfl, by simp [Expr.size]⟩
  have hp2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.const compOffVCap))))
      { st0 with regs := r1 } .normal { st0 with regs := r2 } 5 :=
    runs_assign_iff.mpr ⟨x.vCap, Expr.eval_load_of_eq (by
      have := hb_off_w compOffVCap (by decide); simp [r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_vCap,
      rfl, rfl, by simp [Expr.size]⟩
  have hp3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const compOffTouchMarkPtr))))
      { st0 with regs := r2 } .normal { st0 with regs := r3 } 5 :=
    runs_assign_iff.mpr ⟨tmBase, Expr.eval_load_of_eq (by
      have := hb_off_w compOffTouchMarkPtr (by decide)
      simp [r2, r1, st0, startState, Expr.eval, BinOp.eval, this.1, this.2]) hmem_tmPtr,
      rfl, rfl, by simp [Expr.size]⟩
  have hp4 : Runs w p ω (.assign 6 (.load (.reg 1)))
      { st0 with regs := r3 } .normal { st0 with regs := r4 } 3 :=
    runs_assign_iff.mpr ⟨numU, Expr.eval_load_of_eq (by
      simp [r3, r2, r1, st0, startState, Expr.eval]) hnumU_m,
      rfl, rfl, by simp [Expr.size]⟩
  have hp5 : Runs w p ω (.assign 7 (.bin .add (.bin .add (.bin .add (.reg 2) (.const 1)) (.bin .mul (.const 2) (.reg 6)))
      (.bin .mul (.reg 3) (.bin .add (.const 3) (.bin .mul (.const 2) (.reg 4))))))
      { st0 with regs := r4 } .normal { st0 with regs := r5 } 16 :=
    runs_assign_iff.mpr ⟨cntBase, by
      have h2v : 2 * x.vCap < 2 ^ w := by
        have : 1 * (4 + 4 * x.vCap) ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_right _ hk; omega
      have h32v : 3 + 2 * x.vCap < 2 ^ w := by
        have : 1 * (4 + 4 * x.vCap) ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_right _ hk; omega
      have hkm : k * (3 + 2 * x.vCap) < 2 ^ w := by
        have : k * (3 + 2 * x.vCap) ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_left k (by omega); omega
      simp [r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw1, hw2, hw3, h2v, h32v, hkm,
        show heap + 1 < 2 ^ w by omega, show 2 * numU < 2 ^ w by omega,
        show heap + 1 + 2 * numU < 2 ^ w by omega, show cntBase < 2 ^ w by omega, cntBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp6 : Runs w p ω (.assign 8 (.bin .add (.bin .add (.reg 7) (.reg 3))
      (.bin .mul (.const 2) (.bin .mul (.reg 3) (.reg 4)))))
      { st0 with regs := r5 } .normal { st0 with regs := r6 } 10 :=
    runs_assign_iff.mpr ⟨splitBase, by
      have hkv : k * x.vCap < 2 ^ w := by
        have : k * x.vCap ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_left k (by omega); omega
      have h2kv : 2 * (k * x.vCap) < 2 ^ w := by
        have : 2 * (k * x.vCap) ≤ k * (4 + 4 * x.vCap) := by
          calc 2 * (k * x.vCap) = k * (2 * x.vCap) := by ring
            _ ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_left k (by omega)
        omega
      simp [r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw2, hkv, h2kv,
        show cntBase + k < 2 ^ w by omega, show splitBase < 2 ^ w by omega, splitBase],
      rfl, rfl, by simp [Expr.size]⟩
  have hp7 : Runs w p ω (.assign 9 (.bin .add (.reg 8) (.reg 6)))
      { st0 with regs := r6 } .normal { st0 with regs := r7 } 4 :=
    runs_assign_iff.mpr ⟨updBuf, by
      simp [r6, r5, r4, Expr.eval, BinOp.eval, show updBuf < 2 ^ w by omega, updBuf],
      rfl, rfl, by simp [Expr.size]⟩
  have hp8 : Runs w p ω (.store (.reg 2) (.const 0))
      { st0 with regs := r7 } .normal { st0 with regs := r7 } 3 :=
    runs_store_iff.mpr ⟨heap, 0, by simp [r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval],
      by simp [Expr.eval, hw0'], rfl, by simp [st0, startState, hupd_mem_eq], by simp [Expr.size]⟩
  have hp9 : Runs w p ω (.assign 10 (.const 0))
      { st0 with regs := r7 } .normal { st0 with regs := r8 } 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  have hp10 : Runs w p ω (.assign 11 (.bin .add (.reg 1) (.const 1)))
      { st0 with regs := r8 } .normal { st0 with regs := r9 } 4 :=
    runs_assign_iff.mpr ⟨batchPtr + 1, by
      simp [r8, r7, r6, r5, r4, r3, r2, r1, st0, startState, Expr.eval, BinOp.eval, hw1,
        show batchPtr + 1 < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  have hp11 : Runs w p ω (.assign 12 (.const 0))
      { st0 with regs := r9 } .normal stP 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  -- Step 2: Main batch loop
  obtain ⟨stL, cL, xL, touched', cuts, sp, hrunL, hrL_lt10, hrL_12,
    hxL1, hxL2, hxL3, hxL4, hxL5, hxL6, hxL7, hxL8, hrepL, hndL, hltL, hlenL, hspL_le,
    hhpL, hlsL, hspL_m, hbrL, hfrL, hzL, hcostL⟩ :=
    compBatchLoop_runs (W := W) (w := w) (k := k) (b := b)
      (batchPtr := batchPtr) (heap := heap) (numU := numU)
      (cntBase := cntBase) (splitBase := splitBase) (updBuf := updBuf) (totalWords := totalWords)
      (mem0 := mem) (ω := ω)
      hpZero hpLogAdd hpPreLog hpLsf hpCons hpErase hpApp hpMark hpDisp hpIns hpDel hpSplit
      hw16 hBWords hBHeap U 0 (batchPtr + 1) 0 (totalWords - 1) S x [] (fun _ => 0) stP
      (by simp [numU]) (le_refl _) (by omega) hBOut (fun _ _ => rfl)
      (compLSFRepDirty_nil_iff.mpr hrep_orig) List.nodup_nil (fun _ h => by simp at h)
      (by simp) (le_refl 0)
      (by simp [stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stP, r10, r9, r8, r7, r6, r5, r4])
      (by simp [stP, r10, r9, r8, r7, r6, r5])
      (by simp [stP, r10, r9, r8, r7, r6])
      (by simp [stP, r10, r9, r8, r7])
      (by simp [stP, r10, r9, r8])
      (by simp [stP, r10, r9])
      (by simp [stP, r10])
      hBAt.2.2 hBVal hBCaps hend_heap (by dsimp only [cntBase]; omega) (le_refl _) (le_refl _)
      (by omega) (fun z hz' => hz z (by omega))
      (by simpa [stP, st0, startState] using hz heap (le_refl _)) (fun _ hi => by simp at hi)
      (fun j => hz (cntBase + j.1) (by omega)) (fun _ => Nat.zero_le _)
  -- Step 3: Load `numTouched`, unmark `touchMark`, zero `[heap + 1 + numTouched, heap + 1 + 2 * numU)`
  let stU0 : State := { stL with regs := Function.update stL.regs 13 touched'.length }
  let stU1 : State := { stU0 with regs := Function.update stU0.regs 14 0 }
  have hu0 : Runs w p ω (.assign 13 (.load (.reg 2))) stL .normal stU0 3 :=
    runs_assign_iff.mpr ⟨touched'.length, Expr.eval_load_of_eq (by
      simp [Expr.eval, hrL_lt10 2 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState]) hhpL, rfl, rfl, by simp [Expr.size]⟩
  have hu1 : Runs w p ω (.assign 14 (.const 0)) stU0 .normal stU1 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hw0'], rfl, rfl, by simp [Expr.size]⟩
  obtain ⟨stU, cU, hrunU, hrU_lt14, hU_zero, hU_fr, hcU⟩ :=
    compUnmarkLoop_runs (heap := heap) (tmBase := tmBase) (vCap := x.vCap) (touched := touched')
      (st := stU1) (ω := ω) hw16 (by omega) (by omega) (by omega)
      (fun c hc => lt_of_lt_of_le (hltL c hc) hnumC)
      (by simp [stU1, stU0, hrL_lt10 2 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
      (by simp [stU1, stU0, hrL_lt10 5 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3])
      (by simp [stU1, stU0]) (by simp [stU1]) hlsL
  have hU_ge_h : ∀ a, heap ≤ a → stU.mem a = stL.mem a := fun a ha =>
    hU_fr a fun c hc => by have := lt_of_lt_of_le (hltL c hc) hnumC; omega
  -- Step 4: Zero gap `[heap + 1 + touched'.length, heap + 1 + 2 * numU)`
  set gapPtr := heap + 1 + touched'.length
  set gapLen := 2 * numU - touched'.length
  obtain ⟨oZ, stZ0, cZ, hrunZ0, _, hZ_zero, hZ_fr, hcZ⟩ :=
    compBatchZeroRange_call (ptr := gapPtr) (len := gapLen) (mem := stU.mem) (pos := stU.pos) (ω := ω)
      hpZero hw16 (by omega)
  let stZ : State := { stU with regs := Function.update stU.regs 15 oZ.value, mem := stZ0.mem, pos := stZ0.pos }
  have hrunZ : Runs w p ω (.call 15 bZero
      [.bin .add (.bin .add (.reg 2) (.const 1)) (.reg 13),
       .bin .sub (.bin .mul (.const 2) (.reg 6)) (.reg 13)]) stU .normal stZ (cZ + 11) := by
    rw [runs_call_iff]
    refine ⟨[gapPtr, gapLen], compZeroRangeProc, oZ, stZ0, cZ, ?_, hpZero, hrunZ0, rfl, rfl,
      by simp [argsSize, Expr.size]; omega⟩
    have hr2_U : stU.regs 2 = heap := (hrU_lt14 2 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 2 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
    have hr6_U : stU.regs 6 = numU := (hrU_lt14 6 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 6 (by omega), stP, r10, r9, r8, r7, r6, r5, r4])
    have hr13_U : stU.regs 13 = touched'.length := (hrU_lt14 13 (by omega)).trans (by simp [stU1, stU0])
    simp [evalArgs, Expr.eval, BinOp.eval, hr2_U, hr6_U, hr13_U, hw1, hw2,
      show heap + 1 < 2 ^ w by omega, show gapPtr < 2 ^ w by omega,
      show 2 * numU < 2 ^ w by omega, show 2 * numU - touched'.length < 2 ^ w by omega, gapPtr, gapLen]
  -- Step 5: Pack per-branch `LSFChangeAt` records via `compPackChangesProc`
  set S' := compLSFBatchFamily S U
  have hcut_bd : ∀ j : Fin k, (cuts j).length + sp.length ≤ x.vCap := fun j => by
    obtain ⟨_, _, _, _, _, _, hndR, hndS, hdisjR, hsR, _⟩ := hbrL j
    have hcard_u : ((cuts j).map Prod.snd).toFinset.card + sp.toFinset.card =
        ((S' j).RF.R \ (S j).RF.R).card := by
      rw [← hsR, Finset.card_union_of_disjoint]
      exact Finset.disjoint_left.mpr fun r h1 h2 =>
        hdisjR r (List.mem_toFinset.mp h1) (List.mem_toFinset.mp h2)
    rw [List.toFinset_card_of_nodup hndR, List.length_map, List.toFinset_card_of_nodup hndS] at hcard_u
    obtain ⟨ℓ₀', hBr'⟩ := hrepL.2.2.2.2.2.2.2.2.2.2.2.1
    have hT' := compEdgeTrack_of_same_graph hrepL.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (hBr' j).2.1 (hBr' j).2.2.1 (hBr' j).2.2.2.2.1 (hBr' j).2.2.2.2.2.2
    have hR_le : (S' j).RF.R.card ≤ x.vCap := by
      rw [← hxL1]
      exact (Finset.card_le_card fun r hr => Finset.mem_range.mpr
        (hT'.hVlt r ((compLSF_RF_isRSF (hBr' j).1).2.2.1 hr))).trans (by simp)
    have hsdiff_le : ((S' j).RF.R \ (S j).RF.R).card ≤ (S' j).RF.R.card :=
      Finset.card_le_card Finset.sdiff_subset
    omega
  have hZ_hdr_ag : ∀ a, b ≤ a → a < b + compHdrSize → stZ.mem a = stL.mem a := fun a ha1 ha2 => by
    have hlt_tm : a < tmBase := by
      dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase,
        compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha2 ⊢; omega
    exact (hZ_fr a (Or.inl (by omega))).trans (hU_fr a fun c _ => by omega)
  have hZ_ge_cnt : ∀ a, cntBase ≤ a → stZ.mem a = stL.mem a := fun a ha =>
    (hZ_fr a (Or.inr (by omega))).trans (hU_ge_h a (by omega))
  have hZ_zero_ptr : ∀ a, heap + 1 + touched'.length ≤ a → a < cntBase → stZ.mem a = 0 := fun a ha1 ha2 => by
    by_cases hgap : a < heap + 1 + 2 * numU
    · have h := hZ_zero (a - gapPtr) (by omega)
      rwa [show gapPtr + (a - gapPtr) = a by omega] at h
    · rw [hZ_fr a (Or.inr (by omega)), hU_ge_h a (by omega)]
      rw [hfrL a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)]
      exact hz a (by omega)
  have hZ_zero_roots : ∀ j : Fin k, ∀ i, (cuts j).length ≤ i → i < x.vCap →
      stZ.mem (cntBase + k + j.1 * x.vCap + i) = 0 ∧
      stZ.mem (cntBase + k + k * x.vCap + j.1 * x.vCap + i) = 0 := fun j i hi1 hi2 => by
    have hj_mul : (j.1 + 1) * x.vCap ≤ k * x.vCap := Nat.mul_le_mul_right x.vCap (by have := j.2; omega)
    rw [Nat.add_mul, Nat.one_mul] at hj_mul
    have hsep : ∀ (j0 : Fin k) (base : ℕ), base = cntBase + k ∨ base = cntBase + k + k * x.vCap →
        base + j.1 * x.vCap + i < base + j0.1 * x.vCap ∨
        base + j0.1 * x.vCap + (cuts j0).length ≤ base + j.1 * x.vCap + i := fun j0 base _ => by
      by_cases hjj : j0 = j
      · subst hjj; right; omega
      · have hne : j0.1 ≠ j.1 := fun h => hjj (Fin.ext h)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · right; have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ j.1 by omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega
        · left; have h := Nat.mul_le_mul_right x.vCap (show j.1 + 1 ≤ j0.1 by omega)
          rw [Nat.add_mul, Nat.one_mul] at h; omega
    constructor
    · rw [hZ_ge_cnt _ (by omega), hfrL _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun j0 => by have := j0.2; omega)
        (fun j0 => by simpa using hsep j0 (cntBase + k) (Or.inl rfl))
        (fun j0 => Or.inl (by omega)) (by omega)]
      exact hz _ (by omega)
    · rw [hZ_ge_cnt _ (by omega), hfrL _ (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (fun j0 => by have := j0.2; omega)
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (fun j0 => by simpa using hsep j0 (cntBase + k + k * x.vCap) (Or.inr rfl)) (by omega)]
      exact hz _ (by omega)
  have hZ_zero_above : ZeroFrom stZ.mem (splitBase + sp.length) := fun a ha => by
    rw [hZ_ge_cnt a (by omega)]
    by_cases hbuf : updBuf ≤ a
    · exact hzL a hbuf
    · rw [hfrL a (Or.inr (by omega)) (by omega) (Or.inr (by omega)) (Or.inr (by omega))
        (fun j0 => by have := j0.2; omega)
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (fun j0 => Or.inr (by
          have h := Nat.mul_le_mul_right x.vCap (show j0.1 + 1 ≤ k by have := j0.2; omega)
          rw [Nat.add_mul, Nat.one_mul] at h; have := hcut_bd j0; omega))
        (by omega)]
      exact hz a (by omega)
  obtain ⟨stP0, cPk, hrunPk0, hPk_br, hout_le_cnt, hzPk, hPk_fr, hcPk⟩ :=
    compPackChanges_runs (b := b) (heap := heap) (numTouched := touched'.length)
      (cntBase := cntBase) (splitBase := splitBase) (vCap := x.vCap)
      (cuts := cuts) (splitVerts := sp) (mem := stZ.mem) (pos := stZ.pos) (ω := ω)
      hpZero hw16 hk
      ((hZ_hdr_ag _ (by dsimp only [compOffK]; omega) (by dsimp only [compOffK, compHdrSize]; omega)).trans hrepL.2.2.2.2.2.2.2.2.2.2.1.2.2.1)
      ((hZ_hdr_ag _ (by dsimp only [compOffVCap]; omega) (by dsimp only [compOffVCap, compHdrSize]; omega)).trans (hxL1 ▸ hrepL.2.2.2.2.2.2.2.2.2.2.1.1))
      (by omega)
      (by
        have hmul_c : k + k * (2 + 2 * x.vCap) = k * (3 + 2 * x.vCap) := by ring
        dsimp only [cntBase]; omega)
      (le_refl _) (by omega) hcut_bd
      (fun j => (hZ_ge_cnt _ (by omega)).trans (by simpa using (hbrL j).1))
      (fun j i hi => by
        rw [hZ_ge_cnt _ (by omega), hZ_ge_cnt _ (by omega)]
        simpa using (hbrL j).2.1 i hi)
      (fun i hi => (hZ_ge_cnt _ (by omega)).trans (by simpa using hspL_m i hi))
      hZ_zero_ptr hZ_zero_roots (fun a h1 h2 => by omega) hZ_zero_above
  set outEnd := heap + 1 + touched'.length + k + compPackedPrefixWords cuts sp k
  let stPk : State := { stZ with regs := Function.update stZ.regs 15 outEnd, mem := stP0.mem, pos := stP0.pos }
  have hrunPk : Runs w p ω (.call 15 bPack [.reg 0, .reg 2, .reg 13, .reg 7, .reg 8, .reg 12])
      stZ .normal stPk (cPk + 7) := by
    rw [runs_call_iff]
    refine ⟨[b, heap, touched'.length, cntBase, splitBase, sp.length], compPackChangesProc bZero,
      .returned outEnd, stP0, cPk, ?_, hpPack, hrunPk0, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have hr0_Z : stZ.regs 0 = b := (hrU_lt14 0 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 0 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
    have hr2_Z : stZ.regs 2 = heap := (hrU_lt14 2 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 2 (by omega), stP, r10, r9, r8, r7, r6, r5, r4, r3, r2, r1, st0, startState])
    have hr7_Z : stZ.regs 7 = cntBase := (hrU_lt14 7 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 7 (by omega), stP, r10, r9, r8, r7, r6, r5])
    have hr8_Z : stZ.regs 8 = splitBase := (hrU_lt14 8 (by omega)).trans (by simp [stU1, stU0, hrL_lt10 8 (by omega), stP, r10, r9, r8, r7, r6])
    have hr12_Z : stZ.regs 12 = sp.length := (hrU_lt14 12 (by omega)).trans (by simpa [stU1, stU0] using hrL_12)
    have hr13_Z : stZ.regs 13 = touched'.length := (hrU_lt14 13 (by omega)).trans (by simp [stU1, stU0])
    simp only [evalArgs, Expr.eval, hr0_Z, hr2_Z, hr7_Z, hr8_Z, hr12_Z, hr13_Z]
  have hrunRet : Runs w p ω (.ret (.reg 15)) stPk (.returned outEnd) stPk 2 :=
    runs_ret_iff.mpr ⟨outEnd, by simp [stPk, Expr.eval], rfl, rfl, by simp [Expr.size]⟩
  -- Chain full execution
  have hrun_full : Runs w p ω (compBatchUpdateProc bZero bIns bDel bSplit bPack) st0
      (.returned outEnd) stPk (101 + cL + cU + cZ + cPk) :=
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp1,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp2,
    runs_seq_iff.mpr (Or.inr ⟨_, 5, _, hp3,
    runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hp4,
    runs_seq_iff.mpr (Or.inr ⟨_, 16, _, hp5,
    runs_seq_iff.mpr (Or.inr ⟨_, 10, _, hp6,
    runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp7,
    runs_seq_iff.mpr (Or.inr ⟨_, 3, _, hp8,
    runs_seq_iff.mpr (Or.inr ⟨_, 2, _, hp9,
    runs_seq_iff.mpr (Or.inr ⟨_, 4, _, hp10,
    runs_seq_iff.mpr (Or.inr ⟨stP, 2, _, hp11,
    runs_seq_iff.mpr (Or.inr ⟨stL, cL, _, hrunL,
    runs_seq_iff.mpr (Or.inr ⟨stU0, 3, _, hu0,
    runs_seq_iff.mpr (Or.inr ⟨stU1, 2, _, hu1,
    runs_seq_iff.mpr (Or.inr ⟨stU, cU, _, hrunU,
    runs_seq_iff.mpr (Or.inr ⟨stZ, cZ + 11, _, hrunZ,
    runs_seq_iff.mpr (Or.inr ⟨stPk, cPk + 7, 2, hrunPk, hrunRet, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), by omega⟩)
  -- Restore `CompLSFRepAt` (`stPk.mem` agrees with `stU.mem` below `heap + 1 + touched'.length`, hence below `x.endAddr`)
  have hPk_lt_end : ∀ a < x.endAddr, stPk.mem a = stU.mem a := fun a ha =>
    (hPk_fr a (by omega)).trans (hZ_fr a (Or.inl (by omega)))
  have hPk_not_tm : ∀ a < x.endAddr, (a < tmBase ∨ tmBase + x.vCap ≤ a) → stPk.mem a = stL.mem a := fun a ha hnt =>
    (hPk_lt_end a ha).trans (hU_fr a fun c hc => by have := lt_of_lt_of_le (hltL c hc) hnumC; omega)
  have hrep_final : CompLSFRepAt W k b S' xL stPk.mem := by
    rw [← compLSFRepDirty_nil_iff]
    obtain ⟨hkL, hhL, hLinL, hPfpL, hLwL, hhLwL, heCapL, hncL, hneL, hTEL, hhdrL, hBrL, hm0L,
      hTL, hCompL, hEfL, hVCL, hECL, hFlL, hGhL, hTML, hOneL, hWinL, hDisjL⟩ := hrepL
    have htm_eq_L : compTouchMarkBase b xL.vCap xL.eCap = tmBase := by rw [hxL1, hxL2]
    refine ⟨hkL, hhL, hLinL, hPfpL, hLwL, hhLwL, heCapL, hncL, hneL, hTEL,
      compHeaderAt_of_agree hhdrL (fun a ha1 ha2 => hPk_not_tm a (by omega) (Or.inl (by
        dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase,
          compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
          compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize] at ha2 ⊢; omega))),
      hBrL, hm0L, hTL, ?_, hEfL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hDisjL⟩
    · intro c; obtain ⟨c1, c2, c3, c4⟩ := hCompL c; have hc_lt : c.1 < x.vCap := lt_of_lt_of_le (hxL4 ▸ c.2) hnumC
      refine ⟨(hPk_not_tm _ (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase]; omega))).trans c1,
        (hPk_not_tm _ (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base]; omega))).trans c2,
        (hPk_not_tm _ (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base]; omega))).trans c3, fun hp => ?_⟩
      obtain ⟨ec, e1, e2, e3⟩ := c4 hp
      exact ⟨ec, e1, (hPk_not_tm _ (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase]; omega))).trans e2, e3⟩
    · intro c v hv
      have hv_lt : v < x.vCap := hxL1 ▸ hTL.hVlt v (by
        obtain ⟨ℓ₀', hBr'⟩ := hBrL
        exact (hBr' ⟨0, hkL⟩).1.hV_eq ▸ Finset.mem_biUnion.mpr ⟨xL.compOf c, hTL.compOf_mem c, hv⟩)
      exact (hPk_not_tm _ (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase] at htm_le_end ⊢; omega) (Or.inl (by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase]; omega))).trans (hVCL c v hv)
    · intro e he; have he_lt : e < x.eCap := hxL2 ▸ hTL.hElt e he
      exact ⟨(hPk_not_tm _ (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base]; omega))).trans (hECL e he).1,
        (hPk_not_tm _ (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base]; omega))).trans (hECL e he).2⟩
    · intro e he; have he_lt : e < x.eCap := hxL2 ▸ he
      exact ⟨(hPk_not_tm _ (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase]; omega))).trans (hFlL e he).1,
        (hPk_not_tm _ (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase] at htm_le_end ⊢; omega) (Or.inl (by rw [hxL1, hxL2]; dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize, compIsInsBase]; omega))).trans (hFlL e he).2⟩
    · set gPtr := compGhostBase b xL.vCap xL.eCap
      have hgh_ag : ∀ a, gPtr ≤ a → a < tmBase → stPk.mem a = stL.mem a := fun a h1 h2 =>
        hPk_not_tm a (by omega) (Or.inl h2)
      refine ⟨fun u hu => ?_, fun e he hcr => ?_⟩
      · obtain ⟨g1, g2, g3, g4⟩ := hGhL.1 u hu; have hu' : u < x.vCap := hxL1 ▸ hu
        exact ⟨g1.of_agree
            (hgh_ag _ (by dsimp only [ghostTHeadBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostTHeadBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTPrevBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostTPrevBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGT u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostTNextBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostTNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostTCntBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostTCntBase, gPtr]; omega)).trans g2,
          g3.of_agree
            (hgh_ag _ (by dsimp only [ghostHHeadBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostHHeadBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHPrevBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostHPrevBase, gPtr]; omega))
            (fun f hf => have := (hTL.hGH u hu).2.1 f hf; hgh_ag _ (by dsimp only [ghostHNextBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostHNextBase, gPtr]; omega)),
          (hgh_ag _ (by dsimp only [ghostHCntBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostHCntBase, gPtr]; omega)).trans g4⟩
      · have he_lt : e < xL.eCap := hTL.hElt e he
        exact ⟨(hgh_ag _ (by dsimp only [ghostTVertBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostTVertBase, gPtr]; omega)).trans (hGhL.2 e he hcr).1,
          (hgh_ag _ (by dsimp only [ghostHVertBase]; omega) (by rw [← htm_eq_L]; dsimp only [compTouchMarkBase, compGhostSize, ghostHVertBase, gPtr]; omega)).trans (hGhL.2 e he hcr).2⟩
    · intro c hc; simp only [List.not_mem_nil, ↓reduceIte]; rw [htm_eq_L]
      rw [hPk_lt_end (tmBase + c) (by rw [hxL1] at hc; omega)]
      by_cases hct : c ∈ touched'
      · exact hU_zero c hct
      · rw [hU_fr (tmBase + c) (fun c' hc' heq => hct ((Nat.add_left_cancel heq) ▸ hc'))]
        have := hTML c hc; rw [htm_eq_L] at this; simpa [hct] using this
    · have hone_ag : ∀ i < xL.L_w, stPk.mem (compOneLimbBase b xL.vCap xL.eCap + i) =
          stL.mem (compOneLimbBase b xL.vCap xL.eCap + i) := fun i hi => by
        have h1e := compOneLimb_end_eq b xL.vCap xL.eCap xL.L_w
        have hlt_e : compOneLimbBase b xL.vCap xL.eCap + i < x.endAddr := by
          rw [← hxL7]; dsimp only [compTablesEnd] at hTEL; omega
        exact hPk_not_tm _ hlt_e (Or.inr (by rw [← htm_eq_L]; dsimp only [compOneLimbBase]; omega))
      exact ⟨(hone_ag 0 hLwL).trans hOneL.1, fun i h1 h2 => (hone_ag i h2).trans (hOneL.2 i h1 h2)⟩
    · intro ec j; obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := hWinL ec j
      have hge_tm : tmBase + x.vCap ≤ compHandlesBase b xL.vCap xL.eCap xL.L_w := by
        rw [← htm_eq_L, ← hxL1]; dsimp only [compHandlesBase, compStaticSize, compTouchMarkBase,
          compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
          compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
      have hslot_lt : compHandlesBase b xL.vCap xL.eCap xL.L_w + (ec.1 * k + j.1) < x.endAddr := by
        have h1 : (ec.1 + 1) * k ≤ xL.m0Total * k := Nat.mul_le_mul_right k (by have := ec.2; omega)
        have h2 : ec.1 * k + j.1 < (ec.1 + 1) * k := by rw [Nat.add_mul, Nat.one_mul]; exact Nat.add_lt_add_left j.2 _
        rw [← hxL7]; dsimp only [compTablesEnd] at hTEL; omega
      refine ⟨(hPk_not_tm _ hslot_lt (Or.inr (by omega))).trans w1,
        (lsfRep_local W.h _ _ _ stL.mem stPk.mem fun a ha => (hPk_not_tm a (lt_of_lt_of_le ha.2 (hxL7 ▸ w7))
          (Or.inr (by have := ha.1; dsimp only [compTablesEnd] at w6; omega))).symm).1 w2,
        w3, w4, w5, w6, w7⟩
  -- Potential equality `compPhi b xL stPk.mem = compPhi b xL stL.mem`
  have hphi_eq : compPhi b xL stPk.mem = compPhi b xL stL.mem := by
    rw [compPhi_eq_sum_dirty (compLSFRepDirty_nil_iff.mpr hrep_final), compPhi_eq_sum_dirty hrepL]
    refine Finset.sum_congr rfl fun ec _ => Finset.sum_congr rfl fun j _ => ?_
    obtain ⟨_, _, _, _, _, w6, w7⟩ := hrepL.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ec j
    have hge_tm : tmBase + x.vCap ≤ compHandlesBase b xL.vCap xL.eCap xL.L_w := by
      dsimp only [tmBase, compHandlesBase, compStaticSize, compTouchMarkBase,
        compGhostBase, compGhostSize, compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base,
        compM0Base, compN0Base, compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]
      rw [hxL1, hxL2]; omega
    exact lsfPhi_congr fun a ha1 ha2 => hPk_not_tm a (lt_of_lt_of_le ha2 (hxL7 ▸ w7))
      (Or.inr (by dsimp only [compTablesEnd] at w6; omega))
  -- Cost bound
  have hcost_final : (101 + cL + cU + cZ + cPk) + compPhi b xL stPk.mem ≤
      (compLSFDS W w k G₀).cost 0 S [b, batchPtr, heap] mem + compPhi b x mem := by
    have hsubE : ∀ C ∈ components (S ⟨0, hk⟩).G₀, ((S ⟨0, hk⟩).compSt C).G.E ⊆ (S ⟨0, hk⟩).G.E := fun C hC =>
      (hBr ⟨0, hk⟩).1.hCE_sub C hC
    rw [compLSFDS_batchCost_eq W hk hsubE hBAt, hmem_Lw, hphi_eq]
    have hstP_mem : stP.mem = mem := rfl
    have hcostL' : cL + 120 * ∑ j, (cuts j).length + compPhi b xL stL.mem ≤
        compPhi b x mem + 645 * U.length + 10 + k * compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U :=
      hcostL
    have hsteps_le : compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U ≤
        3 * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U :=
      compBatchStepsCost_le_three_mul hLw (hBr ⟨0, hk⟩).1 hBVal hBAt
    have hmul_steps : k * compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U ≤
        compBatchLsfMul * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U := by
      calc k * compBatchStepsCost mem x.L_w (S ⟨0, hk⟩) (batchPtr + 1) U
          ≤ k * (3 * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U) := Nat.mul_le_mul_left k hsteps_le
        _ = 3 * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U := by ring
        _ ≤ compBatchLsfMul * k * sumTouchedLsfBatchCost mem (S ⟨0, hk⟩) batchPtr x.L_w U :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right k (by decide))
    have hgap_cancel : cU + cZ ≤ 52 * numU + 25 := by dsimp only [gapLen] at hcZ; omega
    have hnon_lsf : 101 + 645 * numU + 10 + (52 * numU + 25) + 45 * k * sp.length + 260 * k + 20 * sp.length + 90 ≤
        compBatchUpdMul * k * (numU + 1) := by
      have h1 : 45 * k * sp.length ≤ 45 * k * numU := Nat.mul_le_mul_left _ hspL_le
      have h2 : 717 * numU ≤ 717 * (k * numU) := by
        calc 717 * numU = 1 * (717 * numU) := by ring
          _ ≤ k * (717 * numU) := Nat.mul_le_mul_right _ hk
          _ = 717 * (k * numU) := by ring
      have h3 : 226 ≤ 226 * k := Nat.le_mul_of_pos_right 226 hk
      have h4 : compBatchUpdMul * k * (numU + 1) = 800 * (k * numU) + 800 * k := by
        dsimp only [compBatchUpdMul]; ring
      have h5 : 45 * k * numU = 45 * (k * numU) := by ring
      omega
    dsimp only [numU] at hgap_cancel hnon_lsf
    have hsum_le : 100 * ∑ j, (cuts j).length ≤ 120 * ∑ j, (cuts j).length :=
      Nat.mul_le_mul_right _ (by decide)
    omega
  -- Assemble `CompBatchPost` and `Respects`
  have hheap_val : stPk.mem heap = touched'.length :=
    (hPk_fr heap (by omega)).trans ((hZ_fr heap (Or.inl (by omega))).trans ((hU_ge_h heap (le_refl _)).trans hhpL))
  have hcnt_le_sp : cntBase ≤ heap + compBatchSpace k [b, batchPtr, heap] mem := by
    have hmul_le : k * (3 + 2 * x.vCap) ≤ k * (4 + 4 * x.vCap) := Nat.mul_le_mul_left k (by omega)
    simp only [compBatchSpace, List.getD_cons_zero, List.getD_cons_succ, hmem_vCap, hmem_eCap, htw_eq, hnumU_m]
    dsimp only [cntBase]; omega
  refine ⟨.returned outEnd, stPk, 101 + cL + cU + cZ + cPk, hrun_full, S', xL, hrep_final, ?_, ?_, hcost_final⟩
  · refine ⟨hk, b, batchPtr, heap, totalWords, U, rfl, hBAt, rfl, hheap_val ▸ hlenL,
      fun j => compBranchChange (cuts j) sp, fun j => ?_⟩
    obtain ⟨hptr_eq, hAt, hge_p, hle_o⟩ := hPk_br j
    obtain ⟨_, _, hval_j, hndE_j, hsE_j, hEsub_j, hndR_j, hndS_j, hdisj_j, hsR_j, _⟩ := hbrL j
    have hchg := compForestCuts_to_lsfChange hval_j hndE_j hsE_j hEsub_j hndR_j hndS_j hdisj_j hsR_j
    rw [hheap_val, hmem_vCap]
    exact ⟨hAt, hchg.1, hchg.2.1, hchg.2.2.2.1, hchg.2.2.2.2, hge_p,
      le_trans hle_o (le_trans hout_le_cnt hcnt_le_sp)⟩
  · refine ⟨by dsimp only [outEnd, Outcome.value]; omega,
      le_trans hout_le_cnt (by rw [hsp_eq]; simpa [compBatchSpace, List.getD_cons_zero, List.getD_cons_succ, hmem_vCap, hmem_eCap, htw_eq, hnumU_m] using hcnt_le_sp),
      hzPk, fun a ha hnf => ?_, fun a ha => Or.inl (by simpa [compLSFRep, compFoot, hxL7] using ha)⟩
    have hout : a < b ∨ x.endAddr ≤ a := by
      simp only [compFoot, not_and, not_lt] at hnf
      by_cases h1 : a < b; exact Or.inl h1; exact Or.inr (hnf (le_of_not_gt h1))
    rw [hPk_fr a (by omega), hZ_fr a (Or.inl (by omega)), hU_fr a (fun c hc => by
      have : b ≤ tmBase + c := by dsimp only [tmBase, compTouchMarkBase, compGhostBase, compGhostSize,
        compIsInsBase, compIsCrossBase, compEdgeC2Base, compEdgeC1Base, compM0Base, compN0Base,
        compEdgefulIdxBase, compEdgefulBase, compVCompBase, compHdrSize]; omega
      have := lt_of_lt_of_le (hltL c hc) hnumC; rcases hout with h | h <;> omega)]
    exact hfrL a hout (by omega) (Or.inl (by omega)) (Or.inl (by omega))
      (fun _ => by omega) (fun _ => Or.inl (by omega)) (fun _ => Or.inl (by omega)) (by omega)

end

end MinCostFlow.SparseCore.Program
