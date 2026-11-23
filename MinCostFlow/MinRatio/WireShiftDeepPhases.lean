module

public import MinCostFlow.MinRatio.WireRebuildSuffixLoopK
public import MinCostFlow.MinRatio.WireSuffixEdits
import WordRAM.Tactic

/-!
# Deep shift phases and shared LSF forest collector (`WireShiftDeepPhases`)

Provides the deterministic Word-RAM phase procedures for `ShiftDeepChainSyncSpecW`
(non-terminal Algorithm 2 level shift `i < d`, pages 20 and 29):
1. `shiftDeepInitRegs`: decodes `[root, i, heap]` into high registers `70..83` and reserves
   `oldPtrs[0..d-i]` and `newPtrs[0..d-i]` at `[heap, heap + 2*(d - i + 1))`.
2. `collectLSFForestsLoop`: shared loop (reusable by both deep shift and chain update) that
   reads active forest `DynGraphAt` headers for levels `[first, d)` via op `2` (`ordCoreReadLSFStmt`)
   into `mem[reg dstReg + (j - baseIdx)]` while preserving `Rcore.rep` and telescoping `Rcore.phi`.
3. `shiftDeepCollectOld`: copies level `i`'s old forest via `copyGraphFromHeader` (so the in-place
   restart at level `i` cannot overwrite it), collects levels `i + 1 .. d - 1` via
   `collectLSFForestsLoop`, and appends terminal level `d`'s old active forest.
4. `shiftDeepRestartAndReadout`: restarts level `i` via `ordCoreRestartStmt`, reads out
   `(G'_{i+1}, ℓ'_{i+1}, ord'_{i+1})` via `ordReadoutNextLevelK`, stores `levelMeta[i + 1]`
   and `levelMeta[d + i + 1]` when `i + 1 < d`, and prepares registers for
   `ordRebuildSuffixProgramKStore`.
5. `shiftDeepCollectNew`: collects new active forests on `[i, d]` into `newPtrs`.
6. `shiftDeepChainBody`: composes all phases with `wireSuffixPackEditsBody`, `shiftTermSetupLoop`,
   and `wireTreeSyncLoop`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

section Programs

/-- Phase 0: load `[root, i, heap]` (`reg 0..2`) and solver header addresses into `reg 70..83`,
reserving `[heap, heap + 2 * (d - i + 1))` for `oldPtrs` and `newPtrs`. -/
@[expose] def shiftDeepInitRegs : Stmt :=
  .assign 70 (.reg 0) ;;
  .assign 71 (.reg 1) ;;
  .assign 72 (.reg 2) ;;
  .assign 73 (.load (.reg 70)) ;;
  .assign 74 (.load (.bin .add (.reg 70) (.const 1))) ;;
  .assign 75 (.load (.bin .add (.reg 73) (.const 11))) ;;
  .assign 76 (.load (.bin .add (.reg 73) (.const 12))) ;;
  .assign 77 (.bin .add (.reg 73) (.const 18)) ;;
  .assign 78 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 79 (.bin .add (.bin .sub (.reg 75) (.reg 71)) (.const 1)) ;;
  .assign 80 (.reg 72) ;;
  .assign 81 (.bin .add (.reg 72) (.reg 79)) ;;
  .assign 82 (.bin .add (.bin .add (.reg 74) (.bin .add (.reg 75) (.const 1))) (.const 1)) ;;
  .assign 83 (.bin .add (.reg 82) (.reg 75)) ;;
  .assign 4 (.bin .add (.reg 81) (.reg 79))

theorem shiftDeepInitRegs_noRand : shiftDeepInitRegs.NoRand := by
  simp [shiftDeepInitRegs, Stmt.NoRand]

/-- Shared loop collecting active LSF forest `DynGraphAt` headers for levels `j ∈ [reg 20, reg 75)`
into `mem[reg dstReg + (j - reg 71)]` using op `2` (`ordCoreReadLSFStmt`). -/
@[expose] def collectLSFForestsLoop (readLSF dstReg : ℕ) : Stmt :=
  forRange 19 (.reg 20) (.reg 75)
    (.assign 3 (.load (.bin .add (.reg 77) (.reg 19))) ;;
     .assign 2 (.load (.bin .add (.reg 78) (.reg 19))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))) ;;
     ordCoreReadLSFStmt readLSF ;;
     .store (.bin .add (.reg dstReg) (.bin .sub (.reg 19) (.reg 71)))
       (.load (.bin .add (.reg 4) (.const 1))) ;;
     .assign 4 (.reg 5))

theorem collectLSFForestsLoop_noRand (readLSF dstReg : ℕ) :
    (collectLSFForestsLoop readLSF dstReg).NoRand := by
  simp [collectLSFForestsLoop, forRange, forUp, ordCoreReadLSFStmt_noRand, Stmt.NoRand]

/-- Store terminal level `d`'s active forest `DynGraphAt` header into `mem[reg dstReg + (d - reg 71)]`. -/
@[expose] def collectTermForestStmt (dstReg : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 77) (.reg 75))) ;;
  .assign 11 (.load (.bin .add (.reg 78) (.reg 75))) ;;
  .assign 12 (.load (.bin .add (.bin .add (.reg 10) (.const 1)) (.reg 11))) ;;
  .store (.bin .add (.reg dstReg) (.bin .sub (.reg 75) (.reg 71)))
    (.load (.bin .add (.reg 12) (.const 1)))

theorem collectTermForestStmt_noRand (dstReg : ℕ) :
    (collectTermForestStmt dstReg).NoRand := by
  simp [collectTermForestStmt, Stmt.NoRand]

/-- Phase 1: snapshot old active forests on `[i, d]` into `oldPtrs` (`reg 80`), copying level `i`'s
old forest into fresh heap via `copyGraphFromHeader` before level `i` is restarted in place. -/
@[expose] def shiftDeepCollectOld (readLSF : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 77) (.reg 71))) ;;
  .assign 2 (.load (.bin .add (.reg 78) (.reg 71))) ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))) ;;
  ordCoreReadLSFStmt readLSF ;;
  .assign 6 (.load (.bin .add (.reg 4) (.const 1))) ;;
  .assign 4 (.reg 5) ;;
  copyGraphFromHeader ;;
  .store (.reg 80) (.reg 6) ;;
  .assign 4 (.reg 5) ;;
  .assign 20 (.bin .add (.reg 71) (.const 1)) ;;
  collectLSFForestsLoop readLSF 80 ;;
  collectTermForestStmt 80

theorem shiftDeepCollectOld_noRand (readLSF : ℕ) :
    (shiftDeepCollectOld readLSF).NoRand := by
  simp [shiftDeepCollectOld, ordCoreReadLSFStmt_noRand, copyGraphFromHeader, readGraphCopySize,
    copyReadoutGraphAtHeap, copyReadoutGraph, copyWordsStmt, collectLSFForestsLoop_noRand,
    collectTermForestStmt_noRand, Stmt.NoRand]

/-- Phase 2: restart level `i`, read out `(G'_{i+1}, ℓ'_{i+1}, ord'_{i+1})` via
`ordReadoutNextLevelK`, update `levelMeta[i + 1]` / `levelMeta[d + i + 1]` if `i + 1 < d`,
and load registers for `ordRebuildSuffixProgramKStore`. -/
@[expose] def shiftDeepRestartAndReadout
    (restart readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 0 (.bin .add (.reg 78) (.reg 71)) ;;
  .assign 1 (.reg 76) ;;
  .assign 3 (.load (.bin .add (.reg 77) (.reg 71))) ;;
  ordCoreRestartStmt restart ;;
  .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 71))) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 71))) ;;
  .assign 67 (.load (.bin .add (.reg 73) (.const 5))) ;;
  ordReadoutNextLevelK readGraph readLSF coreLenProc readOrd ;;
  .cond (.bin .lt (.bin .add (.reg 71) (.const 1)) (.reg 75))
    (.store (.bin .add (.reg 83) (.bin .add (.reg 71) (.const 1))) (.reg 7) ;;
     .store (.bin .add (.bin .add (.reg 83) (.reg 75)) (.bin .add (.reg 71) (.const 1))) (.reg 6))
    .nop ;;
  .assign 20 (.bin .add (.reg 71) (.const 1)) ;;
  .assign 21 (.reg 75) ;;
  .assign 51 (.bin .add (.reg 77) (.reg 20)) ;;
  .assign 52 (.bin .add (.reg 78) (.reg 20)) ;;
  .assign 56 (.load (.bin .sub (.reg 82) (.const 1))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 68 (.load (.bin .add (.reg 73) (.const 8)))

theorem shiftDeepRestartAndReadout_noRand (restart readGraph readLSF coreLenProc readOrd : ℕ) :
    (shiftDeepRestartAndReadout restart readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [shiftDeepRestartAndReadout, ordCoreRestartStmt_noRand, ordReadoutNextLevelK_noRand,
    Stmt.NoRand]

/-- Phase 4: collect new active forests on `[i, d]` into `newPtrs` (`reg 81`), pack symmetric
edge differences via `packEditsProc` (`wireSuffixPackEditsBody`), and sync the path tree. -/
@[expose] def shiftDeepCollectNewAndSync
    (readLSF packEditsProc readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  .assign 20 (.reg 71) ;;
  collectLSFForestsLoop readLSF 81 ;;
  collectTermForestStmt 81 ;;
  .assign 10 (.load (.bin .add (.reg 70) (.const 15))) ;;
  .assign 6 (.bin .add (.reg 4) (.bin .mul (.const 3) (.reg 10))) ;;
  .call 18 packEditsProc [.reg 80, .reg 81, .reg 79, .reg 10, .reg 4] ;;
  .assign 27 (.reg 70) ;;
  .assign 29 (.reg 73) ;;
  shiftTermSetupLoop ;;
  wireTreeSyncLoop readTree cutTree linkTree bind canonCopy isNeg ;;
  .ret (.reg 3)

theorem shiftDeepCollectNewAndSync_noRand
    (readLSF packEditsProc readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (shiftDeepCollectNewAndSync readLSF packEditsProc readTree cutTree linkTree bind canonCopy
      isNeg).NoRand := by
  simp [shiftDeepCollectNewAndSync, collectLSFForestsLoop_noRand, collectTermForestStmt_noRand,
    shiftTermSetupLoop_noRand, wireTreeSyncLoop_noRand, Stmt.NoRand]

/-- Complete deterministic Word-RAM body for `ShiftDeepChainSyncSpecW` taking `[root, i, heap]`
(`i < d`) and returning `nextHeap`. -/
@[expose] def shiftDeepChainBody
    (init restart readGraph readLSF coreLenProc readOrd lastInit packEditsProc
      readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  shiftDeepInitRegs ;;
  shiftDeepCollectOld readLSF ;;
  shiftDeepRestartAndReadout restart readGraph readLSF coreLenProc readOrd ;;
  ordRebuildSuffixProgramKStore init readGraph readLSF coreLenProc readOrd lastInit ;;
  shiftDeepCollectNewAndSync readLSF packEditsProc readTree cutTree linkTree bind canonCopy isNeg

theorem shiftDeepChainBody_noRand
    (init restart readGraph readLSF coreLenProc readOrd lastInit packEditsProc
      readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (shiftDeepChainBody init restart readGraph readLSF coreLenProc readOrd lastInit packEditsProc
      readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [shiftDeepChainBody, shiftDeepInitRegs_noRand, shiftDeepCollectOld_noRand,
    shiftDeepRestartAndReadout_noRand, ordRebuildSuffixProgramKStore_noRand,
    shiftDeepCollectNewAndSync_noRand, Stmt.NoRand]

end Programs

section PhaseRuns

/-- Execute Phase 0 (`shiftDeepInitRegs`): decodes `[root, i, heap0]` into `reg 70..83` and
advances `reg 4 := heap0 + 2 * (d - i + 1)` without modifying memory. -/
theorem shiftDeepInitRegs_runs {w root i heap0 handle table d k pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hH : mem root = handle) (hTab : mem (root + 1) = table)
    (hD : mem (handle + 11) = d) (hK : mem (handle + 12) = k)
    (_hiLt : i < d) (hRoot1W : root + 1 < 2 ^ w) (hH12W : handle + 12 < 2 ^ w)
    (hBrBaseW : handle + 18 + (d + 1) < 2 ^ w)
    (hMetaW : table + (d + 1) + 1 + d < 2 ^ w)
    (hHeapW : heap0 + 2 * (d - i + 1) < 2 ^ w) (_hw17 : 17 < 2 ^ w) :
    let cnt := d - i + 1
    let handleBase := handle + 18
    let branchBase := handleBase + (d + 1)
    let lvlMTable := table + (d + 1) + 1
    let levelMeta := lvlMTable + d
    ∃ out c,
      Runs w p ω shiftDeepInitRegs (startState [root, i, heap0] mem pos) .normal out c ∧
      c ≤ 80 ∧ out.mem = mem ∧
      out.regs 70 = root ∧ out.regs 71 = i ∧ out.regs 72 = heap0 ∧
      out.regs 73 = handle ∧ out.regs 74 = table ∧ out.regs 75 = d ∧ out.regs 76 = k ∧
      out.regs 77 = handleBase ∧ out.regs 78 = branchBase ∧ out.regs 79 = cnt ∧
      out.regs 80 = heap0 ∧ out.regs 81 = heap0 + cnt ∧
      out.regs 82 = lvlMTable ∧ out.regs 83 = levelMeta ∧
      out.regs 4 = heap0 + 2 * cnt := by
  dsimp only
  let cnt := d - i + 1
  let s0 := startState [root, i, heap0] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 70 root }
  let s2 := { s1 with regs := Function.update s1.regs 71 i }
  let s3 := { s2 with regs := Function.update s2.regs 72 heap0 }
  let s4 := { s3 with regs := Function.update s3.regs 73 handle }
  let s5 := { s4 with regs := Function.update s4.regs 74 table }
  let s6 := { s5 with regs := Function.update s5.regs 75 d }
  let s7 := { s6 with regs := Function.update s6.regs 76 k }
  let s8 := { s7 with regs := Function.update s7.regs 77 (handle + 18) }
  let s9 := { s8 with regs := Function.update s8.regs 78 (handle + 18 + (d + 1)) }
  let s10 := { s9 with regs := Function.update s9.regs 79 cnt }
  let s11 := { s10 with regs := Function.update s10.regs 80 heap0 }
  let s12 := { s11 with regs := Function.update s11.regs 81 (heap0 + cnt) }
  let s13 := { s12 with regs := Function.update s12.regs 82 (table + (d + 1) + 1) }
  let s14 := { s13 with regs := Function.update s13.regs 83 (table + (d + 1) + 1 + d) }
  let s15 := { s14 with regs := Function.update s14.regs 4 (heap0 + 2 * cnt) }
  have r1 : Runs w p ω (.assign 70 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 71 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨i, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 72 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap0, by simp [Expr.eval, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 73 (.load (.reg 70))) s3 .normal s4 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s3, s2, s1, s0, startState, hH], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 74 (.load (.bin .add (.reg 70) (.const 1)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨table, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState,
      show 1 < 2 ^ w by omega, hRoot1W, hTab], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 75 (.load (.bin .add (.reg 73) (.const 11)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨d, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState,
      show 11 < 2 ^ w by omega, show handle + 11 < 2 ^ w by omega, hD], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 76 (.load (.bin .add (.reg 73) (.const 12)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨k, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState,
      show 12 < 2 ^ w by omega, hH12W, hK], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 77 (.bin .add (.reg 73) (.const 18))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨handle + 18, by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4,
      show 18 < 2 ^ w by omega, show handle + 18 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 78 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1)))) s8 .normal s9 6 :=
    runs_assign_iff.mpr ⟨handle + 18 + (d + 1), by simp [Expr.eval, BinOp.eval, s8, s7, s6,
      show 1 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega, hBrBaseW], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 79 (.bin .add (.bin .sub (.reg 75) (.reg 71)) (.const 1))) s9 .normal s10 6 :=
    runs_assign_iff.mpr ⟨cnt, by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2,
      show 1 < 2 ^ w by omega, show d - i < 2 ^ w by omega, show d - i + 1 < 2 ^ w by omega, cnt],
      rfl, rfl, rfl⟩
  have r11 : Runs w p ω (.assign 80 (.reg 72)) s10 .normal s11 2 :=
    runs_assign_iff.mpr ⟨heap0, by simp [Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3], rfl, rfl, rfl⟩
  have r12 : Runs w p ω (.assign 81 (.bin .add (.reg 72) (.reg 79))) s11 .normal s12 4 :=
    runs_assign_iff.mpr ⟨heap0 + cnt, by simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, s6,
      s5, s4, s3, show heap0 + cnt < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 82 (.bin .add (.bin .add (.reg 74) (.bin .add (.reg 75) (.const 1))) (.const 1))) s12 .normal s13 8 :=
    runs_assign_iff.mpr ⟨table + (d + 1) + 1, by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8,
      s7, s6, s5, show 1 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega,
      show table + (d + 1) < 2 ^ w by omega, show table + (d + 1) + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r14 : Runs w p ω (.assign 83 (.bin .add (.reg 82) (.reg 75))) s13 .normal s14 4 :=
    runs_assign_iff.mpr ⟨table + (d + 1) + 1 + d, by simp [Expr.eval, BinOp.eval, s13, s12, s11, s10,
      s9, s8, s7, s6, hMetaW], rfl, rfl, rfl⟩
  have r15 : Runs w p ω (.assign 4 (.bin .add (.reg 81) (.reg 79))) s14 .normal s15 4 :=
    runs_assign_iff.mpr ⟨heap0 + 2 * cnt, by
      have hEq : heap0 + cnt + cnt = heap0 + 2 * cnt := by omega
      simp [Expr.eval, BinOp.eval, s14, s13, s12, s11, s10, hEq, show heap0 + 2 * cnt < 2 ^ w by omega], rfl, rfl, rfl⟩
  refine ⟨s15, _,
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 3, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 6, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 6, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 2, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 4, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 8, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 4, 4, r14, r15, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by omega, rfl,
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7, s6],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8, s7],
    by simp [s15, s14, s13, s12, s11, s10, s9, s8],
    by simp [s15, s14, s13, s12, s11, s10, s9],
    by simp [s15, s14, s13, s12, s11, s10, cnt],
    by simp [s15, s14, s13, s12, s11],
    by simp [s15, s14, s13, s12, cnt],
    by simp [s15, s14, s13],
    by simp [s15, s14],
    by simp [s15, cnt]⟩

/-- Shared invariant for `collectLSFForestsLoop_runs`. -/
private structure CollectLSFInv {w L first baseIdx dstReg dstPtrs handleBase branchBase
    levelMeta intCap : ℕ} {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T CP)
    (coreHandle : ℕ → ℕ) (tok0 : ℕ → Rcore.τ) (forestSafe : ℕ → Prop) (st0 : State)
    (cur : ℕ) (s : State) (pot : ℕ) : Prop where
  r19 : s.regs 19 = cur
  r20 : s.regs 20 = first
  r71 : s.regs 71 = baseIdx
  r75 : s.regs 75 = CP.d
  r77 : s.regs 77 = handleBase
  r78 : s.regs 78 = branchBase
  r83 : s.regs 83 = levelMeta
  rDst : s.regs dstReg = dstPtrs
  rKeep : ∀ r, (70 ≤ r) ∨ r = 20 ∨ r = 21 → s.regs r = st0.regs r
  hLo : st0.regs 4 ≤ s.regs 4
  hHi : s.regs 4 ≤ st0.regs 4 + 5 * (cur - first)
  hz : ZeroFrom s.mem (s.regs 4)
  toks : ∃ tok : ℕ → Rcore.τ,
    (∀ j, first ≤ j → j < CP.d →
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s.mem ∧
      (j < cur → ∀ a, Rcore.foot (coreHandle j) (tok j) a →
        Rcore.foot (coreHandle j) (tok0 j) a ∨ (st0.regs 4 ≤ a ∧ a < s.regs 4)) ∧
      (cur ≤ j → tok j = tok0 j)) ∧
    (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (tok j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (tok j₂) a) ∧
    (∀ j, first ≤ j → j < cur →
      ∃ vc ec,
        DynGraphAt s.mem (s.mem (dstPtrs + (j - baseIdx))) vc ec
          (T.lsfs (chain.scState j) (chain.bran j)).F.F ∧
        s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec ≤ s.regs 4 ∧
        (∀ r, cur ≤ r → r < CP.d → ∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
          a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec →
          ¬ Rcore.foot (coreHandle r) (tok0 r) a) ∧
        (∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
          a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec →
          a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx + 1) ≤ a) ∧
        (∀ a, s.mem (dstPtrs + (j - baseIdx)) ≤ a →
          a < s.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec → forestSafe a) ∧
        (∀ e ∈ (T.lsfs (chain.scState j) (chain.bran j)).F.F.E, e < intCap)) ∧
    pot = (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem)
  frame : ∀ a < st0.regs 4,
    (∀ j, first ≤ j → j < cur → ¬ Rcore.foot (coreHandle j) (tok0 j) a) →
    (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (cur - baseIdx) ≤ a) →
    s.mem a = st0.mem a

/-- Execute `collectLSFForestsLoop` over levels `j ∈ [first, d)`: reads each active LSF forest
pointer via op `2` into `mem[dstPtrs + (j - baseIdx)]`, preserves every core representation and
disjointness, and telescopes `Rcore.phi` across `[first, d)` with cost `(d - first) * (P.readout + 48) + 7`. -/
theorem collectLSFForestsLoop_runs
    {w L capExp init first baseIdx dstReg dstPtrs handleBase branchBase levelMeta intCap : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation : ℕ → ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (chain : ChainState T CP) (coreHandle : ℕ → ℕ) (coreTok0 : ℕ → Rcore.τ)
    (forestSafe : ℕ → Prop)
    (hCoreLocal : Rcore.Local)
    (hDstReg : 70 ≤ dstReg)
    (hBaseLe : baseIdx ≤ first) (hFirstLe : first ≤ CP.d)
    (h20 : st.regs 20 = first) (h71 : st.regs 71 = baseIdx) (h75 : st.regs 75 = CP.d)
    (h77 : st.regs 77 = handleBase) (h78 : st.regs 78 = branchBase)
    (h83 : st.regs 83 = levelMeta) (hDst : st.regs dstReg = dstPtrs)
    (hkW : CP.k < 2 ^ w) (hdW : CP.d < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hMetaEnd : levelMeta + 2 * CP.d ≤ st.regs 4) (hHEnd : handleBase + CP.d ≤ st.regs 4)
    (hBEnd : branchBase + CP.d ≤ st.regs 4)
    (hDstEnd : dstPtrs + (CP.d - baseIdx) ≤ st.regs 4)
    (hRoom : st.regs 4 + 5 * (CP.d - first) < 2 ^ w)
    (hz0 : ZeroFrom st.mem (st.regs 4))
    (hCoreImpl : ∀ j, first ≤ j → j < CP.d → ∀ vc ec,
      Rcore.Implements w p init op
        (sparseCoreOrdMachineContractK fmt L T (chain.G j) CP.k (chain.lvlM j) chain.N₀
          vc ec capExp P (allocation j)))
    (hCores : ∀ j, first ≤ j → j < CP.d →
      st.mem (handleBase + j) = coreHandle j ∧
      st.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < CP.k ∧ coreHandle j < 2 ^ w ∧
      Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok0 j) st.mem ∧
      SparseCoreOrdInput T CP.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (coreHandle j) (coreTok0 j) a → a < st.regs 4) ∧
      (∀ r, first ≤ r → r < CP.d →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (handleBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (branchBase + j) ∧
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) (levelMeta + CP.d + j)) ∧
      (handleBase + j < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ handleBase + j) ∧
      (branchBase + j < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ branchBase + j) ∧
      (levelMeta + CP.d + j < dstPtrs + (first - baseIdx) ∨
        dstPtrs + (CP.d - baseIdx) ≤ levelMeta + CP.d + j) ∧
      (∀ t, first - baseIdx ≤ t → t < CP.d - baseIdx →
        ¬ Rcore.foot (coreHandle j) (coreTok0 j) (dstPtrs + t)) ∧
      (∃ vc ec,
        DynGraphAt st.mem (st.mem (levelMeta + CP.d + j)) vc ec (chain.G j) ∧
        st.mem (levelMeta + CP.d + j) + dynGraphSize vc ec ≤ st.regs 4 ∧
        (∀ a, st.mem (levelMeta + CP.d + j) ≤ a →
          a < st.mem (levelMeta + CP.d + j) + dynGraphSize vc ec →
          (∀ r, first ≤ r → r < CP.d → ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
          (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ a))))
    (hCoreDisj : ∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
      ∀ a, Rcore.foot (coreHandle j₁) (coreTok0 j₁) a →
        ¬ Rcore.foot (coreHandle j₂) (coreTok0 j₂) a)
    (hForestRead : ∀ j, first ≤ j → j < CP.d → ∀ m h ret vcF ecF Lw,
      LSFAt m h vcF ecF fmt.limbBits Lw fmt.precision (chain.G j).E
        (T.lsfs (chain.scState j) (chain.bran j)) →
      st.regs 4 ≤ h → h ≤ ret → ret ≤ h + 5 →
      m (h + 1) + dynGraphSize vcF ecF ≤ ret ∧
      (∀ r, j < r → r < CP.d → ∀ a, m (h + 1) ≤ a → a < m (h + 1) + dynGraphSize vcF ecF →
        ¬ Rcore.foot (coreHandle r) (coreTok0 r) a) ∧
      (∀ a, m (h + 1) ≤ a → a < m (h + 1) + dynGraphSize vcF ecF →
        a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx + 1) ≤ a) ∧
      (∀ a, m (h + 1) ≤ a → a < m (h + 1) + dynGraphSize vcF ecF → forestSafe a) ∧
      (∀ e ∈ (T.lsfs (chain.scState j) (chain.bran j)).F.F.E, e < intCap)) :
    ∃ (out : State) (c : ℕ) (coreTok' : ℕ → Rcore.τ),
      Runs w p ω (collectLSFForestsLoop (op 2) dstReg) st .normal out c ∧
      st.regs 4 ≤ out.regs 4 ∧ out.regs 4 ≤ st.regs 4 + 5 * (CP.d - first) ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d →
        Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (coreTok' j) out.mem ∧
        (∀ a, Rcore.foot (coreHandle j) (coreTok' j) a →
          Rcore.foot (coreHandle j) (coreTok0 j) a ∨ (st.regs 4 ≤ a ∧ a < out.regs 4))) ∧
      (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (coreHandle j₁) (coreTok' j₁) a →
          ¬ Rcore.foot (coreHandle j₂) (coreTok' j₂) a) ∧
      (∀ j, first ≤ j → j < CP.d →
        ∃ vc ec,
          DynGraphAt out.mem (out.mem (dstPtrs + (j - baseIdx))) vc ec
            (T.lsfs (chain.scState j) (chain.bran j)).F.F ∧
          out.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec ≤ out.regs 4 ∧
          (∀ a, out.mem (dstPtrs + (j - baseIdx)) ≤ a →
            a < out.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec →
            a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx + 1) ≤ a) ∧
          (∀ a, out.mem (dstPtrs + (j - baseIdx)) ≤ a →
            a < out.mem (dstPtrs + (j - baseIdx)) + dynGraphSize vc ec → forestSafe a) ∧
          (∀ e ∈ (T.lsfs (chain.scState j) (chain.bran j)).F.F.E, e < intCap)) ∧
      (∀ a < st.regs 4,
        (∀ j, first ≤ j → j < CP.d → ¬ Rcore.foot (coreHandle j) (coreTok0 j) a) →
        (a < dstPtrs + (first - baseIdx) ∨ dstPtrs + (CP.d - baseIdx) ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r, (70 ≤ r) ∨ r = 20 ∨ r = 21 → out.regs r = st.regs r) ∧
      c + (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok' j) out.mem) ≤
        (CP.d - first) * (P.readout + 48) + 7 +
        (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem) := by
  let Inv := CollectLSFInv (w := w) (L := L) (first := first) (baseIdx := baseIdx)
    (dstReg := dstReg) (dstPtrs := dstPtrs) (handleBase := handleBase) (branchBase := branchBase)
    (levelMeta := levelMeta) (intCap := intCap) (fmt := fmt) Rcore chain coreHandle coreTok0 forestSafe st
  let pot0 := (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (coreTok0 j) st.mem)
  have hInv0 : Inv first { st with regs := Function.update st.regs 19 first } pot0 :=
    { r19 := by simp, r20 := by simp [h20], r71 := by simp [h71], r75 := by simp [h75],
      r77 := by simp [h77], r78 := by simp [h78], r83 := by simp [h83],
      rDst := by simp [Function.update_of_ne (by omega : dstReg ≠ 19), hDst],
      rKeep := fun r hr => Function.update_of_ne (by omega) _ _,
      hLo := le_rfl, hHi := by simp, hz := hz0,
      toks := ⟨coreTok0, fun j hj1 hj2 => ⟨(hCores j hj1 hj2).2.2.2.2.1, fun h => by omega, fun _ => rfl⟩,
        hCoreDisj, fun _ h1 h2 => by omega, rfl⟩,
      frame := fun _ _ _ _ => rfl }
  -- Note `forRange 19 (.reg 20) (.reg 75)` has upper bound `.reg 75` (not `.reg 21`),
  -- so we prove the loop by direct induction on `rem = CP.d - cur` mirroring `forRange19_runs_with_pot`.
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  let body : Stmt :=
    .assign 3 (.load (.bin .add (.reg 77) (.reg 19))) ;;
    .assign 2 (.load (.bin .add (.reg 78) (.reg 19))) ;;
    .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))) ;;
    ordCoreReadLSFStmt (op 2) ;;
    .store (.bin .add (.reg dstReg) (.bin .sub (.reg 19) (.reg 71)))
      (.load (.bin .add (.reg 4) (.const 1))) ;;
    .assign 4 (.reg 5)
  let sInit := { st with regs := Function.update st.regs 19 first }
  have rInit : Runs w p ω (.assign 19 (.reg 20)) st .normal sInit 2 :=
    runs_assign_iff.mpr ⟨first, by simp [Expr.eval, h20], rfl, rfl, rfl⟩
  suffices hUp : ∀ (rem cur : ℕ) (s : State) (pot : ℕ),
      first ≤ cur → cur + rem = CP.d → Inv cur s pot →
      ∃ out c potEnd,
        Runs w p ω (forUp 19 (.reg 75) body) s .normal out c ∧
        Inv CP.d out potEnd ∧
        c + potEnd ≤ rem * (P.readout + 48) + pot + 4 by
    obtain ⟨out, c, potEnd, rLoop, hEnd, hc⟩ := hUp (CP.d - first) first sInit pot0 le_rfl (by omega) hInv0
    obtain ⟨tokEnd, hTokRep, hTokDisj, hForests, hPotEq⟩ := hEnd.toks
    refine ⟨out, 2 + c + 1, tokEnd, runs_seq_iff.mpr (Or.inr ⟨sInit, 2, c, rInit, rLoop, rfl⟩),
      hEnd.hLo, hEnd.hHi, hEnd.hz,
      fun j hj1 hj2 => ⟨(hTokRep j hj1 hj2).1, (hTokRep j hj1 hj2).2.1 hj2⟩,
      hTokDisj,
      fun j hj1 hj2 => by
        obtain ⟨vc, ec, hG, hE, _, hO, hS, hC⟩ := hForests j hj1 hj2
        exact ⟨vc, ec, hG, hE, hO, hS, hC⟩,
      hEnd.frame, hEnd.rKeep, by rw [← hPotEq]; omega⟩
  intro rem
  induction rem with
  | zero =>
    intro cur s pot hge hsum hInv
    have hcur : cur = CP.d := by omega
    subst hcur
    refine ⟨s, 4, pot, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75],
      rfl, rfl, by simp [Expr.size]⟩), hInv, by simp; omega⟩
  | succ rem ih =>
    intro cur s pot hge hsum hInv
    have hlt : cur < CP.d := by omega
    obtain ⟨tok, hTokRep, hTokDisj, hForests, hPotEq⟩ := hInv.toks
    obtain ⟨hHCell, hBCell, hBrLt, hChW, _, hInCur, hFoot0Cur, hNotCell, hHOutD, hBOutD,
      hMOutD, hDstNotF, ⟨vcG, ecG, hDG0, hDGEnd0, hDGDisj0⟩⟩ := hCores cur hge hlt
    have hTokCurEq : tok cur = coreTok0 cur := (hTokRep cur hge hlt).2.2 le_rfl
    have hHCellS : s.mem (handleBase + cur) = coreHandle cur :=
      (hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).1)
        (by rcases hHOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hHCell
    have hBCellS : s.mem (branchBase + cur) = chain.bran cur :=
      (hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).2.1)
        (by rcases hBOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])).trans hBCell
    have hGPtrS : s.mem (levelMeta + CP.d + cur) = st.mem (levelMeta + CP.d + cur) :=
      hInv.frame _ (by omega) (fun r hr1 hr2 => (hNotCell r hr1 (by omega)).2.2)
        (by rcases hMOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)])
    have hDGS : DynGraphAt s.mem (st.mem (levelMeta + CP.d + cur)) vcG ecG (chain.G cur) :=
      dynGraphAt_of_agree hDG0 (fun a ha1 ha2 => by
        obtain ⟨hNF, hOutD⟩ := hDGDisj0 a ha1 ha2
        exact hInv.frame a (by omega) (fun r hr1 hr2 => hNF r hr1 (by omega))
          (by rcases hOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]))
    let s1 := { s with regs := Function.update s.regs 3 (coreHandle cur) }
    let s2 := { s1 with regs := Function.update s1.regs 2 (chain.bran cur) }
    let s3 := { s2 with regs := Function.update s2.regs 6 (st.mem (levelMeta + CP.d + cur)) }
    have r1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 19)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨coreHandle cur, by simp [Expr.eval, BinOp.eval, hInv.r77, hInv.r19,
        show handleBase + cur < 2 ^ w by omega, hHCellS], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 19)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨chain.bran cur, by simp [Expr.eval, BinOp.eval, s1, hInv.r78, hInv.r19,
        show branchBase + cur < 2 ^ w by omega, hBCellS], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 19))))
        s2 .normal s3 7 :=
      runs_assign_iff.mpr ⟨st.mem (levelMeta + CP.d + cur), by simp [Expr.eval, BinOp.eval, s2, s1,
        hInv.r83, hInv.r75, hInv.r19, show levelMeta + CP.d < 2 ^ w by omega,
        show levelMeta + CP.d + cur < 2 ^ w by omega, hGPtrS], rfl, rfl, rfl⟩
    have hFootCurS : ∀ a, Rcore.foot (coreHandle cur) (tok cur) a → a < s.regs 4 := fun a ha =>
      (hFoot0Cur a (hTokCurEq ▸ ha)).trans_le hInv.hLo
    obtain ⟨s4, ret4, c4, y4, r4, hs4_5, hrep4, _, ⟨vcF, ecF, hLSF4⟩, hresp4, hc4, hs4_regs⟩ :=
      ordCoreReadLSFK_runs (ω := ω) (st := s3) (hCoreImpl cur hge hlt vcG ecG)
        (by simp [s3, s2]) (by simp [s3, s2, s1]) (by simp [s3]) (by simp [s3, s2, s1])
        hBrLt hkW hChW hDGS (hDGEnd0.trans hInv.hLo) (hTokRep cur hge hlt).1 hInCur hFootCurS
        hInv.hz (by have := hInv.hHi; omega)
    have hretLo : s.regs 4 ≤ ret4 := hresp4.1
    have hretHi : ret4 ≤ s.regs 4 + 5 := hresp4.2.1
    let dstCell := dstPtrs + (cur - baseIdx)
    let fPtr := s4.mem (s.regs 4 + 1)
    let s5 := { s4 with mem := Function.update s4.mem dstCell fPtr }
    let s6 := { s5 with regs := Function.update s5.regs 4 ret4 }
    have hs4_r (r : ℕ) (hr : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 5 ∧ r ≠ 6) : s4.regs r = s.regs r := by
      rw [hs4_regs r hr.2.2.1]
      simp [s3, s2, s1, Function.update_of_ne hr.2.2.2, Function.update_of_ne hr.1,
        Function.update_of_ne hr.2.1]
    have hs4_1W : s.regs 4 + 1 < 2 ^ w := by have := hInv.hHi; omega
    have r5 : Runs w p ω (.store (.bin .add (.reg dstReg) (.bin .sub (.reg 19) (.reg 71)))
        (.load (.bin .add (.reg 4) (.const 1)))) s4 .normal s5 10 :=
      runs_store_iff.mpr ⟨dstCell, fPtr,
        by simp [Expr.eval, BinOp.eval, hs4_r dstReg (by omega), hs4_r 19 (by omega),
          hs4_r 71 (by omega), hInv.rDst, hInv.r19, hInv.r71, dstCell,
          show cur - baseIdx < 2 ^ w by omega,
          show dstPtrs + (cur - baseIdx) < 2 ^ w by omega],
        by simp [Expr.eval, BinOp.eval, hs4_r 4 (by omega), hw1, hs4_1W, fPtr],
        rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 4 (.reg 5)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨ret4, by simp [Expr.eval, s5, hs4_5], rfl, rfl, rfl⟩
    have rBody : Runs w p ω body s .normal s6 (5 + (5 + (7 + (c4 + (10 + 2 + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 10, 2, r5, r6, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    -- Update tokens and potential
    let tok' : ℕ → Rcore.τ := fun j => if j = cur then y4 else tok j
    have hDstNotFootCur : ¬ Rcore.foot (coreHandle cur) y4 dstCell := by
      intro hf
      rcases hresp4.2.2.2.2 dstCell hf with h0 | ⟨hlo, _⟩
      · exact hDstNotF (cur - baseIdx) (by omega) (by omega) (hTokCurEq ▸ h0)
      · have := hInv.hLo; omega
    have hlocY4 := hCoreLocal (coreHandle cur) (chainLevelOrdAbs chain cur) y4 s4.mem s6.mem
      (fun a ha => by
        have hne : a ≠ dstCell := fun h => hDstNotFootCur (h ▸ ha)
        simp [s6, s5, Function.update_of_ne hne])
    have hOtherPres (j : ℕ) (hj1 : first ≤ j) (hj2 : j < CP.d) (hne : j ≠ cur) :
        Rcore.rep (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s6.mem ∧
        Rcore.phi (coreHandle j) (tok j) s6.mem = Rcore.phi (coreHandle j) (tok j) s.mem := by
      have hlocJ := hCoreLocal (coreHandle j) (chainLevelOrdAbs chain j) (tok j) s.mem s6.mem
        (fun a ha => by
          have hnfCur : ¬ Rcore.foot (coreHandle cur) (tok cur) a := fun hc =>
            hTokDisj cur j hge hlt hj1 hj2 hne.symm a hc ha
          have haLt : a < s.regs 4 := by
            by_cases hjlt : j < cur
            · rcases (hTokRep j hj1 hj2).2.1 hjlt a ha with h0 | ⟨_, hhi⟩
              · exact ((hCores j hj1 hj2).2.2.2.2.2.2.1 a h0).trans_le hInv.hLo
              · exact hhi
            · have hjeq := (hTokRep j hj1 hj2).2.2 (by omega)
              exact ((hCores j hj1 hj2).2.2.2.2.2.2.1 a (hjeq ▸ ha)).trans_le hInv.hLo
          have hneDst : a ≠ dstCell := by
            intro heq; subst heq
            by_cases hjlt : j < cur
            · rcases (hTokRep j hj1 hj2).2.1 hjlt dstCell ha with h0 | ⟨hlo, _⟩
              · exact (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 (cur - baseIdx) (by omega) (by omega) h0
              · omega
            · have hjeq := (hTokRep j hj1 hj2).2.2 (by omega)
              exact (hCores j hj1 hj2).2.2.2.2.2.2.2.2.2.2.2.1 (cur - baseIdx) (by omega) (by omega)
                (hjeq ▸ ha)
          change s.mem a = Function.update s4.mem dstCell fPtr a
          rw [Function.update_of_ne hneDst, hresp4.2.2.2.1 a haLt hnfCur])
      exact ⟨hlocJ.1 (hTokRep j hj1 hj2).1, hlocJ.2.symm⟩
    let pot' := (Finset.Ico first CP.d).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem)
    have hPotDiff :
        pot' + Rcore.phi (coreHandle cur) (tok cur) s.mem =
          pot + Rcore.phi (coreHandle cur) y4 s4.mem := by
      have hMem : cur ∈ Finset.Ico first CP.d := Finset.mem_Ico.mpr ⟨hge, hlt⟩
      have hS1 := Finset.add_sum_erase (Finset.Ico first CP.d)
        (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem) hMem
      have hS2 := Finset.add_sum_erase (Finset.Ico first CP.d)
        (fun j => Rcore.phi (coreHandle j) (tok j) s.mem) hMem
      have hEraseEq :
          (Finset.Ico first CP.d |>.erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok' j) s6.mem) =
          (Finset.Ico first CP.d |>.erase cur).sum (fun j => Rcore.phi (coreHandle j) (tok j) s.mem) :=
        Finset.sum_congr rfl (fun j hj => by
          obtain ⟨hne, hmem'⟩ := Finset.mem_erase.mp hj
          obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hmem'
          simp only [tok', hne, ↓reduceIte]
          exact (hOtherPres j hj1 hj2 hne).2)
      have hCurEq : Rcore.phi (coreHandle cur) (tok' cur) s6.mem =
          Rcore.phi (coreHandle cur) y4 s4.mem := by
        simp only [tok', ↓reduceIte]; exact hlocY4.2.symm
      dsimp only [pot']; rw [hPotEq, ← hS1, ← hS2, hCurEq, hEraseEq]; omega
    -- Build `Inv (cur + 1)` on `s7`
    let s7 := { s6 with regs := Function.update s6.regs 19 (cur + 1) }
    have hs7_r (r : ℕ) (h19 : r ≠ 19) (h4 : r ≠ 4) (h2 : r ≠ 2) (h3 : r ≠ 3) (h5 : r ≠ 5) (h6 : r ≠ 6) :
        s7.regs r = s.regs r := by
      simp only [s7, s6, s5, Function.update_of_ne h19, Function.update_of_ne h4]
      exact hs4_r r ⟨h2, h3, h5, h6⟩
    obtain ⟨hFEnd4, hFDisj4, hFOutDst4, hFSafe4, hFCap4⟩ :=
      hForestRead cur hge hlt s4.mem (s.regs 4) ret4 vcF ecF (s4.mem (s.regs 4 + 4))
        hLSF4 hInv.hLo hretLo hretHi
    have hInvNext : Inv (cur + 1) s7 pot' :=
      { r19 := by simp [s7],
        r20 := (hs7_r 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r20,
        r71 := (hs7_r 71 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r71,
        r75 := (hs7_r 75 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r75,
        r77 := (hs7_r 77 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r77,
        r78 := (hs7_r 78 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r78,
        r83 := (hs7_r 83 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hInv.r83,
        rDst := (hs7_r dstReg (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans hInv.rDst,
        rKeep := fun r hr =>
          (hs7_r r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans (hInv.rKeep r hr),
        hLo := by simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; exact hInv.hLo.trans hretLo,
        hHi := by simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; have := hInv.hHi; omega,
        hz := fun a ha => by
          simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self] at ha
          have hne : a ≠ dstCell := by have := hInv.hLo; omega
          simp only [s7, s6, s5, Function.update_of_ne hne]
          exact hresp4.2.2.1 a ha,
        toks := ⟨tok',
          fun j hj1 hj2 => by
            by_cases hjeq : j = cur
            · subst hjeq
              simp only [s7, tok', ↓reduceIte]
              refine ⟨hlocY4.1 hrep4, fun _ a ha => ?_, fun h => by omega⟩
              simp only [s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              rcases hresp4.2.2.2.2 a ha with h0 | ⟨hlo, hhi⟩
              · exact Or.inl (hTokCurEq ▸ h0)
              · exact Or.inr ⟨hInv.hLo.trans hlo, hhi⟩
            · simp only [s7, tok', hjeq, ↓reduceIte]
              refine ⟨(hOtherPres j hj1 hj2 hjeq).1, fun hjlt a ha => ?_,
                fun hjge => (hTokRep j hj1 hj2).2.2 (by omega)⟩
              simp only [s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]
              rcases (hTokRep j hj1 hj2).2.1 (by omega) a ha with h0 | ⟨hlo, hhi⟩
              · exact Or.inl h0
              · exact Or.inr ⟨hlo, hhi.trans_le hretLo⟩,
          fun j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2 => by
            by_cases e1 : j₁ = cur <;> by_cases e2 : j₂ = cur
            · exact hne (e1.trans e2.symm)
            · subst e1; simp only [tok', ↓reduceIte, e2] at ha1 ha2
              rcases hresp4.2.2.2.2 a ha1 with h0 | ⟨hlo, _⟩
              · exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a h0 ha2
              · by_cases hj2lt : j₂ < j₁
                · rcases (hTokRep j₂ h3 h4).2.1 hj2lt a ha2 with h0' | ⟨_, hhi'⟩
                  · have := (hCores j₂ h3 h4).2.2.2.2.2.2.1 a h0'; have := hInv.hLo; omega
                  · omega
                · have hjeq := (hTokRep j₂ h3 h4).2.2 (by omega)
                  have := (hCores j₂ h3 h4).2.2.2.2.2.2.1 a (hjeq ▸ ha2); have := hInv.hLo; omega
            · subst e2; simp only [tok', ↓reduceIte, e1] at ha1 ha2
              rcases hresp4.2.2.2.2 a ha2 with h0 | ⟨hlo, _⟩
              · exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a ha1 h0
              · by_cases hj1lt : j₁ < j₂
                · rcases (hTokRep j₁ h1 h2).2.1 hj1lt a ha1 with h0' | ⟨_, hhi'⟩
                  · have := (hCores j₁ h1 h2).2.2.2.2.2.2.1 a h0'; have := hInv.hLo; omega
                  · omega
                · have hjeq := (hTokRep j₁ h1 h2).2.2 (by omega)
                  have := (hCores j₁ h1 h2).2.2.2.2.2.2.1 a (hjeq ▸ ha1); have := hInv.hLo; omega
            · simp only [tok', e1, e2, ↓reduceIte] at ha1 ha2
              exact hTokDisj j₁ j₂ h1 h2 h3 h4 hne a ha1 ha2,
          fun j hj1 hj2 => by
            by_cases hjeq : j = cur
            · subst hjeq
              have hDstEq : s7.mem (dstPtrs + (j - baseIdx)) = fPtr := by simp [s7, s6, s5, dstCell]
              refine ⟨vcF, ecF, ?_, ?_, ?_, ?_, ?_, hFCap4⟩
              · rw [hDstEq]
                exact dynGraphAt_of_agree hLSF4.2.1 (fun a ha1 ha2 => by
                  have hne : a ≠ dstCell := by
                    rcases hFOutDst4 a ha1 ha2 with h | h <;> (dsimp [dstCell]; omega)
                  simp [s7, s6, s5, Function.update_of_ne hne])
              · rw [hDstEq]; simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; exact hFEnd4
              · rw [hDstEq]; exact fun r hr1 hr2 a ha1 ha2 => hFDisj4 r hr1 hr2 a ha1 ha2
              · rw [hDstEq]; exact hFOutDst4
              · rw [hDstEq]; exact hFSafe4
            · obtain ⟨vcJ, ecJ, hDGJ, hEndJ, hDisjJ, hOutDstJ, hSafeJ, hCapJ⟩ := hForests j hj1 (by omega)
              have hCellNe : dstPtrs + (j - baseIdx) ≠ dstCell := by dsimp [dstCell]; omega
              have hPtrEq : s7.mem (dstPtrs + (j - baseIdx)) = s.mem (dstPtrs + (j - baseIdx)) := by
                simp only [s7, s6, s5, Function.update_of_ne hCellNe]
                exact hresp4.2.2.2.1 _ (by have := hInv.hLo; omega)
                  (fun hf => hDstNotF (j - baseIdx) (by omega) (by omega) (hTokCurEq ▸ hf))
              refine ⟨vcJ, ecJ, ?_, by rw [hPtrEq]; simp only [s7, s6, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19), Function.update_self]; exact hEndJ.trans hretLo,
                fun r hr1 hr2 a ha1 ha2 => hDisjJ r (by omega) hr2 a (hPtrEq ▸ ha1) (hPtrEq ▸ ha2),
                fun a ha1 ha2 => hOutDstJ a (hPtrEq ▸ ha1) (hPtrEq ▸ ha2),
                fun a ha1 ha2 => hSafeJ a (hPtrEq ▸ ha1) (hPtrEq ▸ ha2), hCapJ⟩
              rw [hPtrEq]
              exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 => by
                have hneDst : a ≠ dstCell := by
                  rcases hOutDstJ a ha1 ha2 with h | h <;> (dsimp [dstCell]; omega)
                simp only [s7, s6, s5, Function.update_of_ne hneDst]
                exact hresp4.2.2.2.1 a (by omega) (fun hf => hDisjJ cur le_rfl hlt a ha1 ha2 (hTokCurEq ▸ hf)))
          , rfl⟩,
        frame := fun a ha hNF hOutD => by
          have hneDst : a ≠ dstCell := by dsimp [dstCell]; omega
          simp only [s7, s6, s5, Function.update_of_ne hneDst]
          rw [hresp4.2.2.2.1 a (ha.trans_le hInv.hLo) (fun hf => hNF cur hge (Nat.lt_succ_self cur) (hTokCurEq ▸ hf))]
          exact hInv.frame a ha (fun r hr1 hr2 => hNF r hr1 (by omega))
            (by rcases hOutD with h | h <;> [exact Or.inl h; exact Or.inr (by omega)]) }
    have rInc : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) s6 .normal s7 4 :=
      runs_assign_iff.mpr ⟨cur + 1, by simp [Expr.eval, BinOp.eval, s6, s5, hs4_r 19 (by omega),
        hInv.r19, hw1, show cur + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    obtain ⟨out, cRest, potEnd, rRest, hInvEnd, hcRest⟩ := ih (cur + 1) s7 pot' (by omega) (by omega) hInvNext
    have rAll : Runs w p ω (forUp 19 (.reg 75) body) s .normal out
        (((5 + (5 + (7 + (c4 + (10 + 2 + 1) + 1) + 1) + 1) + 1) + 4 + 1) + cRest + 4) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s7, _, cRest,
        by simp [Expr.eval, BinOp.eval, hInv.r19, hInv.r75, hlt, hwne0],
        by omega,
        runs_seq_iff.mpr (Or.inr ⟨s6, _, 4, rBody, rInc, rfl⟩),
        rRest, by simp [Expr.size]; omega⟩))
    refine ⟨out, _, potEnd, rAll, hInvEnd, ?_⟩
    have hmul : (rem + 1) * (P.readout + 48) = rem * (P.readout + 48) + (P.readout + 48) := by ring
    change c4 + Rcore.phi (coreHandle cur) y4 s4.mem ≤ P.readout + 5 + Rcore.phi (coreHandle cur) (tok cur) s.mem at hc4
    omega

end PhaseRuns

end MinCostFlow.MinRatio
