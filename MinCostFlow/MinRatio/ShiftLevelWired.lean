module

public import MinCostFlow.MinRatio.UpdateCycleLoopBase
public import MinCostFlow.MinRatio.ShiftLastLevel
public import MinCostFlow.MinRatio.ShiftGuards
public import MinCostFlow.MinRatio.ConcreteRebuildShift
public import MinCostFlow.MinRatio.TreeEditConcrete
import WordRAM.Tactic

/-!
# Wired level-shift procedure (`ShiftLevelStepSpec`)

Implements the deterministic Word-RAM entry `shiftLevelWiredBody` for Algorithm 2's
level shift (`[root, i, heap]`, pages 20 and 29):
1. Increments `shiftCount[i]` via `recordAcceptedShift` (`ShiftGuards.lean`).
2. Branches on `i < d` vs `i = d`:
   - If `i < d`: reads `chain.bran i`, computes `wrapped := ((bran + 1) % k == 0)`, updates
     `passes[i..d]` via `advanceShiftPasses` (`PassReset.lean`), resets `branD := 0` and
     `updCount[i+1..d-1] := 0` via `resetPassSuffix`, and invokes `shiftDeepChainProc`
     (which executes `shiftRestart` + suffix rebuild + `treeEditLoop`).
   - If `i = d`: updates `branD` and `passes[d]` via `shiftTerminalSchedule` (`ShiftLastLevel.lean`)
     and invokes `shiftTermChainProc` (which advances `lastBran` via `shiftBranch` and syncs the
     path tree via `treeEditLoop`).
3. Proves `shiftLevelStepSpec_wired`, discharging `ShiftLevelStepSpec` cleanly from the modular
   chain-sync specs `ShiftTermChainSyncSpec` and `ShiftDeepChainSyncSpec`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Modular contract for the terminal-level (`i = d`) chain branch advance and path-tree
synchronization step called by `shiftLevelWiredBody` after `SolverScheduleAt` has already been
updated to `alg2LoopShiftStep cfg model (Fin.last cfg.P.d)`. -/
@[expose] def ShiftTermChainSyncSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftTermChainProc : ℕ) (termSpace termBudget : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftTermChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      Rrep.rep root model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + termSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        Rrep.rep root model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ termBudget + Rrep.phi root tok mem0

/-- Modular contract for the non-terminal (`i < d`) restart, deeper suffix rebuild, and path-tree
synchronization step called by `shiftLevelWiredBody` after `SolverScheduleAt` has already been
updated to `alg2LoopShiftStep cfg model i`. -/
@[expose] def ShiftDeepChainSyncSpec (w L P m V psi k epsExp drainUnit : ℕ)
    (cfg : Alg2Config) (Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)) (p : Program)
    (shiftDeepChainProc : ℕ) (deepSpace deepBudget : ℕ) : Prop :=
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  ∃ body, p.procs[shiftDeepChainProc]? = some body ∧
    ∀ (root heap pos : ℕ) (i : Fin (cfg.P.d + 1)) (ω : ℕ → Bool) (mem0 mem : ℕ → ℕ)
      (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (B R : ℤ),
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      Rrep.rep root model tok mem0 →
      (∀ a, tok.tag a ≠ 5 → mem a = mem0 a) →
      SolverScheduleAt mem tok.levelsEnd model' →
      PathTreeNumericInv tok.tree tok.trees B R →
      OffTreeRecInv model L mem0 tok.edgeRecords B →
      (∀ a, Rrep.foot root tok a → a < heap) →
      ZeroFrom mem heap →
      heap + deepSpace < 2 ^ w →
      ∃ nextHeap cost out tok',
        Runs w p ω body (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
        heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
        tok'.levelsEnd = tok.levelsEnd ∧
        Rrep.rep root model' tok' out.mem ∧
        PathTreeNumericInv tok'.tree tok'.trees B R ∧
        OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
        ZeroFrom out.mem nextHeap ∧
        (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
        (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
        cost + Rrep.phi root tok' out.mem ≤ deepBudget + Rrep.phi root tok mem0

/-- Deterministic wired `ShiftLevel` entry procedure taking `[root, i, heap]` (`reg 0..2`) and
returning `nextHeap`. Updates the entire `SolverScheduleAt` block (`shiftCount`, `passes`,
`updCount`, `branD`) using `recordAcceptedShift`, `advanceShiftPasses`, `resetPassSuffix`, and
`shiftTerminalSchedule`, then dispatches to `shiftDeepChainProc` (`i < d`) or
`shiftTermChainProc` (`i = d`). -/
@[expose] def shiftLevelWiredBody (shiftTermChainProc shiftDeepChainProc : ℕ) : Stmt :=
  .assign 20 (.reg 0) ;;
  .assign 21 (.reg 1) ;;
  .assign 22 (.reg 2) ;;
  .assign 23 (.load (.reg 20)) ;;
  .assign 24 (.load (.bin .add (.reg 20) (.const 2))) ;;
  .assign 25 (.load (.bin .add (.reg 23) (.const 11))) ;;
  .assign 26 (.load (.bin .add (.reg 23) (.const 12))) ;;
  .assign 27 (.bin .add (.reg 25) (.const 1)) ;;
  .assign 0 (.bin .add (.reg 24) (.reg 27)) ;;
  .assign 1 (.reg 21) ;;
  recordAcceptedShift ;;
  .cond (.bin .lt (.reg 21) (.reg 25))
    (.assign 28 (.bin .add (.bin .add (.reg 23) (.const 18)) (.reg 27)) ;;
     .assign 29 (.load (.bin .add (.reg 28) (.reg 21))) ;;
     .assign 3 (.bin .eq (.bin .mod (.bin .add (.reg 29) (.const 1)) (.reg 26)) (.const 0)) ;;
     .assign 0 (.reg 24) ;;
     .assign 1 (.reg 21) ;;
     .assign 2 (.reg 27) ;;
     advanceShiftPasses ;;
     .store (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))) (.const 0) ;;
     .assign 0 (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 27))) ;;
     .assign 1 (.bin .add (.reg 21) (.const 1)) ;;
     .assign 2 (.reg 25) ;;
     resetPassSuffix ;;
     .call 30 shiftDeepChainProc [.reg 20, .reg 21, .reg 22] ;;
     .ret (.reg 30))
    (.assign 0 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))) ;;
     .assign 1 (.reg 26) ;;
     .assign 4 (.reg 24) ;;
     .assign 5 (.reg 25) ;;
     shiftTerminalSchedule ;;
     .call 30 shiftTermChainProc [.reg 20, .reg 22] ;;
     .ret (.reg 30))

theorem shiftLevelWiredBody_noRand (shiftTermChainProc shiftDeepChainProc : ℕ) :
    (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc).NoRand := by
  simp [shiftLevelWiredBody, recordAcceptedShift_noRand, advanceShiftPasses_noRand,
    resetPassSuffix_noRand, shiftTerminalSchedule_noRand, Stmt.NoRand]

/-- Single-call generic runner for `shiftLevelWiredBody`, parameterized by per-call
terminal/deep space and budget bounds and an extra postcondition `Q` on `(tok', out.mem)`.
Used by both `shiftLevelStepSpec_wired` (fixed budget) and `shiftLevelStepSpecW_wired`
(credit-bearing `ShiftTermChainSyncSpecW` / `ShiftDeepChainSyncSpecW`). -/
theorem shiftLevelWiredBody_runs_gen
    {w L P m V psi k epsExp drainUnit shiftTermChainProc shiftDeepChainProc
      termSpace termBudget deepSpace deepBudget : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    {root heap pos : ℕ} {i : Fin (cfg.P.d + 1)} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B R : ℤ}
    {Q : SolverToken cfg L Rcore → (ℕ → ℕ) → Prop}
    {bTerm bDeep : Stmt}
    (hbTerm : p.procs[shiftTermChainProc]? = some bTerm)
    (hbDeep : p.procs[shiftDeepChainProc]? = some bDeep)
    (hTermCall :
      let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
      let model' := alg2LoopShiftStep cfg model (Fin.last cfg.P.d)
      i = Fin.last cfg.P.d →
      ∀ (posIn : ℕ) (memIn : ℕ → ℕ),
        (∀ a, tok.tag a ≠ 5 → memIn a = mem a) →
        SolverScheduleAt memIn tok.levelsEnd model' →
        ZeroFrom memIn heap →
        heap + termSpace < 2 ^ w →
        ∃ nextHeap cost out tok',
          Runs w p ω bTerm (startState [root, heap] memIn posIn) (.returned nextHeap) out cost ∧
          heap ≤ nextHeap ∧ nextHeap ≤ heap + termSpace ∧
          tok'.levelsEnd = tok.levelsEnd ∧
          Rrep.rep root model' tok' out.mem ∧
          PathTreeNumericInv tok'.tree tok'.trees B R ∧
          OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
          ZeroFrom out.mem nextHeap ∧
          (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = memIn a) ∧
          (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
          cost + Rrep.phi root tok' out.mem ≤ termBudget + Rrep.phi root tok mem ∧
          Q tok' out.mem)
    (hDeepCall :
      let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
      let model' := alg2LoopShiftStep cfg model i
      i.val < cfg.P.d →
      ∀ (posIn : ℕ) (memIn : ℕ → ℕ),
        (∀ a, tok.tag a ≠ 5 → memIn a = mem a) →
        SolverScheduleAt memIn tok.levelsEnd model' →
        ZeroFrom memIn heap →
        heap + deepSpace < 2 ^ w →
        ∃ nextHeap cost out tok',
          Runs w p ω bDeep (startState [root, i.val, heap] memIn posIn) (.returned nextHeap) out cost ∧
          heap ≤ nextHeap ∧ nextHeap ≤ heap + deepSpace ∧
          tok'.levelsEnd = tok.levelsEnd ∧
          Rrep.rep root model' tok' out.mem ∧
          PathTreeNumericInv tok'.tree tok'.trees B R ∧
          OffTreeRecInv model' L out.mem tok'.edgeRecords B ∧
          ZeroFrom out.mem nextHeap ∧
          (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = memIn a) ∧
          (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
          cost + Rrep.phi root tok' out.mem ≤ deepBudget + Rrep.phi root tok mem ∧
          Q tok' out.mem)
    (_hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w)
    (hAcc : (model.chain.shiftCount i.val : ℝ) + 1 ≤
      gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val)
    (hBranchLt : (if i.val < cfg.P.d then model.chain.bran i.val else model.branD) < cfg.P.k)
    (hQuotaW : shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val < 2 ^ w)
    (hPassW : model.passes i + 1 < 2 ^ w)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hz : ZeroFrom mem heap)
    (hroom : heap + max termSpace deepSpace < 2 ^ w) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
    ∃ nextHeap cost out tok',
      Runs w p ω (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc)
        (startState [root, i.val, heap] mem pos) (.returned nextHeap) out cost ∧
      heap ≤ nextHeap ∧ nextHeap ≤ heap + max termSpace deepSpace ∧
      tok'.levelsEnd = tok.levelsEnd ∧
      Rrep.rep root (alg2LoopShiftStep cfg model i) tok' out.mem ∧
      PathTreeNumericInv tok'.tree tok'.trees B R ∧
      OffTreeRecInv (alg2LoopShiftStep cfg model i) L out.mem tok'.edgeRecords B ∧
      ZeroFrom out.mem nextHeap ∧
      (∀ a < heap, ¬ Rrep.foot root tok a → out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → Rrep.foot root tok a ∨ (heap ≤ a ∧ a < nextHeap)) ∧
      cost + Rrep.phi root tok' out.mem ≤
        (max termBudget deepBudget + 28 * (cfg.P.d + 1) + 220) + Rrep.phi root tok mem ∧
      Q tok' out.mem := by
  let Rrep := solverStateRep cfg L P m V psi k epsExp drainUnit Rcore
  have hrep0 := hrep
  obtain ⟨hrootDir, _, _, hchainP, _, _, _, _, hsched, _, _, _, _, _, hcores, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _, t4, t5, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hltH {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hrootW : root < 2 ^ w := lt_trans (hltH (t1 0 (by omega)) (by decide)) hheapW
  have hroot2W : root + 2 < 2 ^ w := lt_trans (hltH (t1 2 (by omega)) (by decide)) hheapW
  have hh11W : tok.handle + 11 < 2 ^ w := lt_trans (hltH (t2 11 (by omega)) (by decide)) hheapW
  have hh12W : tok.handle + 12 < 2 ^ w := lt_trans (hltH (t2 12 (by omega)) (by decide)) hheapW
  have hh17W : tok.handle + 18 < 2 ^ w :=
    lt_trans (hltH (t4 0 (by omega)) (by decide)) hheapW
  have hbrEndW : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d < 2 ^ w := by
    have hlt := hltH (t4 (2 * cfg.P.d + 1) (by omega)) (by decide)
    have heq : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
    rw [heq]; exact lt_trans hlt hheapW
  have hlvEndW : tok.levelsEnd + 4 * (cfg.P.d + 1) < 2 ^ w :=
    lt_trans (hltH (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide)) hheapW
  have h4d1W : 4 * (cfg.P.d + 1) < 2 ^ w := lt_of_le_of_lt (Nat.le_add_left _ _) hlvEndW
  have h3d1W : 3 * (cfg.P.d + 1) < 2 ^ w := by omega
  have hhandleEq : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hlevEq : mem (root + 2) = tok.levelsEnd := by simpa using hrootDir 2 (by simp)
  have hdEq : mem (tok.handle + 11) = cfg.P.d := by simpa [Nat.add_assoc] using hchainP 2 (by simp)
  have hkEq : mem (tok.handle + 12) = cfg.P.k := by simpa [Nat.add_assoc] using hchainP 3 (by simp)
  have hw1 : 1 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hw12 : 12 < 2 ^ w := by omega
  have hiLt : i.val < cfg.P.d + 1 := i.isLt
  have hiLe : i.val ≤ cfg.P.d := Nat.lt_succ_iff.mp hiLt
  -- Prefix: load parameters and run `recordAcceptedShift`
  let s0 := startState [root, i.val, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 20 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 21 i.val }
  let s3 : State := { s2 with regs := Function.update s2.regs 22 heap }
  let s4 : State := { s3 with regs := Function.update s3.regs 23 tok.handle }
  let s5 : State := { s4 with regs := Function.update s4.regs 24 tok.levelsEnd }
  let s6 : State := { s5 with regs := Function.update s5.regs 25 cfg.P.d }
  let s7 : State := { s6 with regs := Function.update s6.regs 26 cfg.P.k }
  let s8 : State := { s7 with regs := Function.update s7.regs 27 (cfg.P.d + 1) }
  let s9 : State := { s8 with regs := Function.update s8.regs 0 (tok.levelsEnd + (cfg.P.d + 1)) }
  let s10 : State := { s9 with regs := Function.update s9.regs 1 i.val }
  have r1 : Runs w p ω (.assign 20 (.reg 0)) s0 .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, s0, startState], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 21 (.reg 1)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 22 (.reg 2)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s2, s1, s0, startState], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 23 (.load (.reg 20))) s3 .normal s4 3 :=
    runs_assign_iff.mpr ⟨tok.handle, by simp [Expr.eval, s3, s2, s1, s0, startState, hhandleEq], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 24 (.load (.bin .add (.reg 20) (.const 2)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 2 < 2 ^ w by omega, hroot2W, hlevEq],
      rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 25 (.load (.bin .add (.reg 23) (.const 11)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨cfg.P.d, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, show 11 < 2 ^ w by omega, hh11W, hdEq],
      rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 26 (.load (.bin .add (.reg 23) (.const 12)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨cfg.P.k, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, hw12, hh12W, hkEq], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 27 (.bin .add (.reg 25) (.const 1))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨cfg.P.d + 1, by
      simp [Expr.eval, BinOp.eval, s7, s6, hw1, hdW], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.reg 27))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨tok.levelsEnd + (cfg.P.d + 1), by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, show tok.levelsEnd + (cfg.P.d + 1) < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 1 (.reg 21)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, s9, s8, s7, s6, s5, s4, s3, s2], rfl, rfl, rfl⟩
  have hpsiNN : 0 ≤ alg2PsiGame cfg.Ψ cfg.P.M₀ :=
    le_trans (by norm_num) (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀)
  have hshiftLtQuota : model.chain.shiftCount i.val <
      shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val :=
    (shiftQuotaWord_lt_iff cfg.P _ model.chain.rebuildCount i.val _ hpsiNN).mpr hAcc
  obtain ⟨s11, r11, hs11Mem, hs11Regs, _⟩ :=
    recordAcceptedShift_runs (w := w) (base := tok.levelsEnd + (cfg.P.d + 1)) (level := i.val)
      (count := model.chain.shiftCount i.val)
      (quota := shiftQuotaWord cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) model.chain.rebuildCount i.val)
      (p := p) (st := s10) (ω := ω)
      (by simp [s10, s9]) (by simp [s10])
      (by simp only [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState]; exact hsched.2.1 i.val hiLe)
      (by omega) hshiftLtQuota hQuotaW
  have hs11Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : s11.mem a = mem a := by
    rw [hs11Mem]
    have hne : a ≠ tok.levelsEnd + (cfg.P.d + 1) + i.val := by
      intro heq; apply hne5; rw [heq, Nat.add_assoc]; exact t5 (cfg.P.d + 1 + i.val) (by omega)
    rw [Function.update_of_ne hne]; rfl
  have hrChain {tail : Stmt} {res : Outcome} {endSt : State} {cTail : ℕ}
      (htail : Runs w p ω tail s11 res endSt cTail) :
      Runs w p ω
        (.assign 20 (.reg 0) ;; .assign 21 (.reg 1) ;; .assign 22 (.reg 2) ;;
         .assign 23 (.load (.reg 20)) ;; .assign 24 (.load (.bin .add (.reg 20) (.const 2))) ;;
         .assign 25 (.load (.bin .add (.reg 23) (.const 11))) ;;
         .assign 26 (.load (.bin .add (.reg 23) (.const 12))) ;;
         .assign 27 (.bin .add (.reg 25) (.const 1)) ;;
         .assign 0 (.bin .add (.reg 24) (.reg 27)) ;; .assign 1 (.reg 21) ;;
         recordAcceptedShift ;; tail)
        s0 res endSt (cTail + 55) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, cTail + 52, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, cTail + 49, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, cTail + 46, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 3, cTail + 42, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, cTail + 36, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, cTail + 30, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, cTail + 24, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, cTail + 19, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 4, cTail + 14, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, cTail + 11, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 10, cTail, r11, htail, by omega⟩), by omega⟩),
    by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  -- Helper lemmas for `s11.regs 20..27`
  have hs11_20 : s11.regs 20 = root := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1]
  have hs11_21 : s11.regs 21 = i.val := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3, s2]
  have hs11_22 : s11.regs 22 = heap := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4, s3]
  have hs11_23 : s11.regs 23 = tok.handle := by simp [hs11Regs, s10, s9, s8, s7, s6, s5, s4]
  have hs11_24 : s11.regs 24 = tok.levelsEnd := by simp [hs11Regs, s10, s9, s8, s7, s6, s5]
  have hs11_25 : s11.regs 25 = cfg.P.d := by simp [hs11Regs, s10, s9, s8, s7, s6]
  have hs11_26 : s11.regs 26 = cfg.P.k := by simp [hs11Regs, s10, s9, s8, s7]
  have hs11_27 : s11.regs 27 = cfg.P.d + 1 := by simp [hs11Regs, s10, s9, s8]
  -- Branch on `i.val < cfg.P.d` vs `i.val = cfg.P.d`
  by_cases hiD : i.val < cfg.P.d
  · -- Non-terminal branch (`i < cfg.P.d`)
    have hcond1 : (Expr.bin .lt (.reg 21) (.reg 25)).eval w s11 = some 1 := by
      simp [Expr.eval, BinOp.eval, hs11_21, hs11_25, hiD, hw1]
    have hcurB : model.chain.bran i.val < cfg.P.k := by
      simpa [hiD] using hBranchLt
    have hbrMem : s11.mem (tok.handle + 18 + (cfg.P.d + 1) + i.val) = model.chain.bran i.val := by
      have hne5 : tok.tag (tok.handle + 18 + (cfg.P.d + 1) + i.val) ≠ 5 := by
        have h4 := t4 (cfg.P.d + 1 + i.val) (by omega)
        rw [← Nat.add_assoc] at h4; rw [h4]; decide
      exact (hs11Tag _ hne5).trans (hcores i.val hiD).2.1
    let wrapped : Bool := decide ((model.chain.bran i.val + 1) % cfg.P.k = 0)
    let t1St : State := { s11 with regs := Function.update s11.regs 28 (tok.handle + 18 + (cfg.P.d + 1)) }
    let t2St : State := { t1St with regs := Function.update t1St.regs 29 (model.chain.bran i.val) }
    let t3St : State := { t2St with regs := Function.update t2St.regs 3 (if wrapped then 1 else 0) }
    let t4St : State := { t3St with regs := Function.update t3St.regs 0 tok.levelsEnd }
    let t5St : State := { t4St with regs := Function.update t4St.regs 1 i.val }
    let t6St : State := { t5St with regs := Function.update t5St.regs 2 (cfg.P.d + 1) }
    have rt1 : Runs w p ω (.assign 28 (.bin .add (.bin .add (.reg 23) (.const 18)) (.reg 27)))
        s11 .normal t1St 6 :=
      runs_assign_iff.mpr ⟨tok.handle + 18 + (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, hs11_23, hs11_27, show 18 < 2 ^ w by omega, hh17W,
          show tok.handle + 18 + (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt2 : Runs w p ω (.assign 29 (.load (.bin .add (.reg 28) (.reg 21))))
        t1St .normal t2St 5 :=
      runs_assign_iff.mpr ⟨model.chain.bran i.val, by
        simp [Expr.eval, BinOp.eval, t1St, hs11_21,
          show tok.handle + 18 + (cfg.P.d + 1) + i.val < 2 ^ w by omega, hbrMem], rfl, rfl, rfl⟩
    have hmodW : (model.chain.bran i.val + 1) % cfg.P.k < 2 ^ w :=
      lt_trans (Nat.mod_lt _ (by omega)) hkW
    have rt3 : Runs w p ω (.assign 3 (.bin .eq (.bin .mod (.bin .add (.reg 29) (.const 1)) (.reg 26)) (.const 0)))
        t2St .normal t3St 8 :=
      runs_assign_iff.mpr ⟨if wrapped then 1 else 0, by
        by_cases h0 : (model.chain.bran i.val + 1) % cfg.P.k = 0 <;>
          simp [Expr.eval, BinOp.eval, t2St, t1St, hs11_26, hw1,
            show model.chain.bran i.val + 1 < 2 ^ w by omega,
            hmodW, show 0 < 2 ^ w by omega, wrapped, h0], rfl, rfl, rfl⟩
    have rt4 : Runs w p ω (.assign 0 (.reg 24)) t3St .normal t4St 2 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd, by simp [Expr.eval, t3St, t2St, t1St, hs11_24], rfl, rfl, rfl⟩
    have rt5 : Runs w p ω (.assign 1 (.reg 21)) t4St .normal t5St 2 :=
      runs_assign_iff.mpr ⟨i.val, by simp [Expr.eval, t4St, t3St, t2St, t1St, hs11_21], rfl, rfl, rfl⟩
    have rt6 : Runs w p ω (.assign 2 (.reg 27)) t5St .normal t6St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d + 1, by simp [Expr.eval, t5St, t4St, t3St, t2St, t1St, hs11_27], rfl, rfl, rfl⟩
    have hpassTable6 : ∀ j : Fin (cfg.P.d + 1), t6St.mem (tok.levelsEnd + j.val) = model.passes j := by
      intro j
      change s11.mem (tok.levelsEnd + j.val) = model.passes j
      rw [hs11Mem, Function.update_of_ne (by have := j.isLt; omega)]
      exact hsched.1 j
    obtain ⟨t7St, cPass, rt7, hcPass, _, ht7Frame, ht7Passes⟩ :=
      advanceShiftPasses_table_runs (w := w) (base := tok.levelsEnd) (levels := cfg.P.d + 1) (p := p)
        (st := t6St) (ω := ω) i model.passes wrapped
        (by simp [t6St, t5St, t4St]) (by simp [t6St, t5St]) (by simp [t6St])
        (by simp [t6St, t5St, t4St, t3St]) hpassTable6 (by omega) hw1 (fun _ => hPassW)
    have ht7_reg (r : ℕ) (hr : 20 ≤ r) : t7St.regs r = t6St.regs r :=
      runs_preserves_above hr (by rfl) rt7
    let t8St : State := { t7St with mem := Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 }
    let t9St : State := { t8St with regs := Function.update t8St.regs 0 (tok.levelsEnd + 3 * (cfg.P.d + 1)) }
    let t10St : State := { t9St with regs := Function.update t9St.regs 1 (i.val + 1) }
    let t11St : State := { t10St with regs := Function.update t10St.regs 2 cfg.P.d }
    have rt8 : Runs w p ω (.store (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))) (.const 0))
        t7St .normal t8St 7 :=
      runs_store_iff.mpr ⟨tok.levelsEnd + 4 * (cfg.P.d + 1), 0, by
        simp [Expr.eval, BinOp.eval, ht7_reg 24 (by decide), ht7_reg 27 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_24, hs11_27, hw4, h4d1W, hlvEndW],
        by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt9 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.bin .mul (.const 3) (.reg 27))))
        t8St .normal t9St 6 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd + 3 * (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, t8St, ht7_reg 24 (by decide), ht7_reg 27 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_24, hs11_27, show 3 < 2 ^ w by omega,
          h3d1W, show tok.levelsEnd + 3 * (cfg.P.d + 1) < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rt10 : Runs w p ω (.assign 1 (.bin .add (.reg 21) (.const 1))) t9St .normal t10St 4 :=
      runs_assign_iff.mpr ⟨i.val + 1, by
        simp [Expr.eval, BinOp.eval, t9St, t8St, ht7_reg 21 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_21, hw1, show i.val + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have rt11 : Runs w p ω (.assign 2 (.reg 25)) t10St .normal t11St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d, by
        simp [Expr.eval, t10St, t9St, t8St, ht7_reg 25 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_25], rfl, rfl, rfl⟩
    obtain ⟨t12St, cUpd, rt12, hcUpd, ht12Mem, ht12Regs, _⟩ :=
      resetPassSuffix_runs (w := w) (base := tok.levelsEnd + 3 * (cfg.P.d + 1)) (first := i.val + 1)
        (stop := cfg.P.d) (p := p) (st := t11St) (ω := ω)
        (by simp [t11St, t10St, t9St]) (by simp [t11St, t10St]) (by simp [t11St])
        (by omega) (by omega) hw1
    -- Verify `t12St.mem` agrees with `mem` outside tag 5 and holds `SolverScheduleAt` for `model'`
    have ht12Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : t12St.mem a = mem a := by
      have hnot5 : ¬ (tok.levelsEnd ≤ a ∧ a < tok.levelsEnd + (4 * (cfg.P.d + 1) + 1)) := by
        intro hIn
        apply hne5
        have hsub : tok.levelsEnd + (a - tok.levelsEnd) = a := Nat.add_sub_of_le hIn.1
        rw [← hsub]; exact t5 (a - tok.levelsEnd) (by omega)
      rw [ht12Mem a, ite_eq_right (by omega)]
      change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 a = mem a
      rw [Function.update_of_ne (by omega)]
      rw [ht7Frame a (by omega)]
      exact hs11Tag a hne5
    have ht12Sched : SolverScheduleAt t12St.mem tok.levelsEnd (alg2LoopShiftStep cfg model i) := by
      refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · have hjLt : j.val < cfg.P.d + 1 := j.isLt
        rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 (tok.levelsEnd + j.val) = _
        rw [Function.update_of_ne (by omega), ht7Passes j]
        simp [alg2LoopShiftStep, hiD, wrapped]
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
        change s11.mem (tok.levelsEnd + (cfg.P.d + 1) + j) = _
        rw [hs11Mem, alg2LoopShiftStep, ordAlgorithm1_shift_shiftCount model.chain hiLe]
        by_cases hji : j = i.val
        · subst hji; simp
        · rw [Function.update_of_ne (by omega), ite_eq_right hji]; exact hsched.2.1 j hj
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
        change s11.mem (tok.levelsEnd + 2 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, ordAlgorithm1_shift_rebuildCount]
        exact hsched.2.2.1 j hj
      · rw [ht12Mem, alg2LoopShiftStep, ordAlgorithm1_shift_updCount_lt model.chain hiD]
        have hiff : (tok.levelsEnd + 3 * (cfg.P.d + 1) + (i.val + 1) ≤ tok.levelsEnd + 3 * (cfg.P.d + 1) + j ∧
            tok.levelsEnd + 3 * (cfg.P.d + 1) + j < tok.levelsEnd + 3 * (cfg.P.d + 1) + cfg.P.d) ↔
            (i.val + 1 ≤ j ∧ j < cfg.P.d) := by omega
        simp only [hiff]
        split_ifs with hIn
        · rfl
        · change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
          rw [Function.update_of_ne (by omega), ht7Frame _ (by omega)]
          change s11.mem (tok.levelsEnd + 3 * (cfg.P.d + 1) + j) = _
          rw [hs11Mem, Function.update_of_ne (by omega)]
          exact hsched.2.2.2.1 j hj
      · rw [ht12Mem, ite_eq_right (by omega)]
        change Function.update t7St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) 0 _ = _
        simp [alg2LoopShiftStep, hiD]
    have ht12Zero : ZeroFrom t12St.mem heap := fun a ha => by
      have hne5 : tok.tag a ≠ 5 := fun h5 => Nat.not_lt_of_ge ha (hltH h5 (by decide))
      exact (ht12Tag a hne5).trans (hz a ha)
    -- Call `shiftDeepChainProc [root, i.val, heap]`
    obtain ⟨nextHeap, cDeep, out, tok', hrDeep, hloD, hhiD, hlevD, hrepD, hnumD, hoffD,
        hzD, hfrD, hftD, hcD, hQD⟩ :=
      hDeepCall hiD t12St.pos t12St.mem ht12Tag ht12Sched ht12Zero (by omega)
    let t13St : State := { regs := Function.update t12St.regs 30 nextHeap, mem := out.mem, pos := out.pos }
    have rt13 : Runs w p ω (.call 30 shiftDeepChainProc [.reg 20, .reg 21, .reg 22])
        t12St .normal t13St (cDeep + 4) :=
      runs_call_iff.mpr ⟨[root, i.val, heap], bDeep, .returned nextHeap, out, cDeep, by
        simp [evalArgs, Expr.eval, ht12Regs 20 (by decide), ht12Regs 21 (by decide), ht12Regs 22 (by decide),
          t11St, t10St, t9St, t8St, ht7_reg 20 (by decide), ht7_reg 21 (by decide), ht7_reg 22 (by decide),
          t6St, t5St, t4St, t3St, t2St, t1St, hs11_20, hs11_21, hs11_22],
        hbDeep, hrDeep, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have rt14 : Runs w p ω (.ret (.reg 30)) t13St (.returned nextHeap) t13St 2 :=
      runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, t13St], rfl, rfl, rfl⟩
    have hrThen : Runs w p ω _ s11 (.returned nextHeap) t13St
        (6 + (5 + (8 + (2 + (2 + (2 + (cPass + (7 + (6 + (4 + (2 + (cUpd + ((cDeep + 4) + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨t1St, 6, _, rt1,
      runs_seq_iff.mpr (Or.inr ⟨t2St, 5, _, rt2,
      runs_seq_iff.mpr (Or.inr ⟨t3St, 8, _, rt3,
      runs_seq_iff.mpr (Or.inr ⟨t4St, 2, _, rt4,
      runs_seq_iff.mpr (Or.inr ⟨t5St, 2, _, rt5,
      runs_seq_iff.mpr (Or.inr ⟨t6St, 2, _, rt6,
      runs_seq_iff.mpr (Or.inr ⟨t7St, cPass, _, rt7,
      runs_seq_iff.mpr (Or.inr ⟨t8St, 7, _, rt8,
      runs_seq_iff.mpr (Or.inr ⟨t9St, 6, _, rt9,
      runs_seq_iff.mpr (Or.inr ⟨t10St, 4, _, rt10,
      runs_seq_iff.mpr (Or.inr ⟨t11St, 2, _, rt11,
      runs_seq_iff.mpr (Or.inr ⟨t12St, cUpd, _, rt12,
      runs_seq_iff.mpr (Or.inr ⟨t13St, cDeep + 4, 2, rt13, rt14, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextHeap, _, t13St, tok',
      hrChain (runs_cond_iff.mpr ⟨1, _, hcond1,
        by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]; exact hrThen, rfl⟩),
      hloD, le_trans hhiD (Nat.add_le_add_left (le_max_right _ _) _), hlevD, hrepD, hnumD, hoffD,
      hzD, fun a ha hnot => (hfrD a ha hnot).trans (ht12Tag a (fun h5 => hnot (Or.inl (hOwn a (h5 ▸ by decide))))),
      hftD, by dsimp only [t13St]; simp only [Expr.size]; have := le_max_right termBudget deepBudget; omega,
      hQD⟩
  · -- Terminal branch (`i = cfg.P.d`)
    have hiEqD : i = Fin.last cfg.P.d := Fin.ext (by simp only [Fin.val_last]; omega)
    have hcond0 : (Expr.bin .lt (.reg 21) (.reg 25)).eval w s11 = some 0 := by
      simp [Expr.eval, BinOp.eval, hs11_21, hs11_25, hiD, show 0 < 2 ^ w by omega]
    have hbranD_lt : model.branD < cfg.P.k := by
      simpa [hiD] using hBranchLt
    let e1St : State := { s11 with regs := Function.update s11.regs 0 (tok.levelsEnd + 4 * (cfg.P.d + 1)) }
    let e2St : State := { e1St with regs := Function.update e1St.regs 1 cfg.P.k }
    let e3St : State := { e2St with regs := Function.update e2St.regs 4 tok.levelsEnd }
    let e4St : State := { e3St with regs := Function.update e3St.regs 5 cfg.P.d }
    have re1 : Runs w p ω (.assign 0 (.bin .add (.reg 24) (.bin .mul (.const 4) (.reg 27))))
        s11 .normal e1St 6 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd + 4 * (cfg.P.d + 1), by
        simp [Expr.eval, BinOp.eval, hs11_24, hs11_27, hw4, h4d1W, hlvEndW], rfl, rfl, rfl⟩
    have re2 : Runs w p ω (.assign 1 (.reg 26)) e1St .normal e2St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.k, by simp [Expr.eval, e1St, hs11_26], rfl, rfl, rfl⟩
    have re3 : Runs w p ω (.assign 4 (.reg 24)) e2St .normal e3St 2 :=
      runs_assign_iff.mpr ⟨tok.levelsEnd, by simp [Expr.eval, e2St, e1St, hs11_24], rfl, rfl, rfl⟩
    have re4 : Runs w p ω (.assign 5 (.reg 25)) e3St .normal e4St 2 :=
      runs_assign_iff.mpr ⟨cfg.P.d, by simp [Expr.eval, e3St, e2St, e1St, hs11_25], rfl, rfl, rfl⟩
    have he4BranD : e4St.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) = model.branD := by
      change s11.mem (tok.levelsEnd + 4 * (cfg.P.d + 1)) = model.branD
      rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.2.2.2.2
    have he4Pass : e4St.mem (tok.levelsEnd + cfg.P.d) = model.passes (Fin.last cfg.P.d) := by
      change s11.mem (tok.levelsEnd + cfg.P.d) = model.passes (Fin.last cfg.P.d)
      rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.1 (Fin.last cfg.P.d)
    obtain ⟨e5St, cTermSched, re5, hcTermSched, _, he5Mem⟩ :=
      shiftTerminalSchedule_runs (w := w) (addr := tok.levelsEnd + 4 * (cfg.P.d + 1)) (branch := model.branD)
        (k := cfg.P.k) (base := tok.levelsEnd) (d := cfg.P.d) (count := model.passes (Fin.last cfg.P.d))
        (p := p) (st := e4St) (ω := ω)
        (by simp [e4St, e3St, e2St, e1St]) (by simp [e4St, e3St, e2St])
        he4BranD hbranD_lt hkW (by simp [e4St, e3St]) (by simp [e4St]) he4Pass
        (by omega) (by omega) (fun _ => hiEqD ▸ hPassW)
    have he5_reg (r : ℕ) (hr : 20 ≤ r) : e5St.regs r = e4St.regs r :=
      runs_preserves_above hr (by rfl) re5
    have he5Tag (a : ℕ) (hne5 : tok.tag a ≠ 5) : e5St.mem a = mem a := by
      have hnot5 : ¬ (tok.levelsEnd ≤ a ∧ a < tok.levelsEnd + (4 * (cfg.P.d + 1) + 1)) := by
        intro hIn
        apply hne5
        have hsub : tok.levelsEnd + (a - tok.levelsEnd) = a := Nat.add_sub_of_le hIn.1
        rw [← hsub]; exact t5 (a - tok.levelsEnd) (by omega)
      rw [he5Mem a, ite_eq_right (by omega)]
      rw [Function.update_of_ne (by omega)]
      exact hs11Tag a hne5
    have he5Sched : SolverScheduleAt e5St.mem tok.levelsEnd (alg2LoopShiftStep cfg model (Fin.last cfg.P.d)) := by
      refine ⟨fun j => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, ?_⟩
      · rw [he5Mem]
        have hneBr : tok.levelsEnd + j.val ≠ tok.levelsEnd + 4 * (cfg.P.d + 1) := by have := j.isLt; omega
        rw [Function.update_of_ne hneBr]
        have hjNotGt : ¬ Fin.last cfg.P.d < j := Fin.not_lt.mpr (Fin.le_last j)
        change _ = if Fin.last cfg.P.d < j then 0 else if j = Fin.last cfg.P.d then _ else model.passes j
        rw [ite_eq_right hjNotGt]
        by_cases hjd : j = Fin.last cfg.P.d
        · subst hjd
          simp only [Fin.val_last, true_and, ↓reduceIte, Nat.lt_irrefl]
          split_ifs with hw
          · rfl
          · exact he4Pass
        · have hneVal : j.val ≠ cfg.P.d := fun h => hjd (Fin.ext h)
          rw [ite_eq_right (by omega), ite_eq_right hjd]
          change s11.mem (tok.levelsEnd + j.val) = _
          rw [hs11Mem, Function.update_of_ne (by omega)]; exact hsched.1 j
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + (cfg.P.d + 1) + j) = _
        rw [hs11Mem, alg2LoopShiftStep, Fin.val_last, ordAlgorithm1_shift_shiftCount model.chain le_rfl]
        have hiValD : i.val = cfg.P.d := congrArg Fin.val hiEqD
        rw [hiValD]
        by_cases hjd : j = cfg.P.d
        · subst hjd; simp
        · rw [Function.update_of_ne (by omega), ite_eq_right hjd]; exact hsched.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + 2 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, ordAlgorithm1_shift_rebuildCount]
        exact hsched.2.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_of_ne (by omega)]
        change s11.mem (tok.levelsEnd + 3 * (cfg.P.d + 1) + j) = _
        rw [hs11Mem, Function.update_of_ne (by omega), alg2LoopShiftStep, Fin.val_last, ordAlgorithm1_shift_updCount_eq]
        exact hsched.2.2.2.1 j hj
      · rw [he5Mem, ite_eq_right (by omega), Function.update_self]
        simp [alg2LoopShiftStep]
    have he5Zero : ZeroFrom e5St.mem heap := fun a ha => by
      have hne5 : tok.tag a ≠ 5 := fun h5 => Nat.not_lt_of_ge ha (hltH h5 (by decide))
      exact (he5Tag a hne5).trans (hz a ha)
    obtain ⟨nextHeap, cTerm, out, tok', hrTerm, hloT, hhiT, hlevT, hrepT, hnumT, hoffT,
        hzT, hfrT, hftT, hcT, hQT⟩ :=
      hTermCall hiEqD e5St.pos e5St.mem he5Tag he5Sched he5Zero (by omega)
    let e6St : State := { regs := Function.update e5St.regs 30 nextHeap, mem := out.mem, pos := out.pos }
    have re6 : Runs w p ω (.call 30 shiftTermChainProc [.reg 20, .reg 22])
        e5St .normal e6St (cTerm + 3) :=
      runs_call_iff.mpr ⟨[root, heap], bTerm, .returned nextHeap, out, cTerm, by
        simp [evalArgs, Expr.eval, he5_reg 20 (by decide), he5_reg 22 (by decide),
          e4St, e3St, e2St, e1St, hs11_20, hs11_22],
        hbTerm, hrTerm, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
    have re7 : Runs w p ω (.ret (.reg 30)) e6St (.returned nextHeap) e6St 2 :=
      runs_ret_iff.mpr ⟨nextHeap, by simp [Expr.eval, e6St], rfl, rfl, rfl⟩
    have hrElse : Runs w p ω _ s11 (.returned nextHeap) e6St
        (6 + (2 + (2 + (2 + (cTermSched + ((cTerm + 3) + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨e1St, 6, _, re1,
      runs_seq_iff.mpr (Or.inr ⟨e2St, 2, _, re2,
      runs_seq_iff.mpr (Or.inr ⟨e3St, 2, _, re3,
      runs_seq_iff.mpr (Or.inr ⟨e4St, 2, _, re4,
      runs_seq_iff.mpr (Or.inr ⟨e5St, cTermSched, _, re5,
      runs_seq_iff.mpr (Or.inr ⟨e6St, cTerm + 3, 2, re6, re7, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨nextHeap, _, e6St, tok',
      hrChain (runs_cond_iff.mpr ⟨0, _, hcond0, by simp only [↓reduceIte]; exact hrElse, rfl⟩),
      hloT, le_trans hhiT (Nat.add_le_add_left (le_max_left _ _) _), hlevT,
      hiEqD.symm ▸ hrepT, hnumT, hiEqD.symm ▸ hoffT, hzT,
      fun a ha hnot => (hfrT a ha hnot).trans (he5Tag a (fun h5 => hnot (Or.inl (hOwn a (h5 ▸ by decide))))),
      hftT, by dsimp only [e6St]; simp only [Expr.size]; have := le_max_left termBudget deepBudget; omega,
      hQT⟩

/-- Discharges `ShiftLevelStepSpec` for `shiftLevelWiredBody` from `ShiftTermChainSyncSpec`,
`ShiftDeepChainSyncSpec`, and word-size bounds for the schedule counters. -/
theorem shiftLevelStepSpec_wired
    {w L P m V psi k epsExp drainUnit shiftLevelProc shiftTermChainProc shiftDeepChainProc
      termSpace termBudget deepSpace deepBudget : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)} {p : Program}
    (hAt : p.procs[shiftLevelProc]? = some (shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc))
    (hTerm : ShiftTermChainSyncSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftTermChainProc termSpace termBudget)
    (hDeep : ShiftDeepChainSyncSpec w L P m V psi k epsExp drainUnit cfg Rcore p
      shiftDeepChainProc deepSpace deepBudget)
    (hw17 : 17 < 2 ^ w)
    (hdW : cfg.P.d + 1 < 2 ^ w)
    (hkW : cfg.P.k < 2 ^ w) :
    ShiftLevelStepSpec w L P m V psi k epsExp drainUnit cfg Rcore p shiftLevelProc
      (max termSpace deepSpace)
      (max termBudget deepBudget + 28 * (cfg.P.d + 1) + 220) := by
  obtain ⟨bTerm, hbTerm, hTermRun⟩ := hTerm
  obtain ⟨bDeep, hbDeep, hDeepRun⟩ := hDeep
  refine ⟨shiftLevelWiredBody shiftTermChainProc shiftDeepChainProc, hAt, ?_⟩
  intro root heap pos i ω mem model tok B R hAcc hBranchLt hQuotaW hPassW hrep hnum hoff hbelow hz hroom
  obtain ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hrep', hnum', hoff', hz', hfr, hft, hc, _⟩ :=
    shiftLevelWiredBody_runs_gen (Q := fun _ _ => True) hbTerm hbDeep
      (fun _ posIn memIn htag hsched hzIn hrmIn => by
        obtain ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, hc⟩ :=
          hTermRun root heap posIn ω mem memIn model tok B R hrep htag hsched hnum hoff hbelow hzIn hrmIn
        exact ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, hc, trivial⟩)
      (fun hiD posIn memIn htag hsched hzIn hrmIn => by
        obtain ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, hc⟩ :=
          hDeepRun root heap posIn i ω mem memIn model tok B R hiD hrep htag hsched hnum hoff hbelow hzIn hrmIn
        exact ⟨nh, c, o, t', r, lo, hi, lv, rep, num, off, z', fr, ft, hc, trivial⟩)
      hw17 hdW hkW hAcc hBranchLt hQuotaW hPassW hrep hbelow hz hroom
  exact ⟨nh, c, out, tok', hr, hlo, hhi, hlev, hrep', hnum', hoff', hz', hfr, hft, hc⟩

end MinCostFlow.MinRatio
