module

public import MinCostFlow.Final.AssemblyDryRunSCSelBridge
public import MinCostFlow.Final.WireInitSelectSizes
public import MinCostFlow.MinRatio.SelectInitWired
public import MinCostFlow.MinRatio.WireSelectEvalKeyBridge
public import MinCostFlow.MinRatio.WireSelectHeapClear
public import MinCostFlow.MinRatio.SelectPhiFill
public import MinCostFlow.MinRatio.WireParamProg
public import MinCostFlow.Num.IPM.BitLength
public import MinCostFlow.DynSpanner.Program.DynGraphInit
public import MinCostFlow.DynSpanner.Program.DynGraphRefill
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Concrete `selInitCode` block for `dryLinkedProgramSel` (`AssemblyDryRunSCSelInitCode`)

Packages `solverInitWiredSelBody` (`MinRatio/SelectInitWiredCore.lean`) together with all of its
deterministic Word-RAM helpers (`dryPLastBody`, `drySlotBody`, `Num.IPM.bitLengthBody`,
`selectInitRegionBody`, `selectRegionSkeletonBody`, `selectHeapInitBody`, `selTableWriteBody`,
`selTableRowBody`, `dgCopyRefillBody`, `selCopyValuesBody`, `selectInitInteriorLoopBody`,
`selectFillInteriorLevelBody`, `selectFillLastLevelBody`, `selectInitFinalizeBody`,
`selCoreLenFillBody`, `selCoreLenEdgeBody`, `wireCoreLenEdgeBody`, `selFilterAbsentBody`,
`selEmbCopyBody`, `selectPhiLoopBody`, `selectRebuildSuffixBody`, `selectRebuildLevelBody`,
`selectProcessListBody`, `selectProcessEdgeBody`, `dgRefillModule`, `dgSplitProcs`, `dgBatchProcs`,
`selectHeapOpsModule`, `selectPhiFillModule`, and `evalKeyModule`) into a single relocatable
deterministic 96-procedure `SolverInnerSubCode` block `drySelInitCode`.

Provides:
* `dryPLastBody`, `dryPLast_meetsContract`: computes `dryLastStretchP J` from `[I.m]` in
  `14 * (I.m + 1).size + 40` steps.
* `drySlotBody`, `drySlot_meetsContract`: computes `drySlot I.m` from `[I.m, V, L, P]` in
  `14 * (M₀.size + (M₀.size + 1).size) + 60` steps.
* `dryPLastCost_add_drySlotCost_le_dryParamCost`: proves the combined cost of `dryPLastBody` and
  `drySlotBody` is at most `dryParamCost source J`.
* `drySelInitCode`: the relocatable 96-procedure deterministic `SolverInnerSubCode` (`off = 0`).
* `drySelInitCode_hasAll`: extracts every procedure entry and `HasAt` module placement of
  `drySelInitCode` inside `dryLinkedProgramSel`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 1. Concrete `pLast` and `slot` read-only procedures -/

/-- Computes `dryLastStretchP J = (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (m + 1).size`
from `[m]` using `bitLen` (`Num.IPM.bitLengthBody`). -/
def dryPLastBody (bitLen : ℕ) : Stmt :=
  .call 1 bitLen [.bin .add (.reg 0) (.const 1)] ;;
  .ret (.bin .add (.const (1024 * ⌈max 1 lastCanonConst⌉₊).size) (.bin .mul (.const 3) (.reg 1)))

theorem dryPLastBody_noRand (bitLen : ℕ) : (dryPLastBody bitLen).NoRand := by
  simp [dryPLastBody, Stmt.NoRand]

/-- Step-cost bound for `dryPLastBody` on input `m`. -/
def dryPLastCost (m : ℕ) : ℕ := 14 * (m + 1).size + 40

/-- Computes `drySlot m = 1 + 2 * 2 ^ (cappedQualityExponent threshold A m)` from `[m, V, L, P]`
using `bitLen` (`Num.IPM.bitLengthBody`). -/
def drySlotBody (bitLen threshold A : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 0) (.const threshold))
    (.assign 4 (.const threshold))
    (.assign 4 (.reg 0)) ;;
  .call 5 bitLen [.reg 4] ;;
  .call 6 bitLen [.bin .add (.reg 5) (.const 1)] ;;
  .assign 7 (.bin .div (.bin .add (.bin .mul (.const 47) (.reg 6)) (.const 47)) (.const 48)) ;;
  .assign 8 (.bin .shiftLeft (.const 1) (.reg 7)) ;;
  .assign 9 (.bin .mul (.bin .mul (.const (128 * (A + 1))) (.reg 6)) (.reg 8)) ;;
  .assign 10 (.bin .shiftLeft (.const 1) (.reg 9)) ;;
  .ret (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 10)))

theorem drySlotBody_noRand (bitLen threshold A : ℕ) : (drySlotBody bitLen threshold A).NoRand := by
  simp [drySlotBody, Stmt.NoRand]

/-- Step-cost bound for `drySlotBody` on input `M₀ = max m threshold`. -/
def drySlotCost (M₀ : ℕ) : ℕ := 14 * (M₀.size + (M₀.size + 1).size) + 60

/-! ## 2. Concrete 96-procedure deterministic `SolverInnerSubCode` block `drySelInitCode` -/

/-- Fixed length (`96`) of `drySelInitProcs`. -/
def drySelInitCodeLen : ℕ := 96

/-- Concrete relocatable 96-procedure block placed at `env.innerBase` implementing
`solverInitWiredSelBody` (at offset `0`) and all of its select-region initialization helpers,
reusing `solverCycleInit`, `env.scOp 2/3/4`, and `solverOpsProcs` arithmetic (`ops`, `ops + 11`,
`ops + 17`, `ops + 20`, `ops + 22`). -/
def drySelInitProcs (env : SolverInnerEnv) : List Stmt :=
  let b := env.innerBase
  let ops := env.opsBase
  let thr := concreteEdgeThresholdWithLast dryWitnessUsed
  let A := concreteQualityBudgetWithLast dryWitnessUsed
  [solverInitWiredSelBody solverCycleInit (env.scOp 3) (b + 25 + dgIdxInitEmpty) (b + 9)
      (b + 4) (b + 1) (b + 2),
   dryPLastBody (b + 3),
   drySlotBody (b + 3) thr A,
   Num.IPM.bitLengthBody (b + 3),
   selectInitRegionBody (b + 5) (b + 10) (b + 11) (b + 13) (b + 14),
   selectRegionSkeletonBody (b + 6) (b + 7) (b + 40 + dgIdxInitFromLists),
   selectHeapInitBody,
   selTableWriteBody (b + 8),
   selTableRowBody,
   dgCopyRefillBody (b + 36),
   selCopyValuesBody (b + 55),
   selectInitInteriorLoopBody (b + 11) (b + 12),
   selectFillInteriorLevelBody (env.scOp 2) (env.scOp 4) (b + 9) (b + 15) (b + 18) (b + 19),
   selectFillLastLevelBody (b + 9) (b + 15),
   selectInitFinalizeBody (b + 20) (b + 21),
   selCoreLenFillBody (b + 16),
   selCoreLenEdgeBody (ops + 20) (b + 17),
   wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops,
   selFilterAbsentBody,
   selEmbCopyBody (b + 55),
   selectPhiLoopBody (b + 20) (b + 81),
   selectRebuildSuffixBody (b + 21) (b + 22),
   selectRebuildLevelBody (b + 64) (b + 23),
   selectProcessListBody (b + 23) (b + 24),
   selectProcessEdgeBody (b + 82) (b + 61) (b + 63)] ++
  (dgRefillModule (b + 25) ++
  (dgSplitProcs (b + 25) (b + 37) ++
  (dgBatchProcs (b + 25) (b + 32) (b + 37) (b + 40) ++
  (selectHeapOpsModule (b + 43) 4 ++
  (selectPhiFillModule (b + 65) 4 ++
   evalKeyModule (b + 82) 4)))))

theorem drySelInitProcs_length (env : SolverInnerEnv) :
    (drySelInitProcs env).length = drySelInitCodeLen := by
  unfold drySelInitProcs drySelInitCodeLen
  simp only [List.length_append, List.length_cons, List.length_nil,
    dgRefillModule_length, dgSplitProcs_length, dgBatchProcs_length,
    selectHeapOpsModule_length, selectPhiFillModule_length, evalKeyModule_length]

theorem drySelInitProcs_noRand (env : SolverInnerEnv) :
    ∀ s ∈ drySelInitProcs env, s.NoRand := by
  intro s hs
  unfold drySelInitProcs at hs
  simp only [List.mem_append] at hs
  rcases hs with hHead | hDgRef | hDgSp | hDgBat | hHeap | hPhi | hEval
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hHead
    rcases hHead with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact solverInitWiredSelBody_noRand ..
    · exact dryPLastBody_noRand _
    · exact drySlotBody_noRand ..
    · exact Num.IPM.bitLengthModule_noRand _ _ (List.mem_singleton.mpr rfl)
    · exact selectInitRegionBody_noRand ..
    · exact selectRegionSkeletonBody_noRand ..
    · exact selectHeapInitBody_noRand
    · exact selTableWriteBody_noRand _
    · exact selTableRowBody_noRand
    · exact dgCopyRefillBody_noRand _
    · exact selCopyValuesBody_noRand _
    · exact selectInitInteriorLoopBody_noRand ..
    · exact selectFillInteriorLevelBody_noRand ..
    · exact selectFillLastLevelBody_noRand ..
    · exact selectInitFinalizeBody_noRand ..
    · exact selCoreLenFillBody_noRand _
    · exact selCoreLenEdgeBody_noRand ..
    · exact wireCoreLenEdgeBody_noRand ..
    · exact selFilterAbsentBody_noRand
    · exact selEmbCopyBody_noRand _
    · exact selectPhiLoopBody_noRand ..
    · exact selectRebuildSuffixBody_noRand ..
    · exact selectRebuildLevelBody_noRand ..
    · exact selectProcessListBody_noRand ..
    · exact selectProcessEdgeBody_noRand ..
  · exact dgRefillModule_noRand _ s hDgRef
  · exact dgSplitProcs_noRand _ _ s hDgSp
  · exact dgBatchProcs_noRand _ _ _ _ s hDgBat
  · exact selectHeapOpsModule_noRand _ _ s hHeap
  · exact selectPhiFillModule_noRand _ _ s hPhi
  · exact evalKeyModule_noRand _ _ s hEval

/-- Relocatable deterministic `SolverInnerSubCode` for select-aware solver initialization
(`solverInitWiredSelBody` at offset `0`). -/
def drySelInitCode : SolverInnerSubCode where
  procs := drySelInitProcs
  len := drySelInitCodeLen
  hlen := drySelInitProcs_length
  hnoRand := drySelInitProcs_noRand
  off := 0

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## 3. Execution bounds for `dryPLastBody` and `drySlotBody` -/

theorem dryPLastBody_runs {w bitLen pos : ℕ} {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (J : Circulation)
    (hbits : MeetsContract w p bitLen Num.IPM.bitLengthContract)
    (hw14 : 14 ≤ w)
    (hm1W : (solverConnectedAugmented J).m + 1 < 2 ^ w)
    (hpLastW : dryLastStretchP J < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (dryPLastBody bitLen)
        (startState [(solverConnectedAugmented J).m] mem pos)
        (.returned (dryLastStretchP J)) out cost ∧
      out.mem = mem ∧ cost ≤ dryPLastCost (solverConnectedAugmented J).m := by
  set m := (solverConnectedAugmented J).m
  have hw2 : 2 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 2 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hmW : m < 2 ^ w := by omega
  have h1W : 1 < 2 ^ w := by omega
  have h3W : 3 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 3 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hcW : (1024 * ⌈max 1 lastCanonConst⌉₊).size < 2 ^ w := by
    unfold dryLastStretchP at hpLastW; omega
  have hszW : (m + 1).size < 2 ^ w := by unfold dryLastStretchP at hpLastW; dsimp only [m]; omega
  have h3szW : 3 * (m + 1).size < 2 ^ w := by unfold dryLastStretchP at hpLastW; dsimp only [m]; omega
  have hRetW : (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (m + 1).size < 2 ^ w := hpLastW
  let s0 := startState [m] mem pos
  have ha1 : evalArgs w s0 [.bin .add (.reg 0) (.const 1)] = some [m + 1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, s0, startState, h1W, hm1W]
  obtain ⟨s1, c1, v1, r1, hp1, hs1_1, _, hc1⟩ :=
    runs_call_of_meetsContract (r := 1) hbits ha1 (by simp [hm1W]) ⟨m + 1, rfl⟩ ω
  dsimp only [Num.IPM.bitLengthContract, List.getD, List.getElem?_cons_zero, Option.getD_some]
    at hp1 hc1
  obtain ⟨hMem1, hRet1⟩ := hp1
  have hr2 : Runs w p ω
      (.ret (.bin .add (.const (1024 * ⌈max 1 lastCanonConst⌉₊).size) (.bin .mul (.const 3) (.reg 1))))
      s1 (.returned (dryLastStretchP J)) s1 6 :=
    runs_ret_iff.mpr ⟨dryLastStretchP J, by
      simp [Expr.eval, BinOp.eval, hs1_1, hRet1, h3W, hcW, h3szW, hRetW, dryLastStretchP, m],
      rfl, rfl, by simp [Expr.size]⟩
  refine ⟨s1, _, runs_seq_normal r1 hr2, hMem1, ?_⟩
  simp only [dryPLastCost, argsSize, Expr.size, m] at hc1 ⊢
  omega

theorem drySlotBody_runs {w bitLen V L P pos : ℕ} {p : Program} {mem : ℕ → ℕ} {ω : ℕ → Bool}
    (m : ℕ)
    (hbits : MeetsContract w p bitLen Num.IPM.bitLengthContract)
    (hw14 : 14 ≤ w)
    (hthrW : concreteEdgeThresholdWithLast dryWitnessUsed < 2 ^ w)
    (hM0W : max m (concreteEdgeThresholdWithLast dryWitnessUsed) < 2 ^ w)
    (hSlotW : drySlot m < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω
        (drySlotBody bitLen (concreteEdgeThresholdWithLast dryWitnessUsed)
          (concreteQualityBudgetWithLast dryWitnessUsed))
        (startState [m, V, L, P] mem pos) (.returned (drySlot m)) out cost ∧
      out.mem = mem ∧
      cost ≤ drySlotCost (max m (concreteEdgeThresholdWithLast dryWitnessUsed)) := by
  set thr := concreteEdgeThresholdWithLast dryWitnessUsed
  set A := concreteQualityBudgetWithLast dryWitnessUsed
  set M₀ := max m thr
  have hw14' : 2 ^ 14 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw14
  have h48W : 48 < 2 ^ w := by omega
  have hbPos : 0 < (M₀.size + 1).size := Nat.size_pos.mpr (by omega)
  let b := (M₀.size + 1).size
  let sh := (47 * b + 47) / 48
  let q := cappedQualityExponent thr A m
  have hqEq : q = 128 * (A + 1) * b * 2 ^ sh := by
    simp [q, cappedQualityExponent, chainEdgeCap, integerQualityExponent, b, sh, M₀]
  have hSlotEq : drySlot m = 1 + 2 * 2 ^ q := rfl
  have h2qW : 2 ^ q < 2 ^ w := by omega
  have hqW : q < 2 ^ w := lt_trans Nat.lt_two_pow_self h2qW
  have h2q2W : 2 * 2 ^ q < 2 ^ w := by omega
  have hpowPos : 1 ≤ 2 ^ sh := Nat.one_le_two_pow
  have h128bW : 128 * (A + 1) * b < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hpowPos) (hqEq ▸ hqW)
  have h128W : 128 * (A + 1) < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hbPos) h128bW
  have h47b47W : 47 * b + 47 < 2 ^ w := by
    have h1 : 128 * b ≤ 128 * (A + 1) * b :=
      Nat.mul_le_mul_right b (Nat.le_mul_of_pos_right 128 (Nat.succ_pos A))
    omega
  have h47bW : 47 * b < 2 ^ w := by omega
  have hshW : sh < 2 ^ w := lt_of_le_of_lt (Nat.div_le_self _ _) h47b47W
  have h2shW : 2 ^ sh < 2 ^ w := by
    have h1 : 1 ≤ 128 * (A + 1) * b := Nat.mul_pos (by omega) hbPos
    exact lt_of_le_of_lt (Nat.le_mul_of_pos_left _ h1) (hqEq ▸ hqW)
  have hM0sz1W : M₀.size + 1 < 2 ^ w := by
    have h1 : M₀.size ≤ w := Nat.size_le.mpr hM0W
    have h2 : w + 1 < 2 ^ w := by
      have := Nat.lt_two_pow_self (n := w - 1)
      have h3 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      have h4 : 2 ^ 1 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    omega
  have hbW : b < 2 ^ w := by
    have h1 : b ≤ M₀.size + 1 := Nat.size_le.mpr (Nat.lt_two_pow_self)
    omega
  let s0 := startState [m, V, L, P] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 4 M₀ }
  have r1 : Runs w p ω
      (.cond (.bin .lt (.reg 0) (.const thr)) (.assign 4 (.const thr)) (.assign 4 (.reg 0)))
      s0 .normal s1 6 := by
    by_cases hlt : m < thr
    · have hM0 : M₀ = thr := max_eq_right hlt.le
      refine runs_cond_iff.mpr ⟨1, 2,
        by simp [Expr.eval, BinOp.eval, s0, startState, hthrW, hlt, show 1 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨thr, by simp [Expr.eval, hthrW], rfl, by simp [s1, hM0], rfl⟩, rfl⟩
    · have hM0 : M₀ = m := max_eq_left (by omega)
      refine runs_cond_iff.mpr ⟨0, 2,
        by simp [Expr.eval, BinOp.eval, s0, startState, hthrW, hlt, show 0 < 2 ^ w by omega],
        runs_assign_iff.mpr ⟨m, by simp [Expr.eval, s0, startState], rfl, by simp [s1, hM0], rfl⟩,
        rfl⟩
  have ha2 : evalArgs w s1 [.reg 4] = some [M₀] := by simp [evalArgs, Expr.eval, s1]
  obtain ⟨s2, c2, v2, r2, hp2, hs2_5, _, hc2⟩ :=
    runs_call_of_meetsContract (r := 5) hbits ha2 (by simp [hM0W]) ⟨M₀, rfl⟩ ω
  dsimp only [Num.IPM.bitLengthContract, List.getD, List.getElem?_cons_zero, Option.getD_some]
    at hp2 hc2
  obtain ⟨hMem2, hRet2⟩ := hp2
  have ha3 : evalArgs w s2 [.bin .add (.reg 5) (.const 1)] = some [M₀.size + 1] := by
    simp [evalArgs, Expr.eval, BinOp.eval, hs2_5, hRet2, show 1 < 2 ^ w by omega, hM0sz1W]
  obtain ⟨s3, c3, v3, r3, hp3, hs3_6, _, hc3⟩ :=
    runs_call_of_meetsContract (r := 6) hbits ha3 (by simp [hM0sz1W]) ⟨M₀.size + 1, rfl⟩ ω
  dsimp only [Num.IPM.bitLengthContract, List.getD, List.getElem?_cons_zero, Option.getD_some]
    at hp3 hc3
  obtain ⟨hMem3, hRet3⟩ := hp3
  let s4 := { s3 with regs := Function.update s3.regs 7 sh }
  let s5 := { s4 with regs := Function.update s4.regs 8 (2 ^ sh) }
  let s6 := { s5 with regs := Function.update s5.regs 9 q }
  let s7 := { s6 with regs := Function.update s6.regs 10 (2 ^ q) }
  have r4 : Runs w p ω
      (.assign 7 (.bin .div (.bin .add (.bin .mul (.const 47) (.reg 6)) (.const 47)) (.const 48)))
      s3 .normal s4 8 :=
    runs_assign_iff.mpr ⟨sh, by
      simp [Expr.eval, BinOp.eval, hs3_6, hRet3, show 47 < 2 ^ w by omega, h48W, h47bW, h47b47W,
        hshW, sh, b],
      rfl, rfl, by simp [Expr.size]⟩
  have r5 : Runs w p ω (.assign 8 (.bin .shiftLeft (.const 1) (.reg 7))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨2 ^ sh, by
      simp [Expr.eval, BinOp.eval, s4, Nat.shiftLeft_eq, show 1 < 2 ^ w by omega, h2shW],
      rfl, rfl, by simp [Expr.size]⟩
  have hqProdW : 128 * (A + 1) * (M₀.size + 1).size * 2 ^ sh < 2 ^ w := hqEq ▸ hqW
  have r6 : Runs w p ω
      (.assign 9 (.bin .mul (.bin .mul (.const (128 * (A + 1))) (.reg 6)) (.reg 8)))
      s5 .normal s6 6 :=
    runs_assign_iff.mpr ⟨q, by
      simp [Expr.eval, BinOp.eval, s5, s4, hs3_6, hRet3, h128W, h128bW, hqProdW, hqEq, b],
      rfl, rfl, by simp [Expr.size]⟩
  have r7 : Runs w p ω (.assign 10 (.bin .shiftLeft (.const 1) (.reg 9))) s6 .normal s7 4 :=
    runs_assign_iff.mpr ⟨2 ^ q, by
      simp [Expr.eval, BinOp.eval, s6, Nat.shiftLeft_eq, show 1 < 2 ^ w by omega, h2qW],
      rfl, rfl, by simp [Expr.size]⟩
  have r8 : Runs w p ω (.ret (.bin .add (.const 1) (.bin .mul (.const 2) (.reg 10))))
      s7 (.returned (drySlot m)) s7 6 :=
    runs_ret_iff.mpr ⟨drySlot m, by
      simp [Expr.eval, BinOp.eval, s7, show 1 < 2 ^ w by omega, show 2 < 2 ^ w by omega,
        h2q2W, hSlotEq, show 1 + 2 * 2 ^ q < 2 ^ w by omega],
      rfl, rfl, by simp [Expr.size]⟩
  unfold drySlotBody
  refine ⟨s7, _,
    runs_seq_normal r1 (runs_seq_normal r2 (runs_seq_normal r3
      (runs_seq_normal r4 (runs_seq_normal r5 (runs_seq_normal r6 (runs_seq_normal r7 r8)))))),
    hMem3.trans hMem2, ?_⟩
  simp only [drySlotCost, argsSize, Expr.size] at hc2 hc3 ⊢
  omega

/-- The combined cost of `dryPLastBody` and `drySlotBody` fits inside `dryParamCost source J`. -/
theorem dryPLastCost_add_drySlotCost_le_dryParamCost (source J : Circulation) :
    let I := solverConnectedAugmented J
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    dryPLastCost I.m + drySlotCost cfg.P.M₀ ≤ dryParamCost source J := by
  intro I cfg
  have hmLe : I.m + 1 ≤ cfg.P.M₀ + 2 := by
    have : I.m ≤ cfg.P.M₀ := le_max_left _ _
    omega
  have hsz : (I.m + 1).size ≤ (cfg.P.M₀ + 2).size := Nat.size_le_size hmLe
  unfold dryPLastCost drySlotCost dryParamCost wireParamCost scalarParamsCost
  dsimp only [I, cfg] at hsz ⊢
  omega

/-! ## 4. Procedure placement inside `dryLinkedProgramSel` -/

private theorem hasAt_peel_selInit {p : Program} {b b' : ℕ} {xs ys : List Stmt}
    (h : p.HasAt b (xs ++ ys)) (hlen : b + xs.length = b') :
    p.HasAt b xs ∧ p.HasAt b' ys :=
  ⟨Num.hasAt_append_left h, hlen ▸ Num.hasAt_append_right h⟩

/-- Extracts every procedure entry and module placement of `drySelInitCode` inside
`dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode`. -/
theorem drySelInitCode_hasAll (Psc : DrySparseCorePieces) (inner : SolverInnerCode) :
    let p := dryLinkedProgramSel dryWitnessUsed Psc.sc inner drySelInitCode
    let env := drySelInitEnv (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) Psc.sc inner
    let b := env.innerBase
    let ops := mrdsCycleBase
    let lay := dryTailLay Psc.sc inner
    p.procs[b]? = some (solverInitWiredSelBody solverCycleInit (lay.scOp 3)
        (b + 25 + dgIdxInitEmpty) (b + 9) (b + 4) (b + 1) (b + 2)) ∧
    p.procs[b + 1]? = some (dryPLastBody (b + 3)) ∧
    p.procs[b + 2]? = some (drySlotBody (b + 3) (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed)) ∧
    p.HasAt (b + 3) (Num.IPM.bitLengthModule (b + 3)) ∧
    p.procs[b + 4]? = some (selectInitRegionBody (b + 5) (b + 10) (b + 11) (b + 13) (b + 14)) ∧
    p.procs[b + 5]? = some (selectRegionSkeletonBody (b + 6) (b + 7)
        (b + 40 + dgIdxInitFromLists)) ∧
    p.procs[b + 6]? = some selectHeapInitBody ∧
    p.procs[b + 7]? = some (selTableWriteBody (b + 8)) ∧
    p.procs[b + 8]? = some selTableRowBody ∧
    p.procs[b + 9]? = some (dgCopyRefillBody (b + 36)) ∧
    p.procs[b + 10]? = some (selCopyValuesBody (b + 55)) ∧
    p.procs[b + 11]? = some (selectInitInteriorLoopBody (b + 11) (b + 12)) ∧
    p.procs[b + 12]? = some (selectFillInteriorLevelBody (lay.scOp 2) (lay.scOp 4) (b + 9)
        (b + 15) (b + 18) (b + 19)) ∧
    p.procs[b + 13]? = some (selectFillLastLevelBody (b + 9) (b + 15)) ∧
    p.procs[b + 14]? = some (selectInitFinalizeBody (b + 20) (b + 21)) ∧
    p.procs[b + 15]? = some (selCoreLenFillBody (b + 16)) ∧
    p.procs[b + 16]? = some (selCoreLenEdgeBody (ops + 20) (b + 17)) ∧
    p.procs[b + 17]? = some (wireCoreLenEdgeBody (ops + 17) (ops + 11) (ops + 22) ops) ∧
    p.procs[b + 18]? = some selFilterAbsentBody ∧
    p.procs[b + 19]? = some (selEmbCopyBody (b + 55)) ∧
    p.procs[b + 20]? = some (selectPhiLoopBody (b + 20) (b + 81)) ∧
    p.procs[b + 21]? = some (selectRebuildSuffixBody (b + 21) (b + 22)) ∧
    p.procs[b + 22]? = some (selectRebuildLevelBody (b + 64) (b + 23)) ∧
    p.procs[b + 23]? = some (selectProcessListBody (b + 23) (b + 24)) ∧
    p.procs[b + 24]? = some (selectProcessEdgeBody (b + 82) (b + 61) (b + 63)) ∧
    p.HasAt (b + 25) (dgRefillModule (b + 25)) ∧
    p.HasAt (b + 25) dgOpsProcs ∧
    p.HasAt (b + 32) (dgEdgeProcs (b + 25)) ∧
    p.HasAt (b + 37) (dgSplitProcs (b + 25) (b + 37)) ∧
    p.HasAt (b + 40) (dgBatchProcs (b + 25) (b + 32) (b + 37) (b + 40)) ∧
    p.HasAt (b + 43) (selectHeapOpsModule (b + 43) 4) ∧
    p.HasAt (b + 65) (selectPhiFillModule (b + 65) 4) ∧
    p.HasAt (b + 82) (evalKeyModule (b + 82) 4) := by
  intro p env b ops lay
  have hAt := dryLinkedProgramSel_selInit_hasAt dryWitnessUsed Psc.sc inner drySelInitCode
  change p.HasAt b (drySelInitProcs env) at hAt
  unfold drySelInitProcs at hAt
  obtain ⟨hHead, r1⟩ := hasAt_peel_selInit (b' := b + 25) hAt (by simp)
  obtain ⟨hDgRef, r2⟩ := hasAt_peel_selInit (b' := b + 37) r1
    (by rw [dgRefillModule_length])
  obtain ⟨hDgSp, r3⟩ := hasAt_peel_selInit (b' := b + 40) r2
    (by rw [dgSplitProcs_length])
  obtain ⟨hDgBat, r4⟩ := hasAt_peel_selInit (b' := b + 43) r3
    (by rw [dgBatchProcs_length])
  obtain ⟨hHeap, r5⟩ := hasAt_peel_selInit (b' := b + 65) r4
    (by rw [selectHeapOpsModule_length])
  obtain ⟨hPhi, hEval⟩ := hasAt_peel_selInit (b' := b + 82) r5
    (by rw [selectPhiFillModule_length])
  have hDgOps : p.HasAt (b + 25) dgOpsProcs := by
    have h1 := hDgRef
    unfold dgRefillModule at h1
    exact Num.hasAt_append_left (Num.hasAt_append_left h1)
  have hDgEdge : p.HasAt (b + 32) (dgEdgeProcs (b + 25)) := by
    have h1 := hDgRef
    unfold dgRefillModule at h1
    have h12 := Num.hasAt_append_left h1
    have hE := Num.hasAt_append_right h12
    simpa only [dgOpsProcs_length, Nat.add_assoc] using hE
  have hBitAt : p.HasAt (b + 3) (Num.IPM.bitLengthModule (b + 3)) := by
    intro i hi
    have hi0 : i = 0 := by simp [Num.IPM.bitLengthModule] at hi; omega
    subst hi0
    simpa [Num.IPM.bitLengthModule] using hHead.get (i := 3) (by simp)
  have hScOp : ∀ j, env.scOp j = lay.scOp j := fun _ => rfl
  have hOpsEq : env.opsBase = ops := rfl
  refine ⟨?_, ?_, ?_, hBitAt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, hDgRef, hDgOps, hDgEdge, hDgSp, hDgBat, hHeap, hPhi, hEval⟩
  · simpa [hScOp, hOpsEq] using hHead.get (i := 0) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 1) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 2) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 4) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 5) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 6) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 7) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 8) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 9) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 10) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 11) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 12) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 13) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 14) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 15) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 16) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 17) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 18) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 19) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 20) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 21) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 22) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 23) (by simp)
  · simpa [hScOp, hOpsEq] using hHead.get (i := 24) (by simp)

end MinCostFlow.Final.DryRun

end
