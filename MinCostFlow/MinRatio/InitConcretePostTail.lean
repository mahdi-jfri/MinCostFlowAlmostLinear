module

public import MinCostFlow.MinRatio.InitTail
public import MinCostFlow.MinRatio.InitDetectThresholds
public import MinCostFlow.MinRatio.InitPathTreeChain
import MinCostFlow.MinRatio.ShiftForestScan

/-!
# Concrete post-tail initialization: Detect thresholds, path-tree edge insertion, and root directory

Runs immediately after `finishSolverInitBody` inside the concrete Init pipeline:
1. Reserves `slots`, `names`, `slotThresholds`, `edgeRecords`, `offReadyList`, `inOffReady`
   above `treeEnd`, and updates `DetectHeaderAt` (`handle + 1 := names`,
   `handle + 3 := slotThresholds`).
2. Runs `initDetectThresholdsAndRecords` to build `edgeThresholds[0..m)` and initial
   `PathEdgeAt` records `edgeRecords[0..m)`.
3. Runs `initLinkChainForests` to insert every edge of `chain.toTreeChain.chainTree` into
   the Section 6 link-cut path tree with exact `InitPathTreeInv`.
4. Writes the 16-word root directory `SolverRootDirAt` at `[root, root + 16)` where
   `root + 16 = alphaPtr` is the working heap base of `solverInitFullProgram`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Sixteen-word root directory written at the caller's initial heap address `root`,
giving `Update`, `Query`, and `Detect` constant-time access to all solver tables. -/
@[expose] def SolverRootDirAt (mem : ℕ → ℕ) (root handle table levelsEnd forward inverse
    freshCounter slots names slotThresholds edgeThresholds edgeRecords
    offReadyCount offReadyList inOffReady rootGraph intCap : ℕ) : Prop :=
  ListAt mem root [handle, table, levelsEnd, forward, inverse, freshCounter,
    slots, names, slotThresholds, edgeThresholds, edgeRecords,
    offReadyCount, offReadyList, inOffReady, rootGraph, intCap]

/-- `finishSolverInitBody` leaves every register `1 ≤ r ≤ 79` unchanged. -/
theorem finishSolverInitBody_preserves_regs {w treeInit r cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State}
    (hr1 : 1 ≤ r) (hr79 : r ≤ 79)
    (hrun : Runs w p ω (finishSolverInitBody treeInit) st .normal out cost) :
    out.regs r = st.regs r := by
  unfold finishSolverInitBody at hrun
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, hbad, _⟩ | ⟨s1, _, _, h1, r1, _⟩; · cases hbad
  rcases runs_seq_iff.mp r1 with ⟨_, _, _, hbad, _⟩ | ⟨s2, _, _, h2, r2, _⟩; · cases hbad
  rcases runs_seq_iff.mp r2 with ⟨_, _, _, hbad, _⟩ | ⟨s3, _, _, h3, r3, _⟩; · cases hbad
  rcases runs_seq_iff.mp r3 with ⟨_, _, _, hbad, _⟩ | ⟨s4, _, _, h4, r4, _⟩; · cases hbad
  rcases runs_seq_iff.mp r4 with ⟨_, _, _, hbad, _⟩ | ⟨s5, _, _, h5, r5, _⟩; · cases hbad
  rcases runs_seq_iff.mp r5 with ⟨_, _, _, hbad, _⟩ | ⟨s6, _, _, h6, r6, _⟩; · cases hbad
  rcases runs_seq_iff.mp r6 with ⟨_, _, _, hbad, _⟩ | ⟨s7, _, _, h7, r7, _⟩; · cases hbad
  rcases runs_seq_iff.mp r7 with ⟨_, _, _, hbad, _⟩ | ⟨s8, _, _, h8, r8, _⟩; · cases hbad
  rcases runs_seq_iff.mp r8 with ⟨_, _, _, hbad, _⟩ | ⟨s9, _, _, h9, r9, _⟩; · cases hbad
  rcases runs_seq_iff.mp r9 with ⟨_, _, _, hbad, _⟩ | ⟨s10, _, _, h10, h11, _⟩; · cases hbad
  have ha1 : s1.regs r = st.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h1; rw [hs]; simp [Function.update_of_ne (show r ≠ 84 by omega)]
  have ha2 : s2.regs r = s1.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h2; rw [hs]; simp [Function.update_of_ne (show r ≠ 92 by omega)]
  have ha3 : s3.regs r = s2.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h3; rw [hs]; simp [Function.update_of_ne (show r ≠ 85 by omega)]
  have ha4 : s4.regs r = s3.regs r := by
    obtain ⟨_, _, _, _, _, hs, _⟩ := runs_store_iff.mp h4; rw [hs]
  have ha5 : s5.regs r = s4.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h5; rw [hs]; simp [Function.update_of_ne (show r ≠ 81 by omega)]
  have ha6 : s6.regs r = s5.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h6; rw [hs]; simp [Function.update_of_ne (show r ≠ 82 by omega)]
  have ha7 : s7.regs r = s6.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h7; rw [hs]; simp [Function.update_of_ne (show r ≠ 83 by omega)]
  have ha8 : s8.regs r = s7.regs r := by
    obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp h8; rw [hs]; simp [Function.update_of_ne (show r ≠ 99 by omega)]
  have ha9 : s9.regs r = s8.regs r := by
    unfold initFreshIdentityTables at h9
    exact runs_preserves_above (bound := 1) hr1 (by rfl) h9
  have ha10 : s10.regs r = s9.regs r := by
    unfold initPathTreeAtHeap callInitPathTree at h10
    rcases runs_seq_iff.mp h10 with ⟨_, _, _, hbad, _⟩ | ⟨m1, _, _, hm1, hm2, _⟩; · cases hbad
    have hm1r : m1.regs r = s9.regs r := by
      obtain ⟨_, _, _, hs, _⟩ := runs_assign_iff.mp hm1; rw [hs]; simp [Function.update_of_ne (show r ≠ 80 by omega)]
    have hm2r : s10.regs r = m1.regs r := by
      obtain ⟨_, _, _, _, _, _, _, _, _, hs, _⟩ := runs_call_iff.mp hm2
      rw [hs]; simp [Function.update_of_ne (show r ≠ 99 by omega)]
    exact hm2r.trans hm1r
  have ha11 : out.regs r = s10.regs r := by
    unfold storeMinRatioDetectDescriptors at h11
    exact runs_preserves_above (bound := 0) (Nat.zero_le r) (by rfl) h11
  omega

/-- Stage 1 of the post-tail: reserve `slots`, `names`, `slotThresholds`, `edgeRecords`,
`offReadyList`, `inOffReady` at `treeEnd`, update `DetectHeaderAt`, and load `epsExp`. -/
@[expose] def initPostTailSetup : Stmt :=
  .assign 92 (.load (.bin .add (.reg 69) (.const 2))) ;;
  .assign 87 (.reg 99) ;;
  .assign 88 (.bin .add (.reg 87) (.reg 84)) ;;
  .assign 89 (.bin .add (.reg 88) (.bin .mul (.const 2) (.reg 92))) ;;
  .assign 86 (.bin .add (.reg 89) (.bin .mul (.const 2) (.reg 92))) ;;
  .assign 90 (.bin .add (.reg 86) (.reg 84)) ;;
  .assign 91 (.bin .add (.reg 90) (.reg 84)) ;;
  .assign 99 (.bin .add (.reg 91) (.reg 84)) ;;
  .store (.bin .add (.reg 74) (.const 1)) (.reg 88) ;;
  .store (.bin .add (.reg 74) (.const 3)) (.reg 89) ;;
  .assign 73 (.load (.bin .add (.reg 74) (.const 16)))

theorem initPostTailSetup_noRand : initPostTailSetup.NoRand := by
  simp [initPostTailSetup, Stmt.NoRand]

/-- Stage 2 setup parameterized by header size `hdr` and edge-capacity expression `ecExpr`:
move table pointers and `DynGraphAt` offsets into registers `0..34` for `initLinkChainForests`. -/
@[expose] def initPostTailLinkArgsGen (hdr : ℕ) (ecExpr : Expr) : Stmt :=
  .assign 0 (.reg 80) ;;
  .assign 3 (.reg 99) ;;
  .assign 11 (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 4) (.reg 92))) ;;
  .assign 9 (.bin .add (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 7) (.reg 92)))
    (.bin .mul (.const 3) ecExpr)) ;;
  .assign 10 (.bin .add (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 7) (.reg 92)))
    (.bin .mul (.const 4) ecExpr)) ;;
  .assign 19 (.reg 87) ;;
  .assign 20 (.reg 88) ;;
  .assign 22 (.reg 86) ;;
  .assign 23 (.reg 83) ;;
  .assign 24 (.reg 89) ;;
  .assign 29 (.bin .add (.reg 74) (.const hdr)) ;;
  .assign 30 (.bin .add (.reg 29) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 31 (.reg 75) ;;
  .assign 34 (.reg 69)

/-- Stage 2 setup: move table pointers and `DynGraphAt` offsets into registers `0..34`
for `initLinkChainForests` (17-word header, edge capacity in register `84`). -/
@[expose] def initPostTailLinkArgs : Stmt :=
  initPostTailLinkArgsGen 17 (.reg 84)

theorem initPostTailLinkArgs_noRand : initPostTailLinkArgs.NoRand := by
  simp [initPostTailLinkArgs, initPostTailLinkArgsGen, Stmt.NoRand]

/-- `initPostTailLinkArgs` with the level table at `handle + hdr`, reading `eCap` dynamically from
`mem[rootGraph + 1]` (`dgECapOff = 1`). The solver header has `hdr = 18` words. -/
@[expose] def initPostTailLinkArgsAt (hdr : ℕ) : Stmt :=
  initPostTailLinkArgsGen hdr (.load (.bin .add (.reg 69) (.const 1)))

theorem initPostTailLinkArgsAt_noRand (hdr : ℕ) : (initPostTailLinkArgsAt hdr).NoRand := by
  simp [initPostTailLinkArgsAt, initPostTailLinkArgsGen, Stmt.NoRand]

/-- Shared 16-store tail of `initPostTailStoreRootDir` and `initPostTailStoreRootDirMeta`. -/
@[expose] def initPostTailStoreRootDirBody : Stmt :=
  .store (.bin .add (.reg 1) (.const 0)) (.reg 74) ;;
  .store (.bin .add (.reg 1) (.const 1)) (.reg 2) ;;
  .store (.bin .add (.reg 1) (.const 2)) (.reg 4) ;;
  .store (.bin .add (.reg 1) (.const 3)) (.reg 81) ;;
  .store (.bin .add (.reg 1) (.const 4)) (.reg 82) ;;
  .store (.bin .add (.reg 1) (.const 5)) (.reg 85) ;;
  .store (.bin .add (.reg 1) (.const 6)) (.reg 87) ;;
  .store (.bin .add (.reg 1) (.const 7)) (.reg 88) ;;
  .store (.bin .add (.reg 1) (.const 8)) (.reg 89) ;;
  .store (.bin .add (.reg 1) (.const 9)) (.reg 83) ;;
  .store (.bin .add (.reg 1) (.const 10)) (.reg 86) ;;
  .store (.bin .add (.reg 1) (.const 11)) (.const 0) ;;
  .store (.bin .add (.reg 1) (.const 12)) (.reg 90) ;;
  .store (.bin .add (.reg 1) (.const 13)) (.reg 91) ;;
  .store (.bin .add (.reg 1) (.const 14)) (.reg 69) ;;
  .store (.bin .add (.reg 1) (.const 15)) (.reg 84)

/-- Stage 3: copy `finalHeap` to register `99` and populate the 16-word root directory
at `[root, root + 16)` where `root = mem (handle + 14) - 16`. -/
@[expose] def initPostTailStoreRootDir : Stmt :=
  .assign 99 (.reg 3) ;;
  .assign 1 (.bin .sub (.load (.bin .add (.reg 74) (.const 14))) (.const 16)) ;;
  .assign 2 (.bin .sub (.reg 74) (.bin .add (.reg 75) (.const 1))) ;;
  .assign 4 (.bin .sub (.reg 85) (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1))) ;;
  initPostTailStoreRootDirBody

theorem initPostTailStoreRootDir_noRand : initPostTailStoreRootDir.NoRand := by
  simp [initPostTailStoreRootDir, initPostTailStoreRootDirBody, Stmt.NoRand]

/-- Stage 3 variant when the level-metadata and select-pointer block (`N₀`, `lvlM[0..d)`,
`levelMeta[0..2*d)`, select heap base, select blocks base) sits between `table[0..d]` and `handle`,
so `handle = table + (4 * d + 4)`. -/
@[expose] def initPostTailStoreRootDirMeta : Stmt :=
  .assign 99 (.reg 3) ;;
  .assign 1 (.bin .sub (.load (.bin .add (.reg 74) (.const 14))) (.const 16)) ;;
  .assign 2 (.bin .sub (.reg 74) (.bin .add (.bin .mul (.const 4) (.reg 75)) (.const 4))) ;;
  .assign 4 (.bin .sub (.reg 85) (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1))) ;;
  initPostTailStoreRootDirBody

theorem initPostTailStoreRootDirMeta_noRand : initPostTailStoreRootDirMeta.NoRand := by
  simp [initPostTailStoreRootDirMeta, initPostTailStoreRootDirBody, Stmt.NoRand]

/-- Full concrete Init post-tail executed after `finishSolverInitBody`. -/
@[expose] def solverInitPostTailBody
    (shift divide negate copy readCore readGraph readLast linkOp bind : ℕ) : Stmt :=
  initPostTailSetup ;;
  initDetectThresholdsAndRecords shift divide negate copy ;;
  initPostTailLinkArgs ;;
  initLinkChainForests readCore readGraph readLast linkOp bind ;;
  initPostTailStoreRootDir

theorem solverInitPostTailBody_noRand
    (shift divide negate copy readCore readGraph readLast linkOp bind : ℕ) :
    (solverInitPostTailBody shift divide negate copy readCore readGraph readLast linkOp bind).NoRand := by
  simp [solverInitPostTailBody, initPostTailSetup_noRand, initDetectThresholdsAndRecords_noRand,
    initPostTailLinkArgs_noRand, initLinkChainForests_noRand, initPostTailStoreRootDir_noRand,
    Stmt.NoRand]

/-- `solverInitPostTailBody` with the level table at `handle + hdr` and the level-metadata block
between `table[0..d]` and `handle` (`handle = table + (4 * d + 2)`). -/
@[expose] def solverInitPostTailBodyAt (hdr : ℕ)
    (shift divide negate copy readCore readGraph readLast linkOp bind : ℕ) : Stmt :=
  initPostTailSetup ;;
  initDetectThresholdsAndRecords shift divide negate copy ;;
  initPostTailLinkArgsAt hdr ;;
  initLinkChainForests readCore readGraph readLast linkOp bind ;;
  initPostTailStoreRootDirMeta

theorem solverInitPostTailBodyAt_noRand (hdr : ℕ)
    (shift divide negate copy readCore readGraph readLast linkOp bind : ℕ) :
    (solverInitPostTailBodyAt hdr shift divide negate copy readCore readGraph readLast linkOp
      bind).NoRand := by
  simp [solverInitPostTailBodyAt, initPostTailSetup_noRand, initDetectThresholdsAndRecords_noRand,
    initPostTailLinkArgsAt_noRand, initLinkChainForests_noRand, initPostTailStoreRootDirMeta_noRand,
    Stmt.NoRand]

private theorem eval_assign_step {w r v : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {e : Expr}
    (he : e.eval w st = some v) :
    Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v } (e.size + 1) :=
  runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

private theorem eval_store_step {w a v : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {ea ev : Expr}
    (ha : ea.eval w st = some a) (hv : ev.eval w st = some v) :
    Runs w p ω (.store ea ev) st .normal { st with mem := Function.update st.mem a v } (ea.size + ev.size + 1) :=
  runs_store_iff.mpr ⟨a, v, ha, hv, rfl, rfl, rfl⟩

theorem initPostTailSetup_runs {w handle rootGraph m n treeEnd epsExp : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h69 : st.regs 69 = rootGraph) (h74 : st.regs 74 = handle)
    (h84 : st.regs 84 = m) (h99 : st.regs 99 = treeEnd)
    (hnCell : st.mem (rootGraph + 2) = n) (hepsCell : st.mem (handle + 16) = epsExp)
    (hrootW : rootGraph + 2 < 2 ^ w) (hhandleW : handle + 16 < 2 ^ w)
    (hroom : treeEnd + m + 2 * n + 2 * n + m + m + m < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    let slots := treeEnd
    let names := slots + m
    let slotThresholds := names + 2 * n
    let edgeRecords := slotThresholds + 2 * n
    let offReadyList := edgeRecords + m
    let inOffReady := offReadyList + m
    let threshHeap := inOffReady + m
    ∃ out cost, Runs w p ω initPostTailSetup st .normal out cost ∧
      out.regs 92 = n ∧ out.regs 87 = slots ∧ out.regs 88 = names ∧
      out.regs 89 = slotThresholds ∧ out.regs 86 = edgeRecords ∧
      out.regs 90 = offReadyList ∧ out.regs 91 = inOffReady ∧
      out.regs 99 = threshHeap ∧ out.regs 73 = epsExp ∧
      (∀ r, r ≠ 92 → r ≠ 87 → r ≠ 88 → r ≠ 89 → r ≠ 86 → r ≠ 90 → r ≠ 91 → r ≠ 99 → r ≠ 73 →
        out.regs r = st.regs r) ∧
      out.mem (handle + 1) = names ∧ out.mem (handle + 3) = slotThresholds ∧
      (∀ a, a ≠ handle + 1 → a ≠ handle + 3 → out.mem a = st.mem a) := by
  dsimp only
  let slots := treeEnd
  let names := slots + m
  let slotThresholds := names + 2 * n
  let edgeRecords := slotThresholds + 2 * n
  let offReadyList := edgeRecords + m
  let inOffReady := offReadyList + m
  let threshHeap := inOffReady + m
  let s1 := { st with regs := Function.update st.regs 92 n }
  let s2 := { s1 with regs := Function.update s1.regs 87 slots }
  let s3 := { s2 with regs := Function.update s2.regs 88 names }
  let s4 := { s3 with regs := Function.update s3.regs 89 slotThresholds }
  let s5 := { s4 with regs := Function.update s4.regs 86 edgeRecords }
  let s6 := { s5 with regs := Function.update s5.regs 90 offReadyList }
  let s7 := { s6 with regs := Function.update s6.regs 91 inOffReady }
  let s8 := { s7 with regs := Function.update s7.regs 99 threshHeap }
  let s9 := { s8 with mem := Function.update s8.mem (handle + 1) names }
  let s10 := { s9 with mem := Function.update s9.mem (handle + 3) slotThresholds }
  let s11 := { s10 with regs := Function.update s10.regs 73 epsExp }
  have hr1 : Runs w p ω (.assign 92 (.load (.bin .add (.reg 69) (.const 2)))) st .normal s1 _ :=
    eval_assign_step (by simp [Expr.eval, BinOp.eval, h69, hnCell, hrootW, show 2 < 2 ^ w by omega])
  have hr2 : Runs w p ω (.assign 87 (.reg 99)) s1 .normal s2 _ :=
    eval_assign_step (by simp [Expr.eval, s1, h99, slots])
  have hr3 : Runs w p ω (.assign 88 (.bin .add (.reg 87) (.reg 84))) s2 .normal s3 _ :=
    eval_assign_step (by simp [Expr.eval, BinOp.eval, s2, s1, h84, names, slots, show slots + m < 2 ^ w by omega])
  have hr4 : Runs w p ω (.assign 89 (.bin .add (.reg 88) (.bin .mul (.const 2) (.reg 92)))) s3 .normal s4 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, slotThresholds, names, slots,
        show 2 < 2 ^ w by omega, show 2 * n < 2 ^ w by omega, show names + 2 * n < 2 ^ w by omega])
  have hr5 : Runs w p ω (.assign 86 (.bin .add (.reg 89) (.bin .mul (.const 2) (.reg 92)))) s4 .normal s5 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, edgeRecords, slotThresholds, names, slots,
        show 2 < 2 ^ w by omega, show 2 * n < 2 ^ w by omega, show slotThresholds + 2 * n < 2 ^ w by omega])
  have hr6 : Runs w p ω (.assign 90 (.bin .add (.reg 86) (.reg 84))) s5 .normal s6 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, h84, offReadyList,
        show edgeRecords + m < 2 ^ w by omega])
  have hr7 : Runs w p ω (.assign 91 (.bin .add (.reg 90) (.reg 84))) s6 .normal s7 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, h84, inOffReady,
        show offReadyList + m < 2 ^ w by omega])
  have hr8 : Runs w p ω (.assign 99 (.bin .add (.reg 91) (.reg 84))) s7 .normal s8 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, h84, threshHeap,
        show inOffReady + m < 2 ^ w by omega])
  have hr9 : Runs w p ω (.store (.bin .add (.reg 74) (.const 1)) (.reg 88)) s8 .normal s9 _ :=
    eval_store_step
      (by simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, h74,
        show 1 < 2 ^ w by omega, show handle + 1 < 2 ^ w by omega])
      (by simp [Expr.eval, s8, s7, s6, s5, s4, s3])
  have hr10 : Runs w p ω (.store (.bin .add (.reg 74) (.const 3)) (.reg 89)) s9 .normal s10 _ :=
    eval_store_step
      (by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, h74,
        show 3 < 2 ^ w by omega, show handle + 3 < 2 ^ w by omega])
      (by simp [Expr.eval, s9, s8, s7, s6, s5, s4])
  have hr11 : Runs w p ω (.assign 73 (.load (.bin .add (.reg 74) (.const 16)))) s10 .normal s11 _ :=
    eval_assign_step (by
      simp only [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Function.update_of_ne (by decide : 74 ≠ 99), Function.update_of_ne (by decide : 74 ≠ 91),
        Function.update_of_ne (by decide : 74 ≠ 90), Function.update_of_ne (by decide : 74 ≠ 86),
        Function.update_of_ne (by decide : 74 ≠ 89), Function.update_of_ne (by decide : 74 ≠ 88),
        Function.update_of_ne (by decide : 74 ≠ 87), Function.update_of_ne (by decide : 74 ≠ 92),
        h74, show 16 < 2 ^ w by omega, ↓reduceIte, hhandleW, Option.map_some,
        Function.update_of_ne (show handle + 16 ≠ handle + 3 by omega),
        Function.update_of_ne (show handle + 16 ≠ handle + 1 by omega), hepsCell])
  refine ⟨s11, _,
    runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hr2,
        runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hr3,
          runs_seq_iff.mpr (Or.inr ⟨s4, _, _, hr4,
            runs_seq_iff.mpr (Or.inr ⟨s5, _, _, hr5,
              runs_seq_iff.mpr (Or.inr ⟨s6, _, _, hr6,
                runs_seq_iff.mpr (Or.inr ⟨s7, _, _, hr7,
                  runs_seq_iff.mpr (Or.inr ⟨s8, _, _, hr8,
                    runs_seq_iff.mpr (Or.inr ⟨s9, _, _, hr9,
                      runs_seq_iff.mpr (Or.inr ⟨s10, _, _, hr10, hr11, rfl⟩),
                      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1],
    by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, slots],
    by simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, names, slots],
    by simp [s11, s10, s9, s8, s7, s6, s5, s4, slotThresholds, names, slots],
    by simp [s11, s10, s9, s8, s7, s6, s5, edgeRecords, slotThresholds, names, slots],
    by simp [s11, s10, s9, s8, s7, s6, offReadyList, edgeRecords, slotThresholds, names, slots],
    by simp [s11, s10, s9, s8, s7, inOffReady, offReadyList, edgeRecords, slotThresholds, names, slots],
    by simp [s11, s10, s9, s8, threshHeap, inOffReady, offReadyList, edgeRecords, slotThresholds, names, slots],
    by simp [s11],
    fun r h92 h87 h88 h89 h86 h90 h91 h99 h73 => by
      simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Function.update_of_ne h73, Function.update_of_ne h99, Function.update_of_ne h91,
        Function.update_of_ne h90, Function.update_of_ne h86, Function.update_of_ne h89,
        Function.update_of_ne h88, Function.update_of_ne h87, Function.update_of_ne h92],
    by simp [s11, s10, s9, names, slots],
    by simp [s11, s10, slotThresholds, names, slots],
    fun a ha1 ha3 => by
      simp [s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne ha3, Function.update_of_ne ha1]⟩

private theorem initPostTailLinkArgsGen_runs {w hdr treeHeap afterThresh rootGraph n ec slots names
    edgeRecords edgeThresholds slotThresholds handle d : ℕ} {ecExpr : Expr}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h80 : st.regs 80 = treeHeap) (h99 : st.regs 99 = afterThresh)
    (h69 : st.regs 69 = rootGraph) (h92 : st.regs 92 = n)
    (hecEval : ∀ s : State, s.mem = st.mem → (∀ r, 36 ≤ r → s.regs r = st.regs r) →
      ecExpr.eval w s = some ec)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names) (h86 : st.regs 86 = edgeRecords)
    (h83 : st.regs 83 = edgeThresholds) (h89 : st.regs 89 = slotThresholds)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (hdgW : rootGraph + 4 + 7 * n + 4 * ec < 2 ^ w)
    (hbrW : handle + hdr + (d + 1) < 2 ^ w) (hw17 : 17 < 2 ^ w) (hwH : hdr < 2 ^ w) :
    ∃ out cost, Runs w p ω (initPostTailLinkArgsGen hdr ecExpr) st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 0 = treeHeap ∧ out.regs 3 = afterThresh ∧
      out.regs 9 = dgETailSlotBase rootGraph n ec ∧
      out.regs 10 = dgEHeadSlotBase rootGraph n ec ∧
      out.regs 11 = dgIntToExtBase rootGraph n ∧
      out.regs 19 = slots ∧ out.regs 20 = names ∧ out.regs 22 = edgeRecords ∧
      out.regs 23 = edgeThresholds ∧ out.regs 24 = slotThresholds ∧
      out.regs 29 = handle + hdr ∧ out.regs 30 = handle + hdr + (d + 1) ∧
      out.regs 31 = d ∧ out.regs 34 = rootGraph ∧
      (∀ r, 36 ≤ r → out.regs r = st.regs r) := by
  let s1 := { st with regs := Function.update st.regs 0 treeHeap }
  let s2 := { s1 with regs := Function.update s1.regs 3 afterThresh }
  let s3 := { s2 with regs := Function.update s2.regs 11 (dgIntToExtBase rootGraph n) }
  let s4 := { s3 with regs := Function.update s3.regs 9 (dgETailSlotBase rootGraph n ec) }
  let s5 := { s4 with regs := Function.update s4.regs 10 (dgEHeadSlotBase rootGraph n ec) }
  let s6 := { s5 with regs := Function.update s5.regs 19 slots }
  let s7 := { s6 with regs := Function.update s6.regs 20 names }
  let s8 := { s7 with regs := Function.update s7.regs 22 edgeRecords }
  let s9 := { s8 with regs := Function.update s8.regs 23 edgeThresholds }
  let s10 := { s9 with regs := Function.update s9.regs 24 slotThresholds }
  let s11 := { s10 with regs := Function.update s10.regs 29 (handle + hdr) }
  let s12 := { s11 with regs := Function.update s11.regs 30 (handle + hdr + (d + 1)) }
  let s13 := { s12 with regs := Function.update s12.regs 31 d }
  let s14 := { s13 with regs := Function.update s13.regs 34 rootGraph }
  have hr1 : Runs w p ω (.assign 0 (.reg 80)) st .normal s1 _ :=
    eval_assign_step (by simp [Expr.eval, h80])
  have hr2 : Runs w p ω (.assign 3 (.reg 99)) s1 .normal s2 _ :=
    eval_assign_step (by simp [Expr.eval, s1, h99])
  have hr3 : Runs w p ω (.assign 11 (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 4) (.reg 92)))) s2 .normal s3 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s2, s1, h69, h92, dgIntToExtBase,
        show 4 < 2 ^ w by omega, show rootGraph + 4 < 2 ^ w by omega,
        show 4 * n < 2 ^ w by omega, show rootGraph + 4 + 4 * n < 2 ^ w by omega])
  have hecS3 : ecExpr.eval w s3 = some ec :=
    hecEval s3 rfl (fun r hr => by simp [s3, s2, s1, Function.update_of_ne (show r ≠ 11 by omega),
      Function.update_of_ne (show r ≠ 3 by omega), Function.update_of_ne (show r ≠ 0 by omega)])
  have hecS4 : ecExpr.eval w s4 = some ec :=
    hecEval s4 rfl (fun r hr => by simp [s4, s3, s2, s1, Function.update_of_ne (show r ≠ 9 by omega),
      Function.update_of_ne (show r ≠ 11 by omega), Function.update_of_ne (show r ≠ 3 by omega),
      Function.update_of_ne (show r ≠ 0 by omega)])
  have hr4 : Runs w p ω (.assign 9 (.bin .add (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 7) (.reg 92)))
      (.bin .mul (.const 3) ecExpr))) s3 .normal s4 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, hecS3, s3, s2, s1, h69, h92, dgETailSlotBase,
        show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega, show 3 < 2 ^ w by omega,
        show rootGraph + 4 < 2 ^ w by omega, show 7 * n < 2 ^ w by omega,
        show rootGraph + 4 + 7 * n < 2 ^ w by omega, show 3 * ec < 2 ^ w by omega,
        show rootGraph + 4 + 7 * n + 3 * ec < 2 ^ w by omega])
  have hr5 : Runs w p ω (.assign 10 (.bin .add (.bin .add (.bin .add (.reg 69) (.const 4)) (.bin .mul (.const 7) (.reg 92)))
      (.bin .mul (.const 4) ecExpr))) s4 .normal s5 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, hecS4, s4, s3, s2, s1, h69, h92, dgEHeadSlotBase,
        show 4 < 2 ^ w by omega, show 7 < 2 ^ w by omega,
        show rootGraph + 4 < 2 ^ w by omega, show 7 * n < 2 ^ w by omega,
        show rootGraph + 4 + 7 * n < 2 ^ w by omega, show 4 * ec < 2 ^ w by omega, hdgW])
  have hr6 : Runs w p ω (.assign 19 (.reg 87)) s5 .normal s6 _ :=
    eval_assign_step (by simp [Expr.eval, s5, s4, s3, s2, s1, h87])
  have hr7 : Runs w p ω (.assign 20 (.reg 88)) s6 .normal s7 _ :=
    eval_assign_step (by simp [Expr.eval, s6, s5, s4, s3, s2, s1, h88])
  have hr8 : Runs w p ω (.assign 22 (.reg 86)) s7 .normal s8 _ :=
    eval_assign_step (by simp [Expr.eval, s7, s6, s5, s4, s3, s2, s1, h86])
  have hr9 : Runs w p ω (.assign 23 (.reg 83)) s8 .normal s9 _ :=
    eval_assign_step (by simp [Expr.eval, s8, s7, s6, s5, s4, s3, s2, s1, h83])
  have hr10 : Runs w p ω (.assign 24 (.reg 89)) s9 .normal s10 _ :=
    eval_assign_step (by simp [Expr.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, h89])
  have hr11 : Runs w p ω (.assign 29 (.bin .add (.reg 74) (.const hdr))) s10 .normal s11 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h74,
        hwH, show handle + hdr < 2 ^ w by omega])
  have hr12 : Runs w p ω (.assign 30 (.bin .add (.reg 29) (.bin .add (.reg 75) (.const 1)))) s11 .normal s12 _ :=
    eval_assign_step (by
      simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h75,
        show 1 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega, hbrW])
  have hr13 : Runs w p ω (.assign 31 (.reg 75)) s12 .normal s13 _ :=
    eval_assign_step (by simp [Expr.eval, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h75])
  have hr14 : Runs w p ω (.assign 34 (.reg 69)) s13 .normal s14 _ :=
    eval_assign_step (by simp [Expr.eval, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h69])
  refine ⟨s14, _,
    runs_seq_iff.mpr (Or.inr ⟨s1, _, _, hr1,
      runs_seq_iff.mpr (Or.inr ⟨s2, _, _, hr2,
        runs_seq_iff.mpr (Or.inr ⟨s3, _, _, hr3,
          runs_seq_iff.mpr (Or.inr ⟨s4, _, _, hr4,
            runs_seq_iff.mpr (Or.inr ⟨s5, _, _, hr5,
              runs_seq_iff.mpr (Or.inr ⟨s6, _, _, hr6,
                runs_seq_iff.mpr (Or.inr ⟨s7, _, _, hr7,
                  runs_seq_iff.mpr (Or.inr ⟨s8, _, _, hr8,
                    runs_seq_iff.mpr (Or.inr ⟨s9, _, _, hr9,
                      runs_seq_iff.mpr (Or.inr ⟨s10, _, _, hr10,
                        runs_seq_iff.mpr (Or.inr ⟨s11, _, _, hr11,
                          runs_seq_iff.mpr (Or.inr ⟨s12, _, _, hr12,
                            runs_seq_iff.mpr (Or.inr ⟨s13, _, _, hr13, hr14, rfl⟩),
                            rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
            rfl⟩), rfl⟩), rfl⟩),
    rfl,
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7, s6],
    by simp [s14, s13, s12, s11, s10, s9, s8, s7],
    by simp [s14, s13, s12, s11, s10, s9, s8],
    by simp [s14, s13, s12, s11, s10, s9],
    by simp [s14, s13, s12, s11, s10],
    by simp [s14, s13, s12, s11],
    by simp [s14, s13, s12],
    by simp [s14, s13],
    by simp [s14],
    fun r hr => by
      simp [s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Function.update_of_ne (show r ≠ 34 by omega), Function.update_of_ne (show r ≠ 31 by omega),
        Function.update_of_ne (show r ≠ 30 by omega), Function.update_of_ne (show r ≠ 29 by omega),
        Function.update_of_ne (show r ≠ 24 by omega), Function.update_of_ne (show r ≠ 23 by omega),
        Function.update_of_ne (show r ≠ 22 by omega), Function.update_of_ne (show r ≠ 20 by omega),
        Function.update_of_ne (show r ≠ 19 by omega), Function.update_of_ne (show r ≠ 10 by omega),
        Function.update_of_ne (show r ≠ 9 by omega), Function.update_of_ne (show r ≠ 11 by omega),
        Function.update_of_ne (show r ≠ 3 by omega), Function.update_of_ne (show r ≠ 0 by omega)]⟩

theorem initPostTailLinkArgsAt_runs {w hdr treeHeap afterThresh rootGraph n ec slots names
    edgeRecords edgeThresholds slotThresholds handle d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h80 : st.regs 80 = treeHeap) (h99 : st.regs 99 = afterThresh)
    (h69 : st.regs 69 = rootGraph) (h92 : st.regs 92 = n) (hecCell : st.mem (rootGraph + 1) = ec)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names) (h86 : st.regs 86 = edgeRecords)
    (h83 : st.regs 83 = edgeThresholds) (h89 : st.regs 89 = slotThresholds)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (hdgW : rootGraph + 4 + 7 * n + 4 * ec < 2 ^ w)
    (hbrW : handle + hdr + (d + 1) < 2 ^ w) (hw17 : 17 < 2 ^ w) (hwH : hdr < 2 ^ w) :
    ∃ out cost, Runs w p ω (initPostTailLinkArgsAt hdr) st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 0 = treeHeap ∧ out.regs 3 = afterThresh ∧
      out.regs 9 = dgETailSlotBase rootGraph n ec ∧
      out.regs 10 = dgEHeadSlotBase rootGraph n ec ∧
      out.regs 11 = dgIntToExtBase rootGraph n ∧
      out.regs 19 = slots ∧ out.regs 20 = names ∧ out.regs 22 = edgeRecords ∧
      out.regs 23 = edgeThresholds ∧ out.regs 24 = slotThresholds ∧
      out.regs 29 = handle + hdr ∧ out.regs 30 = handle + hdr + (d + 1) ∧
      out.regs 31 = d ∧ out.regs 34 = rootGraph ∧
      (∀ r, 36 ≤ r → out.regs r = st.regs r) :=
  initPostTailLinkArgsGen_runs h80 h99 h69 h92
    (fun s hsm hsr => by
      simp [Expr.eval, BinOp.eval, hsm, hsr 69 (by decide), h69, hecCell,
        show 1 < 2 ^ w by omega, show rootGraph + 1 < 2 ^ w by omega])
    h87 h88 h86 h83 h89 h74 h75 hdgW hbrW hw17 hwH

/-- The header-17 instance of `initPostTailLinkArgsGen_runs`. -/
theorem initPostTailLinkArgs_runs {w treeHeap afterThresh rootGraph n m slots names
    edgeRecords edgeThresholds slotThresholds handle d : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h80 : st.regs 80 = treeHeap) (h99 : st.regs 99 = afterThresh)
    (h69 : st.regs 69 = rootGraph) (h92 : st.regs 92 = n) (h84 : st.regs 84 = m)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names) (h86 : st.regs 86 = edgeRecords)
    (h83 : st.regs 83 = edgeThresholds) (h89 : st.regs 89 = slotThresholds)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (hdgW : rootGraph + 4 + 7 * n + 4 * m < 2 ^ w)
    (hbrW : handle + 17 + (d + 1) < 2 ^ w) (hw17 : 17 < 2 ^ w) :
    ∃ out cost, Runs w p ω initPostTailLinkArgs st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 0 = treeHeap ∧ out.regs 3 = afterThresh ∧
      out.regs 9 = dgETailSlotBase rootGraph n m ∧
      out.regs 10 = dgEHeadSlotBase rootGraph n m ∧
      out.regs 11 = dgIntToExtBase rootGraph n ∧
      out.regs 19 = slots ∧ out.regs 20 = names ∧ out.regs 22 = edgeRecords ∧
      out.regs 23 = edgeThresholds ∧ out.regs 24 = slotThresholds ∧
      out.regs 29 = handle + 17 ∧ out.regs 30 = handle + 17 + (d + 1) ∧
      out.regs 31 = d ∧ out.regs 34 = rootGraph ∧
      (∀ r, 36 ≤ r → out.regs r = st.regs r) :=
  initPostTailLinkArgsGen_runs (hdr := 17) h80 h99 h69 h92
    (fun s _ hsr => by simp [Expr.eval, hsr 84 (by decide), h84])
    h87 h88 h86 h83 h89 h74 h75 hdgW hbrW hw17 hw17

private theorem initPostTailStoreRootDirBody_runs {w root table levelsEnd handle forward inverse
    freshCounter slots names slotThresholds edgeThresholds edgeRecords offReadyList inOffReady
    rootGraph m finalHeap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h1 : st.regs 1 = root) (h2 : st.regs 2 = table) (h4 : st.regs 4 = levelsEnd)
    (h69 : st.regs 69 = rootGraph) (h74 : st.regs 74 = handle)
    (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m)
    (h85 : st.regs 85 = freshCounter) (h86 : st.regs 86 = edgeRecords)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names)
    (h89 : st.regs 89 = slotThresholds) (h90 : st.regs 90 = offReadyList)
    (h91 : st.regs 91 = inOffReady) (h99 : st.regs 99 = finalHeap)
    (hrootW : root + 16 < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    ∃ out cost, Runs w p ω initPostTailStoreRootDirBody st .normal out cost ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      (∀ a, a < root ∨ root + 16 ≤ a → out.mem a = st.mem a) := by
  have hstore (s : State) (off : ℕ) (ev : Expr) (v : ℕ) (ho : off < 16)
      (hr1s : s.regs 1 = root) (hev : ev.eval w s = some v) :
      Runs w p ω (.store (.bin .add (.reg 1) (.const off)) ev) s .normal
        { s with mem := Function.update s.mem (root + off) v } _ :=
    eval_store_step (by simp [Expr.eval, BinOp.eval, hr1s, show off < 2 ^ w by omega, show root + off < 2 ^ w by omega]) hev
  let m0 := { st with mem := Function.update st.mem (root + 0) handle }
  let m1 := { m0 with mem := Function.update m0.mem (root + 1) table }
  let m2 := { m1 with mem := Function.update m1.mem (root + 2) levelsEnd }
  let m3 := { m2 with mem := Function.update m2.mem (root + 3) forward }
  let m4 := { m3 with mem := Function.update m3.mem (root + 4) inverse }
  let m5 := { m4 with mem := Function.update m4.mem (root + 5) freshCounter }
  let m6 := { m5 with mem := Function.update m5.mem (root + 6) slots }
  let m7 := { m6 with mem := Function.update m6.mem (root + 7) names }
  let m8 := { m7 with mem := Function.update m7.mem (root + 8) slotThresholds }
  let m9 := { m8 with mem := Function.update m8.mem (root + 9) edgeThresholds }
  let m10 := { m9 with mem := Function.update m9.mem (root + 10) edgeRecords }
  let m11 := { m10 with mem := Function.update m10.mem (root + 11) 0 }
  let m12 := { m11 with mem := Function.update m11.mem (root + 12) offReadyList }
  let m13 := { m12 with mem := Function.update m12.mem (root + 13) inOffReady }
  let m14 := { m13 with mem := Function.update m13.mem (root + 14) rootGraph }
  let m15 := { m14 with mem := Function.update m14.mem (root + 15) m }
  have hs0 := hstore st 0 (.reg 74) handle (by decide) h1 (by simp [Expr.eval, h74])
  have hs1 := hstore m0 1 (.reg 2) table (by decide) h1 (by simp [Expr.eval, m0, h2])
  have hs2 := hstore m1 2 (.reg 4) levelsEnd (by decide) h1 (by simp [Expr.eval, m1, m0, h4])
  have hs3 := hstore m2 3 (.reg 81) forward (by decide) h1 (by simp [Expr.eval, m2, m1, m0, h81])
  have hs4 := hstore m3 4 (.reg 82) inverse (by decide) h1 (by simp [Expr.eval, m3, m2, m1, m0, h82])
  have hs5 := hstore m4 5 (.reg 85) freshCounter (by decide) h1 (by simp [Expr.eval, m4, m3, m2, m1, m0, h85])
  have hs6 := hstore m5 6 (.reg 87) slots (by decide) h1 (by simp [Expr.eval, m5, m4, m3, m2, m1, m0, h87])
  have hs7 := hstore m6 7 (.reg 88) names (by decide) h1 (by simp [Expr.eval, m6, m5, m4, m3, m2, m1, m0, h88])
  have hs8 := hstore m7 8 (.reg 89) slotThresholds (by decide) h1 (by simp [Expr.eval, m7, m6, m5, m4, m3, m2, m1, m0, h89])
  have hs9 := hstore m8 9 (.reg 83) edgeThresholds (by decide) h1 (by simp [Expr.eval, m8, m7, m6, m5, m4, m3, m2, m1, m0, h83])
  have hs10 := hstore m9 10 (.reg 86) edgeRecords (by decide) h1 (by simp [Expr.eval, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h86])
  have hs11 := hstore m10 11 (.const 0) 0 (by decide) h1 (by simp [Expr.eval, show 0 < 2 ^ w by omega])
  have hs12 := hstore m11 12 (.reg 90) offReadyList (by decide) h1 (by simp [Expr.eval, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h90])
  have hs13 := hstore m12 13 (.reg 91) inOffReady (by decide) h1 (by simp [Expr.eval, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h91])
  have hs14 := hstore m13 14 (.reg 69) rootGraph (by decide) h1 (by simp [Expr.eval, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h69])
  have hs15 := hstore m14 15 (.reg 84) m (by decide) h1 (by simp [Expr.eval, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h84])
  refine ⟨m15, _,
    runs_seq_iff.mpr (Or.inr ⟨m0, _, _, hs0,
      runs_seq_iff.mpr (Or.inr ⟨m1, _, _, hs1,
        runs_seq_iff.mpr (Or.inr ⟨m2, _, _, hs2,
          runs_seq_iff.mpr (Or.inr ⟨m3, _, _, hs3,
            runs_seq_iff.mpr (Or.inr ⟨m4, _, _, hs4,
              runs_seq_iff.mpr (Or.inr ⟨m5, _, _, hs5,
                runs_seq_iff.mpr (Or.inr ⟨m6, _, _, hs6,
                  runs_seq_iff.mpr (Or.inr ⟨m7, _, _, hs7,
                    runs_seq_iff.mpr (Or.inr ⟨m8, _, _, hs8,
                      runs_seq_iff.mpr (Or.inr ⟨m9, _, _, hs9,
                        runs_seq_iff.mpr (Or.inr ⟨m10, _, _, hs10,
                          runs_seq_iff.mpr (Or.inr ⟨m11, _, _, hs11,
                            runs_seq_iff.mpr (Or.inr ⟨m12, _, _, hs12,
                              runs_seq_iff.mpr (Or.inr ⟨m13, _, _, hs13,
                                runs_seq_iff.mpr (Or.inr ⟨m14, _, _, hs14, hs15, rfl⟩),
                                rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
                rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    by simp [m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0, h99],
    fun j hj => by
      have hj' : j < 16 := hj
      interval_cases j <;> simp [m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0],
    fun a ha => by
      simp only [m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1, m0]
      rw [Function.update_of_ne (show a ≠ root + 15 by omega),
        Function.update_of_ne (show a ≠ root + 14 by omega),
        Function.update_of_ne (show a ≠ root + 13 by omega),
        Function.update_of_ne (show a ≠ root + 12 by omega),
        Function.update_of_ne (show a ≠ root + 11 by omega),
        Function.update_of_ne (show a ≠ root + 10 by omega),
        Function.update_of_ne (show a ≠ root + 9 by omega),
        Function.update_of_ne (show a ≠ root + 8 by omega),
        Function.update_of_ne (show a ≠ root + 7 by omega),
        Function.update_of_ne (show a ≠ root + 6 by omega),
        Function.update_of_ne (show a ≠ root + 5 by omega),
        Function.update_of_ne (show a ≠ root + 4 by omega),
        Function.update_of_ne (show a ≠ root + 3 by omega),
        Function.update_of_ne (show a ≠ root + 2 by omega),
        Function.update_of_ne (show a ≠ root + 1 by omega),
        Function.update_of_ne (show a ≠ root + 0 by omega)]⟩

theorem initPostTailStoreRootDir_runs {w root table levelsEnd handle d forward inverse freshCounter
    slots names slotThresholds edgeThresholds edgeRecords offReadyList inOffReady rootGraph m finalHeap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h3 : st.regs 3 = finalHeap) (h69 : st.regs 69 = rootGraph)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m)
    (h85 : st.regs 85 = freshCounter) (h86 : st.regs 86 = edgeRecords)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names)
    (h89 : st.regs 89 = slotThresholds) (h90 : st.regs 90 = offReadyList)
    (h91 : st.regs 91 = inOffReady)
    (hhandleEq : handle = table + (d + 1))
    (hfreshEq : freshCounter = levelsEnd + (4 * (d + 1) + 1))
    (halphaCell : st.mem (handle + 14) = root + 16)
    (hrootW : root + 16 < 2 ^ w) (hhandleW : handle + 14 < 2 ^ w)
    (hfcW : freshCounter < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    ∃ out cost, Runs w p ω initPostTailStoreRootDir st .normal out cost ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      (∀ a, a < root ∨ root + 16 ≤ a → out.mem a = st.mem a) := by
  let a1 := { st with regs := Function.update st.regs 99 finalHeap }
  let a2 := { a1 with regs := Function.update a1.regs 1 root }
  let a3 := { a2 with regs := Function.update a2.regs 2 table }
  let a4 := { a3 with regs := Function.update a3.regs 4 levelsEnd }
  have hr1 : Runs w p ω (.assign 99 (.reg 3)) st .normal a1 _ :=
    eval_assign_step (by simp [Expr.eval, h3])
  have hr2 : Runs w p ω (.assign 1 (.bin .sub (.load (.bin .add (.reg 74) (.const 14))) (.const 16))) a1 .normal a2 _ :=
    eval_assign_step (by
      have : root + 16 - 16 = root := by omega
      simp [Expr.eval, BinOp.eval, a1, h74, halphaCell, show 14 < 2 ^ w by omega,
        hhandleW, hw16, this, show root < 2 ^ w by omega])
  have hr3 : Runs w p ω (.assign 2 (.bin .sub (.reg 74) (.bin .add (.reg 75) (.const 1)))) a2 .normal a3 _ :=
    eval_assign_step (by
      have : handle - (d + 1) = table := by omega
      simp [Expr.eval, BinOp.eval, a2, a1, h74, h75, show 1 < 2 ^ w by omega,
        show d + 1 < 2 ^ w by omega, this, show table < 2 ^ w by omega])
  have hr4 : Runs w p ω (.assign 4 (.bin .sub (.reg 85)
      (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1)))) a3 .normal a4 _ :=
    eval_assign_step (by
      have : freshCounter - (4 * (d + 1) + 1) = levelsEnd := by omega
      simp [Expr.eval, BinOp.eval, a3, a2, a1, h85, h75, show 1 < 2 ^ w by omega,
        show 4 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega,
        show 4 * (d + 1) < 2 ^ w by omega, show 4 * (d + 1) + 1 < 2 ^ w by omega,
        this, show levelsEnd < 2 ^ w by omega])
  obtain ⟨out, cB, hrB, hout99, hdir, hfr⟩ :=
    initPostTailStoreRootDirBody_runs (w := w) (root := root) (table := table)
      (levelsEnd := levelsEnd) (handle := handle) (forward := forward) (inverse := inverse)
      (freshCounter := freshCounter) (slots := slots) (names := names)
      (slotThresholds := slotThresholds) (edgeThresholds := edgeThresholds)
      (edgeRecords := edgeRecords) (offReadyList := offReadyList) (inOffReady := inOffReady)
      (rootGraph := rootGraph) (m := m) (finalHeap := finalHeap) (p := p) (ω := ω) (st := a4)
      (by simp [a4, a3, a2]) (by simp [a4, a3]) (by simp [a4])
      (by simp [a4, a3, a2, a1, h69]) (by simp [a4, a3, a2, a1, h74])
      (by simp [a4, a3, a2, a1, h81]) (by simp [a4, a3, a2, a1, h82])
      (by simp [a4, a3, a2, a1, h83]) (by simp [a4, a3, a2, a1, h84])
      (by simp [a4, a3, a2, a1, h85]) (by simp [a4, a3, a2, a1, h86])
      (by simp [a4, a3, a2, a1, h87]) (by simp [a4, a3, a2, a1, h88])
      (by simp [a4, a3, a2, a1, h89]) (by simp [a4, a3, a2, a1, h90])
      (by simp [a4, a3, a2, a1, h91]) (by simp [a4, a3, a2, a1]) hrootW hw16
  exact ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨a1, _, _, hr1, runs_seq_iff.mpr (Or.inr ⟨a2, _, _, hr2,
    runs_seq_iff.mpr (Or.inr ⟨a3, _, _, hr3, runs_seq_iff.mpr (Or.inr ⟨a4, _, _, hr4, hrB, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), hout99, hdir, hfr⟩

theorem initPostTailStoreRootDirMeta_runs {w root table levelsEnd handle d forward inverse freshCounter
    slots names slotThresholds edgeThresholds edgeRecords offReadyList inOffReady rootGraph m finalHeap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h3 : st.regs 3 = finalHeap) (h69 : st.regs 69 = rootGraph)
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse)
    (h83 : st.regs 83 = edgeThresholds) (h84 : st.regs 84 = m)
    (h85 : st.regs 85 = freshCounter) (h86 : st.regs 86 = edgeRecords)
    (h87 : st.regs 87 = slots) (h88 : st.regs 88 = names)
    (h89 : st.regs 89 = slotThresholds) (h90 : st.regs 90 = offReadyList)
    (h91 : st.regs 91 = inOffReady)
    (hhandleEq : handle = table + (4 * d + 4))
    (hfreshEq : freshCounter = levelsEnd + (4 * (d + 1) + 1))
    (halphaCell : st.mem (handle + 14) = root + 16)
    (hrootW : root + 16 < 2 ^ w) (hhandleW : handle + 14 < 2 ^ w)
    (hfcW : freshCounter < 2 ^ w) (hw16 : 16 < 2 ^ w) :
    ∃ out cost, Runs w p ω initPostTailStoreRootDirMeta st .normal out cost ∧
      out.regs 99 = finalHeap ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      (∀ a, a < root ∨ root + 16 ≤ a → out.mem a = st.mem a) := by
  let a1 := { st with regs := Function.update st.regs 99 finalHeap }
  let a2 := { a1 with regs := Function.update a1.regs 1 root }
  let a3 := { a2 with regs := Function.update a2.regs 2 table }
  let a4 := { a3 with regs := Function.update a3.regs 4 levelsEnd }
  have hr1 : Runs w p ω (.assign 99 (.reg 3)) st .normal a1 _ :=
    eval_assign_step (by simp [Expr.eval, h3])
  have hr2 : Runs w p ω (.assign 1 (.bin .sub (.load (.bin .add (.reg 74) (.const 14))) (.const 16))) a1 .normal a2 _ :=
    eval_assign_step (by
      have : root + 16 - 16 = root := by omega
      simp [Expr.eval, BinOp.eval, a1, h74, halphaCell, show 14 < 2 ^ w by omega,
        hhandleW, hw16, this, show root < 2 ^ w by omega])
  have hr3 : Runs w p ω (.assign 2 (.bin .sub (.reg 74) (.bin .add (.bin .mul (.const 4) (.reg 75)) (.const 4)))) a2 .normal a3 _ :=
    eval_assign_step (by
      have : handle - (4 * d + 4) = table := by omega
      simp [Expr.eval, BinOp.eval, a2, a1, h74, h75, show 4 < 2 ^ w by omega,
        show 4 * d < 2 ^ w by omega, show 4 * d + 4 < 2 ^ w by omega,
        this, show table < 2 ^ w by omega])
  have hr4 : Runs w p ω (.assign 4 (.bin .sub (.reg 85)
      (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1)))) a3 .normal a4 _ :=
    eval_assign_step (by
      have : freshCounter - (4 * (d + 1) + 1) = levelsEnd := by omega
      simp [Expr.eval, BinOp.eval, a3, a2, a1, h85, h75, show 1 < 2 ^ w by omega,
        show 4 < 2 ^ w by omega, show d + 1 < 2 ^ w by omega,
        show 4 * (d + 1) < 2 ^ w by omega, show 4 * (d + 1) + 1 < 2 ^ w by omega,
        this, show levelsEnd < 2 ^ w by omega])
  obtain ⟨out, cB, hrB, hout99, hdir, hfr⟩ :=
    initPostTailStoreRootDirBody_runs (w := w) (root := root) (table := table)
      (levelsEnd := levelsEnd) (handle := handle) (forward := forward) (inverse := inverse)
      (freshCounter := freshCounter) (slots := slots) (names := names)
      (slotThresholds := slotThresholds) (edgeThresholds := edgeThresholds)
      (edgeRecords := edgeRecords) (offReadyList := offReadyList) (inOffReady := inOffReady)
      (rootGraph := rootGraph) (m := m) (finalHeap := finalHeap) (p := p) (ω := ω) (st := a4)
      (by simp [a4, a3, a2]) (by simp [a4, a3]) (by simp [a4])
      (by simp [a4, a3, a2, a1, h69]) (by simp [a4, a3, a2, a1, h74])
      (by simp [a4, a3, a2, a1, h81]) (by simp [a4, a3, a2, a1, h82])
      (by simp [a4, a3, a2, a1, h83]) (by simp [a4, a3, a2, a1, h84])
      (by simp [a4, a3, a2, a1, h85]) (by simp [a4, a3, a2, a1, h86])
      (by simp [a4, a3, a2, a1, h87]) (by simp [a4, a3, a2, a1, h88])
      (by simp [a4, a3, a2, a1, h89]) (by simp [a4, a3, a2, a1, h90])
      (by simp [a4, a3, a2, a1, h91]) (by simp [a4, a3, a2, a1]) hrootW hw16
  exact ⟨out, _, runs_seq_iff.mpr (Or.inr ⟨a1, _, _, hr1, runs_seq_iff.mpr (Or.inr ⟨a2, _, _, hr2,
    runs_seq_iff.mpr (Or.inr ⟨a3, _, _, hr3, runs_seq_iff.mpr (Or.inr ⟨a4, _, _, hr4, hrB, rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), hout99, hdir, hfr⟩

end MinCostFlow.MinRatio
