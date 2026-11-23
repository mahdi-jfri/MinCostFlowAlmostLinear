module

public import MinCostFlow.MinRatio.WireChainCoreCollect
import WordRAM.Tactic

/-!
# Branch A (level-0 rebuild) chain execution (`WireChainCoreBranchA`)

Provides `wireCoreBranchAChainStmt` and `wireCoreBranchAChainStmt_runs` for the level-0 rebuild
branch of `ordChainUpdateCoreBody`:
1. Renames live edges of `G0'` to `0 .. G0'.m - 1` via `level0RenameBody` (using `cap = min rootECap intCap`).
2. Compacts `edgeThresholds`, `edgeRecords`, `newLen0`, `newRootGraph`, and `newLvlGraph0`, and
   zeroes `inOffReady` and `root + 11` via `wireCompactLevel0Body`.
3. Builds `OrdListAt` for `sortedEnds G0'.compact` via `buildSortedEndsBody`.
4. Increments `rebuildCount[0]` via `incrementLevelCounter`.
5. Rebuilds all chain levels `0 .. d` via `ordRebuildSuffixProgramKStore`, zeroes `updCount[0 .. d - 1]`
   via `wireZeroUpdCountLoop`, and collects new active forest headers into `newPtrs[0 .. d]` via
   `collectLSFForestsLoop` and `collectTermForestStmt`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Step 1–3 prefix of `wireCoreBranchAChainStmt`: rename, compact, and build `sortedEnds`. -/
@[expose] def wireBranchAPrefixStmt (renameProc compactProc sortedEndsProc : ℕ) : Stmt :=
  .assign 10 (.load (.bin .add (.reg 70) (.const 14))) ;;
  .assign 11 (.load (.reg 10)) ;;
  .assign 12 (.load (.bin .add (.reg 10) (.const 1))) ;;
  .assign 13 (.load (.bin .add (.reg 70) (.const 15))) ;;
  .cond (.bin .lt (.reg 12) (.reg 13))
    (.assign 24 (.reg 12))
    (.assign 24 (.reg 13)) ;;
  .assign 14 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 11))) ;;
  .assign 15 (.load (.bin .add (.reg 70) (.const 3))) ;;
  .assign 16 (.load (.bin .add (.reg 73) (.const 9))) ;;
  .assign 17 (.load (.bin .add (.reg 70) (.const 4))) ;;
  .assign 18 (.load (.bin .add (.reg 70) (.const 5))) ;;
  .call 25 renameProc [.reg 14, .reg 24, .reg 15, .reg 16, .reg 17, .reg 18, .reg 4] ;;
  .assign 26 (.bin .add (.reg 4) (.reg 24)) ;;
  .assign 4 (.bin .add (.reg 26) (.reg 24)) ;;
  .assign 27 (.load (.reg 83)) ;;
  .assign 28 (.reg 4) ;;
  .call 4 compactProc [.reg 70, .reg 27, .reg 26, .reg 25, .reg 4] ;;
  .assign 29 (.load (.bin .add (.reg 83) (.reg 75))) ;;
  .assign 30 (.reg 4) ;;
  .call 4 sortedEndsProc [.reg 29, .reg 4]

/-- Suffix of `wireCoreBranchAChainStmt` after `wireBranchAPrefixStmt`: increments
`rebuildCount[0]`, sets up suffix-rebuild registers, calls `ordRebuildSuffixProgramKStore (0..d)`,
zeroes `updCount[0..d-1]`, and collects `newPtrs[0..d]`. -/
@[expose] def wireBranchASuffixStmt
    (initCore readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  .assign 0 (.reg 86) ;;
  .assign 1 (.const 0) ;;
  incrementLevelCounter ;;
  .assign 1 (.reg 76) ;;
  .assign 6 (.reg 29) ;;
  .assign 7 (.reg 28) ;;
  .assign 8 (.reg 28) ;;
  .assign 9 (.reg 30) ;;
  .assign 20 (.const 0) ;;
  .assign 21 (.reg 75) ;;
  .assign 51 (.reg 77) ;;
  .assign 52 (.reg 78) ;;
  .assign 56 (.load (.bin .add (.reg 73) (.const 10))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 67 (.reg 94) ;;
  .assign 68 (.reg 95) ;;
  ordRebuildSuffixProgramKStore initCore readGraph readLSF coreLenProc readOrd lastInit ;;
  .assign 20 (.const 0) ;;
  wireZeroUpdCountLoop ;;
  (.assign 20 (.reg 71) ;;
   collectLSFForestsLoop readLSF 81 ;;
   collectTermForestStmt 81)

/-- Branch A chain rebuild statement: runs after `wireTreeSyncLoop (oldF → ∅)`,
`wireRefreshAccountsBody`, `dgApplyBatch` on `rootGraph`, and `wireUpdateLen0FromBatchBody`.
Expects `regs 70..95` populated by `updateCoreInitRegs`, `reg 4 = heap`, and `mem[root + 14]`
holding `G0'`, `mem[levelMeta]` holding `oldLen0`. -/
@[expose] def wireCoreBranchAChainStmt
    (renameProc compactProc sortedEndsProc initCore readGraph readLSF coreLenProc readOrd
      lastInit : ℕ) : Stmt :=
  wireBranchAPrefixStmt renameProc compactProc sortedEndsProc ;;
  wireBranchASuffixStmt initCore readGraph readLSF coreLenProc readOrd lastInit

theorem wireCoreBranchAChainStmt_noRand
    (renameProc compactProc sortedEndsProc initCore readGraph readLSF coreLenProc readOrd
      lastInit : ℕ) :
    (wireCoreBranchAChainStmt renameProc compactProc sortedEndsProc initCore readGraph readLSF
      coreLenProc readOrd lastInit).NoRand := by
  simp [wireCoreBranchAChainStmt, wireBranchAPrefixStmt, wireBranchASuffixStmt,
    incrementLevelCounter_noRand, ordRebuildSuffixProgramKStore_noRand,
    wireZeroUpdCountLoop_noRand, collectLSFForestsLoop_noRand, collectTermForestStmt_noRand,
    Stmt.NoRand]

theorem wireBranchAPrefix_runs
    {w L P m n rootECap oldLenECap intCap d root handle table levelsEnd forward inverse freshCounter
      slots names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      oldRootGraph oldLen0 heap0
      renameProc compactProc sortedEndsProc copyWords dgInit : ℕ}
    {G0' : MGraph} {oldℓ : ℕ → ℝ} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hRenProc : p.procs[renameProc]? = some level0RenameBody)
    (hCompProc : p.procs[compactProc]? = some (wireCompactLevel0Body copyWords dgInit))
    (hSortProc : p.procs[sortedEndsProc]? = some buildSortedEndsBody)
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hDGInit : ∀ vL eTriples, MeetsContract w p dgInit (dgInitFromListsContract w n rootECap G0'.compact vL eTriples))
    (h70 : st.regs 70 = root) (h73 : st.regs 73 = handle) (h75 : st.regs 75 = d)
    (h83 : st.regs 83 = solverLevelMetaAddr table d) (h4 : st.regs 4 = heap0)
    (hRoot : SolverRootDirAt st.mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady
      oldRootGraph intCap)
    (hH5 : st.mem (handle + 5) = L) (hH9 : st.mem (handle + 9) = m) (hH11 : st.mem (handle + 11) = d)
    (hLM0 : st.mem (solverLevelMetaAddr table d) = oldLen0)
    (hFresh : FreshTablesAt st.mem forward inverse freshCounter m intCap e2i i2e nf)
    (hDG : DynGraphAt st.mem oldRootGraph n rootECap G0')
    (hOldLen : EdgeValuesAt st.mem oldLen0 4 L P G0'.E oldℓ)
    (hCapE : ∀ e ∈ G0'.E, e < rootECap ∧ e < intCap)
    (hCapOldLen : ∀ e ∈ G0'.E, e < oldLenECap)
    (hdPos : 0 < d) (hw18 : 18 < 2 ^ w)
    (hBelow :
      let lm := solverLevelMetaAddr table d
      root + 16 ≤ heap0 ∧ handle + 18 ≤ heap0 ∧ lm + 2 * d ≤ heap0 ∧
      oldRootGraph + dynGraphSize n rootECap ≤ heap0 ∧ oldLen0 + oldLenECap * L ≤ heap0 ∧
      forward + m ≤ heap0 ∧ inverse + intCap ≤ heap0 ∧ freshCounter < heap0 ∧
      edgeThresholds + intCap ≤ heap0 ∧ edgeRecords + intCap ≤ heap0 ∧ inOffReady + intCap ≤ heap0)
    (hDisj :
      let lm := solverLevelMetaAddr table d
      (forward + m ≤ inverse ∨ inverse + intCap ≤ forward) ∧
      (freshCounter < forward ∨ forward + m ≤ freshCounter) ∧
      (freshCounter < inverse ∨ inverse + intCap ≤ freshCounter) ∧
      (root + 16 ≤ forward ∨ forward + m ≤ root) ∧
      (root + 16 ≤ inverse ∨ inverse + intCap ≤ root) ∧
      (root + 16 ≤ freshCounter ∨ freshCounter < root) ∧
      (handle + 18 ≤ forward ∨ forward + m ≤ handle) ∧
      (handle + 18 ≤ inverse ∨ inverse + intCap ≤ handle) ∧
      (handle + 18 ≤ freshCounter ∨ freshCounter < handle) ∧
      (lm + 2 * d ≤ forward ∨ forward + m ≤ lm) ∧
      (lm + 2 * d ≤ inverse ∨ inverse + intCap ≤ lm) ∧
      (lm + 2 * d ≤ freshCounter ∨ freshCounter < lm) ∧
      (oldRootGraph + dynGraphSize n rootECap ≤ forward ∨ forward + m ≤ oldRootGraph) ∧
      (oldRootGraph + dynGraphSize n rootECap ≤ inverse ∨ inverse + intCap ≤ oldRootGraph) ∧
      (oldRootGraph + dynGraphSize n rootECap ≤ freshCounter ∨ freshCounter < oldRootGraph) ∧
      (oldLen0 + oldLenECap * L ≤ forward ∨ forward + m ≤ oldLen0) ∧
      (oldLen0 + oldLenECap * L ≤ inverse ∨ inverse + intCap ≤ oldLen0) ∧
      (oldLen0 + oldLenECap * L ≤ freshCounter ∨ freshCounter < oldLen0) ∧
      (edgeThresholds + intCap ≤ forward ∨ forward + m ≤ edgeThresholds) ∧
      (edgeThresholds + intCap ≤ inverse ∨ inverse + intCap ≤ edgeThresholds) ∧
      (edgeThresholds + intCap ≤ freshCounter ∨ freshCounter < edgeThresholds) ∧
      (edgeRecords + intCap ≤ forward ∨ forward + m ≤ edgeRecords) ∧
      (edgeRecords + intCap ≤ inverse ∨ inverse + intCap ≤ edgeRecords) ∧
      (edgeRecords + intCap ≤ freshCounter ∨ freshCounter < edgeRecords) ∧
      (inOffReady + intCap ≤ forward ∨ forward + m ≤ inOffReady) ∧
      (inOffReady + intCap ≤ inverse ∨ inverse + intCap ≤ inOffReady) ∧
      (inOffReady + intCap ≤ freshCounter ∨ freshCounter < inOffReady) ∧
      (offReadyList + intCap ≤ forward ∨ forward + m ≤ offReadyList) ∧
      (offReadyList + intCap ≤ inverse ∨ inverse + intCap ≤ offReadyList) ∧
      (offReadyList + intCap ≤ freshCounter ∨ freshCounter < offReadyList) ∧
      (edgeThresholds + intCap ≤ edgeRecords ∨ edgeRecords + intCap ≤ edgeThresholds) ∧
      (edgeThresholds + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeThresholds) ∧
      (edgeRecords + intCap ≤ inOffReady ∨ inOffReady + intCap ≤ edgeRecords) ∧
      (root + 16 ≤ lm ∨ lm + 2 * d ≤ root) ∧
      (root + 16 ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ root) ∧
      (root + 16 ≤ edgeRecords ∨ edgeRecords + intCap ≤ root) ∧
      (root + 16 ≤ inOffReady ∨ inOffReady + intCap ≤ root) ∧
      (lm + 2 * d ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ lm) ∧
      (lm + 2 * d ≤ edgeRecords ∨ edgeRecords + intCap ≤ lm) ∧
      (lm + 2 * d ≤ inOffReady ∨ inOffReady + intCap ≤ lm) ∧
      (oldLen0 + oldLenECap * L ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ oldLen0) ∧
      (oldLen0 + oldLenECap * L ≤ edgeRecords ∨ edgeRecords + intCap ≤ oldLen0) ∧
      (oldRootGraph + dynGraphSize n rootECap ≤ edgeThresholds ∨ edgeThresholds + intCap ≤ oldRootGraph) ∧
      (oldRootGraph + dynGraphSize n rootECap ≤ edgeRecords ∨ edgeRecords + intCap ≤ oldRootGraph))
    (hz : ZeroFrom st.mem heap0)
    (hRoom : heap0 + 2 * intCap + wireCompactLevel0Space n rootECap L G0'.m + (1 + 4 * n + 2 * rootECap) < 2 ^ w) :
    let cap := min rootECap intCap
    let heap1 := heap0 + 2 * cap
    let newRootGraph := heap1 + rootECap * L + 3 * G0'.m
    let newLvlGraph0 := newRootGraph + dynGraphSize n rootECap
    let heap2 := heap1 + wireCompactLevel0Space n rootECap L G0'.m
    let heap3 := heap2 + 1 + 4 * n + 2 * rootECap
    let ordW := 1 + 2 * n + 2 * G0'.compact.m
    ∃ out c,
      Runs w p ω (wireBranchAPrefixStmt renameProc compactProc sortedEndsProc) st .normal out c ∧
      c ≤ (70 * intCap + 40 * m + 80) + wireCompactLevel0Cost n rootECap intCap L G0'.m +
        (150 * rootECap + 60 * n + 120) + 150 ∧
      out.regs 4 = heap3 ∧ out.regs 28 = heap1 ∧ out.regs 29 = newLvlGraph0 ∧ out.regs 30 = heap2 ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      FreshTablesAt out.mem forward inverse freshCounter m intCap
        (level0E2I true G0' e2i) (level0I2E true G0' i2e) (level0NF true G0' nf) ∧
      (∀ j < G0'.m, out.mem (edgeThresholds + j) = st.mem (edgeThresholds + compactUnrank G0'.E j) ∧
        out.mem (edgeRecords + j) = st.mem (edgeRecords + compactUnrank G0'.E j)) ∧
      EdgeValuesAt out.mem heap1 4 L P G0'.compact.E (fun j => oldℓ (compactUnrank G0'.E j)) ∧
      DynGraphAt out.mem newRootGraph n rootECap G0'.compact ∧
      DynGraphAt out.mem newLvlGraph0 n rootECap G0'.compact ∧
      OrdListAt out.mem heap2 (sortedEnds G0'.compact) ordW ∧
      (∀ t < ordW, out.mem (heap2 + t) < 2 ^ w) ∧
      heap2 + ordW ≤ heap3 ∧
      out.mem (root + 14) = newRootGraph ∧ out.mem (root + 11) = 0 ∧
      out.mem (solverLevelMetaAddr table d) = heap1 ∧ out.mem (solverLevelMetaAddr table d + d) = newLvlGraph0 ∧
      (∀ e < intCap, out.mem (inOffReady + e) = 0) ∧
      OffReadyInv out.mem 0 offReadyList inOffReady intCap ∧
      ZeroFrom out.mem heap3 ∧
      ∀ a < heap0,
        ¬ (forward ≤ a ∧ a < forward + m) → ¬ (inverse ≤ a ∧ a < inverse + intCap) → a ≠ freshCounter →
        ¬ InCompactMutable root table d edgeThresholds edgeRecords offReadyList inOffReady intCap a →
        out.mem a = st.mem a := by
  dsimp only
  set lm := solverLevelMetaAddr table d
  set cap := min rootECap intCap
  set heap1 := heap0 + 2 * cap
  set newRootGraph := heap1 + rootECap * L + 3 * G0'.m
  set newLvlGraph0 := newRootGraph + dynGraphSize n rootECap
  set heap2 := heap1 + wireCompactLevel0Space n rootECap L G0'.m
  set heap3 := heap2 + 1 + 4 * n + 2 * rootECap
  have hCapLeR : cap ≤ rootECap := Nat.min_le_left _ _
  have hCapLeI : cap ≤ intCap := Nat.min_le_right _ _
  have hw1 : 1 < 2 ^ w := by omega
  have hw7 : 7 < 2 ^ w := by omega
  have hDgDef : dynGraphSize n rootECap = 4 + 7 * n + 9 * rootECap := rfl
  have hGmLeC : G0'.m ≤ cap := by
    have := Finset.card_le_card (fun e he => Finset.mem_range.mpr (Nat.lt_min.mpr (hCapE e he)))
    rw [Finset.card_range] at this
    exact this
  have hNotFIC (a : ℕ) (h1 : forward + m ≤ a ∨ a < forward) (h2 : inverse + intCap ≤ a ∨ a < inverse)
      (h3 : a ≠ freshCounter) :
      ¬ (forward ≤ a ∧ a < forward + m) ∧ ¬ (inverse ≤ a ∧ a < inverse + intCap) ∧ a ≠ freshCounter :=
    ⟨by omega, by omega, h3⟩
  rcases hDisj with ⟨hFI, hCF, hCI,
    hRF, hRI, hRC,
    hHF, hHI, hHC,
    hLF, hLI, hLC,
    hGF, hGI, hGC,
    hOF, hOI, hOC,
    hETF, hETI, hETC,
    hERF, hERI, hERC,
    hIOF, hIOI, hIOC,
    hOLF, hOLI, hOLC,
    hETER, hETIO, hERIO,
    hRL, hRET, hRER, hRIO,
    hLET, hLER, hLIO,
    hOET, hOER, hGET, hGER⟩
  -- Execute preamble registers 10..18 and `cap` in reg 24
  let s1 := { st with regs := Function.update st.regs 10 oldRootGraph }
  let s2 := { s1 with regs := Function.update s1.regs 11 n }
  let s3 := { s2 with regs := Function.update s2.regs 12 rootECap }
  let s4 := { s3 with regs := Function.update s3.regs 13 intCap }
  let s5 := { s4 with regs := Function.update s4.regs 24 cap }
  let s6 := { s5 with regs := Function.update s5.regs 14 (dgEPresBase oldRootGraph n) }
  let s7 := { s6 with regs := Function.update s6.regs 15 forward }
  let s8 := { s7 with regs := Function.update s7.regs 16 m }
  let s9 := { s8 with regs := Function.update s8.regs 17 inverse }
  let s10 := { s9 with regs := Function.update s9.regs 18 freshCounter }
  have r1 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 70) (.const 14)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨oldRootGraph, by simp [Expr.eval, BinOp.eval, h70, show 14 < 2 ^ w by omega,
      show root + 14 < 2 ^ w by omega, show st.mem (root + 14) = oldRootGraph by simpa using hRoot 14 (by simp)], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 11 (.load (.reg 10))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨n, by simp [Expr.eval, s1, show st.mem oldRootGraph = n by simpa [dgVCapOff] using hDG.2.2.2.1], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 12 (.load (.bin .add (.reg 10) (.const 1)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨rootECap, by simp [Expr.eval, BinOp.eval, s2, s1, hw1, show oldRootGraph + 1 < 2 ^ w by omega,
      show st.mem (oldRootGraph + 1) = rootECap by simpa [dgECapOff] using hDG.2.2.2.2.1], rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 70) (.const 15)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨intCap, by simp [Expr.eval, BinOp.eval, s3, s2, s1, h70, show 15 < 2 ^ w by omega,
      show root + 15 < 2 ^ w by omega, show st.mem (root + 15) = intCap by simpa using hRoot 15 (by simp)], rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.cond (.bin .lt (.reg 12) (.reg 13)) (.assign 24 (.reg 12)) (.assign 24 (.reg 13)))
      s4 .normal s5 6 := by
    by_cases hlt : rootECap < intCap
    · have hcapEq : cap = rootECap := Nat.min_eq_left (le_of_lt hlt)
      refine runs_cond_iff.mpr ⟨1, 2, by simp [Expr.eval, BinOp.eval, s4, s3, hlt, hw1], ?_, by simp [Expr.size]⟩
      simpa [s5, hcapEq] using (runs_assign_iff (w := w) (p := p) (ω := ω) (r := 24) (e := .reg 12) (st := s4)).mpr
        ⟨rootECap, by simp [Expr.eval, s4, s3], rfl, rfl, rfl⟩
    · have hcapEq : cap = intCap := Nat.min_eq_right (Nat.le_of_not_lt hlt)
      refine runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, BinOp.eval, s4, s3, hlt, show 0 < 2 ^ w by omega], ?_, by simp [Expr.size]⟩
      simpa [s5, hcapEq] using (runs_assign_iff (w := w) (p := p) (ω := ω) (r := 24) (e := .reg 13) (st := s4)).mpr
        ⟨intCap, by simp [Expr.eval, s4], rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 14 (.bin .add (.bin .add (.reg 10) (.const 4)) (.bin .mul (.const 7) (.reg 11))))
      s5 .normal s6 8 :=
    runs_assign_iff.mpr ⟨dgEPresBase oldRootGraph n, by simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1,
      show 4 < 2 ^ w by omega, hw7, show oldRootGraph + 4 < 2 ^ w by omega, show 7 * n < 2 ^ w by omega,
      show oldRootGraph + 4 + 7 * n < 2 ^ w by omega, dgEPresBase], rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 70) (.const 3)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨forward, by simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, h70,
      show 3 < 2 ^ w by omega, show root + 3 < 2 ^ w by omega, show st.mem (root + 3) = forward by simpa using hRoot 3 (by simp)], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 73) (.const 9)))) s7 .normal s8 5 :=
    runs_assign_iff.mpr ⟨m, by simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, h73,
      show 9 < 2 ^ w by omega, show handle + 9 < 2 ^ w by omega, hH9], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 17 (.load (.bin .add (.reg 70) (.const 4)))) s8 .normal s9 5 :=
    runs_assign_iff.mpr ⟨inverse, by simp [Expr.eval, BinOp.eval, s8, s7, s6, s5, s4, s3, s2, s1, h70,
      show 4 < 2 ^ w by omega, show root + 4 < 2 ^ w by omega, show st.mem (root + 4) = inverse by simpa using hRoot 4 (by simp)], rfl, rfl, rfl⟩
  have r10 : Runs w p ω (.assign 18 (.load (.bin .add (.reg 70) (.const 5)))) s9 .normal s10 5 :=
    runs_assign_iff.mpr ⟨freshCounter, by simp [Expr.eval, BinOp.eval, s9, s8, s7, s6, s5, s4, s3, s2, s1, h70,
      show 5 < 2 ^ w by omega, show root + 5 < 2 ^ w by omega, show st.mem (root + 5) = freshCounter by simpa using hRoot 5 (by simp)], rfl, rfl, rfl⟩
  -- Call `renameProc`
  obtain ⟨outRen, cRen, rRenBody, hcRen, hFreshRen, hUnrRen, hRenBelow, hRenAbove⟩ :=
    level0RenameBody_runs_with_unrank (w := w) (bits := dgEPresBase oldRootGraph n) (cap := cap)
      (forward := forward) (extCap := m) (inverse := inverse) (intCap := intCap)
      (counter := freshCounter) (heap := heap0) (pos := s10.pos) (G := G0') (e2i := e2i)
      (i2e := i2e) (nf := nf) (p := p) (ω := ω) (mem := s10.mem)
      (fun j hj => hDG.2.2.2.2.2.2.2.2.2.2.2.1 j (by omega))
      (fun e he => Nat.lt_min.mpr (hCapE e he)) hCapLeI hFresh
      (by unfold dgEPresBase; omega) (by omega) (by omega) (by omega)
      hFI hCF hCI (by omega) hw1
  let s11 : State := { regs := Function.update s10.regs 25 G0'.m, mem := outRen.mem, pos := outRen.pos }
  have r11 : Runs w p ω (.call 25 renameProc [.reg 14, .reg 24, .reg 15, .reg 16, .reg 17, .reg 18, .reg 4])
      s10 .normal s11 (7 + cRen + 1) :=
    runs_call_iff.mpr ⟨[dgEPresBase oldRootGraph n, cap, forward, m, inverse, freshCounter, heap0],
      level0RenameBody, .returned G0'.m, outRen, cRen,
      by simp [evalArgs, Expr.eval, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h4],
      hRenProc, rRenBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  let s12 := { s11 with regs := Function.update s11.regs 26 (heap0 + cap) }
  let s13 := { s12 with regs := Function.update s12.regs 4 heap1 }
  let s14 := { s13 with regs := Function.update s13.regs 27 oldLen0 }
  let s15 := { s14 with regs := Function.update s14.regs 28 heap1 }
  have h11Eq (a : ℕ) (ha : a < heap0) (h1 : a < forward ∨ forward + m ≤ a)
      (h2 : a < inverse ∨ inverse + intCap ≤ a) (h3 : a ≠ freshCounter) : s11.mem a = st.mem a :=
    hRenBelow a ha (by omega) (by omega) h3
  have r12 : Runs w p ω (.assign 26 (.bin .add (.reg 4) (.reg 24))) s11 .normal s12 4 :=
    runs_assign_iff.mpr ⟨heap0 + cap, by simp [Expr.eval, BinOp.eval, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      h4, show heap0 + cap < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 4 (.bin .add (.reg 26) (.reg 24))) s12 .normal s13 4 :=
    runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, BinOp.eval, s12, s11, s10, s9, s8, s7, s6, s5,
      show heap0 + cap + cap = heap1 by dsimp [heap1]; omega, show heap1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hLM0_13 : s13.mem lm = oldLen0 :=
    (h11Eq lm (by omega) (by rcases hLF with h | h <;> omega)
      (by rcases hLI with h | h <;> omega) (by rcases hLC with h | h <;> omega)).trans hLM0
  have r14 : Runs w p ω (.assign 27 (.load (.reg 83))) s13 .normal s14 3 :=
    runs_assign_iff.mpr ⟨oldLen0, by
      have hm : outRen.mem lm = oldLen0 := hLM0_13
      simp [Expr.eval, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h83, hm], rfl, rfl, rfl⟩
  have r15 : Runs w p ω (.assign 28 (.reg 4)) s14 .normal s15 2 :=
    runs_assign_iff.mpr ⟨heap1, by simp [Expr.eval, s14, s13], rfl, rfl, rfl⟩
  -- Call `compactProc`
  have hRoot15 : SolverRootDirAt s15.mem root handle table levelsEnd forward inverse freshCounter slots
      names slotThresholds edgeThresholds edgeRecords offReadyCount offReadyList inOffReady oldRootGraph intCap :=
    fun j hj => (h11Eq (root + j) (by simp at hj; omega)
      (by simp at hj; rcases hRF with h | h <;> omega)
      (by simp at hj; rcases hRI with h | h <;> omega)
      (by simp at hj; rcases hRC with h | h <;> omega)).trans (hRoot j hj)
  have hDG15 : DynGraphAt s15.mem oldRootGraph n rootECap G0' :=
    dynGraphAt_of_agree hDG (fun a ha1 ha2 => h11Eq a (by omega)
      (by rcases hGF with h | h <;> omega)
      (by rcases hGI with h | h <;> omega)
      (by rcases hGC with h | h <;> omega))
  have hLen15 : EdgeValuesAt s15.mem oldLen0 4 L P G0'.E oldℓ :=
    hOldLen.congr (fun e he t ht => by
      have heL : e * L + L ≤ oldLenECap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (hCapOldLen e he))
      exact h11Eq _ (by omega) (by rcases hOF with h | h <;> omega)
        (by rcases hOI with h | h <;> omega) (by rcases hOC with h | h <;> omega))
  obtain ⟨outComp, cComp, rCompBody, hcComp, hTabComp, hLenComp, hRGComp, hLG0Comp, hR14Comp,
      hR11Comp, hLM0Comp, hLMdComp, hZeroInComp, hOffInvComp, hzComp, hFrComp⟩ :=
    wireCompactLevel0Body_runs (w := w) (copyWords := copyWords) (dgInit := dgInit) (root := root)
      (oldLen0 := oldLen0) (unrankPtr := heap0 + cap) (heap := heap1) (oldLenECap := oldLenECap)
      (G := G0') (oldℓ := oldℓ)
      (p := p) (ω := ω) (mem := s15.mem) (pos := s15.pos) hCopy hDGInit hRoot15
      ((h11Eq (handle + 11) (by omega) (by rcases hHF with h | h <;> omega)
        (by rcases hHI with h | h <;> omega) (by rcases hHC with h | h <;> omega)).trans hH11)
      ((h11Eq (handle + 5) (by omega) (by rcases hHF with h | h <;> omega)
        (by rcases hHI with h | h <;> omega) (by rcases hHC with h | h <;> omega)).trans hH5)
      hDG15 hLen15 hUnrRen (fun e he => (hCapE e he).1) hCapOldLen (fun e he => (hCapE e he).2) hdPos
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      ⟨hETER, hETIO, hERIO, hRL, hRET, hRER, hRIO, hLET, hLER, hLIO⟩
      ⟨Or.inr (by omega), Or.inr (by omega), hOET, hOER, hGET, hGER⟩
      (fun a ha => (hRenAbove a ha).trans (hz a (by omega))) (by omega) (by omega)
  let s16 : State := { regs := Function.update s15.regs 4 heap2, mem := outComp.mem, pos := outComp.pos }
  have r16 : Runs w p ω (.call 4 compactProc [.reg 70, .reg 27, .reg 26, .reg 25, .reg 4])
      s15 .normal s16 (5 + cComp + 1) :=
    runs_call_iff.mpr ⟨[root, oldLen0, heap0 + cap, G0'.m, heap1], wireCompactLevel0Body copyWords dgInit,
      .returned heap2, outComp, cComp,
      by simp [evalArgs, Expr.eval, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, h70],
      hCompProc, rCompBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  let s17 := { s16 with regs := Function.update s16.regs 29 newLvlGraph0 }
  let s18 := { s17 with regs := Function.update s17.regs 30 heap2 }
  have r17 : Runs w p ω (.assign 29 (.load (.bin .add (.reg 83) (.reg 75)))) s16 .normal s17 5 :=
    runs_assign_iff.mpr ⟨newLvlGraph0, by
      have hm : outComp.mem (lm + d) = newLvlGraph0 := hLMdComp
      simp [Expr.eval, BinOp.eval, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
        h83, h75, show lm + d < 2 ^ w by omega, hm], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.assign 30 (.reg 4)) s17 .normal s18 2 :=
    runs_assign_iff.mpr ⟨heap2, by simp [Expr.eval, s17, s16], rfl, rfl, rfl⟩
  -- Call `sortedEndsProc`
  obtain ⟨cSort, outSort, rSortBody, hcSort, hOrdLe, hOrdAt, _, hOrdW, hzSort, hFrSort⟩ :=
    buildSortedEndsBody_runs (w := w) (graph := newLvlGraph0) (out := heap2) (vCap := n)
      (eCap := rootECap) (pos := s18.pos) (p := p) (ω := ω) (mem := s18.mem) (G := G0'.compact)
      hLG0Comp (by dsimp [heap2, newLvlGraph0, newRootGraph, wireCompactLevel0Space]; omega)
      hzComp (by omega) hw7
  let s19 : State := { regs := Function.update s18.regs 4 heap3, mem := outSort.mem, pos := outSort.pos }
  have r19 : Runs w p ω (.call 4 sortedEndsProc [.reg 29, .reg 4]) s18 .normal s19 (2 + cSort + 1) :=
    runs_call_iff.mpr ⟨[newLvlGraph0, heap2], buildSortedEndsBody, .returned heap3, outSort, cSort,
      by simp [evalArgs, Expr.eval, s18, s17, s16], hSortProc, rSortBody, rfl, rfl, by simp [argsSize, Expr.size]⟩
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 6, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 8, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 5, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 5, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 5, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, 7 + cRen + 1, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 4, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 4, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, 3, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 2, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 5 + cComp + 1, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 5, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 2, 2 + cSort + 1, r18, r19, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hNotMutOf (a : ℕ) (h1 : a ≠ root + 11) (h2 : a ≠ root + 14) (h3 : a ≠ lm) (h4' : a ≠ lm + d)
      (h5' : a < edgeThresholds ∨ edgeThresholds + intCap ≤ a)
      (h6' : a < edgeRecords ∨ edgeRecords + intCap ≤ a)
      (h7' : a < offReadyList ∨ offReadyList + intCap ≤ a)
      (h8' : a < inOffReady ∨ inOffReady + intCap ≤ a) :
      ¬ InCompactMutable root table d edgeThresholds edgeRecords offReadyList inOffReady intCap a := by
    intro hm
    rcases hm with h | h | h | h | h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 (by dsimp [lm]; omega)
    · exact h4' (by dsimp [lm]; omega)
    · rcases h5' with h' | h' <;> omega
    · rcases h6' with h' | h' <;> omega
    · rcases h7' with h' | h' <;> omega
    · rcases h8' with h' | h' <;> omega
  have h19Comp (a : ℕ) (ha : a < heap2) : s19.mem a = outComp.mem a := hFrSort a ha
  have hFresh19 : FreshTablesAt s19.mem forward inverse freshCounter m intCap
      (level0E2I true G0' e2i) (level0I2E true G0' i2e) (level0NF true G0' nf) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [h19Comp freshCounter (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega),
        hFrComp freshCounter (by omega) (hNotMutOf _
          (by rcases hRC with h | h <;> omega) (by rcases hRC with h | h <;> omega)
          (by rcases hLC with h | h <;> omega) (by rcases hLC with h | h <;> omega)
          (by rcases hETC with h | h <;> omega) (by rcases hERC with h | h <;> omega)
          (by rcases hOLC with h | h <;> omega) (by rcases hIOC with h | h <;> omega))]
      exact hFreshRen.1
    · intro e he
      rw [h19Comp (forward + e) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega),
        hFrComp (forward + e) (by omega) (hNotMutOf _
          (by rcases hRF with h | h <;> omega) (by rcases hRF with h | h <;> omega)
          (by rcases hLF with h | h <;> omega) (by rcases hLF with h | h <;> omega)
          (by rcases hETF with h | h <;> omega) (by rcases hERF with h | h <;> omega)
          (by rcases hOLF with h | h <;> omega) (by rcases hIOF with h | h <;> omega))]
      exact hFreshRen.2.1 e he
    · intro j hj
      rw [h19Comp (inverse + j) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega),
        hFrComp (inverse + j) (by omega) (hNotMutOf _
          (by rcases hRI with h | h <;> omega) (by rcases hRI with h | h <;> omega)
          (by rcases hLI with h | h <;> omega) (by rcases hLI with h | h <;> omega)
          (by rcases hETI with h | h <;> omega) (by rcases hERI with h | h <;> omega)
          (by rcases hOLI with h | h <;> omega) (by rcases hIOI with h | h <;> omega))]
      exact hFreshRen.2.2 j hj
  have hTab19 (j : ℕ) (hj : j < G0'.m) :
      s19.mem (edgeThresholds + j) = st.mem (edgeThresholds + compactUnrank G0'.E j) ∧
      s19.mem (edgeRecords + j) = st.mem (edgeRecords + compactUnrank G0'.E j) := by
    have huLt : compactUnrank G0'.E j < intCap :=
      (hCapE _ (compactUnrank_mem hj)).2
    have h1 := (h19Comp (edgeThresholds + j) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans (hTabComp j hj).1
    have h2 := (h19Comp (edgeRecords + j) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans (hTabComp j hj).2
    refine ⟨h1.trans (h11Eq _ (by omega)
      (by rcases hETF with h | h <;> omega) (by rcases hETI with h | h <;> omega) (by rcases hETC with h | h <;> omega)),
      h2.trans (h11Eq _ (by omega)
      (by rcases hERF with h | h <;> omega) (by rcases hERI with h | h <;> omega) (by rcases hERC with h | h <;> omega))⟩
  have hLen19 : EdgeValuesAt s19.mem heap1 4 L P G0'.compact.E (fun j => oldℓ (compactUnrank G0'.E j)) :=
    hLenComp.congr (fun j hj t ht => by
      have hjM : j < G0'.m := by simpa [MGraph.compact, MGraph.m] using hj
      have hjL : j * L + L ≤ rootECap * L := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (by omega : j + 1 ≤ rootECap)
      exact h19Comp _ (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega))
  have hZeroIn19 (e : ℕ) (he : e < intCap) : s19.mem (inOffReady + e) = 0 :=
    (h19Comp _ (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans (hZeroInComp e he)
  refine ⟨s19, _, rAll, by omega, by simp [s19], by simp [s19, s18, s17, s16, s15],
    by simp [s19, s18, s17], by simp [s19, s18],
    fun r hr => by simp [s19, s18, s17, s16, s15, s14, s13, s12, s11, s10, s9, s8, s7, s6, s5, s4, s3, s2, s1,
      Function.update_of_ne (by omega : r ≠ 4), Function.update_of_ne (by omega : r ≠ 30),
      Function.update_of_ne (by omega : r ≠ 29), Function.update_of_ne (by omega : r ≠ 28),
      Function.update_of_ne (by omega : r ≠ 27), Function.update_of_ne (by omega : r ≠ 26),
      Function.update_of_ne (by omega : r ≠ 25), Function.update_of_ne (by omega : r ≠ 24),
      Function.update_of_ne (by omega : r ≠ 18), Function.update_of_ne (by omega : r ≠ 17),
      Function.update_of_ne (by omega : r ≠ 16), Function.update_of_ne (by omega : r ≠ 15),
      Function.update_of_ne (by omega : r ≠ 14), Function.update_of_ne (by omega : r ≠ 13),
      Function.update_of_ne (by omega : r ≠ 12), Function.update_of_ne (by omega : r ≠ 11),
      Function.update_of_ne (by omega : r ≠ 10)],
    hFresh19, hTab19, hLen19,
    dynGraphAt_of_agree hRGComp (fun a _ ha2 => h19Comp a (by dsimp [heap2, newRootGraph, wireCompactLevel0Space] at *; omega)),
    dynGraphAt_of_agree hLG0Comp (fun a _ ha2 => h19Comp a (by dsimp [heap2, newLvlGraph0, newRootGraph, wireCompactLevel0Space] at *; omega)),
    hOrdAt, hOrdW, by dsimp [heap3]; omega,
    (h19Comp (root + 14) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans hR14Comp,
    (h19Comp (root + 11) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans hR11Comp,
    (h19Comp lm (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans hLM0Comp,
    (h19Comp (lm + d) (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans hLMdComp,
    hZeroIn19,
    ⟨Nat.zero_le _, fun _ h => by omega, fun _ h => by omega,
      fun e he => Or.inl (hZeroIn19 e he), fun e he h1 => by rw [hZeroIn19 e he] at h1; omega⟩,
    hzSort,
    fun a ha hnf hni hnc hnm =>
      (h19Comp a (by dsimp [heap2, heap1, wireCompactLevel0Space]; omega)).trans
        ((hFrComp a (by omega) hnm).trans (hRenBelow a ha hnf hni hnc))⟩

theorem wireBranchA_compose {w renameProc compactProc sortedEndsProc initCore readGraph
    readLSF coreLenProc readOrd lastInit c1 c2 : ℕ} {p : Program} {ω : ℕ → Bool}
    {s0 s1 s2 : State}
    (h1 : Runs w p ω (wireBranchAPrefixStmt renameProc compactProc sortedEndsProc) s0 .normal s1 c1)
    (h2 : Runs w p ω (wireBranchASuffixStmt initCore readGraph readLSF coreLenProc readOrd lastInit) s1 .normal s2 c2) :
    Runs w p ω
      (wireCoreBranchAChainStmt renameProc compactProc sortedEndsProc initCore readGraph readLSF
        coreLenProc readOrd lastInit) s0 .normal s2 (c1 + c2 + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨s1, c1, c2, h1, h2, rfl⟩)

end MinCostFlow.MinRatio

