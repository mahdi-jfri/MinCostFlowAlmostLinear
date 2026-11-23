module

public import MinCostFlow.MinRatio.WireCoreOpsK
public import MinCostFlow.MinRatio.WireCoreLenK
public import MinCostFlow.MinRatio.OrdRebuildSuffix
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# K-contract ordered suffix rebuild (`WireRebuildSuffixK`)

Provides the deterministic Word-RAM readout and suffix-rebuild procedures targeting the
parameterized ordered sparse-core contract `sparseCoreOrdMachineContractK` (Lemma 5.17,
page 23, with the bundle repair described in the README,
'Where the proof departs from the paper'):
1. `ordReadoutNextLevelK`: after initializing a sparse-core level or restarting a branch,
   reads the sparsifier graph (op `3`) and copies it into caller-owned memory, reads the
   `L_w`-limb LSF (op `2`), computes exact `L`-limb `coreLen` via `wireCoreLenBody`
   (`WireCoreLenK.lean`), passes `nextLen` as both lengths and gradient (valid by
   `ToolInitOrdEqOnE`), and reads the output rotation order `OrdListAt` (op `5`).
2. `ordRebuildLevelBodyK`: one sparse-core iteration (`first ≤ i < d`), loading `M_i` from
   `lvlMTable[i]`, initializing via `ordCoreInitStmtK`, storing `(handle, 0)` into
   `(handleCell, branchCell)`, running `ordReadoutNextLevelK`, and advancing descriptors.
3. `ordRebuildSuffixProgramK`: composes `ordRebuildLevelBodyK` over `first .. d - 1` with
   `rebuildTerminalRuntimeStep` at level `d` via `rebuildSuffixProgram`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

section Programs

/-- Shared K-contract readout tail after `ordCoreInitStmtK` or `ordCoreRestartStmt`:
reads and copies the sparsifier graph (op `3`), reads the `L_w`-limb LSF (op `2`), computes
exact `L`-limb `coreLen` into caller memory via `coreLenProc` (`wireCoreLenBody`), sets both
`nextLen` (`reg 7`) and `nextGrad` (`reg 8`) to that table (valid under `ToolInitOrdEqOnE`),
and reads the output rotation order `OrdListAt` (op `5`) into `reg 9`. -/
@[expose] def ordReadoutNextLevelK (readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 65 (.reg 2) ;;
  .assign 66 (.reg 3) ;;
  .assign 69 (.reg 6) ;;
  ordCoreReadGraphStmt readGraph ;;
  loadShiftGraph ;;
  copyGraphFromHeader ;;
  .assign 64 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 4 (.reg 5) ;;
  .assign 63 (.reg 6) ;;
  .assign 6 (.reg 69) ;;
  ordCoreReadLSFStmt readLSF ;;
  .assign 10 (.load (.bin .add (.reg 4) (.const 3))) ;;
  .assign 11 (.load (.bin .add (.reg 4) (.const 4))) ;;
  .call 4 coreLenProc [.reg 63, .reg 10, .reg 7, .reg 67, .reg 11, .reg 5] ;;
  .assign 7 (.reg 5) ;;
  .assign 8 (.reg 5) ;;
  .assign 2 (.reg 65) ;;
  .assign 3 (.reg 66) ;;
  ordCoreReadOrdStmt readOrd ;;
  .assign 4 (.reg 5) ;;
  .assign 6 (.reg 63)

theorem ordReadoutNextLevelK_noRand (readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordReadoutNextLevelK readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordReadoutNextLevelK, ordCoreReadGraphStmt_noRand, loadShiftGraph, copyGraphFromHeader,
    readGraphCopySize, copyReadoutGraphAtHeap, copyReadoutGraph, copyWordsStmt,
    ordCoreReadLSFStmt_noRand, ordCoreReadOrdStmt_noRand, Stmt.NoRand]

/-- One sparse-core level iteration (`first ≤ i < d`) under `sparseCoreOrdMachineContractK`:
loads `M_i := mem[reg 57 + reg 19]` into `reg 55`, initializes `tool.initOrd`, records
`(handle, 0)` in `(reg 51, reg 52)`, runs `ordReadoutNextLevelK`, and advances descriptors. -/
@[expose] def ordRebuildLevelBodyK (init readGraph readLSF coreLenProc readOrd : ℕ) : Stmt :=
  .assign 55 (.load (.bin .add (.reg 57) (.reg 19))) ;;
  ordCoreInitStmtK init ;;
  storeRebuiltLevel ;;
  ordReadoutNextLevelK readGraph readLSF coreLenProc readOrd ;;
  rebuildAdvanceDescriptors

theorem ordRebuildLevelBodyK_noRand (init readGraph readLSF coreLenProc readOrd : ℕ) :
    (ordRebuildLevelBodyK init readGraph readLSF coreLenProc readOrd).NoRand := by
  simp [ordRebuildLevelBodyK, ordCoreInitStmtK_noRand, storeRebuiltLevel,
    ordReadoutNextLevelK_noRand, rebuildAdvanceDescriptors, Stmt.NoRand]

/-- Complete K-contract ordered suffix rebuild: runs `ordRebuildLevelBodyK` on `first .. d - 1`
and `rebuildTerminalRuntimeStep lastInit` at level `d`. -/
@[expose] def ordRebuildSuffixProgramK
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  rebuildSuffixProgram
    (ordRebuildLevelBodyK init readGraph readLSF coreLenProc readOrd)
    (rebuildTerminalRuntimeStep lastInit)

theorem ordRebuildSuffixProgramK_noRand
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (ordRebuildSuffixProgramK init readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  apply rebuildSuffixProgram_noRand (ordRebuildLevelBodyK_noRand _ _ _ _ _)
  simp [rebuildTerminalRuntimeStep, rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

end Programs

section ReadoutExecution

/-- Execute `ordReadoutNextLevelK` against `sparseCoreOrdMachineContractK`. Produces caller-owned
`nextGraph` (`reg 6`), `nextLen` (`reg 7` and `reg 8`), and `nextOrd` (`reg 9`) for the next
chain level, charging `2 * P.readout + 17 * dynGraphSize vcH ecH + H.m * (wireCoreLenEdgeCost
(max L Lw) + 30) + P.mul * (ordRotWords a branch + 1) * bundleLogFactor M N + 140`. -/
theorem ordReadoutNextLevelK_runs
    {w L k M N vCap eCap capExp init coreLenProc edgeProc signExt mul intDiv copy
      branch handle heap graphBase lenBase : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {initialGraph : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {a : SparseCoreOrdAbs tool} {x : R.τ}
    {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ : ℕ → ℝ)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractK fmt L tool initialGraph k M N vCap eCap capExp P allocation))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hb : st.regs 2 = branch) (hh : st.regs 3 = handle) (hp : st.regs 4 = heap)
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase) (h67 : st.regs 67 = L)
    (hj : branch < k) (hwk : k < 2 ^ w) (hhw : handle < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap a.G)
    (hgEnd : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hFootG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      ¬ R.foot handle x addr)
    (hLen : EdgeValuesAt st.mem lenBase 4 L fmt.precision a.G.E ℓ)
    (hLenEnd : lenBase + eCap * L ≤ heap)
    (hFootLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L → ¬ R.foot handle x addr)
    (hrep : R.rep handle a x st.mem)
    (hIn : SparseCoreOrdInput tool k M N a.st a.G a.ord a.n)
    (hfoot : ∀ addr, R.foot handle x addr → addr < heap)
    (hz : ZeroFrom st.mem heap)
    (hHE : (tool.S a.st branch).E ⊆ a.G.E)
    (hCoreLenFits : ∀ e ∈ (tool.S a.st branch).E,
      ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
        coreLen (tool.lsfs a.st branch) ℓ e)
    (hCopyRoom : ∀ (m1 : ℕ → ℕ) (h1 rawGraph vcH ecH : ℕ),
      DynGraphAt m1 rawGraph vcH ecH (tool.S a.st branch) →
      heap ≤ h1 → h1 ≤ heap + 1 →
      rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 5 < 2 ^ w)
    (hCoreLenRoom : ∀ (m2 : ℕ → ℕ) (vcH ecH vcF ecF h2 h3 Lw : ℕ),
      let forest := tool.lsfs a.st branch
      let H := tool.S a.st branch
      (∃ m1 rawG, DynGraphAt m1 rawG vcH ecH H) →
      LSFAt m2 h2 vcF ecF 4 Lw fmt.precision a.G.E forest →
      Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) →
      heap ≤ h2 → h2 ≤ heap + 1 + dynGraphSize vcH ecH → h2 ≤ h3 → h3 ≤ h2 + 5 →
      m2 (h2 + 3) + 2 ≤ h3 ∧
      (∀ e ∈ H.E, m2 (m2 (h2 + 3)) + e * Lw + Lw ≤ h3) ∧
      (∀ e ∈ H.E, m2 (m2 (h2 + 3) + 1) + e * Lw + Lw ≤ h3) ∧
      h3 + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw) + (1 + ordRotWords a branch) < 2 ^ w)
    (hroom1 : heap + 1 < 2 ^ w) :
    let forest := tool.lsfs a.st branch
    let H := tool.S a.st branch
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)
    ∃ (out : State) (vcH ecH nextOrdWords Lw cost : ℕ) (y : R.τ),
      Runs w p ω (ordReadoutNextLevelK (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
      Lw ≤ LwMax ∧
      R.rep handle a y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a.st branch) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a branch ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH →
        ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot handle y addr) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + 7 + dynGraphSize vcH ecH + ecH * L +
        H.m * wireCoreLenEdgeSpace (max L Lw) + ordRotWords a branch ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, ¬ R.foot handle x addr → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot handle y addr → addr < out.regs 4) ∧
      (∀ addr, R.foot handle y addr → R.foot handle x addr ∨ (heap ≤ addr ∧ addr < out.regs 4)) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 62) ∨ r = 67 ∨ r = 68 ∨ 70 ≤ r →
        out.regs r = st.regs r) ∧
      cost + R.phi handle y out.mem ≤
        2 * P.readout + 17 * dynGraphSize vcH ecH +
          H.m * (wireCoreLenEdgeCost (max L Lw) + 30) +
          P.mul * (ordRotWords a branch + 1) * SparseCore.bundleLogFactor M N +
          R.phi handle x st.mem + 190 := by
  dsimp only
  let forest := tool.lsfs a.st branch
  let H := tool.S a.st branch
  -- Save branch, handle, curGraph
  let s1 := { st with regs := Function.update st.regs 65 branch }
  let s2 := { s1 with regs := Function.update s1.regs 66 handle }
  let s3 := { s2 with regs := Function.update s2.regs 69 graphBase }
  have r1 : Runs w p ω (.assign 65 (.reg 2)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, hb], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 66 (.reg 3)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s1, Function.update_of_ne, hh], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 69 (.reg 6)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨graphBase, by simp [Expr.eval, s2, s1, Function.update_of_ne, hg], rfl, rfl, rfl⟩
  have hs3_r (r : ℕ) (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s3.regs r = st.regs r := by
    simp [s3, s2, s1, Function.update_of_ne h65, Function.update_of_ne h66, Function.update_of_ne h69]
  -- Op 3 (read sparsifier graph)
  obtain ⟨s4, h1, c4, y1, r4, hs4_5, hrep1, ⟨vcH, ecH, hH1⟩, hresp1, hc4, hs4_regs⟩ :=
    ordCoreReadGraphK_runs (ω := ω) (st := s3) himpl
      ((hs3_r 2 (by decide) (by decide) (by decide)).trans hb)
      ((hs3_r 3 (by decide) (by decide) (by decide)).trans hh)
      ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)
      hj hwk hhw hrep hIn hfoot hz hroom1
  obtain ⟨s5, r5, hs5_6, hH5, hs5_mem, _, hs5_regs⟩ :=
    loadShiftGraph_runs (ω := ω) (st := s4)
      ((hs4_regs 4 (by decide)).trans ((hs3_r 4 (by decide) (by decide) (by decide)).trans hp)) hH1
  have hfoot1 : ∀ addr, R.foot handle y1 addr → addr < h1 := fun addr ha => by
    rcases hresp1.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot addr ho).trans_le hresp1.1
    · exact hn
  obtain ⟨hRawEnd, hCopyFit⟩ := hCopyRoom s4.mem h1 (s4.mem heap) vcH ecH hH1 hresp1.1 hresp1.2.1
  -- Copy graph to caller-owned memory [h1, h2)
  obtain ⟨s6, c6, r6, hH6, hs6_6, hs6_5, hz6, hrep6, hphi6, hfootDisj6, hmem6, _, hc6, hs6_regs⟩ :=
    copyShiftGraph_preserves_tool_runs (ω := ω) (st := s5) himpl.1 (hs5_mem.symm ▸ hrep1) hfoot1
      hs5_6 ((hs5_regs 5 (by decide)).trans hs4_5) (hs5_6 ▸ hH5) hRawEnd (by omega) hw9
      (hs5_mem.symm ▸ hresp1.2.2.1)
  let h2 := h1 + dynGraphSize vcH ecH
  have hH6_ec : s6.mem (h1 + 1) = ecH := (hs6_6 ▸ hH6).2.2.2.2.1
  let s7 := { s6 with regs := Function.update s6.regs 64 ecH }
  let s8 := { s7 with regs := Function.update s7.regs 4 h2 }
  let s9 := { s8 with regs := Function.update s8.regs 63 h1 }
  let s10 := { s9 with regs := Function.update s9.regs 6 graphBase }
  have r7 : Runs w p ω (.assign 64 (.load (.bin .add (.reg 6) (.const 1)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨ecH, by
      simp [Expr.eval, BinOp.eval, hs6_6, show 1 < 2 ^ w by omega,
        show h1 + 1 < 2 ^ w by unfold dynGraphSize at hCopyFit; omega, hH6_ec], rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 4 (.reg 5)) s7 .normal s8 2 :=
    runs_assign_iff.mpr ⟨h2, by simp [Expr.eval, s7, Function.update_of_ne, hs6_5, h2], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 63 (.reg 6)) s8 .normal s9 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, s8, s7, Function.update_of_ne, hs6_6], rfl, rfl, rfl⟩
  have hs6_69 : s6.regs 69 = graphBase :=
    (hs6_regs 69 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      ((hs5_regs 69 (by decide)).trans ((hs4_regs 69 (by decide)).trans (by simp [s3])))
  have r10 : Runs w p ω (.assign 6 (.reg 69)) s9 .normal s10 2 :=
    runs_assign_iff.mpr ⟨graphBase, by simp [Expr.eval, s9, s8, s7, Function.update_of_ne, hs6_69], rfl, rfl, rfl⟩
  have hs6_frame (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      s6.mem addr = st.mem addr :=
    (hmem6 addr (hlt.trans_le hresp1.1)).trans ((congrFun hs5_mem addr).trans
      (hresp1.2.2.2.1 addr hlt hnf))
  have hG10 : DynGraphAt s10.mem graphBase vCap eCap a.G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs6_frame addr (by omega) (hFootG addr hlo hhi))
  have hfoot1_h2 : ∀ addr, R.foot handle y1 addr → addr < h2 := fun addr ha =>
    (hfoot1 addr ha).trans_le (Nat.le_add_right h1 _)
  have hs10_keep (r : ℕ) (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h10 : r ≠ 10)
      (h11 : r ≠ 11) (h12 : r ≠ 12) (h63 : r ≠ 63) (h64 : r ≠ 64)
      (h65 : r ≠ 65) (h66 : r ≠ 66) (h69 : r ≠ 69) : s10.regs r = st.regs r := by
    simp only [s10, s9, s8, s7, Function.update_of_ne h6, Function.update_of_ne h63,
      Function.update_of_ne h4, Function.update_of_ne h64]
    exact (hs6_regs r h5 h6 h10 h11 h12).trans ((hs5_regs r h6).trans
      ((hs4_regs r h5).trans (hs3_r r h65 h66 h69)))
  -- Op 2 (read LSF with L_w at h2 + 4)
  obtain ⟨s11, h3, c11, y2, r11, hs11_5, hrep2, hLwLe, ⟨vcF, ecF, hLSF11⟩, hresp2, hc11, hs11_regs⟩ :=
    ordCoreReadLSFK_runs (ω := ω) (st := s10) himpl
      ((hs10_keep 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb)
      ((hs10_keep 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh)
      (by simp [s10]) (by simp [s10, s9, s8, Function.update_of_ne, h2])
      hj hwk hhw hG10 (hgEnd.trans (hresp1.1.trans (Nat.le_add_right h1 _)))
      hrep6 hIn hfoot1_h2 (by simpa [s10, s9, s8, s7, hs6_5, h2] using hz6) (by omega)
  let Lw := s11.mem (h2 + 4)
  have hLSF11' : LSFAt s11.mem h2 vcF ecF 4 Lw fmt.precision a.G.E forest := by
    simpa only [hFour] using hLSF11
  have h11_frame_h2 (addr : ℕ) (hlt : addr < h2) (hnf : ¬ R.foot handle y1 addr) :
      s11.mem addr = s6.mem addr := hresp2.2.2.2.1 addr hlt hnf
  have h11_frame_heap (addr : ℕ) (hlt : addr < heap) (hnf : ¬ R.foot handle x addr) :
      s11.mem addr = st.mem addr := by
    have hnf1 : ¬ R.foot handle y1 addr := fun hf => by
      rcases hresp1.2.2.2.2 addr hf with ho | ⟨hlo, _⟩
      · exact hnf ho
      · omega
    exact (h11_frame_h2 addr (hlt.trans_le (hresp1.1.trans (Nat.le_add_right h1 _))) hnf1).trans
      (hs6_frame addr hlt hnf)
  obtain ⟨hStDescLe, hNumLeCL, hDenLeCL, hCLRoom⟩ :=
    hCoreLenRoom s11.mem vcH ecH vcF ecF h2 h3 Lw ⟨s6.mem, s6.regs 6, hH6⟩ hLSF11' hLwLe
      (hresp1.1.trans (Nat.le_add_right h1 _))
      (by have := hresp1.2.1; dsimp [h2]; omega) hresp2.1 hresp2.2.1
  let stretchDesc := s11.mem (h2 + 3)
  let s12 := { s11 with regs := Function.update s11.regs 10 stretchDesc }
  let s13 := { s12 with regs := Function.update s12.regs 11 Lw }
  have r12 : Runs w p ω (.assign 10 (.load (.bin .add (.reg 4) (.const 3)))) s11 .normal s12 5 :=
    runs_assign_iff.mpr ⟨stretchDesc, by
      simp [Expr.eval, BinOp.eval, hs11_regs 4 (by decide), s10, s9, s8, Function.update_of_ne,
        show 3 < 2 ^ w by omega, show h2 + 3 < 2 ^ w by omega, stretchDesc], rfl, rfl, rfl⟩
  have r13 : Runs w p ω (.assign 11 (.load (.bin .add (.reg 4) (.const 4)))) s12 .normal s13 5 :=
    runs_assign_iff.mpr ⟨Lw, by
      simp [Expr.eval, BinOp.eval, s12, Function.update_of_ne, hs11_regs 4 (by decide),
        s10, s9, s8, show 4 < 2 ^ w by omega, show h2 + 4 < 2 ^ w by omega, Lw], rfl, rfl, rfl⟩
  -- Call `coreLenProc` (`wireCoreLenBody`) at `h3` -> writes `EdgeValuesAt` at `[h3, h3 + ecH * L)`
  have hH13 : DynGraphAt s13.mem h1 vcH ecH H :=
    dynGraphAt_of_agree (hs6_6 ▸ hH6) (fun addr hlo hhi =>
      h11_frame_h2 addr (by dsimp [h2]; omega) (hfootDisj6 addr hlo))
  have hLen13 : EdgeValuesAt s13.mem lenBase 4 L fmt.precision a.G.E ℓ :=
    hLen.congr (fun e he j hj => by
      have heLt : e < eCap := hG.2.2.1 e he
      have hm : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact h11_frame_heap _ (by omega) (hFootLen _ (by omega) (by omega)))
  have hLenLe13 : ∀ e ∈ H.E, lenBase + e * L + L ≤ h3 := fun e he => by
    have heLt : e < eCap := hG.2.2.1 e (hHE he)
    have hm : e * L + L ≤ eCap * L := by
      have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
    have h1le := hresp1.1; have h2le := hresp2.1
    omega
  let K := max L Lw
  let h4 := h3 + ecH * L + H.m * wireCoreLenEdgeSpace K
  have hCLRoom' : h3 + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw) < 2 ^ w := by
    change h3 + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw) + (1 + ordRotWords a branch) < 2 ^ w at hCLRoom
    omega
  obtain ⟨outCL, cCL, rCLBody, hcCL, hNextLenCL, hzCL, hFrCL⟩ :=
    wireCoreLen_runs (w := w) (L := L) (Lw := Lw) (P := fmt.precision) (hBase := h1)
      (vcH := vcH) (ecH := ecH) (stretchDesc := stretchDesc) (lenPtr := lenBase) (heap := h3)
      (H := H) (G_E := a.G.E) (forest := forest) (ℓ := ℓ) (p := p) (ω := ω) (mem := s13.mem)
      (pos := s13.pos) hEdgeProc hSign hMul hDiv hCopy hH13 hHE hLSF11'.2.2.2 hLen13
      hCoreLenFits hresp2.1 hStDescLe hNumLeCL hDenLeCL hLenLe13 hresp2.2.2.1 hCLRoom' (by omega)
  let s14 : State := { regs := Function.update s13.regs 4 h4, mem := outCL.mem, pos := outCL.pos }
  have hs13_7 : s13.regs 7 = lenBase := by
    simp only [s13, s12, Function.update_of_ne (by decide : (7 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (7 : ℕ) ≠ 10)]
    rw [hs11_regs 7 (by decide)]
    exact (hs10_keep 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have hs13_67 : s13.regs 67 = L := by
    simp only [s13, s12, Function.update_of_ne (by decide : (67 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (67 : ℕ) ≠ 10)]
    rw [hs11_regs 67 (by decide)]
    exact (hs10_keep 67 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).trans h67
  have r14 : Runs w p ω
      (.call 4 coreLenProc [.reg 63, .reg 10, .reg 7, .reg 67, .reg 11, .reg 5])
      s13 .normal s14 (cCL + 7) :=
    runs_call_iff.mpr ⟨[h1, stretchDesc, lenBase, L, Lw, h3], wireCoreLenBody edgeProc,
      .returned h4, outCL, cCL, by
        simp only [evalArgs, Expr.eval, hs13_7, hs13_67]
        simp [s13, s12, hs11_regs 63 (by decide), hs11_5, s10, s9, Function.update_of_ne],
      hCoreLenProc, rCLBody, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  -- Set `reg 7 := h3`, `reg 8 := h3`, restore `reg 2 := branch`, `reg 3 := handle`
  let s15 := { s14 with regs := Function.update s14.regs 7 h3 }
  let s16 := { s15 with regs := Function.update s15.regs 8 h3 }
  let s17 := { s16 with regs := Function.update s16.regs 2 branch }
  let s18 := { s17 with regs := Function.update s17.regs 3 handle }
  have hs14_5 : s14.regs 5 = h3 := by
    simp [s14, s13, s12, Function.update_of_ne, hs11_5]
  have hs14_65 : s14.regs 65 = branch := by
    simp only [s14, s13, s12, Function.update_of_ne (by decide : (65 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 10)]
    rw [hs11_regs 65 (by decide)]
    simp only [s10, s9, s8, s7, Function.update_of_ne (by decide : (65 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 63),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (65 : ℕ) ≠ 64)]
    rw [hs6_regs 65 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs5_regs 65 (by decide), hs4_regs 65 (by decide)]
    simp [s3, s2, s1, Function.update_of_ne]
  have hs14_66 : s14.regs 66 = handle := by
    simp only [s14, s13, s12, Function.update_of_ne (by decide : (66 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 11),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 10)]
    rw [hs11_regs 66 (by decide)]
    simp only [s10, s9, s8, s7, Function.update_of_ne (by decide : (66 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 63),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (66 : ℕ) ≠ 64)]
    rw [hs6_regs 66 (by decide) (by decide) (by decide) (by decide) (by decide),
      hs5_regs 66 (by decide), hs4_regs 66 (by decide)]
    simp [s3, s2, Function.update_of_ne]
  have r15 : Runs w p ω (.assign 7 (.reg 5)) s14 .normal s15 2 :=
    runs_assign_iff.mpr ⟨h3, by simp [Expr.eval, hs14_5], rfl, rfl, rfl⟩
  have r16 : Runs w p ω (.assign 8 (.reg 5)) s15 .normal s16 2 :=
    runs_assign_iff.mpr ⟨h3, by simp [Expr.eval, s15, Function.update_of_ne, hs14_5], rfl, rfl, rfl⟩
  have r17 : Runs w p ω (.assign 2 (.reg 65)) s16 .normal s17 2 :=
    runs_assign_iff.mpr ⟨branch, by simp [Expr.eval, s16, s15, Function.update_of_ne, hs14_65], rfl, rfl, rfl⟩
  have r18 : Runs w p ω (.assign 3 (.reg 66)) s17 .normal s18 2 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s17, s16, s15, Function.update_of_ne, hs14_66], rfl, rfl, rfl⟩
  -- Preserve `R.rep handle a y2` across `coreLenProc` (whose writes are all `≥ h3`)
  have hfoot2 : ∀ addr, R.foot handle y2 addr → addr < h3 := fun addr ha => by
    rcases hresp2.2.2.2.2 addr ha with ho | ⟨_, hn⟩
    · exact (hfoot1_h2 addr ho).trans_le hresp2.1
    · exact hn
  have hloc18 := himpl.1 handle a y2 s11.mem s18.mem (fun addr ha => (hFrCL addr (hfoot2 addr ha)).symm)
  have hfoot2_h4 : ∀ addr, R.foot handle y2 addr → addr < h4 := fun addr ha =>
    (hfoot2 addr ha).trans_le (by dsimp [h4]; omega)
  -- Op 5 (read output rotation order) at `h4` -> `h5`
  obtain ⟨s19, h5, nextOrdWords, c19, y3, r19, hs19_5, hs19_9, hrep3, hOrd19, hOrdLe19,
      hresp3, hc19, hs19_regs⟩ :=
    ordCoreReadOrdK_runs (ω := ω) (st := s18) himpl
      (by simp [s18, s17, Function.update_of_ne]) (by simp [s18])
      (by simp [s18, s17, s16, s15, s14, Function.update_of_ne])
      hj hwk hhw (hloc18.1 hrep2) hIn hfoot2_h4 hzCL (by dsimp [h4, K]; exact hCLRoom)
  let s20 := { s19 with regs := Function.update s19.regs 4 h5 }
  let out := { s20 with regs := Function.update s20.regs 6 h1 }
  have hs19_63 : s19.regs 63 = h1 := by
    rw [hs19_regs 63 (by decide) (by decide)]
    simp only [s18, s17, s16, s15, s14, s13, s12, Function.update_of_ne (by decide : (63 : ℕ) ≠ 3),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 2), Function.update_of_ne (by decide : (63 : ℕ) ≠ 8),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 7), Function.update_of_ne (by decide : (63 : ℕ) ≠ 4),
      Function.update_of_ne (by decide : (63 : ℕ) ≠ 11), Function.update_of_ne (by decide : (63 : ℕ) ≠ 10)]
    rw [hs11_regs 63 (by decide)]
    simp [s10, s9, Function.update_of_ne]
  have r20 : Runs w p ω (.assign 4 (.reg 5)) s19 .normal s20 2 :=
    runs_assign_iff.mpr ⟨h5, by simp [Expr.eval, hs19_5], rfl, rfl, rfl⟩
  have r21 : Runs w p ω (.assign 6 (.reg 63)) s20 .normal out 2 :=
    runs_assign_iff.mpr ⟨h1, by simp [Expr.eval, s20, Function.update_of_ne, hs19_63], rfl, rfl, rfl⟩
  have rFull : Runs w p ω (ordReadoutNextLevelK (op 3) (op 2) coreLenProc (op 5)) st .normal out
      (2 + (2 + (2 + (c4 + (3 + (c6 + (5 + (2 + (2 + (2 + (c11 + (5 + (5 + ((cCL + 7) +
        (2 + (2 + (2 + (2 + (c19 + (2 + 2 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, _, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 3, _, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, c6, _, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, _, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 2, _, r8,
    runs_seq_iff.mpr (Or.inr ⟨s9, 2, _, r9,
    runs_seq_iff.mpr (Or.inr ⟨s10, 2, _, r10,
    runs_seq_iff.mpr (Or.inr ⟨s11, c11, _, r11,
    runs_seq_iff.mpr (Or.inr ⟨s12, 5, _, r12,
    runs_seq_iff.mpr (Or.inr ⟨s13, 5, _, r13,
    runs_seq_iff.mpr (Or.inr ⟨s14, cCL + 7, _, r14,
    runs_seq_iff.mpr (Or.inr ⟨s15, 2, _, r15,
    runs_seq_iff.mpr (Or.inr ⟨s16, 2, _, r16,
    runs_seq_iff.mpr (Or.inr ⟨s17, 2, _, r17,
    runs_seq_iff.mpr (Or.inr ⟨s18, 2, _, r18,
    runs_seq_iff.mpr (Or.inr ⟨s19, c19, _, r19,
    runs_seq_iff.mpr (Or.inr ⟨s20, 2, 2, r20, r21, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  -- Verify outputs, footprint disjointness, frame, preserved registers, and cost
  have h1le2 : h1 ≤ h2 := Nat.le_add_right h1 _
  have h2le3 : h2 ≤ h3 := hresp2.1
  have h3le4 : h3 ≤ h4 := by dsimp [h4]; omega
  have h4le5 : h4 ≤ h5 := hresp3.1
  have hnf2_h1 : ∀ addr, h1 ≤ addr → addr < h2 → ¬ R.foot handle y2 addr := fun addr hlo hhi hf => by
    rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo2, _⟩
    · exact hfootDisj6 addr hlo hy1
    · omega
  have hnf3_h1 : ∀ addr, h1 ≤ addr → addr < h2 → ¬ R.foot handle y3 addr := fun addr hlo hhi hf => by
    rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, _⟩
    · exact hnf2_h1 addr hlo hhi hy2
    · omega
  have hnf3_h3 : ∀ addr, h3 ≤ addr → addr < h3 + ecH * L → ¬ R.foot handle y3 addr :=
    fun addr hlo hhi hf => by
      rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, _⟩
      · have := hfoot2 addr hy2; omega
      · dsimp [h4] at hlo3; omega
  have hHOut : DynGraphAt out.mem h1 vcH ecH H :=
    dynGraphAt_of_agree hH13 (fun addr hlo hhi =>
      (hresp3.2.2.2.1 addr (by dsimp [h2, h4]; omega) (hnf2_h1 addr hlo hhi)).trans
        (hFrCL addr (by dsimp [h2] at h2le3; omega)))
  have hLenOut : EdgeValuesAt out.mem h3 4 L fmt.precision H.E (coreLen forest ℓ) :=
    hNextLenCL.congr (fun e he j hj => by
      have heLt : e < ecH := hH13.2.2.1 e he
      have hm : e * L + L ≤ ecH * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hresp3.2.2.2.1 _ (by dsimp [h4]; omega) (fun hf => by have := hfoot2 _ hf; omega))
  have hout6 : out.regs 6 = h1 := by simp [out]
  have hout4 : out.regs 4 = h5 := by simp [out, s20, Function.update_of_ne]
  have hout7 : out.regs 7 = h3 := by
    simp only [out, s20, Function.update_of_ne (by decide : (7 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (7 : ℕ) ≠ 4)]
    rw [hs19_regs 7 (by decide) (by decide)]
    simp [s18, s17, s16, s15, Function.update_of_ne]
  have hout8 : out.regs 8 = h3 := by
    simp only [out, s20, Function.update_of_ne (by decide : (8 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (8 : ℕ) ≠ 4)]
    rw [hs19_regs 8 (by decide) (by decide)]
    simp [s18, s17, s16, Function.update_of_ne]
  have hout9 : out.regs 9 = s19.regs 9 := by
    simp [out, s20, Function.update_of_ne]
  refine ⟨out, vcH, ecH, nextOrdWords, Lw, _, y3, rFull, hLwLe, hrep3,
    hout6.symm ▸ hHOut, hout7.symm ▸ hLenOut, hout8.trans hout7.symm,
    hout9.symm ▸ hOrd19, hOrdLe19,
    hout6.symm ▸ hresp1.1, by rw [hout6, hout4]; dsimp [h2] at h2le3; omega,
    fun addr hlo hhi => hnf3_h1 addr (hout6 ▸ hlo) (by rw [hout6] at hhi; exact hhi),
    by rw [hout7]; have := hresp1.1; omega,
    by rw [hout7, hout4]; dsimp [h4] at h4le5; omega,
    fun addr hlo hhi => hnf3_h3 addr (hout7 ▸ hlo) (hout7 ▸ hhi),
    by rw [hout4]; have := hresp1.1; omega,
    by rw [hout4]; have := hresp1.2.1; have := hresp2.2.1; have := hresp3.2.1; dsimp only [h2, h4, K, H] at *; omega,
    hout4.symm ▸ hresp3.2.2.1,
    fun addr hlt hnf => ?_, fun addr hf => ?_, fun addr hf => ?_, fun r hr => ?_, ?_⟩
  · have hnf1 : ¬ R.foot handle y1 addr := fun hf => by
      rcases hresp1.2.2.2.2 addr hf with hx | ⟨hlo, _⟩
      · exact hnf hx
      · omega
    have hnf2 : ¬ R.foot handle y2 addr := fun hf => by
      rcases hresp2.2.2.2.2 addr hf with hy1 | ⟨hlo, _⟩
      · exact hnf1 hy1
      · have := hresp1.1; omega
    have h1le := hresp1.1
    exact (hresp3.2.2.2.1 addr (by omega) hnf2).trans
      ((hFrCL addr (by omega)).trans (h11_frame_heap addr hlt hnf))
  · rw [hout4]
    rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨_, hlt⟩
    · exact (hfoot2_h4 addr hy2).trans_le h4le5
    · exact hlt
  · rw [hout4]
    have h1le := hresp1.1
    rcases hresp3.2.2.2.2 addr hf with hy2 | ⟨hlo3, hhi3⟩
    · rcases hresp2.2.2.2.2 addr hy2 with hy1 | ⟨hlo2, hhi2⟩
      · rcases hresp1.2.2.2.2 addr hy1 with hx | ⟨hlo1, hhi1⟩
        · exact Or.inl hx
        · exact Or.inr ⟨hlo1, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · exact Or.inr ⟨by omega, hhi3⟩
  · have hne : r ≠ 2 ∧ r ≠ 3 ∧ r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧
        r ≠ 10 ∧ r ≠ 11 ∧ r ≠ 12 ∧ r ≠ 63 ∧ r ≠ 64 ∧ r ≠ 65 ∧ r ≠ 66 ∧ r ≠ 69 := by omega
    simp only [out, s20, Function.update_of_ne hne.2.2.2.2.1, Function.update_of_ne hne.2.2.1]
    rw [hs19_regs r hne.2.2.2.1 hne.2.2.2.2.2.2.2.1]
    simp only [s18, s17, s16, s15, s14, s13, s12, Function.update_of_ne hne.2.1,
      Function.update_of_ne hne.1, Function.update_of_ne hne.2.2.2.2.2.2.1,
      Function.update_of_ne hne.2.2.2.2.2.1, Function.update_of_ne hne.2.2.1,
      Function.update_of_ne hne.2.2.2.2.2.2.2.2.2.1, Function.update_of_ne hne.2.2.2.2.2.2.2.2.1]
    rw [hs11_regs r hne.2.2.2.1]
    exact hs10_keep r hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.1
      hne.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.1
      hne.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hne.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  · change _ + R.phi handle y3 s19.mem ≤ _
    have hphi18 : R.phi handle y2 s18.mem = R.phi handle y2 s11.mem := hloc18.2.symm
    have hphi6' : R.phi handle y1 s10.mem = R.phi handle y1 s4.mem := by
      change R.phi handle y1 s6.mem = R.phi handle y1 s4.mem
      rw [hphi6, hs5_mem]
    have hc4' : c4 + R.phi handle y1 s4.mem ≤ P.readout + 4 + R.phi handle x st.mem := hc4
    rw [hphi18] at hc19
    rw [hphi6'] at hc11
    change cCL ≤ (tool.S a.st branch).m * (wireCoreLenEdgeCost (max L Lw) + 30) + 60 at hcCL
    omega

end ReadoutExecution

section LevelExecution

/-- Execute one iteration of `ordRebuildLevelBodyK` against `sparseCoreOrdMachineContractK`
under `ToolInitOrdEqOnE`. Loads `M_i` from `lvlMTable[i]`, initializes `tool.initOrd`,
installs `(heap, 0)` into `(handleCell, branchCell)`, runs `ordReadoutNextLevelK`, and
advances `(handleCell, branchCell)`. -/
theorem ordRebuildLevelBodyK_runs
    {w L k M N vCap eCap capExp init coreLenProc edgeProc signExt mul intDiv copy
      graphBase lenBase gradBase ordBase ordWords heap handleCell branchCell lvlMTable idx : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {R : DSRep (SparseCoreOrdAbs tool)} {p : Program} {op : ℕ → ℕ} {st : State} {ω : ℕ → Bool}
    (ℓ g : ℕ → ℝ) (ordFn : ℕ → List End)
    (hFour : fmt.limbBits = 4)
    (himpl : R.Implements w p init op
      (sparseCoreOrdMachineContractK fmt L tool G k M N vCap eCap capExp P allocation))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hg : st.regs 6 = graphBase) (hl : st.regs 7 = lenBase)
    (hgr : st.regs 8 = gradBase) (ho : st.regs 9 = ordBase) (hh : st.regs 4 = heap)
    (hkR : st.regs 1 = k) (hNR : st.regs 56 = N) (hMTab : st.regs 57 = lvlMTable)
    (hIdx : st.regs 19 = idx)
    (h51 : st.regs 51 = handleCell) (h52 : st.regs 52 = branchCell) (h67 : st.regs 67 = L)
    (hMCell : st.mem (lvlMTable + idx) = M) (hMAddrW : lvlMTable + idx < 2 ^ w)
    (hk : 0 < k) (hwk : k < 2 ^ w) (hMw : M < 2 ^ w) (hNw : N < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hword : (M + N + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hne : handleCell ≠ branchCell) (hhBelow : handleCell < heap) (hbBelow : branchCell < heap)
    (hhNextW : handleCell + 1 < 2 ^ w) (hbNextW : branchCell + 1 < 2 ^ w)
    (hG : DynGraphAt st.mem graphBase vCap eCap G) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgb : graphBase + dynGraphSize vCap eCap ≤ heap)
    (hDisjG : ∀ addr, graphBase ≤ addr → addr < graphBase + dynGraphSize vCap eCap →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hlb : lenBase + eCap * L ≤ heap) (hgrb : gradBase + eCap * L ≤ heap)
    (hDisjLen : ∀ addr, lenBase ≤ addr → addr < lenBase + eCap * L →
      addr ≠ handleCell ∧ addr ≠ branchCell)
    (hord : OrdListAt st.mem ordBase ordFn ordWords)
    (hordb : ordBase + ordWords ≤ heap)
    (hordW : ∀ j < ordWords, st.mem (ordBase + j) < 2 ^ w)
    (hrot : IsRotationOrder G ordFn)
    (hℓ : EdgeValuesAt st.mem lenBase 4 L fmt.precision G.E ℓ)
    (hgv : EdgeValuesAt st.mem gradBase 4 L fmt.precision G.E g)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e)
    (hz : ZeroFrom st.mem heap)
    (hroomInit : heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, k, M, N, heap] + 1 < 2 ^ w)
    (hHE :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G
          (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      (tool.S a0.st 0).E ⊆ G.E)
    (hCoreLenFits :
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G
          (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      ∀ e ∈ (tool.S a0.st 0).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          coreLen (tool.lsfs a0.st 0) ℓ e)
    (hTailRoom : ∀ (ret0 : ℕ),
      let a0 : SparseCoreOrdAbs tool :=
        ⟨tool.initOrd k M N G
          (fun e => if e ∈ G.E then ℓ e else 0)
          (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
      let forest := tool.lsfs a0.st 0
      let H := tool.S a0.st 0
      heap ≤ ret0 → ret0 ≤ heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, k, M, N, heap] →
      (∀ (m1 : ℕ → ℕ) (h1 rawGraph vcH ecH : ℕ),
        DynGraphAt m1 rawGraph vcH ecH H → ret0 ≤ h1 → h1 ≤ ret0 + 1 →
        rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ h1 + dynGraphSize vcH ecH + 5 < 2 ^ w) ∧
      (∀ (m2 : ℕ → ℕ) (vcH ecH vcF ecF h2 h3 Lw : ℕ),
        (∃ m1 rawG, DynGraphAt m1 rawG vcH ecH H) →
        LSFAt m2 h2 vcF ecF 4 Lw fmt.precision G.E forest →
        Lw ≤ L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1) →
        ret0 ≤ h2 → h2 ≤ ret0 + 1 + dynGraphSize vcH ecH → h2 ≤ h3 → h3 ≤ h2 + 5 →
        m2 (h2 + 3) + 2 ≤ h3 ∧
        (∀ e ∈ H.E, m2 (m2 (h2 + 3)) + e * Lw + Lw ≤ h3) ∧
        (∀ e ∈ H.E, m2 (m2 (h2 + 3) + 1) + e * Lw + Lw ≤ h3) ∧
        h3 + ecH * L + H.m * wireCoreLenEdgeSpace (max L Lw) + (1 + ordRotWords a0 0) < 2 ^ w)) :
    let a0 : SparseCoreOrdAbs tool :=
      ⟨tool.initOrd k M N G
        (fun e => if e ∈ G.E then ℓ e else 0)
        (fun e => if e ∈ G.E then g e else 0) ordFn, G, ordFn, 0⟩
    let forest := tool.lsfs a0.st 0
    let H := tool.S a0.st 0
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) * (Nat.log 2 (M + N + 2) + 1)
    ∃ (out : State) (vcH ecH nextOrdWords Lw cost : ℕ) (y : R.τ),
      Runs w p ω (ordRebuildLevelBodyK init (op 3) (op 2) coreLenProc (op 5)) st .normal out cost ∧
      Lw ≤ LwMax ∧
      out.mem handleCell = heap ∧ out.mem branchCell = 0 ∧
      out.regs 19 = idx ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      R.rep heap a0 y out.mem ∧
      DynGraphAt out.mem (out.regs 6) vcH ecH H ∧
      EdgeValuesAt out.mem (out.regs 7) 4 L fmt.precision H.E (coreLen forest ℓ) ∧
      out.regs 8 = out.regs 7 ∧
      OrdListAt out.mem (out.regs 9) (tool.rot a0.st 0) nextOrdWords ∧
      nextOrdWords ≤ ordRotWords a0 0 ∧
      heap ≤ out.regs 6 ∧ out.regs 6 + dynGraphSize vcH ecH ≤ out.regs 4 ∧
      (∀ addr, out.regs 6 ≤ addr → addr < out.regs 6 + dynGraphSize vcH ecH → ¬ R.foot heap y addr) ∧
      heap ≤ out.regs 7 ∧ out.regs 7 + ecH * L ≤ out.regs 4 ∧
      (∀ addr, out.regs 7 ≤ addr → addr < out.regs 7 + ecH * L → ¬ R.foot heap y addr) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + allocation 6 [graphBase, lenBase, gradBase, ordBase, k, M, N, heap] +
        7 + dynGraphSize vcH ecH + ecH * L +
        H.m * wireCoreLenEdgeSpace (max L Lw) + ordRotWords a0 0 ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ addr < heap, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = st.mem addr) ∧
      (∀ addr, R.foot heap y addr → heap ≤ addr ∧ addr < out.regs 4) ∧
      (∀ r, r = 0 ∨ r = 1 ∨ (13 ≤ r ∧ r ≤ 50) ∨ (53 ≤ r ∧ r ≤ 54) ∨ (56 ≤ r ∧ r ≤ 62) ∨
        r = 67 ∨ r = 68 ∨ 70 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi heap y out.mem ≤
        P.mul * (tool.cost a0.st + G.n + G.m + ordWords + 1) +
          P.mul * (ordRotWords a0 0 + 1) * SparseCore.bundleLogFactor M N +
          2 * P.readout + 17 * dynGraphSize vcH ecH +
          H.m * (wireCoreLenEdgeCost (max L Lw) + 30) + 235 := by
  dsimp only
  -- Step 1: Load `M` from `lvlMTable + idx` into `reg 55`
  let s1 := { st with regs := Function.update st.regs 55 M }
  have r1 : Runs w p ω (.assign 55 (.load (.bin .add (.reg 57) (.reg 19)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨M, by simp [Expr.eval, BinOp.eval, hMTab, hIdx, hMAddrW, hMCell], rfl, rfl, rfl⟩
  have hs1_r (r : ℕ) (h55 : r ≠ 55) : s1.regs r = st.regs r := Function.update_of_ne h55 _ _
  -- Step 2: Init ordered sparse-core level under `sparseCoreOrdMachineContractK`
  obtain ⟨s2, ret0, c2, y0, r2, hs2_2, hs2_3, hs2_4, hrep0, hIn0, hresp0, hc2⟩ :=
    ordCoreInitK_tables_runs (ω := ω) (st := s1) ℓ g ordFn himpl
      ((hs1_r 6 (by decide)).trans hg) ((hs1_r 7 (by decide)).trans hl)
      ((hs1_r 8 (by decide)).trans hgr) ((hs1_r 9 (by decide)).trans ho)
      ((hs1_r 1 (by decide)).trans hkR) (by simp [s1])
      ((hs1_r 56 (by decide)).trans hNR) ((hs1_r 4 (by decide)).trans hh)
      hk hwk hMw hNw hword hG hm hn hgb hlb hgrb hord hordb hordW hrot
      (hFour ▸ hℓ) (hFour ▸ hgv) hpos hz (by omega)
  have hs2_r (r : ℕ) (h2 : r ≠ 2) (h3 : r ≠ 3) (h4 : r ≠ 4) : s2.regs r = s1.regs r :=
    ordCoreInitStmtK_preserves_regs r2 h2 h3 h4
  have hfoot0 (addr : ℕ) (hf : R.foot heap y0 addr) : heap ≤ addr ∧ addr < ret0 :=
    (hresp0.2.2.2.2 addr hf).resolve_left id
  -- Step 3: Store handle and branch 0 into descriptor cells
  obtain ⟨s3, r3, hs3_h, hs3_b, hrep3, hphi3, hs3_frame, hs3_regs, _⟩ :=
    storeRebuiltLevel_preserves_tool_runs (ω := ω) (st := s2) himpl.1
      ((hs2_r 51 (by decide) (by decide) (by decide)).trans ((hs1_r 51 (by decide)).trans h51))
      ((hs2_r 52 (by decide) (by decide) (by decide)).trans ((hs1_r 52 (by decide)).trans h52))
      hne (hs2_3.symm ▸ hhBelow) (hs2_3.symm ▸ hbBelow)
      (fun addr hf => hs2_3.symm ▸ (hfoot0 addr (hs2_3 ▸ hf)).1) (hs2_3.symm ▸ hrep0)
  have hs3_lt (addr : ℕ) (hlt : addr < heap) (hh' : addr ≠ handleCell) (hb' : addr ≠ branchCell) :
      s3.mem addr = st.mem addr :=
    (hs3_frame addr hh' hb').trans (hresp0.2.2.2.1 addr hlt id)
  have hs3_G : DynGraphAt s3.mem graphBase vCap eCap G :=
    dynGraphAt_of_agree hG (fun addr hlo hhi =>
      hs3_lt addr (by omega) (hDisjG addr hlo hhi).1 (hDisjG addr hlo hhi).2)
  have hs3_Len : EdgeValuesAt s3.mem lenBase 4 L fmt.precision G.E ℓ :=
    hℓ.congr (fun e he j hj => by
      have heLt := hG.2.2.1 e he
      have hm : e * L + L ≤ eCap * L := by
        have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
      exact hs3_lt _ (by omega) (hDisjLen _ (by omega) (by omega)).1 (hDisjLen _ (by omega) (by omega)).2)
  have hs3_hz : ZeroFrom s3.mem ret0 := fun addr ha => by
    have hlo := hresp0.1
    exact (hs3_frame addr (by omega) (by omega)).trans (hresp0.2.2.1 addr ha)
  obtain ⟨hCopyR, hCLRoom⟩ := hTailRoom ret0 hresp0.1 hresp0.2.1
  -- Step 4: Run `ordReadoutNextLevelK`
  obtain ⟨s4, vcH, ecH, nextOrdWords, Lw, c4, y4, r4, hLwLe, hrep4, hH4, hLen4, hGrad4,
      hOrd4, hOrdLe4, h6Lo4, hHEnd4, h6Disj4, h7Lo4, hLenEnd4, h7Disj4, h4Lo4, h4Hi4, hz4, hs4_frame, hs4_footLt,
      hs4_footIn, hs4_regs, hc4⟩ :=
    ordReadoutNextLevelK_runs (ω := ω) (st := s3) ℓ hFour himpl hCoreLenProc hEdgeProc
      hSign hMul hDiv hCopy (hs3_regs.symm ▸ hs2_2) (hs3_regs.symm ▸ hs2_3) (hs3_regs.symm ▸ hs2_4)
      ((hs3_regs.symm ▸ hs2_r 6 (by decide) (by decide) (by decide)).trans ((hs1_r 6 (by decide)).trans hg))
      ((hs3_regs.symm ▸ hs2_r 7 (by decide) (by decide) (by decide)).trans ((hs1_r 7 (by decide)).trans hl))
      ((hs3_regs.symm ▸ hs2_r 67 (by decide) (by decide) (by decide)).trans ((hs1_r 67 (by decide)).trans h67))
      hk hwk (by omega) hw9 hs3_G (hgb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      hs3_Len (hlb.trans hresp0.1)
      (fun addr _ hhi hf => by have := (hfoot0 addr hf).1; omega)
      (by simpa only [hs3_regs, hs2_3] using hrep3) hIn0
      (fun addr hf => (hfoot0 addr hf).2) hs3_hz hHE hCoreLenFits hCopyR hCLRoom
      (by have := hresp0.2.1; omega)
  -- Step 5: Advance descriptor cursors `(51, 52)`
  have hs4_51 : s4.regs 51 = handleCell :=
    (hs4_regs 51 (by omega)).trans (hs3_regs.symm ▸
      ((hs2_r 51 (by decide) (by decide) (by decide)).trans ((hs1_r 51 (by decide)).trans h51)))
  have hs4_52 : s4.regs 52 = branchCell :=
    (hs4_regs 52 (by omega)).trans (hs3_regs.symm ▸
      ((hs2_r 52 (by decide) (by decide) (by decide)).trans ((hs1_r 52 (by decide)).trans h52)))
  obtain ⟨out, r5, hout51, hout52, houtRegs, houtMem⟩ :=
    rebuildAdvanceDescriptors_runs (ω := ω) (st := s4) hs4_51 hs4_52 hhNextW hbNextW
  have rFull : Runs w p ω (ordRebuildLevelBodyK init (op 3) (op 2) coreLenProc (op 5)) st .normal out
      (5 + (c2 + (7 + (c4 + 9 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 7, _, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, c4, 9, r4, r5, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hnf0 (addr : ℕ) (hlt : addr < heap) : ¬ R.foot heap y0 addr :=
    fun hf => by have := (hfoot0 addr hf).1; omega
  have h6Eq := houtRegs 6 (by decide) (by decide)
  have h7Eq := houtRegs 7 (by decide) (by decide)
  have h8Eq := houtRegs 8 (by decide) (by decide)
  have h9Eq := houtRegs 9 (by decide) (by decide)
  have h4Eq := houtRegs 4 (by decide) (by decide)
  refine ⟨out, vcH, ecH, nextOrdWords, Lw, _, y4, rFull, hLwLe, ?_, ?_,
    (houtRegs 19 (by decide) (by decide)).trans ((hs4_regs 19 (by omega)).trans
      (hs3_regs.symm ▸ ((hs2_r 19 (by decide) (by decide) (by decide)).trans ((hs1_r 19 (by decide)).trans hIdx)))),
    hout51, hout52, houtMem.symm ▸ hrep4,
    by rw [houtMem, h6Eq]; exact hH4,
    by rw [houtMem, h7Eq]; exact hLen4,
    by rw [h8Eq, h7Eq]; exact hGrad4,
    by rw [houtMem, h9Eq]; exact hOrd4,
    hOrdLe4,
    by rw [h6Eq]; exact hresp0.1.trans h6Lo4,
    by rw [h6Eq, h4Eq]; exact hHEnd4,
    fun addr hlo hhi => h6Disj4 addr (h6Eq ▸ hlo) (h6Eq ▸ hhi),
    by rw [h7Eq]; exact hresp0.1.trans h7Lo4,
    by rw [h7Eq, h4Eq]; exact hLenEnd4,
    fun addr hlo hhi => h7Disj4 addr (h7Eq ▸ hlo) (h7Eq ▸ hhi),
    by rw [h4Eq]; exact hresp0.1.trans h4Lo4,
    by rw [h4Eq]; have := hresp0.2.1; dsimp only at h4Hi4 ⊢; omega,
    by rw [houtMem, h4Eq]; exact hz4,
    fun addr hlt hneH hneB => by
      rw [houtMem, hs4_frame addr (hlt.trans_le hresp0.1) (hnf0 addr hlt)]
      exact hs3_lt addr hlt hneH hneB,
    fun addr hf => by
      rw [h4Eq]
      rcases hs4_footIn addr hf with hy0 | ⟨hlo, hhi⟩
      · exact ⟨(hfoot0 addr hy0).1, (hfoot0 addr hy0).2.trans_le h4Lo4⟩
      · exact ⟨hresp0.1.trans hlo, hhi⟩,
    fun r hr => by
      rw [houtRegs r (by omega) (by omega), hs4_regs r (by omega), hs3_regs,
        hs2_r r (by omega) (by omega) (by omega), hs1_r r (by omega)],
    ?_⟩
  · rw [houtMem, hs4_frame handleCell (hhBelow.trans_le hresp0.1) (hnf0 handleCell hhBelow),
      hs3_h, hs3_regs, hs2_3]
  · rw [houtMem, hs4_frame branchCell (hbBelow.trans_le hresp0.1) (hnf0 branchCell hbBelow), hs3_b]
  · rw [houtMem]
    rw [hs3_regs, hs2_3] at hphi3
    have hphiEq : R.phi heap y0 s3.mem = R.phi heap y0 s2.mem := hphi3
    rw [hphiEq] at hc4
    dsimp only at hc2 hc4 ⊢
    omega

end LevelExecution

end MinCostFlow.MinRatio
