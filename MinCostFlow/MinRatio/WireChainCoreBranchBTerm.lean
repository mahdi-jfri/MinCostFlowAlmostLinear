module

public import MinCostFlow.MinRatio.WireChainCoreOps
public import MinCostFlow.MinRatio.WireRebuildSuffixK
import MinCostFlow.MinRatio.WireRebuildSuffixLoopKBase
import WordRAM.Tactic

/-!
# Branch B terminal level-`d` update step (`WireChainCoreBranchBTerm`)

Provides `wireBranchBTerminalStep` and `wireBranchBTerminalStep_runs` for the terminal level-`d`
step in Branch B of `ordChainUpdateCoreBody`:
- If `mem[curBatch] = 0` (`curU = []`), executes `.nop` in `O(1)` without modifying memory.
- If `mem[curBatch] ≠ 0` (`curU ≠ []`), reads `G'_d` and `ℓ'_d` from level `d - 1` via
  `ordReadoutNextLevelK` and installs the rebuilt terminal structure at
  `(handleBase + d, branchBase + d)` via `rebuildTerminalRuntimeStep`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Conditional terminal rebuild at `idx = d`: executes `.nop` if `mem[curBatch] = 0` (`curU = []`),
and otherwise reads `G'_d` and `ℓ'_d` from level `d - 1` via `ordReadoutNextLevelK` and installs
the rebuilt terminal structure via `rebuildTerminalRuntimeStep`. -/
@[expose] def wireBranchBTerminalStep
    (readGraph readLSF coreLenProc readOrd lastInit : ℕ) : Stmt :=
  .cond (.load (.reg 10))
    (.assign 22 (.bin .sub (.reg 75) (.const 1)) ;;
     .assign 3 (.load (.bin .add (.reg 77) (.reg 22))) ;;
     .assign 2 (.load (.bin .add (.reg 78) (.reg 22))) ;;
     .assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22))) ;;
     .assign 7 (.load (.bin .add (.reg 83) (.reg 22))) ;;
     .assign 67 (.reg 94) ;;
     .assign 68 (.reg 95) ;;
     ordReadoutNextLevelK readGraph readLSF coreLenProc readOrd ;;
     .assign 51 (.bin .add (.reg 77) (.reg 75)) ;;
     .assign 52 (.bin .add (.reg 78) (.reg 75)) ;;
     rebuildTerminalRuntimeStep lastInit)
    .nop

theorem wireBranchBTerminalStep_noRand (readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (wireBranchBTerminalStep readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchBTerminalStep, ordReadoutNextLevelK_noRand, rebuildTerminalRuntimeStep,
    rebuildLastLevelRuntime, storeRebuiltLevel, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- Execute `wireBranchBTerminalStep` at `idx = d`: if `curU = []`, executes `.nop` in `O(1)`
without changing memory; if `curU ≠ []`, reads `G'_d` and `ℓ'_d` from level `d - 1` and installs
the rebuilt terminal structure at `(handleBase + d, branchBase + d)`. -/
theorem wireBranchBTerminalStep_runs
    {w L P m capExp lastMul intCapMax forestEdgeCap drainUnit stretchPrec
      dgCap ecCap lastSpace termUpdSpace termUpdCost
      initCore coreLenProc edgeProc signExt mul intDiv copy lastInit
      coreHPrev gPtrPrev lPtrPrev vcPrev ecPrev curBatch curHeap
      handleBase branchBase levelMeta : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {levelSpace levelCost updStepSpace updStepCost : ℕ → ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (ch : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update) (ℓPrev : ℕ → ℝ)
    (coreTokPrev0 : Rcore.τ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (hdW : cfg.P.d < 2 ^ w) (hkW : cfg.P.k < 2 ^ w) (hw16 : 16 ≤ 2 ^ w)
    (hCoreImpl : Rcore.Implements w p initCore opCore
      (sparseCoreOrdMachineContractK fmt L cfg.T (ch.G (cfg.P.d - 1)) cfg.P.k
        (ch.lvlM (cfg.P.d - 1)) ch.N₀ vcPrev ecPrev capExp Psc (allocation (cfg.P.d - 1))))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl : ∀ vc ec,
      (LastLevelProgram.lastLevelRepresentation vc ec 4 L fmt.precision curG.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L curG vc ec lastMul stretchPrec lastAlloc))
    (hOps : UpdateCoreOpsHyp (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (lastMul := lastMul) (intCapMax := intCapMax) (forestEdgeCap := forestEdgeCap)
      (drainUnit := drainUnit) (coreSpace := coreSpace) (coreFixed := coreFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc)
      (allocation := allocation) (lastAlloc := lastAlloc)
      Rcore dgCap ecCap levelSpace levelCost updStepSpace updStepCost lastSpace termUpdSpace
      termUpdCost)
    (hRegs :
      st.regs 4 = curHeap ∧ st.regs 10 = curBatch ∧ st.regs 75 = cfg.P.d ∧
      st.regs 77 = handleBase ∧ st.regs 78 = branchBase ∧ st.regs 83 = levelMeta ∧
      st.regs 94 = L ∧ st.regs 95 = P)
    (hBatchLen : st.mem curBatch = curU.length)
    (hPrevCells :
      st.mem (handleBase + (cfg.P.d - 1)) = coreHPrev ∧
      st.mem (branchBase + (cfg.P.d - 1)) = ch.bran (cfg.P.d - 1) ∧
      st.mem (levelMeta + cfg.P.d + (cfg.P.d - 1)) = gPtrPrev ∧
      st.mem (levelMeta + (cfg.P.d - 1)) = lPtrPrev)
    (hBrLt : ch.bran (cfg.P.d - 1) < cfg.P.k)
    (hCoreH_W : coreHPrev < 2 ^ w)
    (hRepPrev : Rcore.rep coreHPrev (chainLevelOrdAbs ch (cfg.P.d - 1)) coreTokPrev0 st.mem)
    (hFootPrev : ∀ a, Rcore.foot coreHPrev coreTokPrev0 a → a < curHeap)
    (hGPrev : DynGraphAt st.mem gPtrPrev vcPrev ecPrev (ch.G (cfg.P.d - 1)))
    (hLenPrev : EdgeValuesAt st.mem lPtrPrev 4 L P (ch.G (cfg.P.d - 1)).E ℓPrev)
    (hNonEmpty : curU ≠ [] →
      let ℓd := coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1))) ℓPrev
      SparseCoreOrdInput cfg.T cfg.P.k (ch.lvlM (cfg.P.d - 1)) ch.N₀
        (ch.scState (cfg.P.d - 1)) (ch.G (cfg.P.d - 1))
        (ch.levelOrd (cfg.P.d - 1)) (ch.updCount (cfg.P.d - 1)) ∧
      curG = cfg.T.S (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1)) ∧
      curG.E ⊆ (ch.G (cfg.P.d - 1)).E ∧
      (∀ e ∈ curG.E, ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P = ℓd e) ∧
      cfg.L.build curG (fun e => if e ∈ curG.E then ℓd e else 0) = cfg.L.build curG ℓd ∧
      (∀ e ∈ curG.E, 0 < ℓd e) ∧
      (∀ e ∈ curG.E, 2 * (2 : ℝ) ^ stretchPrec * lastLevelStretchBound curG ℓd e < Num.capacity 4 L))
    (hBelow :
      handleBase + cfg.P.d < curHeap ∧ branchBase + cfg.P.d < curHeap ∧
      levelMeta + 2 * cfg.P.d ≤ curHeap ∧
      gPtrPrev + dynGraphSize vcPrev ecPrev ≤ curHeap ∧ lPtrPrev + ecPrev * L ≤ curHeap ∧
      handleBase + cfg.P.d ≠ branchBase + cfg.P.d)
    (hDisj :
      (∀ a, gPtrPrev ≤ a → a < gPtrPrev + dynGraphSize vcPrev ecPrev →
        ¬ Rcore.foot coreHPrev coreTokPrev0 a) ∧
      (∀ a, lPtrPrev ≤ a → a < lPtrPrev + ecPrev * L → ¬ Rcore.foot coreHPrev coreTokPrev0 a) ∧
      ¬ Rcore.foot coreHPrev coreTokPrev0 (handleBase + cfg.P.d) ∧
      ¬ Rcore.foot coreHPrev coreTokPrev0 (branchBase + cfg.P.d))
    (hz : ZeroFrom st.mem curHeap)
    (hRoom : curHeap + termUpdSpace < 2 ^ w) :
    let ℓd := coreLen (cfg.T.lsfs (ch.scState (cfg.P.d - 1)) (ch.bran (cfg.P.d - 1))) ℓPrev
    ∃ (out : State) (cost : ℕ) (coreTokPrev' : Rcore.τ),
      Runs w p ω
        (wireBranchBTerminalStep (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal out cost ∧
      curHeap ≤ out.regs 4 ∧ out.regs 4 ≤ curHeap + termUpdSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      Rcore.rep coreHPrev (chainLevelOrdAbs ch (cfg.P.d - 1)) coreTokPrev' out.mem ∧
      (∀ a, Rcore.foot coreHPrev coreTokPrev' a →
        Rcore.foot coreHPrev coreTokPrev0 a ∨ (curHeap ≤ a ∧ a < out.regs 4)) ∧
      (curU = [] →
        out.mem = st.mem ∧ out.regs 4 = curHeap ∧ coreTokPrev' = coreTokPrev0 ∧ cost ≤ 10) ∧
      (curU ≠ [] →
        ∃ vcLast ecLast termTok,
          out.mem (branchBase + cfg.P.d) = 0 ∧
          curHeap ≤ out.mem (handleBase + cfg.P.d) ∧
          (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P curG.E).rep
            (out.mem (handleBase + cfg.P.d)) (cfg.L.build curG ℓd) termTok out.mem ∧
          (∀ a, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P curG.E).foot
              (out.mem (handleBase + cfg.P.d)) termTok a →
            curHeap ≤ a ∧ a < out.regs 4 ∧ ¬ Rcore.foot coreHPrev coreTokPrev' a) ∧
          (∀ a < curHeap, ¬ Rcore.foot coreHPrev coreTokPrev0 a →
            a ≠ handleBase + cfg.P.d → a ≠ branchBase + cfg.P.d → out.mem a = st.mem a) ∧
          cost + Rcore.phi coreHPrev coreTokPrev' out.mem ≤
            termUpdCost + lastMul * (cfg.L.cost curG + 1) +
              Rcore.phi coreHPrev coreTokPrev0 st.mem) := by
  dsimp only
  set d := cfg.P.d
  set ℓd := coreLen (cfg.T.lsfs (ch.scState (d - 1)) (ch.bran (d - 1))) ℓPrev
  obtain ⟨hr4, hr10, hr75, hr77, hr78, hr83, hr94, hr95⟩ := hRegs
  obtain ⟨hHPrev, hBPrev, hGPrevCell, hLPrevCell⟩ := hPrevCells
  obtain ⟨hHBLt, hBBLt, hLMLt, hGLe, hLLe, hHBNe⟩ := hBelow
  obtain ⟨hDisjG, hDisjL, hDisjH, hDisjB⟩ := hDisj
  by_cases hEmp : curU = []
  · have hZero : st.mem curBatch = 0 := by rw [hBatchLen, hEmp]; rfl
    have rCond : Runs w p ω
        (wireBranchBTerminalStep (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal st (1 + 2 + 1) :=
      runs_cond_iff.mpr ⟨0, 1, by simp [Expr.eval, hr10, hZero],
        by simpa using (runs_nop_iff (w := w) (p := p) (ω := ω) (st := st)).mpr ⟨rfl, rfl, rfl⟩, rfl⟩
    refine ⟨st, 4, coreTokPrev0, rCond, by omega, by omega, by rwa [hr4], fun _ _ => rfl,
      hRepPrev, fun _ h => Or.inl h, fun _ => ⟨rfl, hr4, rfl, by omega⟩, fun h => absurd hEmp h⟩
  · have hPos : curU.length ≠ 0 := (List.length_pos_of_ne_nil hEmp).ne'
    obtain ⟨hInPrev, hCurGEq, hCurSub, hCurFits, hBuildEq, hCurPos, hCurStr⟩ := hNonEmpty hEmp
    let s1 := { st with regs := Function.update st.regs 22 (d - 1) }
    let s2 := { s1 with regs := Function.update s1.regs 3 coreHPrev }
    let s3 := { s2 with regs := Function.update s2.regs 2 (ch.bran (d - 1)) }
    let s4 := { s3 with regs := Function.update s3.regs 6 gPtrPrev }
    let s5 := { s4 with regs := Function.update s4.regs 7 lPtrPrev }
    let s6 := { s5 with regs := Function.update s5.regs 67 L }
    let s7 := { s6 with regs := Function.update s6.regs 68 P }
    have r1 : Runs w p ω (.assign 22 (.bin .sub (.reg 75) (.const 1))) st .normal s1 4 :=
      runs_assign_iff.mpr ⟨d - 1, by simp [Expr.eval, BinOp.eval, hr75, show 1 < 2 ^ w by omega,
        show d - 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 77) (.reg 22)))) s1 .normal s2 5 :=
      runs_assign_iff.mpr ⟨coreHPrev, by simp [Expr.eval, BinOp.eval, s1, hr77, show handleBase + (d - 1) < 2 ^ w by omega, hHPrev], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 78) (.reg 22)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨ch.bran (d - 1), by simp [Expr.eval, BinOp.eval, s2, s1, hr78, show branchBase + (d - 1) < 2 ^ w by omega, hBPrev], rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.assign 6 (.load (.bin .add (.bin .add (.reg 83) (.reg 75)) (.reg 22)))) s3 .normal s4 7 :=
      runs_assign_iff.mpr ⟨gPtrPrev, by simp [Expr.eval, BinOp.eval, s3, s2, s1, hr83, hr75,
        show levelMeta + d < 2 ^ w by omega, show levelMeta + d + (d - 1) < 2 ^ w by omega, hGPrevCell], rfl, rfl, rfl⟩
    have r5 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 83) (.reg 22)))) s4 .normal s5 5 :=
      runs_assign_iff.mpr ⟨lPtrPrev, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, hr83,
        show levelMeta + (d - 1) < 2 ^ w by omega, hLPrevCell], rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 67 (.reg 94)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨L, by simp [Expr.eval, s5, s4, s3, s2, s1, hr94], rfl, rfl, rfl⟩
    have r7 : Runs w p ω (.assign 68 (.reg 95)) s6 .normal s7 2 :=
      runs_assign_iff.mpr ⟨P, by simp [Expr.eval, s6, s5, s4, s3, s2, s1, hr95], rfl, rfl, rfl⟩
    have hTermSp := hOps.termUpdSpaceDom curG.m (ch.lvlM (d - 1)) ch.N₀
      (ordRotWords (chainLevelOrdAbs ch (d - 1)) (ch.bran (d - 1)))
    have hTermCost := hOps.termUpdCostDom curG.m (ch.lvlM (d - 1)) ch.N₀
      (ordRotWords (chainLevelOrdAbs ch (d - 1)) (ch.bran (d - 1)))
    dsimp only [chainLevelOrdAbs, d] at hTermSp hTermCost
    obtain ⟨s8, vcH, ecH, _, Lw, cRead, tok1, r8, hLw8, hRep8, hDG8, hLen8, _, _, _,
        _, h6End8, _, _, h7End8, _, h8Lo, h8Hi, hz8, hFr8, hFoot8Lt, hFoot8In, hs8_regs, hc8⟩ :=
      ordReadoutNextLevelK_runs (w := w) (L := L) (k := cfg.P.k) (M := ch.lvlM (d - 1)) (N := ch.N₀)
        (vCap := vcPrev) (eCap := ecPrev) (capExp := capExp) (init := initCore)
        (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
        (intDiv := intDiv) (copy := copy) (branch := ch.bran (d - 1)) (handle := coreHPrev)
        (heap := curHeap) (graphBase := gPtrPrev) (lenBase := lPtrPrev) (st := s7) (ω := ω)
        ℓPrev hFour hCoreImpl hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
        (by simp [s7, s6, s5, s4, s3]) (by simp [s7, s6, s5, s4, s3, s2])
        (by simp [s7, s6, s5, s4, s3, s2, s1, hr4]) (by simp [s7, s6, s5, s4])
        (by simp [s7, s6, s5]) (by simp [s7, s6]) hBrLt hkW hCoreH_W (by omega)
        hGPrev hGLe hDisjG (hPrec.symm ▸ hLenPrev) hLLe hDisjL hRepPrev hInPrev hFootPrev hz
        (hCurGEq.symm ▸ hCurSub) (hCurGEq.symm ▸ (hPrec ▸ hCurFits))
        (fun m1 h1 rawG vcH ecH hDG hh1 hh2 => by
          obtain ⟨hE, hDgH, _⟩ := hOps.op3Placement _ m1 curHeap h1 rawG vcH ecH hDG hh1 hh2
          exact ⟨hE, by omega⟩)
        (fun m2 vcH ecH vcF ecF h2 h3 Lw' hDGEx hLSF hLw' _ hh2Hi hh2 hh3 => by
          obtain ⟨m1, rawG, hDG⟩ := hDGEx
          obtain ⟨_, hDgH, hEcH⟩ := hOps.op3Placement _ m1 h2 h2 rawG vcH ecH hDG le_rfl (by omega)
          obtain ⟨_, _, _, hS2, hSE, _⟩ := hOps.op2Placement (ch.G (d - 1)) coreHPrev coreTokPrev0
            m2 h2 h3 vcF ecF Lw' _ hLSF hh2 hh3
          have hEcMul := Nat.mul_le_mul_right L hEcH
          have hMonoSp := Nat.mul_le_mul_left curG.m (wireCoreLenEdgeSpace_mono (max_le_max_left L hLw'))
          have hmEq : (cfg.T.S (ch.scState (d - 1)) (ch.bran (d - 1))).m = curG.m := congrArg MGraph.m hCurGEq.symm
          dsimp only [chainLevelOrdAbs, d] at hDG hLSF hLw' hMonoSp ⊢
          rw [hmEq]
          exact ⟨hS2, fun e he => (hSE e (hCurSub (hCurGEq.symm ▸ he))).1,
            fun e he => (hSE e (hCurSub (hCurGEq.symm ▸ he))).2, by omega⟩)
        (by omega)
    dsimp only [chainLevelOrdAbs] at hDG8 hLen8 h8Hi hc8
    have hmEq8 : (cfg.T.S (ch.scState (d - 1)) (ch.bran (d - 1))).m = curG.m := congrArg MGraph.m hCurGEq.symm
    obtain ⟨_, hDgH8, hEcH8⟩ := hOps.op3Placement _ s8.mem curHeap curHeap (s8.regs 6) vcH ecH hDG8 le_rfl (by omega)
    have hEcMul8 := Nat.mul_le_mul_right L hEcH8
    have hMonoSp8 := Nat.mul_le_mul_left curG.m (wireCoreLenEdgeSpace_mono (max_le_max_left L hLw8))
    have hMonoCost8 := Nat.mul_le_mul_left curG.m (Nat.add_le_add_right (wireCoreLenEdgeCost_mono (max_le_max_left L hLw8)) 30)
    have h8Hi' : s8.regs 4 ≤ curHeap + 7 + dynGraphSize vcH ecH + ecH * L +
        curG.m * wireCoreLenEdgeSpace (max L Lw) +
        ordRotWords (chainLevelOrdAbs ch (d - 1)) (ch.bran (d - 1)) := by
      rw [hmEq8] at h8Hi; exact h8Hi
    dsimp only [chainLevelOrdAbs, d] at h8Hi' hMonoSp8 hMonoCost8 hc8
    have h8Room : s8.regs 4 + lastSpace < 2 ^ w := by omega
    let s9 := { s8 with regs := Function.update s8.regs 51 (handleBase + d) }
    let s10 := { s9 with regs := Function.update s9.regs 52 (branchBase + d) }
    have r9 : Runs w p ω (.assign 51 (.bin .add (.reg 77) (.reg 75))) s8 .normal s9 4 :=
      runs_assign_iff.mpr ⟨handleBase + d, by
        simp [Expr.eval, BinOp.eval, hs8_regs 77 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))),
          hs8_regs 75 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))),
          s7, s6, s5, s4, s3, s2, s1, hr77, hr75, show handleBase + d < 2 ^ w by omega], rfl, rfl, rfl⟩
    have r10 : Runs w p ω (.assign 52 (.bin .add (.reg 78) (.reg 75))) s9 .normal s10 4 :=
      runs_assign_iff.mpr ⟨branchBase + d, by
        simp [Expr.eval, BinOp.eval, s9, hs8_regs 78 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))),
          hs8_regs 75 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))),
          s7, s6, s5, s4, s3, s2, s1, hr78, hr75, show branchBase + d < 2 ^ w by omega], rfl, rfl, rfl⟩
    have hLastSp := hOps.lastSpaceDom (s8.regs 6) (s8.regs 7) (s8.regs 4)
    obtain ⟨s11, ret11, cTerm, termTok, r11, hTermH11, hTermB11, hs11_4, hTermRep11, hz11,
        hTermFoot11, hFrTerm11, hRet11Lo, hRet11Hi, hcTerm⟩ :=
      wireRebuildTerminalStep_runs (w := w) (L := L) (init := lastInit) (graph := s8.regs 6)
        (lengths := s8.regs 7) (heap := s8.regs 4) (vCap := vcH) (eCap := ecH)
        (multiplier := lastMul) (stretchPrecision := stretchPrec)
        (handleCell := handleBase + d) (branchCell := branchBase + d)
        (st := s10) (ω := ω) (hLastImpl vcH ecH)
        (by simp [s10, s9]) (by simp [s10, s9]) (by simp [s10, s9])
        (by simp [s10, s9, hs8_regs 67 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), s7, s6])
        (by simp [s10, s9, hs8_regs 68 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), s7, hPrec])
        hLWord (hPrec.symm ▸ hPWord) hFour (hPrec.symm ▸ hWidth) ℓd
        (by show DynGraphAt s8.mem (s8.regs 6) vcH ecH curG; rw [hCurGEq]; exact hDG8) h6End8 h7End8
        (by show EdgeValuesAt s8.mem (s8.regs 7) fmt.limbBits L fmt.precision curG.E ℓd
            rw [hFour, hCurGEq]; exact hLen8)
        (hFour.symm ▸ hCurStr) hCurPos hz8 (by omega) hBuildEq
        (by simp [s10, s9]) (by simp [s10]) hHBNe (by omega) (by omega)
    have hLoc11 := hCoreLocal coreHPrev (chainLevelOrdAbs ch (d - 1)) tok1 s8.mem s11.mem
      (fun a ha => (hFrTerm11 a (hFoot8Lt a ha)
        (fun h => (hFoot8In a ha).elim (fun h0 => hDisjH (h ▸ h0)) (fun ⟨hlo, _⟩ => by subst h; omega))
        (fun h => (hFoot8In a ha).elim (fun h0 => hDisjB (h ▸ h0)) (fun ⟨hlo, _⟩ => by subst h; omega))).symm)
    have hs11_ge70 (r : ℕ) (hr : 70 ≤ r) : s11.regs r = st.regs r := by
      have h1' : s11.regs r = s10.regs r :=
        runs_preserves_above (s := rebuildTerminalRuntimeStep lastInit) (by omega : 53 ≤ r) rfl r11
      rw [h1']; simp only [s10, s9, Function.update_of_ne (by omega : r ≠ 52),
        Function.update_of_ne (by omega : r ≠ 51)]
      rw [hs8_regs r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr)))))]
      simp [s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 68),
        Function.update_of_ne (by omega : r ≠ 67), Function.update_of_ne (by omega : r ≠ 7),
        Function.update_of_ne (by omega : r ≠ 6), Function.update_of_ne (by omega : r ≠ 2),
        Function.update_of_ne (by omega : r ≠ 3), Function.update_of_ne (by omega : r ≠ 22)]
    have rThen := runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 7, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 2, _, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, cRead, _, r8,
      runs_seq_iff.mpr (Or.inr ⟨s9, 4, _, r9,
      runs_seq_iff.mpr (Or.inr ⟨s10, 4, cTerm, r10, r11, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
      rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    have rCond : Runs w p ω
        (wireBranchBTerminalStep (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal s11 _ :=
      runs_cond_iff.mpr ⟨curU.length, _, by simp [Expr.eval, hr10, hBatchLen],
        by simpa [hPos] using rThen, rfl⟩
    refine ⟨s11, _, tok1, rCond, by rw [hs11_4]; exact h8Lo.trans hRet11Lo,
      by rw [hs11_4]; omega, hs11_4.symm ▸ hz11, hs11_ge70,
      hLoc11.1 hRep8,
      fun a ha => by
        rcases hFoot8In a ha with h0 | ⟨hlo, hhi⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hlo, hhi.trans_le (hs11_4.symm ▸ hRet11Lo)⟩,
      fun h => absurd h hEmp,
      fun _ => ⟨vcH, ecH, termTok, hTermB11, hTermH11.symm ▸ h8Lo,
        hTermH11.symm ▸ (hPrec ▸ hTermRep11),
        fun a ha => by
          rw [hTermH11] at ha
          have hf := hTermFoot11 a (hPrec.symm ▸ ha)
          exact ⟨h8Lo.trans hf.1, hs11_4.symm ▸ hf.2, fun hfc => by have := hFoot8Lt a hfc; omega⟩,
        fun a ha hnf hnh hnb => (hFrTerm11 a (ha.trans_le h8Lo) hnh hnb).trans (hFr8 a ha hnf),
        ?_⟩⟩
    have hPhi11 : Rcore.phi coreHPrev tok1 s11.mem = Rcore.phi coreHPrev tok1 s8.mem := hLoc11.2.symm
    have hPhi7 : Rcore.phi coreHPrev coreTokPrev0 s7.mem = Rcore.phi coreHPrev coreTokPrev0 st.mem := rfl
    rw [hPhi11]; rw [hmEq8, hPhi7] at hc8
    simp only [Expr.size]
    clear rCond rThen r11 r8 hTermRep11 hRep8 hDG8 hLen8 hNonEmpty
    omega

end MinCostFlow.MinRatio
