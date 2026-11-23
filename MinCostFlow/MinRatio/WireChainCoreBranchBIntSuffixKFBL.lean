module

public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBL
public import MinCostFlow.MinRatio.WireShiftDeepPhase3
import WordRAM.Tactic

/-!
# The suffix rebuild of the interior rebuild step under `KFBL` (`WireChainCoreBranchBIntSuffixKFBL`)

The second part of the interior rebuild step of Branch B sets the registers that the suffix
rebuild reads (`wireBranchBIntSetupStmt`) and rebuilds the levels `idx, …, d` from the graph of
level `idx`, its lengths and the order list of level `idx - 1`
(`ordRebuildSuffixProgramKFBLStore`). `wireBranchBIntSuffixKFBL_runs` is
`ordRebuildSuffixProgramKFBLStore_runs` (`WireRebuildSuffixLoopKFBL.lean`) with the registers of
the chain-update core in place of the registers of the suffix rebuild: the setup loads them from
the core registers `75, 76, 77, 78, 82, 83, 94, 95, 96` and the two cells
`mem (lvlMTable - 1) = N₀` (the cell of `N₀` just below the level sizes, as in Branch A) and
`mem (levelMeta + idx)` (the lengths of level `idx`). The registers
from `70` on do not change.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- The registers of the suffix rebuild from the registers of the chain-update core at level
`idx = reg 96`. -/
@[expose] def wireBranchBIntSetupStmt : Stmt :=
  .assign 1 (.reg 76) ;;
  .assign 7 (.load (.bin .add (.reg 83) (.reg 96))) ;;
  .assign 8 (.reg 7) ;;
  .assign 20 (.reg 96) ;;
  .assign 21 (.reg 75) ;;
  .assign 51 (.bin .add (.reg 77) (.reg 96)) ;;
  .assign 52 (.bin .add (.reg 78) (.reg 96)) ;;
  .assign 56 (.load (.bin .sub (.reg 82) (.const 1))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 67 (.reg 94) ;;
  .assign 68 (.reg 95)

/-- The setup and the suffix rebuild of the interior rebuild step. -/
@[expose] def wireBranchBIntSuffixKFBL (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    Stmt :=
  wireBranchBIntSetupStmt ;;
  ordRebuildSuffixProgramKFBLStore init readGraph readLSF coreLenProc readOrd lastInit

theorem wireBranchBIntSuffixKFBL_noRand
    (init readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (wireBranchBIntSuffixKFBL init readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchBIntSuffixKFBL, wireBranchBIntSetupStmt, Stmt.NoRand,
    ordRebuildSuffixProgramKFBLStore_noRand]

private theorem runs_assign_seq' {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr}
    {s : Stmt} {st sOut : State} {v c : ℕ} (he : e.eval w st = some v)
    (hr : Runs w p ω s { st with regs := Function.update st.regs r v } .normal sOut c) :
    Runs w p ω (.assign r e ;; s) st .normal sOut (e.size + 1 + c + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, c, runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr,
    rfl⟩)

/-- One run of `wireBranchBIntSetupStmt`: it changes only the twelve registers that it sets. -/
theorem wireBranchBIntSetupStmt_runs {w k d first lPtr N0 handle handleBase branchBase lvlMTable
      levelLens L prec : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hRegs : st.regs 73 = handle ∧ st.regs 75 = d ∧ st.regs 76 = k ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 82 = lvlMTable ∧ st.regs 83 = levelLens ∧
      st.regs 94 = L ∧ st.regs 95 = prec ∧ st.regs 96 = first)
    (hw1 : 1 < 2 ^ w) (hCells : st.mem (lvlMTable - 1) = N0 ∧ st.mem (levelLens + first) = lPtr)
    (hAddrW : lvlMTable < 2 ^ w ∧ levelLens + first < 2 ^ w ∧ handleBase + first < 2 ^ w ∧
      branchBase + first < 2 ^ w) :
    ∃ (out : State) (cost : ℕ), Runs w p ω wireBranchBIntSetupStmt st .normal out cost ∧
      out.mem = st.mem ∧
      out.regs 1 = k ∧ out.regs 7 = lPtr ∧ out.regs 8 = lPtr ∧ out.regs 20 = first ∧
      out.regs 21 = d ∧ out.regs 51 = handleBase + first ∧ out.regs 52 = branchBase + first ∧
      out.regs 56 = N0 ∧ out.regs 57 = lvlMTable ∧ out.regs 58 = levelLens ∧ out.regs 67 = L ∧
      out.regs 68 = prec ∧
      (∀ r, r ≠ 1 → r ≠ 7 → r ≠ 8 → r ≠ 20 → r ≠ 21 → r ≠ 51 → r ≠ 52 → r ≠ 56 → r ≠ 57 →
        r ≠ 58 → r ≠ 67 → r ≠ 68 → out.regs r = st.regs r) ∧
      cost ≤ 60 := by
  obtain ⟨_, hr75, hr76, hr77, hr78, hr82, hr83, hr94, hr95, hr96⟩ := hRegs
  obtain ⟨hH10, hLC⟩ := hCells
  obtain ⟨hHW, hLW, hHBW, hBBW⟩ := hAddrW
  refine ⟨_, _, runs_assign_seq' (v := k) (by simp [Expr.eval, hr76]) <|
    runs_assign_seq' (v := lPtr) (by simp [Expr.eval, BinOp.eval, hr83, hr96, hLW, hLC]) <|
    runs_assign_seq' (v := lPtr) (by simp [Expr.eval]) <|
    runs_assign_seq' (v := first) (by simp [Expr.eval, hr96]) <|
    runs_assign_seq' (v := d) (by simp [Expr.eval, hr75]) <|
    runs_assign_seq' (v := handleBase + first) (by simp [Expr.eval, BinOp.eval, hr77, hr96, hHBW]) <|
    runs_assign_seq' (v := branchBase + first) (by simp [Expr.eval, BinOp.eval, hr78, hr96, hBBW]) <|
    runs_assign_seq' (v := N0) (by
      simp [Expr.eval, BinOp.eval, hr82, hw1, show lvlMTable - 1 < 2 ^ w by omega, hH10]) <|
    runs_assign_seq' (v := lvlMTable) (by simp [Expr.eval, hr82]) <|
    runs_assign_seq' (v := levelLens) (by simp [Expr.eval, hr83]) <|
    runs_assign_seq' (v := L) (by simp [Expr.eval, hr94]) <|
    runs_assign_iff.mpr ⟨prec, by simp [Expr.eval, hr95], rfl, rfl, rfl⟩, rfl, ?_⟩
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, by simp, ?_, by simp [Expr.size]⟩
  intro r h1 h7 h8 h20 h21 h51 h52 h56 h57 h58 h67 h68
  simp [Function.update_of_ne, h1, h7, h8, h20, h21, h51, h52, h56, h57, h58, h67, h68]

/-- One run of `wireBranchBIntSuffixKFBL` at level `first = reg 96`, with the heap pointer
`cur = reg 4`, the graph of level `first` at `reg 6`, its lengths at `mem (levelLens + first)` and
the order list at `reg 9`. The result is that of `ordRebuildSuffixProgramKFBLStore_runs`, with `61`
more steps for the setup, and the registers from `70` on do not change. -/
theorem wireBranchBIntSuffixKFBL_runs
    {w L depth vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      lastInit first handleBase branchBase lvlMTable levelLens heapFloor lastMul
      stretchPrec cur gPtr lPtr ordPtr handle : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {LT : LastLevelTool} {CP : ChainParams}
    {P : SparseCoreOrdParams} {allocation lastAlloc : ℕ → List ℕ → ℕ}
    {coreInitSpace nextM : ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {op : ℕ → ℕ} {opLast : ℕ → ℕ}
    {st : State} {ω : ℕ → Bool}
    (next : ChainState T CP)
    (levelSpace levelCost : ℕ → ℕ) (lastSpace : ℕ)
    (hFirstLe : first ≤ CP.d)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hWidth : fmt.precision ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w) (hDWord : depth < 2 ^ w)
    (hdW : CP.d < 2 ^ w) (hkPos : 0 < CP.k) (hkW : CP.k < 2 ^ w) (hNW : next.N₀ < 2 ^ w)
    (hw9 : 9 < 2 ^ w)
    (hRegs : st.regs 4 = cur ∧ st.regs 6 = gPtr ∧ st.regs 9 = ordPtr ∧ st.regs 73 = handle ∧
      st.regs 75 = CP.d ∧ st.regs 76 = CP.k ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 82 = lvlMTable ∧ st.regs 83 = levelLens ∧
      st.regs 94 = L ∧ st.regs 95 = fmt.precision ∧ st.regs 96 = first ∧ st.regs 98 = depth)
    (hCells : st.mem (lvlMTable - 1) = next.N₀ ∧ st.mem (levelLens + first) = lPtr)
    (hAddrW : lvlMTable < 2 ^ w ∧ levelLens + first < 2 ^ w ∧ handleBase + first < 2 ^ w ∧
      branchBase + first < 2 ^ w)
    (hReg4 : heapFloor ≤ cur)
    (hhEnd : handleBase + CP.d < heapFloor) (hbEnd : branchBase + CP.d < heapFloor)
    (hMEnd : lvlMTable + CP.d ≤ heapFloor) (hLEnd : levelLens + 2 * CP.d ≤ heapFloor)
    (hSepHB : handleBase + CP.d < branchBase ∨ branchBase + CP.d < handleBase)
    (hSepHM : handleBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ handleBase)
    (hSepBM : branchBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ branchBase)
    (hSepHL : handleBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ handleBase)
    (hSepBL : branchBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ branchBase)
    (hSepML : lvlMTable + CP.d ≤ levelLens ∨ levelLens + 2 * CP.d ≤ lvlMTable)
    (hLvlM : ∀ j, first ≤ j → j < CP.d → st.mem (lvlMTable + j) = next.lvlM j)
    (hG0 : DynGraphAt st.mem (gPtr) vCap eCap (next.G first))
    (hLen0 : EdgeValuesAt st.mem (lPtr) 4 L fmt.precision (next.G first).E
      (next.toTreeChain.chainLen next.ℓ first))
    (hOrd0 : first < CP.d → ∃ oWords,
      OrdListAt st.mem (ordPtr) (next.levelOrd first) oWords ∧
      (∀ j < oWords, st.mem (ordPtr + j) < 2 ^ w) ∧
      ordPtr + oWords ≤ cur ∧
      oWords ≤ 2 * (next.G first).n + 2 * (next.G first).m + 1)
    (hG0End : gPtr + dynGraphSize vCap eCap ≤ cur)
    (hLen0End : lPtr + eCap * L ≤ cur)
    (hG0Disj : ∀ a, gPtr ≤ a → a < gPtr + dynGraphSize vCap eCap →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hLen0Disj : ∀ a, lPtr ≤ a → a < lPtr + eCap * L →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hz0 : ZeroFrom st.mem (cur))
    (hCoreImpl : ∀ j, first ≤ j → j < CP.d →
      Rcore.Implements w p init op
        (sparseCoreOrdMachineContractKFBL fmt L depth T (next.G j) CP.k (next.lvlM j) next.N₀
          vCap eCap capExp P allocation) ∧
      SparseCoreReadoutFootAt fmt L depth T (next.G j) CP.k (next.lvlM j) next.N₀ vCap eCap
        capExp P allocation Rcore p op)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hInitSpaceLe : ∀ j, first ≤ j → j < CP.d → ∀ g l gr o h,
      allocation 6 [g, l, gr, o, CP.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h] ≤
        coreInitSpace j)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G CP.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L LT (next.G CP.d) vCap eCap lastMul stretchPrec
          lastAlloc))
    (hModelLevel : ∀ j, first ≤ j → j < CP.d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = T.initOrd CP.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (next.levelOrd j) ∧
      next.G (j + 1) = T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧
      (next.G j).m ≤ next.lvlM j ∧ (next.G j).n ≤ next.N₀ ∧
      next.lvlM j < 2 ^ w ∧ (next.lvlM j + next.N₀ + 2) ^ P.wordExp * (L + 1) < 2 ^ w ∧
      IsRotationOrder (next.G j) (next.levelOrd j) ∧
      (∀ e ∈ (next.G j).E, 0 < ℓj e) ∧
      (next.G (j + 1)).E ⊆ (next.G j).E ∧
      (∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen next.ℓ (j + 1) e) ∧
      (next.G (j + 1)).m ≤ nextM j ∧
      (next.G (j + 1)).n ≤ next.N₀ ∧
      ordRotWords (chainLevelOrdAbs next j) 0 ≤ 1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m ∧
      (j + 1 < CP.d → nextM j ≤ next.lvlM (j + 1)))
    (hModelLast :
      (next.lastK, next.lastLSFs) =
        LT.build (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) ∧
      next.lastBran = 0 ∧
      LT.build (next.G CP.d) (fun e => if e ∈ (next.G CP.d).E then
        next.toTreeChain.chainLen next.ℓ CP.d e else 0) =
        LT.build (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) ∧
      (∀ e ∈ (next.G CP.d).E, 0 < next.toTreeChain.chainLen next.ℓ CP.d e) ∧
      (∀ e ∈ (next.G CP.d).E,
        2 * (2 : ℝ) ^ stretchPrec *
          lastLevelStretchBound (next.G CP.d) (next.toTreeChain.chainLen next.ℓ CP.d) e <
          Num.capacity 4 L))
    (hLevelSpace : ∀ j, first ≤ j → j < CP.d →
      ordLevelSpace L capExp capLimit (coreInitSpace j) (next.lvlM j) next.N₀ (nextM j) ≤
        levelSpace j)
    (hLevelCost : ∀ j, first ≤ j → j < CP.d →
      P.mul * T.cost (next.scState j) +
        ordLevelLiveCost L capExp P (next.lvlM j) next.N₀
          (next.G j).n (next.G j).m (next.G (j + 1)).n (next.G (j + 1)).m
          (2 * (next.G j).n + 2 * (next.G j).m + 1)
          (2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m + 1) + 26 ≤
        levelCost j)
    (hLastSpaceLe : ∀ gBase lBase h, lastAlloc 1 [gBase, lBase, L, fmt.precision, h] ≤ lastSpace)
    (hRoom : cur + (Finset.Ico first CP.d).sum levelSpace + lastSpace < 2 ^ w)
    (hTok0 : Rcore.τ) :
    ∃ (out : State) (cost termTok : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL init (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      cur ≤ out.regs 4 ∧
      out.regs 4 ≤ cur + (Finset.Ico first CP.d).sum levelSpace + lastSpace ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d →
        out.mem (branchBase + j) = next.bran j ∧
        heapFloor ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ out.regs 4 ∧
        Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok j) a →
          heapFloor ≤ a ∧ a < out.regs 4)) ∧
      (∀ j₁ j₂, first ≤ j₁ → j₁ < CP.d → first ≤ j₂ → j₂ < CP.d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok j₂) a) ∧
      (∀ j, first + 1 ≤ j → j < CP.d →
        DynGraphAt out.mem (out.mem (levelLens + CP.d + j)) vCap eCap (next.G j) ∧
        heapFloor ≤ out.mem (levelLens + CP.d + j) ∧
        out.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap ≤ out.regs 4 ∧
        EdgeValuesAt out.mem (out.mem (levelLens + j)) 4 L fmt.precision (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        heapFloor ≤ out.mem (levelLens + j) ∧
        out.mem (levelLens + j) + eCap * L ≤ out.regs 4 ∧
        (∀ r, first ≤ r → r < CP.d →
          (∀ a, out.mem (levelLens + j) ≤ a → a < out.mem (levelLens + j) + eCap * L →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
          (∀ a, out.mem (levelLens + CP.d + j) ≤ a →
            a < out.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a)) ∧
        (∀ a, out.mem (levelLens + j) ≤ a → a < out.mem (levelLens + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G CP.d).E).foot (out.mem (handleBase + CP.d)) termTok a) ∧
        (∀ a, out.mem (levelLens + CP.d + j) ≤ a →
          a < out.mem (levelLens + CP.d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G CP.d).E).foot (out.mem (handleBase + CP.d)) termTok a)) ∧
      out.mem (branchBase + CP.d) = next.lastBran ∧
      heapFloor ≤ out.mem (handleBase + CP.d) ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision (next.G CP.d).E).rep
        (out.mem (handleBase + CP.d)) (next.lastK, next.lastLSFs) termTok out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G CP.d).E).foot (out.mem (handleBase + CP.d)) termTok a →
          heapFloor ≤ a ∧ a < out.regs 4) ∧
      (∀ j, first ≤ j → j < CP.d → ∀ a,
        (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
          (next.G CP.d).E).foot (out.mem (handleBase + CP.d)) termTok a →
        ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok j) a) ∧
      (∀ a < heapFloor,
        (a < handleBase + first ∨ handleBase + CP.d < a) →
        (a < branchBase + first ∨ branchBase + CP.d < a) →
        ((a < levelLens + (first + 1) ∨ levelLens + CP.d ≤ a) ∧
         (a < levelLens + CP.d + (first + 1) ∨ levelLens + 2 * CP.d ≤ a)) →
        out.mem a = st.mem a) ∧
      cost + (Finset.Ico first CP.d).sum
          (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok j) out.mem) ≤
        (Finset.Ico first CP.d).sum (fun j => levelCost j + 9) +
          lastMul * (LT.cost (next.G CP.d) + 1) + 89 := by
  obtain ⟨hr4, hr6, hr9, hr73, hr75, hr76, hr77, hr78, hr82, hr83, hr94, hr95, hr96, hr98⟩ := hRegs
  obtain ⟨s1, c1, r1, hm1, h1_1, h1_7, h1_8, h1_20, h1_21, h1_51, h1_52, h1_56, h1_57, h1_58,
      h1_67, h1_68, h1_regs, hc1⟩ :=
    wireBranchBIntSetupStmt_runs (p := p) (ω := ω)
      ⟨hr73, hr75, hr76, hr77, hr78, hr82, hr83, hr94, hr95, hr96⟩ (by omega) hCells hAddrW
  have hk (r : ℕ) (h1 : r ≠ 1) (h7 : r ≠ 7) (h8 : r ≠ 8) (h20 : r ≠ 20) (h21 : r ≠ 21)
      (h51 : r ≠ 51) (h52 : r ≠ 52) (h56 : r ≠ 56) (h57 : r ≠ 57) (h58 : r ≠ 58) (h67 : r ≠ 67)
      (h68 : r ≠ 68) : s1.regs r = st.regs r :=
    h1_regs r h1 h7 h8 h20 h21 h51 h52 h56 h57 h58 h67 h68
  have h1_4 : s1.regs 4 = cur := (hk 4 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr4
  have h1_6 : s1.regs 6 = gPtr := (hk 6 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr6
  have h1_9 : s1.regs 9 = ordPtr := (hk 9 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hr9
  have h1_98 : s1.regs 98 = depth := (hk 98 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).trans hr98
  rw [← hm1] at hLvlM hG0 hLen0 hOrd0 hz0
  obtain ⟨s2, cReb, termTok, coreTok, r2, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12,
      a13⟩ :=
    ordRebuildSuffixProgramKFBLStore_runs (w := w) (L := L) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (capLimit := capLimit) (init := init)
      (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
      (intDiv := intDiv) (copy := copy) (lastInit := lastInit) (first := first)
      (handleBase := handleBase) (branchBase := branchBase) (lvlMTable := lvlMTable)
      (levelLens := levelLens) (heapFloor := heapFloor) (lastMul := lastMul)
      (stretchPrec := stretchPrec) (fmt := fmt) (T := T) (LT := LT) (CP := CP) (P := P)
      (allocation := allocation) (lastAlloc := lastAlloc) (coreInitSpace := coreInitSpace)
      (nextM := nextM) (Rcore := Rcore) (p := p) (op := op) (opLast := opLast) (st := s1)
      (ω := ω) next levelSpace levelCost lastSpace hFirstLe hCoreLocal hFour hWidth hLWord hPWord
      hDWord hdW hkPos hkW hNW hw9 h1_1 (h1_4 ▸ hReg4) h1_20 h1_21 h1_51 h1_52
      h1_56 h1_57 h1_58 h1_67 h1_68
      h1_98 hhEnd hbEnd hMEnd hLEnd hSepHB hSepHM hSepBM hSepHL hSepBL hSepML hLvlM
      (h1_6 ▸ hG0) (h1_7 ▸ hLen0) (h1_8.trans h1_7.symm) (fun h => h1_9 ▸ h1_4 ▸ hOrd0 h)
      (h1_6 ▸ h1_4 ▸ hG0End) (h1_7 ▸ h1_4 ▸ hLen0End) (h1_6 ▸ hG0Disj) (h1_7 ▸ hLen0Disj)
      (h1_4 ▸ hz0) hCoreImpl hcapLim hInitSpaceLe hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      hLastImpl hModelLevel hModelLast hLevelSpace hLevelCost hLastSpaceLe (h1_4 ▸ hRoom) hTok0
  rw [h1_4] at a1 a2
  rw [hm1] at a12
  refine ⟨s2, c1 + cReb + 1, termTok, coreTok, runs_seq_iff.mpr (Or.inr ⟨s1, c1, cReb, r1, r2,
    rfl⟩), fun r hr => ?_, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, by omega⟩
  rw [ordRebuildSuffixProgramKFBLStore_preserves_ge70 r2 r hr]
  exact hk r (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)

end MinCostFlow.MinRatio
