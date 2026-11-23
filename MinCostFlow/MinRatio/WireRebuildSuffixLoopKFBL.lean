module

public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBLOrd

/-!
# The suffix rebuild loop under the layout contract (`WireRebuildSuffixLoopKFBL`)

Legacy wrapper exporting `ordRebuildSuffixProgramKFBLStore_runs` with its exact original
postcondition tuple from `ordRebuildSuffixProgramKFBLStore_runs_ord`
(`WireRebuildSuffixLoopKFBLOrd.lean`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- **The suffix rebuild under the layout contract** (`first ≤ d`). Legacy wrapper around
`ordRebuildSuffixProgramKFBLStore_runs_ord` preserving the exact postcondition tuple. -/
theorem ordRebuildSuffixProgramKFBLStore_runs
    {w L depth vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      lastInit first handleBase branchBase lvlMTable levelLens heapFloor lastMul
      stretchPrec : ℕ}
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
    (hReg1 : st.regs 1 = CP.k) (hReg4 : heapFloor ≤ st.regs 4)
    (hReg20 : st.regs 20 = first) (hReg21 : st.regs 21 = CP.d)
    (hReg51 : st.regs 51 = handleBase + first) (hReg52 : st.regs 52 = branchBase + first)
    (hReg56 : st.regs 56 = next.N₀) (hReg57 : st.regs 57 = lvlMTable)
    (hReg58 : st.regs 58 = levelLens) (hReg67 : st.regs 67 = L)
    (hReg68 : st.regs 68 = fmt.precision) (hReg98 : st.regs 98 = depth)
    (hhEnd : handleBase + CP.d < heapFloor) (hbEnd : branchBase + CP.d < heapFloor)
    (hMEnd : lvlMTable + CP.d ≤ heapFloor) (hLEnd : levelLens + 2 * CP.d ≤ heapFloor)
    (hSepHB : handleBase + CP.d < branchBase ∨ branchBase + CP.d < handleBase)
    (hSepHM : handleBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ handleBase)
    (hSepBM : branchBase + CP.d < lvlMTable ∨ lvlMTable + CP.d ≤ branchBase)
    (hSepHL : handleBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ handleBase)
    (hSepBL : branchBase + CP.d < levelLens ∨ levelLens + 2 * CP.d ≤ branchBase)
    (hSepML : lvlMTable + CP.d ≤ levelLens ∨ levelLens + 2 * CP.d ≤ lvlMTable)
    (hLvlM : ∀ j, first ≤ j → j < CP.d → st.mem (lvlMTable + j) = next.lvlM j)
    (hG0 : DynGraphAt st.mem (st.regs 6) vCap eCap (next.G first))
    (hLen0 : EdgeValuesAt st.mem (st.regs 7) 4 L fmt.precision (next.G first).E
      (next.toTreeChain.chainLen next.ℓ first))
    (hGrad0 : st.regs 8 = st.regs 7)
    (hOrd0 : first < CP.d → ∃ oWords,
      OrdListAt st.mem (st.regs 9) (next.levelOrd first) oWords ∧
      (∀ j < oWords, st.mem (st.regs 9 + j) < 2 ^ w) ∧
      st.regs 9 + oWords ≤ st.regs 4 ∧
      oWords ≤ 2 * (next.G first).n + 2 * (next.G first).m + 1)
    (hG0End : st.regs 6 + dynGraphSize vCap eCap ≤ st.regs 4)
    (hLen0End : st.regs 7 + eCap * L ≤ st.regs 4)
    (hG0Disj : ∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vCap eCap →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hLen0Disj : ∀ a, st.regs 7 ≤ a → a < st.regs 7 + eCap * L →
      (a < handleBase + first ∨ handleBase + CP.d < a) ∧
      (a < branchBase + first ∨ branchBase + CP.d < a) ∧
      (a < levelLens + (first + 1) ∨ levelLens + 2 * CP.d ≤ a))
    (hz0 : ZeroFrom st.mem (st.regs 4))
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
    (hRoom : st.regs 4 + (Finset.Ico first CP.d).sum levelSpace + lastSpace < 2 ^ w)
    (hTok0 : Rcore.τ) :
    ∃ (out : State) (cost termTok : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (ordRebuildSuffixProgramKFBLStore init (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      st.regs 4 ≤ out.regs 4 ∧
      out.regs 4 ≤ st.regs 4 + (Finset.Ico first CP.d).sum levelSpace + lastSpace ∧
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
          lastMul * (LT.cost (next.G CP.d) + 1) + 28 := by
  obtain ⟨out, cost, termTok, coreTok, h1, h2, h3, h4, h5, h6, h7, _, h8, h9, h10, h11, h12, h13,
    h14⟩ :=
    ordRebuildSuffixProgramKFBLStore_runs_ord next levelSpace levelCost lastSpace hFirstLe hCoreLocal
      hFour hWidth hLWord hPWord hDWord hdW hkPos hkW hNW hw9 hReg1 hReg4 hReg20 hReg21 hReg51
      hReg52 hReg56 hReg57 hReg58 hReg67 hReg68 hReg98 hhEnd hbEnd hMEnd hLEnd hSepHB hSepHM
      hSepBM hSepHL hSepBL hSepML hLvlM hG0 hLen0 hGrad0 hOrd0 hG0End hLen0End hG0Disj hLen0Disj
      hz0 hCoreImpl hcapLim hInitSpaceLe hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hLastImpl
      hModelLevel hModelLast hLevelSpace hLevelCost hLastSpaceLe hRoom hTok0
  exact ⟨out, cost, termTok, coreTok, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

end MinCostFlow.MinRatio
