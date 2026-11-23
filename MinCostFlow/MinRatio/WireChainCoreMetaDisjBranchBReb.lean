module

public import MinCostFlow.MinRatio.WireChainCoreBranchBMetaDisjKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchBIntRebNewKFBL
import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBLOrd
import WordRAM.Tactic

/-!
# Block-order preservation across the Branch B interior rebuild (`WireChainCoreMetaDisjBranchBReb`)

This file extracts `BranchBRebuiltOrdKFBL` on the levels `i₀ + 1, …, d - 1` (the exact range of
`levelMeta` entries written by `ordRebuildSuffixProgramKFBLStore_runs_ord`) through the interior
rebuild steps of Branch B:
* `wireBranchBIntSuffixKFBL_runs_ord`: runs `wireBranchBIntSuffixKFBL` using
  `ordRebuildSuffixProgramKFBLStore_runs_ord` to produce `BranchBRebuiltOrdKFBL` at `first + 1`
  and `heapFloor`.
* `wireBranchBIntRebKFBL_runs_ord`: lifts that order to the interior-step state `s` after
  `wireBranchBIntOldKFBL`, at `i₀ + 1` and `s.regs 4`.
* `wireBranchBIntRebNewKFBL_runs_ord`: transports the order across the new-forest collection
  `wireBranchBIntNewStmt`, which leaves all `levelMeta` cells unchanged.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Transport `BranchBRebuiltOrdKFBL` across memory agreement on the `2 * d` cells of
`levelMeta` and a smaller heap lower bound. -/
theorem BranchBRebuiltOrdKFBL.of_agree_le {lm d fr heap heap' vCap eCap L : ℕ}
    {mem mem' : ℕ → ℕ}
    (h : BranchBRebuiltOrdKFBL lm d fr heap vCap eCap L mem)
    (hle : heap' ≤ heap)
    (hag : ∀ j < 2 * d, mem' (lm + j) = mem (lm + j)) :
    BranchBRebuiltOrdKFBL lm d fr heap' vCap eCap L mem' := by
  have hagL (j : ℕ) (hj : j < d) : mem' (lm + j) = mem (lm + j) := hag j (by omega)
  have hagG (j : ℕ) (hj : j < d) : mem' (lm + d + j) = mem (lm + d + j) := by
    rw [Nat.add_assoc]; exact hag (d + j) (by omega)
  refine ⟨fun j hj1 hj2 => ?_, fun j₁ j₂ hj1 hlt hj2 => ?_⟩
  · rw [hagG j hj2, hagL j hj2]
    exact ⟨hle.trans (h.1 j hj1 hj2).1, (h.1 j hj1 hj2).2⟩
  · rw [hagL j₁ (lt_trans hlt hj2), hagG j₂ hj2]
    exact h.2 j₁ j₂ hj1 hlt hj2

/-- Run of `wireBranchBIntSuffixKFBL` yielding `BranchBRebuiltOrdKFBL` on the stored rebuilt
levels `first + 1, …, CP.d - 1` at or above `heapFloor`. -/
theorem wireBranchBIntSuffixKFBL_runs_ord
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
    (hG0 : DynGraphAt st.mem gPtr vCap eCap (next.G first))
    (hLen0 : EdgeValuesAt st.mem lPtr 4 L fmt.precision (next.G first).E
      (next.toTreeChain.chainLen next.ℓ first))
    (hOrd0 : first < CP.d → ∃ oWords,
      OrdListAt st.mem ordPtr (next.levelOrd first) oWords ∧
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
    (hz0 : ZeroFrom st.mem cur)
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
    ∃ (out : State) (cost : ℕ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL init (op 3) (op 2) coreLenProc (op 5) lastInit)
        st .normal out cost ∧
      BranchBRebuiltOrdKFBL levelLens CP.d (first + 1) heapFloor vCap eCap L out.mem := by
  obtain ⟨hr4, hr6, hr9, hr73, hr75, hr76, hr77, hr78, hr82, hr83, hr94, hr95, hr96, hr98⟩ := hRegs
  obtain ⟨s1, c1, r1, hm1, h1_1, h1_7, h1_8, h1_20, h1_21, h1_51, h1_52, h1_56, h1_57, h1_58,
      h1_67, h1_68, h1_regs, _⟩ :=
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
  obtain ⟨s2, cReb, _, _, r2, _, _, _, _, _, hMeta2, hOrd2, _, _, _, _, _, _, _⟩ :=
    ordRebuildSuffixProgramKFBLStore_runs_ord (w := w) (L := L) (depth := depth) (vCap := vCap)
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
  exact ⟨s2, c1 + cReb + 1, runs_seq_iff.mpr (Or.inr ⟨s1, c1, cReb, r1, r2, rfl⟩),
    fun j hj1 hj2 => ⟨(hMeta2 j hj1 hj2).2.1, hOrd2.1 j hj1 hj2⟩, hOrd2.2⟩

set_option maxHeartbeats 1600000 in
/-- Run of the interior-step suffix rebuild `wireBranchBIntSuffixKFBL` from the post-Part-1 state
`s`, yielding `BranchBRebuiltOrdKFBL` on levels `i₀ + 1, …, d - 1` at or above `s.regs 4`. -/
theorem wireBranchBIntRebKFBL_runs_ord
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs i₀ ordPtr ordWords wordExp stretchPrec
      capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE s : State}
    {tok tokM : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldHi : oldPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (M : BranchBIntMidKFBL (w := w) (vCap := vCap) (eCap := eCap) A oldPtrs i₀ ch0 ch curG sE s
      tok tokM ordPtr ordWords)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hReb : UpdateRebuildModelInv w L P wordExp stretchPrec ch i₀ curG ℓ' g' curEnc)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        s .normal out cost ∧
      BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (s.regs 4) vCap eCap L out.mem := by
  obtain ⟨hFloor, _, _, _, _, _, hr73, _, hr75, hr76, hr77, hr78, hr82, hr83, _, _, hr94, hr95,
    hr96, _, hr98, _⟩ := I.regs
  obtain ⟨hPre, hNG, _, hNLvlM, hNN0, _, _, hPrevAbsEq, hNOrd, _, hLenEq, hModelLevel,
    hModelLast⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hN : ch.N₀ = N0 := I.modelFrame.2.2.2.2.2.1
  have hPrevBr : next.bran (i₀ - 1) = ch.bran (i₀ - 1) := (hPre (i₀ - 1) (by omega)).2.2.1
  have hHLt := S.handleLt
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hLvlMLt := S.lvlMLt
  have hMetaLt := S.metaLt
  have hRCLt := S.rcLt
  have hGLt := S.gLt i₀ hLt
  have hLLt := S.lLt i₀ hLt
  have hRCH := S.sepRCH
  have hRCM := S.sepRCM
  have hRCLM := S.sepRCLM
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hSelLt : A.selBase < sE.regs 4 := by omega
  have hs4W : s.regs 4 < 2 ^ w := by omega
  have hKeepS (z : ℕ) (hz : z < A.selBase)
      (hnf : ∀ j < cfg.P.d, ¬ Rcore.foot (A.coreH j) (tok j) z)
      (hg : ¬ (A.gPtr0 i₀ ≤ z ∧ z < A.gPtr0 i₀ + dynGraphSize vCap eCap))
      (hrc : z ≠ A.rcBase + i₀) : s.mem z = sE.mem z :=
    M.frame z (by omega) (fun j _ hj => hnf j hj) (by omega) hrc (Or.inl (by omega))
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := I.cells i₀ hLt
  have hkPos : 0 < cfg.P.k := by omega
  obtain ⟨hN0Pos, hN0Foot, hN0Sep⟩ := I.n0Word
  have hCellN : s.mem (A.lvlMTable - 1) = next.N₀ := by
    rw [hKeepS _ (by omega) hN0Foot
      (fun ⟨h1, h2⟩ => by rcases (hN0Sep i₀ hLt).1 with h | h <;> omega)
      (hN0Sep i₀ hLt).2.2.2, I.hdrCell, hNN0, hN]
  have hCellL : s.mem (A.levelMeta + i₀) = A.lPtr0 i₀ := by
    rw [hKeepS _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 i₀ hLt).2.1)
      (fun ⟨h1, h2⟩ => by obtain ⟨_, _, _, _, _, g6, _⟩ := S.gSep i₀ hLt _ h1 h2; omega)
      (by omega), c8]
  have hLvlMs : ∀ j, i₀ ≤ j → j < cfg.P.d → s.mem (A.lvlMTable + j) = next.lvlM j :=
    fun j _ hj => by
      rw [hKeepS _ (by omega) (fun r hr => ((I.static r hr).2.2.2.1 j hj).1)
        (fun ⟨h1, h2⟩ => by obtain ⟨_, _, _, _, g5, _⟩ := S.gSep i₀ hLt _ h1 h2; omega)
        (by omega), (I.cells j hj).2.1, hNLvlM]
  have hG0 : DynGraphAt s.mem (A.gPtr0 i₀) vCap eCap (next.G i₀) := hNG ▸ M.graph
  have hLen0 : EdgeValuesAt s.mem (A.lPtr0 i₀) 4 L fmt.precision (next.G i₀).E
      (next.toTreeChain.chainLen next.ℓ i₀) := by
    rw [hNG, hLenEq, E.prec]
    refine (I.lensEq hLt).congr (fun e he t ht => ?_)
    have heL : e * L + L ≤ eCap * L := by
      simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt (M.graph.2.2.1 e he))
    have hb1 : A.lPtr0 i₀ ≤ A.lPtr0 i₀ + e * L + t := by omega
    have hb2 : A.lPtr0 i₀ + e * L + t < A.lPtr0 i₀ + eCap * L := by omega
    obtain ⟨_, _, _, _, _, _, l7, _⟩ := S.lSep i₀ hLt _ hb1 hb2
    exact hKeepS _ (by omega) (fun r hr => (I.static r hr).2.2.2.2.2 i₀ hLt _ hb1 hb2)
      (fun ⟨h1, h2⟩ => by
        obtain ⟨_, _, _, _, _, _, _, _, g9⟩ := S.gSep i₀ hLt _ h1 h2
        have := (g9 i₀ hLt).1; omega) (by omega)
  have hOrd0 : i₀ < cfg.P.d → ∃ oWords,
      OrdListAt s.mem ordPtr (next.levelOrd i₀) oWords ∧
      (∀ j < oWords, s.mem (ordPtr + j) < 2 ^ w) ∧
      ordPtr + oWords ≤ s.regs 4 ∧
      oWords ≤ 2 * (next.G i₀).n + 2 * (next.G i₀).m + 1 := fun _ => by
    refine ⟨ordWords, hNOrd ▸ M.ord.1, M.ord.2.2.2, M.ord.2.2.1, ?_⟩
    have h1 := M.ord.2.1
    have h2 := hNextRot (i₀ - 1) (by omega)
    rw [hPrevAbsEq (i₀ - 1) (by omega), hPrevBr, show i₀ - 1 + 1 = i₀ by omega] at h2
    omega
  let restSp : ℕ → ℕ := fun j =>
    ordLevelSpace L capExp capLimit 0 (next.lvlM j) next.N₀ (next.G (j + 1)).m
  let coreInitSpace : ℕ → ℕ := fun j => levelSpace j - restSp j
  have hOrdSpaceAdd : ∀ x j,
      ordLevelSpace L capExp capLimit x (next.lvlM j) next.N₀ (next.G (j + 1)).m =
        x + restSp j := fun x j => by
    unfold restSp ordLevelSpace
    simp only [Nat.zero_add, Nat.add_assoc]
  have hInitSpaceLe : ∀ j, i₀ ≤ j → j < cfg.P.d → ∀ gB lB grB oB h,
      alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h] ≤
        coreInitSpace j := fun j hj1 hj2 gB lB grB oB h => by
    have hdom := hLevelSpaceDom j gB lB grB oB h hj1 hj2
    rw [hOrdSpaceAdd] at hdom
    dsimp only [coreInitSpace]; omega
  have hLvlSpaceLe : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit (coreInitSpace j) (next.lvlM j) next.N₀
        (next.G (j + 1)).m ≤ levelSpace j := fun j hj1 hj2 => by
    have hdom := hLevelSpaceDom j 0 0 0 0 0 hj1 hj2
    rw [hOrdSpaceAdd] at hdom ⊢
    dsimp only [coreInitSpace]; omega
  have hR (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s.regs r = sE.regs r := M.regs r h70 h99
  exact wireBranchBIntSuffixKFBL_runs_ord (w := w) (L := L) (depth := depth) (vCap := vCap)
    (eCap := eCap) (capExp := capExp) (capLimit := capLimit) (init := initCore)
    (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
    (intDiv := intDiv) (copy := copy) (lastInit := lastInit) (first := i₀)
    (handleBase := A.handleBase) (branchBase := A.branchBase) (lvlMTable := A.lvlMTable)
    (levelLens := A.levelMeta) (heapFloor := s.regs 4) (lastMul := lastMul)
    (stretchPrec := stretchPrec) (cur := s.regs 4) (gPtr := A.gPtr0 i₀) (lPtr := A.lPtr0 i₀)
    (ordPtr := ordPtr) (handle := A.handle) (fmt := fmt) (T := cfg.T) (LT := cfg.L)
    (CP := cfg.P) (P := Psc) (allocation := alloc) (lastAlloc := lastAlloc)
    (coreInitSpace := coreInitSpace) (nextM := fun j => (next.G (j + 1)).m) (Rcore := Rcore)
    (p := p) (op := opCore) (opLast := opLast) (st := s) (ω := ω)
    next levelSpace levelCost lastSpace (le_of_lt hLt) E.loc E.four (E.prec ▸ hWidth) hLWord
    (E.prec ▸ hPWord) hDepthW E.dW hkPos E.kW (by rw [hNN0, hN]; exact hNW)
    (by have := E.w16; omega)
    ⟨rfl, M.r6, M.r9, (hR 73 (by decide) (by decide)).trans hr73,
      (hR 75 (by decide) (by decide)).trans hr75, (hR 76 (by decide) (by decide)).trans hr76,
      (hR 77 (by decide) (by decide)).trans hr77, (hR 78 (by decide) (by decide)).trans hr78,
      (hR 82 (by decide) (by decide)).trans hr82, (hR 83 (by decide) (by decide)).trans hr83,
      (hR 94 (by decide) (by decide)).trans hr94,
      (hR 95 (by decide) (by decide)).trans (hr95.trans E.prec.symm),
      (hR 96 (by decide) (by decide)).trans hr96, (hR 98 (by decide) (by decide)).trans hr98⟩
    ⟨hCellN, hCellL⟩ ⟨by omega, by omega, by omega, by omega⟩ le_rfl (by omega) (by omega)
    (by omega) (by omega) S.sepHB S.sepHM S.sepBM S.sepHL S.sepBL S.sepML hLvlMs hG0 hLen0 hOrd0
    (by omega) (by omega)
    (fun a h1 h2 => by
      obtain ⟨_, _, g3, g4, _, g6, _⟩ := S.gSep i₀ hLt a h1 h2
      exact ⟨by omega, by omega, by omega⟩)
    (fun a h1 h2 => by
      obtain ⟨_, _, l3, l4, _, l6, _⟩ := S.lSep i₀ hLt a h1 h2
      exact ⟨by omega, by omega, by omega⟩)
    M.zero hImpl hcapLim hInitSpaceLe hCoreLenProc E.edgeP E.signC E.mulC E.divC E.copyC
    hLastImpl hModelLevel hModelLast hLvlSpaceLe hLevelCostDom hLastSpaceDom hRoom (tok 0)

set_option maxHeartbeats 1600000 in
/-- Run of `wireBranchBIntSuffixKFBL ;; wireBranchBIntNewStmt` from state `s`, transporting
`BranchBRebuiltOrdKFBL` on levels `i₀ + 1, …, d - 1` at or above `s.regs 4` across the
new-forest collection. -/
theorem wireBranchBIntRebNewKFBL_runs_ord
    {w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen slotProc collectProc
      edgeProc signExt mul intDiv copy N0 oldPtrs newPtrs intCap i₀ ordPtr ordWords wordExp
      stretchPrec capLimit coreLenProc lastInit lastMul lastSpace : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {alloc lastAlloc : ℕ → List ℕ → ℕ} {Ginit : ℕ → MGraph} {reembFn : ToolReembFn cfg.T}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {RL : DSRep (ℕ × (ℕ → LSF))} {p : Program}
    {opCore opLast : ℕ → ℕ} {ω : ℕ → Bool} {A : BranchBAddrs} {origLen : ℕ → ℕ → ℝ}
    {ℓ' g' : ℕ → ℝ} {BWc EWc ULc : ℕ → ℕ} {ch0 : ChainState cfg.T cfg.P} {termTok : RL.τ}
    {ch : ChainState cfg.T cfg.P} {curG : MGraph} {curU : List Update}
    {curEditsList : List OrdEdit} {curEnc : ℕ} {oldOrd : ℕ → List End} {sE s : State}
    {tok tokM : ℕ → Rcore.τ} {curBatch curBatchWords curEdits curEditsWords : ℕ}
    {levelU levelUS : ℕ → List Update} {D : ℕ → LevelDiffLists} {levelSpace levelCost : ℕ → ℕ}
    (E : BranchBLoopEnvKFBL w L P depth vCap eCap capExp edMul initCore dgApply copyProc updLen
      slotProc collectProc edgeProc signExt mul intDiv copy fmt cfg Psc alloc Ginit reembFn Rcore
      p opCore)
    (S : BranchBStatic cfg.P.d L A.handle A.table A.handleBase A.branchBase A.lvlMTable
      A.levelMeta A.rcBase A.ucBase A.selBase (fun _ => vCap) (fun _ => eCap) A.gPtr0 A.lPtr0
      A.coreH)
    (hOldLo : A.selBase + 1 + 12 * cfg.P.d ≤ oldPtrs)
    (hOldHi : oldPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hNewLo : A.selBase + 1 + 12 * cfg.P.d ≤ newPtrs)
    (hNewHi : newPtrs + (cfg.P.d + 1) ≤ A.heapFloor)
    (hPos : 0 < i₀) (hLt : i₀ < cfg.P.d)
    (I : BranchBLoopInvKFBL (w := w) (L := L) (P := P) (depth := depth) (vCap := vCap)
      (eCap := eCap) (capExp := capExp) (fmt := fmt) (RL := RL) reembFn A origLen ℓ' N0 BWc
      EWc ULc ch0 termTok i₀ ch curG curU curEditsList oldOrd sE tok curBatch curBatchWords
      curEdits curEditsWords levelU levelUS D)
    (M : BranchBIntMidKFBL (w := w) (vCap := vCap) (eCap := eCap) A oldPtrs i₀ ch0 ch curG sE s
      tok tokM ordPtr ordWords)
    (h71 : sE.regs 71 = 0) (h81 : sE.regs 81 = newPtrs)
    (next : ChainState cfg.T cfg.P)
    (hNext : next = (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P
      { ch with ℓ := ℓ', g := g' } i₀ curG curEnc).1)
    (hReb : UpdateRebuildModelInv w L P wordExp stretchPrec ch i₀ curG ℓ' g' curEnc)
    (hWordExpEq : Psc.wordExp = wordExp) (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hNextN : ∀ j ≤ cfg.P.d, (next.G j).n ≤ next.N₀)
    (hNextRot : ∀ j < cfg.P.d, ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
      1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m)
    (hImpl : ∀ j, i₀ ≤ j → j < cfg.P.d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j)
          next.N₀ vCap eCap capExp Psc alloc) ∧
      SparseCoreReadoutFootAt fmt L depth cfg.T (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap
        eCap capExp Psc alloc Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hLastImpl :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
        (next.G cfg.P.d).E).Implements w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L (next.G cfg.P.d) vCap eCap lastMul
          stretchPrec lastAlloc))
    (hLevelSpaceDom : ∀ j gB lB grB oB h, i₀ ≤ j → j < cfg.P.d →
      ordLevelSpace L capExp capLimit
        (alloc 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision, depth, h])
        (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤ levelSpace j)
    (hLevelCostDom : ∀ j, i₀ ≤ j → j < cfg.P.d →
      updateCoreRebuildLevelCost L capExp cfg Psc next j ≤ levelCost j)
    (hLastSpaceDom : ∀ gB lB h, lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace)
    (hFCap : ∀ j, i₀ ≤ j → j < cfg.P.d →
      ∀ e ∈ (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E, e < intCap)
    (hLastFCap : ∀ e ∈ (next.lastLSFs next.lastBran).F.F.E, e < intCap)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w) (hWidth : P ≤ 4 * L) (hDepthW : depth < 2 ^ w)
    (hNW : N0 < 2 ^ w)
    (hRoom : s.regs 4 + (Finset.Ico i₀ cfg.P.d).sum levelSpace + lastSpace + 5 * (cfg.P.d - i₀) <
      2 ^ w) :
    ∃ (s3 : State) (cost : ℕ),
      Runs w p ω
        (wireBranchBIntSuffixKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
          wireBranchBIntNewStmt (opCore 2))
        s .normal s3 cost ∧
      BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (s.regs 4) vCap eCap L s3.mem := by
  obtain ⟨hFloor, _, _, _, _, _, _, _, hr75, _, hr77, hr78, _, hr83, _, _, _, _, hr96, _, _,
    _⟩ := I.regs
  obtain ⟨s2, c2, termTokN, coreTok2, r2, hR2, h2lo, h2hi, hz2, hCores2, hDisj2, hGr2, hLB2,
      hLH2, hLRep2, hLFoot2, hLDisj2, hFr2, _⟩ :=
    wireBranchBIntRebKFBL_runs (ω := ω) E S hOldLo hOldHi hPos hLt I M next hNext hReb
      hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom
      hLevelCostDom hLastSpaceDom hLWord hPWord hWidth hDepthW hNW (by omega)
  obtain ⟨s2', _, r2', hOrd2'⟩ :=
    wireBranchBIntRebKFBL_runs_ord (ω := ω) E S hOldLo hOldHi hPos hLt I M next hNext hReb
      hWordExpEq hInitOrdEq hNextN hNextRot hImpl hcapLim hCoreLenProc hLastImpl hLevelSpaceDom
      hLevelCostDom hLastSpaceDom hLWord hPWord hWidth hDepthW hNW (by omega)
  have hs2Eq : s2' = s2 := (Runs.det r2' r2).2.1
  have hOrd2 : BranchBRebuiltOrdKFBL A.levelMeta cfg.P.d (i₀ + 1) (s.regs 4) vCap eCap L s2.mem :=
    hs2Eq ▸ hOrd2'
  obtain ⟨_, hNG, _, _, _, _, _, _, _, _, _, hModelLevel, hModelLast⟩ :=
    branchBIntNext_facts (fmt := fmt) (Psc := Psc) ch curG ℓ' g' curEnc i₀ next hNext hPos hLt
      hReb hWordExpEq E.prec hInitOrdEq hNextN hNextRot
  have hLastKPos : 0 < next.lastK := by subst hNext; exact hReb.2.1
  have hLastBr0 : next.lastBran = 0 := hModelLast.2.1
  have hHBLt := S.hbLt
  have hBBLt := S.bbLt
  have hMetaLt := S.metaLt
  have hRCLM := S.sepRCLM
  have hGLt := S.gLt i₀ hLt
  have hsE4 : sE.regs 4 < s.regs 4 := by have := M.heapLo; have := M.ord.2.2.1; omega
  have hR (r : ℕ) (h70 : 70 ≤ r) (h99 : r ≠ 99) : s2.regs r = sE.regs r :=
    (hR2 r h70).trans (M.regs r h70 h99)
  have hkPos : 0 < cfg.P.k := by have := (I.cells i₀ hLt).2.2.2.2.1; omega
  obtain ⟨_, _, _, _, _, _, c7, _, _, _⟩ := I.cells i₀ hLt
  have hSepHL := S.sepHL
  have hSepBL := S.sepBL
  have hNotG : ¬ (A.gPtr0 i₀ ≤ A.levelMeta + cfg.P.d + i₀ ∧
      A.levelMeta + cfg.P.d + i₀ < A.gPtr0 i₀ + dynGraphSize vCap eCap) := fun ⟨h1, h2⟩ => by
    obtain ⟨_, _, _, _, _, g6, _⟩ := S.gSep i₀ hLt _ h1 h2; omega
  have hCellG : s2.mem (A.levelMeta + cfg.P.d + i₀) = A.gPtr0 i₀ := by
    rw [hFr2 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩,
      M.frame _ (by omega) (fun r _ hr => ((I.static r hr).2.2.2.1 i₀ hLt).2.2.1)
        (by omega) (by omega) (Or.inl (by omega)), c7]
  have hG2 : DynGraphAt s2.mem (A.gPtr0 i₀) vCap eCap (next.G i₀) := by
    rw [hNG]
    exact dynGraphAt_of_agree M.graph (fun a h1 h2 => by
      obtain ⟨_, _, g3, g4, _, g6, _⟩ := S.gSep i₀ hLt a h1 h2
      exact hFr2 a (by omega) (by omega) (by omega) ⟨by omega, by omega⟩)
  obtain ⟨hTLo, _, _, hTBr⟩ := hLRep2
  obtain ⟨hTBrHdr, hTLSF⟩ := hTBr next.lastBran (by rw [hLastBr0]; exact hLastKPos)
  set termH := s2.mem (A.handleBase + cfg.P.d)
  set lsfHdr := s2.mem (termH + 1 + next.lastBran)
  set forestPtr := s2.mem (lsfHdr + 1)
  have hInT : ∀ a, termH ≤ a → a < termTokN → s.regs 4 ≤ a ∧ a < s2.regs 4 := fun a h1 h2 =>
    hLFoot2 a ⟨h1, h2⟩
  have hTermEndLe : termTokN ≤ s2.regs 4 := by
    have := (hInT (termTokN - 1) (by omega) (by omega)).2; omega
  obtain ⟨hB1, hB2, _, _, hB5, hB6, _⟩ := hTBrHdr
  have hB1' : termH ≤ lsfHdr := le_trans (by omega) hB1
  have hB5' : termH ≤ forestPtr := le_trans (by omega) hB5
  obtain ⟨s3, c3, _, r3, _, _, _, _, _, _, _, hFr3, _, _⟩ :=
    wireBranchBIntNewKFBL_runs (w := w) (L := L) (depth := depth) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) (i0 := i₀) (handleBase := A.handleBase) (branchBase := A.branchBase)
      (levelMeta := A.levelMeta) (newPtrs := newPtrs) (intCap := intCap) (termHandle := termH)
      (lo := s.regs 4) (vcLast := vCap) (ecLast := eCap) (lsfHdr := lsfHdr)
      (forestPtr := forestPtr) (fmt := fmt) (T := cfg.T) (CP := cfg.P) (P := Psc)
      (allocation := alloc) (Rcore := Rcore) (p := p) (op := opCore) (st := s2) (ω := ω) next
      (fun j => s2.mem (A.handleBase + j)) coreTok2 E.loc hLt
      ((hR 96 (by decide) (by decide)).trans hr96) ((hR 71 (by decide) (by decide)).trans h71)
      ((hR 75 (by decide) (by decide)).trans hr75) ((hR 77 (by decide) (by decide)).trans hr77)
      ((hR 78 (by decide) (by decide)).trans hr78) ((hR 81 (by decide) (by decide)).trans h81)
      ((hR 83 (by decide) (by decide)).trans hr83) E.kW E.dW (by have := E.w16; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) hz2
      (fun j hj1 hj2 => (hImpl j hj1 hj2).2)
      (fun j hj1 hj2 => by
        obtain ⟨hBrJ, hHLoJ, hHHiJ, hRepJ, hFootJ⟩ := hCores2 j hj1 hj2
        obtain ⟨hScJ, _, hBrNJ, hUpdNJ, hmLeJ, hnLeJ, _, _, hRotJ, hPosJ, _⟩ :=
          hModelLevel j hj1 hj2
        have hDGJ :
            DynGraphAt s2.mem (s2.mem (A.levelMeta + cfg.P.d + j)) vCap eCap (next.G j) ∧
            s2.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap ≤ s2.regs 4 ∧
            ∀ a, s2.mem (A.levelMeta + cfg.P.d + j) ≤ a →
              a < s2.mem (A.levelMeta + cfg.P.d + j) + dynGraphSize vCap eCap →
              (∀ r, i₀ ≤ r → r < cfg.P.d →
                ¬ Rcore.foot (s2.mem (A.handleBase + r)) (coreTok2 r) a) ∧
              (a < newPtrs + i₀ ∨ newPtrs + (cfg.P.d + 1) ≤ a) := by
          by_cases hji : j = i₀
          · subst hji; rw [hCellG]
            exact ⟨hG2, by omega, fun a h1 h2 => ⟨fun r hr1 hr2 hf => by
              have := (hCores2 r hr1 hr2).2.2.2.2 a hf; omega, Or.inl (by omega)⟩⟩
          · obtain ⟨hDG, hGLo, hGHi, _, _, _, hDisjC, _, _⟩ := hGr2 j (by omega) hj2
            exact ⟨hDG, hGHi, fun a ha1 ha2 =>
              ⟨fun r hr1 hr2 => (hDisjC r hr1 hr2).2 a ha1 ha2, Or.inr (by omega)⟩⟩
        have hInJ : SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM j) next.N₀ (next.scState j)
            (next.G j) (next.levelOrd j) (next.updCount j) := by
          rw [hScJ, hUpdNJ]
          exact SparseCoreOrdInput.init (next.G j) _ _ (next.levelOrd j) hDGJ.1.1 hmLeJ hnLeJ
            (fun e he => by simp [he, hPosJ e he]) hRotJ
        exact ⟨rfl, hBrJ, by rw [hBrNJ]; exact hkPos, by omega, hRepJ, hInJ,
          fun a ha => (hFootJ a ha).2,
          fun r hr1 hr2 => ⟨fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega⟩,
          Or.inl (by omega), Or.inl (by omega), Or.inl (by omega),
          fun t _ _ hf => by have := (hFootJ _ hf).1; omega, hDGJ⟩)
      hDisj2 rfl hLB2 rfl rfl hTLSF.2.1 (le_trans hB6 hTermEndLe) hLastFCap
      ⟨Or.inl (by omega), Or.inl (by omega),
        Or.inr (by have := (hInT (termH + 1 + next.lastBran) (by omega) (by omega)).1; omega),
        Or.inr (by have := (hInT (lsfHdr + 1) (by omega) (by omega)).1; omega),
        (hInT _ (by omega) (by omega)).2, (hInT _ (by omega) (by omega)).2,
        fun r hr1 hr2 => ⟨fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
          fun hf => by have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega,
          hLDisj2 r hr1 hr2 _ ⟨by omega, by omega⟩, hLDisj2 r hr1 hr2 _ ⟨by omega, by omega⟩⟩,
        fun a ha1 ha2 => ⟨fun r hr1 hr2 => hLDisj2 r hr1 hr2 a ⟨by omega, by omega⟩,
          Or.inr (by have := (hInT a (by omega) (by omega)).1; omega)⟩⟩
      hFCap (fun j hj1 hj2 a ha => ((hCores2 j hj1 hj2).2.2.2.2 a ha).1) h2lo
      (le_trans hLH2 hB5')
  have hMC : ∀ j < 2 * cfg.P.d, s3.mem (A.levelMeta + j) = s2.mem (A.levelMeta + j) :=
    fun j hj => hFr3 _ (by omega) (fun r hr1 hr2 hf => by
      have := ((hCores2 r hr1 hr2).2.2.2.2 _ hf).1; omega) (Or.inl (by omega))
  exact ⟨s3, c2 + c3 + 1, runs_seq_iff.mpr (Or.inr ⟨s2, c2, c3, r2, r3, rfl⟩),
    hOrd2.of_agree_le le_rfl hMC⟩

end MinCostFlow.MinRatio
