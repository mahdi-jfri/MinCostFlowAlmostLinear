module

public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBLBase
public import MinCostFlow.LastLevelProgram.Readout
import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# Ordered Init level loop with metadata recording (`WireInitLevelsLoopK`)

Maintains `InitLevelsLoopInv` across levels `0 .. d - 1` inside `ordRebuildSuffixProgramKFBLStore`
for `Chain.Ordered.algorithm1_initialize`, recording each level `1 ≤ j < d`'s length and graph
pointers in `levelMeta[j]` and `levelMeta[d + j]` while preserving pairwise-disjoint footprints in
`[levelsStart, levelsEnd)` and disjointness of all stored level-metadata blocks from every core.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program MinCostFlow.LastLevelProgram

/-- Loop invariant after initializing sparse-core levels `0 .. i - 1` inside
`ordRebuildSuffixProgramKFBLStore`. Every level built so far has caps `(vCap, eCap)` and every
rebuilt level `1 ≤ j ≤ i` (`j < C.d`) has its length and graph pointers stored in `levelMeta`. -/
structure InitLevelsLoopInv {w : ℕ} {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (chain : ChainState T C)
    (L P_fp depth vCap eCap capExp capLimit levelTable branchTable levelsStart lvlMTable
      levelMeta : ℕ)
    (coreInitSpace lvlM nextM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) (initMem : ℕ → ℕ)
    (i : ℕ) (st : State) (yCore : ∀ j, j < i → Rcore.τ) : Prop where
  reg1 : st.regs 1 = C.k
  reg19 : st.regs 19 = i
  reg21 : st.regs 21 = C.d
  reg51 : st.regs 51 = levelTable + i
  reg52 : st.regs 52 = branchTable + i
  reg56 : st.regs 56 = N₀
  reg57 : st.regs 57 = lvlMTable
  reg58 : st.regs 58 = levelMeta
  reg67 : st.regs 67 = L
  reg68 : st.regs 68 = P_fp
  reg98 : st.regs 98 = depth
  heapLo : levelsStart ≤ st.regs 4
  heapHi : st.regs 4 ≤ levelsStart +
    ∑ j ∈ Finset.range i, ordLevelSpace L capExp capLimit (coreInitSpace j) (lvlM j) N₀ (nextM j)
  zeroFrom : ZeroFrom st.mem (st.regs 4)
  frameBelow : ∀ a < levelsStart,
    (a < levelTable ∨ levelTable + i ≤ a) →
    (a < branchTable ∨ branchTable + i ≤ a) →
    (a < levelMeta + 1 ∨ levelMeta + C.d ≤ a) →
    (a < levelMeta + C.d + 1 ∨ levelMeta + 2 * C.d ≤ a) →
    st.mem a = initMem a
  curGraph : ∃ vc ec, vc = vCap ∧ ec = eCap ∧ vc + ec + 2 ≤ capLimit ∧
    DynGraphAt st.mem (st.regs 6) vc ec (chain.G i) ∧
    st.regs 6 + dynGraphSize vc ec ≤ st.regs 4 ∧
    (∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc ec →
      a < levelTable ∨ levelTable + (C.d + 1) ≤ a) ∧
    (∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc ec →
      a < branchTable ∨ branchTable + (C.d + 1) ≤ a) ∧
    (∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc ec →
      a < levelMeta ∨ levelMeta + 2 * C.d ≤ a) ∧
    EdgeValuesAt st.mem (st.regs 7) 4 L P_fp (chain.G i).E (chain.toTreeChain.chainLen ℓ₀ i) ∧
    st.regs 7 + ec * L ≤ st.regs 4 ∧
    (∀ a, st.regs 7 ≤ a → a < st.regs 7 + ec * L →
      a < levelTable ∨ levelTable + (C.d + 1) ≤ a) ∧
    (∀ a, st.regs 7 ≤ a → a < st.regs 7 + ec * L →
      a < branchTable ∨ branchTable + (C.d + 1) ≤ a) ∧
    (∀ a, st.regs 7 ≤ a → a < st.regs 7 + ec * L →
      a < levelMeta ∨ levelMeta + 2 * C.d ≤ a) ∧
    EdgeValuesAt st.mem (st.regs 8) 4 L P_fp (chain.G i).E
      (fun e => if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) ∧
    st.regs 8 + ec * L ≤ st.regs 4
  curOrd : i < C.d → ∃ ordW,
    OrdListAt st.mem (st.regs 9) (chain.levelOrd i) ordW ∧
    ordW ≤ 2 * N₀ + 2 * lvlM i + 1 ∧
    st.regs 9 + ordW ≤ st.regs 4 ∧
    (∀ j < ordW, st.mem (st.regs 9 + j) < 2 ^ w)
  cores : ∀ j (hj : j < i),
    st.mem (branchTable + j) = chain.bran j ∧
    Rcore.rep (st.mem (levelTable + j)) (chainLevelOrdAbs chain j) (yCore j hj) st.mem ∧
    (∀ a, Rcore.foot (st.mem (levelTable + j)) (yCore j hj) a → levelsStart ≤ a ∧ a < st.regs 4) ∧
    (∀ j' (hj' : j' < i), j' ≠ j → ∀ a, Rcore.foot (st.mem (levelTable + j)) (yCore j hj) a →
      ¬ Rcore.foot (st.mem (levelTable + j')) (yCore j' hj') a)
  metaLevels : ∀ j, 1 ≤ j → j ≤ i → j < C.d →
    DynGraphAt st.mem (st.mem (levelMeta + C.d + j)) vCap eCap (chain.G j) ∧
    levelsStart ≤ st.mem (levelMeta + C.d + j) ∧
    st.mem (levelMeta + C.d + j) + dynGraphSize vCap eCap ≤ st.regs 4 ∧
    EdgeValuesAt st.mem (st.mem (levelMeta + j)) 4 L P_fp (chain.G j).E
      (chain.toTreeChain.chainLen ℓ₀ j) ∧
    levelsStart ≤ st.mem (levelMeta + j) ∧
    st.mem (levelMeta + j) + eCap * L ≤ st.regs 4 ∧
    (∀ r (hr : r < i),
      (∀ a, st.mem (levelMeta + j) ≤ a → a < st.mem (levelMeta + j) + eCap * L →
        ¬ Rcore.foot (st.mem (levelTable + r)) (yCore r hr) a) ∧
      (∀ a, st.mem (levelMeta + C.d + j) ≤ a →
        a < st.mem (levelMeta + C.d + j) + dynGraphSize vCap eCap →
        ¬ Rcore.foot (st.mem (levelTable + r)) (yCore r hr) a))
  metaOrd :
    (∀ j, 1 ≤ j → j ≤ i → j < C.d →
      st.mem (levelMeta + C.d + j) + dynGraphSize vCap eCap ≤ st.mem (levelMeta + j)) ∧
    (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ ≤ i → j₂ < C.d →
      st.mem (levelMeta + j₁) + eCap * L ≤ st.mem (levelMeta + C.d + j₂))
  handlesLe : ∀ j < i, levelsStart ≤ st.mem (levelTable + j) ∧ st.mem (levelTable + j) ≤ st.regs 4

theorem initLevelsLoop_runs
    {w L depth vCap eCap capExp capLimit init coreLenProc edgeProc signExt mul intDiv copy
      levelTable branchTable levelsStart lvlMTable levelMeta : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {p : Program} {opCore : ℕ → ℕ} {ω : ℕ → Bool}
    {G₀ : MGraph} {ℓ₀ g₀ : ℕ → ℝ} {initMem : ℕ → ℕ}
    (hFour : fmt.limbBits = 4)
    (hEq : ToolInitOrdEqOnE T)
    (hlocal : Rcore.Local)
    (hCoreImpl : ∀ i < C.d,
      Rcore.Implements w p init opCore
        (sparseCoreOrdMachineContractKFBL fmt L depth T
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G i)
          C.k (lvlM i) N₀ vCap eCap capExp P allocation) ∧
      SparseCoreReadoutFootAt fmt L depth T
        ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1.G i)
        C.k (lvlM i) N₀ vCap eCap capExp P allocation Rcore p opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hInitSpaceLe : ∀ i < C.d, ∀ g l gr o h,
      allocation 6 [g, l, gr, o, C.k, lvlM i, N₀, L, fmt.precision, depth, h] ≤ coreInitSpace i)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hTableLayout : levelTable + (C.d + 1) = branchTable ∧ branchTable + (C.d + 1) ≤ levelsStart)
    (hMetaLayout : lvlMTable + C.d = levelMeta ∧ levelMeta + 2 * C.d ≤ levelTable)
    (hMTab : ∀ i < C.d, initMem (lvlMTable + i) = lvlM i)
    (hk : 0 < C.k) (hwk : C.k < 2 ^ w) (hNw : N₀ < 2 ^ w) (hdW : C.d < 2 ^ w) (hw9 : 9 < 2 ^ w)
    (hPw : fmt.precision < 2 ^ w) (hDw : depth < 2 ^ w)
    (hMw : ∀ i < C.d, lvlM i < 2 ^ w)
    (hWord : ∀ i < C.d, (lvlM i + N₀ + 2) ^ P.wordExp * (L + 1) < 2 ^ w)
    (hModel :
      let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
      ∀ i < C.d,
        (chain.G i).m ≤ lvlM i ∧ (chain.G i).n ≤ N₀ ∧
        (∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen ℓ₀ i e) ∧
        IsRotationOrder (chain.G i) (chain.levelOrd i) ∧
        (chain.G (i + 1)).E ⊆ (chain.G i).E ∧
        (chain.G (i + 1)).m ≤ nextM i ∧
        (i + 1 < C.d → nextM i ≤ lvlM (i + 1)) ∧
        ordRotWords (chainLevelOrdAbs chain i) 0 ≤ 1 + 2 * N₀ + 2 * nextM i ∧
        (∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e))
    (hroom : levelsStart +
      ∑ j ∈ Finset.range C.d, ordLevelSpace L capExp capLimit (coreInitSpace j) (lvlM j) N₀ (nextM j) < 2 ^ w)
    (rem i : ℕ) (hsum : i + rem = C.d)
    (st : State) (yCore0 : ∀ j, j < i → Rcore.τ)
    (hInv : InitLevelsLoopInv (w := w) Rcore
      (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
      L fmt.precision depth vCap eCap capExp capLimit levelTable branchTable levelsStart
      lvlMTable levelMeta coreInitSpace lvlM nextM N₀ ℓ₀ g₀ initMem i st yCore0) :
    let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
    ∃ (out : State) (c : ℕ) (yCore : ∀ j, j < C.d → Rcore.τ),
      Runs w p ω (forUp 19 (.reg 21) (ordRebuildLevelBodyKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5)))
        st .normal out c ∧
      InitLevelsLoopInv (w := w) Rcore chain L fmt.precision depth vCap eCap capExp capLimit
        levelTable branchTable levelsStart lvlMTable levelMeta coreInitSpace lvlM nextM N₀ ℓ₀ g₀
        initMem C.d out yCore ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      c + (∑ j : Fin C.d, Rcore.phi (out.mem (levelTable + j.val)) (yCore j.val j.isLt) out.mem) ≤
        (∑ j ∈ Finset.range C.d, if i ≤ j then
            P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35
          else 0) +
        (∑ j : Fin i, Rcore.phi (st.mem (levelTable + j.val)) (yCore0 j.val j.isLt) st.mem) + 5 := by
  dsimp only
  set chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G₀ ℓ₀ g₀).1
  have hFacts := ordAlgorithm1_initialize_level_facts hEq lastTool C lvlM N₀ G₀ ℓ₀ g₀
  induction rem generalizing i st yCore0 with
  | zero =>
    have hieq : i = C.d := by omega
    subst hieq
    have hrCond : Runs w p ω
        (forUp 19 (.reg 21) (ordRebuildLevelBodyKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5)))
        st .normal st 4 :=
      runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, hInv.reg19, hInv.reg21, show 0 < 2 ^ w by omega],
        rfl, rfl, rfl⟩)
    refine ⟨st, 4, yCore0, hrCond, hInv, fun _ _ => rfl, ?_⟩
    have hzero : (∑ j ∈ Finset.range C.d,
        if C.d ≤ j then P.mul * T.cost (chain.scState j) +
          ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35 else 0) = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_range] at hj
      simp [show ¬ C.d ≤ j by omega]
    omega
  | succ rem ih =>
    have hi : i < C.d := by omega
    obtain ⟨hbr_i, hupd_i, hGsucc_i, hOrdSucc_i, hSc_i⟩ := hFacts.2.2.2.2 i hi
    obtain ⟨hGim, hGin, hGiPos, hGiRot, hHE_i, hHm_i, hNextLe_i, hRotW_i, hCLFits_i⟩ := hModel i hi
    obtain ⟨vc_i, ec_i, hvc_i, hec_i, _, hG_i, hGEnd_i, hGDisjL_i, hGDisjB_i, _,
        hLen_i, hLenEnd_i, hLenDisjL_i, hLenDisjB_i, _, hGrad_i, hGradEnd_i⟩ := hInv.curGraph
    subst hvc_i hec_i
    obtain ⟨ordW_i, hOrd_i, hOrdWLe_i, hOrdEnd_i, hOrdValW_i⟩ := hInv.curOrd hi
    have hSumPrefix :
        (∑ j ∈ Finset.range i, ordLevelSpace L capExp capLimit (coreInitSpace j) (lvlM j) N₀ (nextM j)) +
          ordLevelSpace L capExp capLimit (coreInitSpace i) (lvlM i) N₀ (nextM i) ≤
        ∑ j ∈ Finset.range C.d, ordLevelSpace L capExp capLimit (coreInitSpace j) (lvlM j) N₀ (nextM j) := by
      rw [← Finset.sum_range_succ]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) (fun _ _ _ => Nat.zero_le _)
    have hStepRoom : st.regs 4 + ordLevelSpace L capExp capLimit (coreInitSpace i) (lvlM i) N₀ (nextM i) < 2 ^ w := by
      have := hInv.heapHi; omega
    have hMCell_i : st.mem (lvlMTable + i) = lvlM i :=
      (hInv.frameBelow (lvlMTable + i) (by omega) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega))).trans (hMTab i hi)
    have ha0St :
        T.initOrd C.k (lvlM i) N₀ (chain.G i)
          (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
          (fun e => if e ∈ (chain.G i).E then
            (if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) else 0)
          (chain.levelOrd i) =
        chain.scState i := hSc_i.symm
    have ha0Eq :
        (⟨T.initOrd C.k (lvlM i) N₀ (chain.G i)
          (fun e => if e ∈ (chain.G i).E then chain.toTreeChain.chainLen ℓ₀ i e else 0)
          (fun e => if e ∈ (chain.G i).E then
            (if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e) else 0)
          (chain.levelOrd i), chain.G i, chain.levelOrd i, 0⟩ : SparseCoreOrdAbs T) =
        chainLevelOrdAbs chain i := by
      unfold chainLevelOrdAbs
      rw [ha0St, hupd_i]
    have hChainLenSucc :
        coreLen (T.lsfs (chain.scState i) 0) (chain.toTreeChain.chainLen ℓ₀ i) =
          chain.toTreeChain.chainLen ℓ₀ (i + 1) := by
      funext e
      change coreLen (T.lsfs (chain.scState i) 0) (chain.toTreeChain.chainLen ℓ₀ i) e =
        coreLen (chain.toTreeChain.activeLSF i) (chain.toTreeChain.chainLen ℓ₀ i) e
      have hact : chain.toTreeChain.activeLSF i = T.lsfs (chain.scState i) 0 := by
        unfold TreeChain.activeLSF
        simp only [ChainState.toTreeChain, hi, ↓reduceIte]
        exact congrArg (T.lsfs (chain.scState i)) hbr_i
      rw [hact]
    obtain ⟨s1, vcH, ecH, nextOrdW, cBody, y_i, rBody, hvcH, hecH, hcapH, hs1_hCell, hs1_bCell,
        hs1_19, hs1_51, hs1_52, hrep_i, hH_i, hLenNext_i, hs1_8, hOrdNext_i, hOrdNextLe_i,
        hOrdNextEnd_i, h9Lo_i, hOrdNextW_i, h6Lo_i, hHEnd_i, h6Disj_i, h7Lo_i, hLenNextEnd_i, h7Disj_i,
        h6Le7_i, h4Lo_i, h4Hi_i, hz1, hs1_frame, hfoot_i, hs1_regs, hcBody⟩ :=
      ordRebuildLevelBodyKFBL_runs_bounded (w := w) (L := L) (depth := depth) (k := C.k)
        (M := lvlM i) (N := N₀)
        (vCap := vc_i) (eCap := ec_i) (capExp := capExp) (capLimit := capLimit)
        (init := init) (coreLenProc := coreLenProc) (edgeProc := edgeProc)
        (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
        (graphBase := st.regs 6) (lenBase := st.regs 7) (gradBase := st.regs 8)
        (ordBase := st.regs 9) (ordWords := ordW_i) (heap := st.regs 4)
        (handleCell := levelTable + i) (branchCell := branchTable + i)
        (lvlMTable := lvlMTable) (idx := i) (nextM := nextM i)
        (fmt := fmt) (tool := T) (G := chain.G i) (P := P) (allocation := allocation)
        (coreInitSpace := coreInitSpace) (R := Rcore) (p := p) (op := opCore)
        (st := st) (ω := ω) (chain.toTreeChain.chainLen ℓ₀ i)
        (fun e => if i = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ i e)
        (chain.levelOrd i) hFour (hCoreImpl i hi).1 (hCoreImpl i hi).2 hcapLim
        (hInitSpaceLe i hi) hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
        rfl rfl rfl rfl rfl hInv.reg1 hInv.reg56 hInv.reg57 hInv.reg19 hInv.reg51 hInv.reg52
        hInv.reg67 hInv.reg68 hInv.reg98 hMCell_i (by have := hInv.heapLo; omega)
        hk hwk (hMw i hi) hNw hw9 hPw hDw (hWord i hi)
        (by omega) (by have := hInv.heapLo; omega) (by have := hInv.heapLo; omega)
        (by have := hInv.heapLo; omega) (by have := hInv.heapLo; omega)
        hG_i hGim hGin hGEnd_i
        (fun addr hlo hhi => ⟨by rcases hGDisjL_i addr hlo hhi with h | h <;> omega,
          by rcases hGDisjB_i addr hlo hhi with h | h <;> omega⟩)
        hLenEnd_i hGradEnd_i
        (fun addr hlo hhi => ⟨by rcases hLenDisjL_i addr hlo hhi with h | h <;> omega,
          by rcases hLenDisjB_i addr hlo hhi with h | h <;> omega⟩)
        hOrd_i hOrdWLe_i hOrdEnd_i hOrdValW_i hGiRot hLen_i hGrad_i hGiPos hInv.zeroFrom hStepRoom
        (by dsimp only; rw [ha0St, ← hGsucc_i]; exact hHE_i)
        (by dsimp only; rw [ha0St, ← hGsucc_i]; exact hHm_i)
        (by dsimp only; rw [ha0Eq]; exact hRotW_i)
        (by
          dsimp only
          rw [ha0St]
          intro e he
          rw [← hGsucc_i] at he
          simpa only [hChainLenSucc] using hCLFits_i e he)
    -- Conditional store of next-level length & graph pointers into `levelMeta`
    have hs1_21 : s1.regs 21 = C.d := (hs1_regs 21 (by omega)).trans hInv.reg21
    have hs1_58 : s1.regs 58 = levelMeta := (hs1_regs 58 (by omega)).trans hInv.reg58
    let condStmt : Stmt :=
      .cond (.bin .lt (.bin .add (.reg 19) (.const 1)) (.reg 21))
        (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7) ;;
         .store (.bin .add (.bin .add (.reg 58) (.reg 21)) (.bin .add (.reg 19) (.const 1))) (.reg 6))
        .nop
    have hCondStep : ∃ s1m cCond,
        Runs w p ω condStmt s1 .normal s1m cCond ∧ cCond ≤ 25 ∧
        s1m.regs = s1.regs ∧
        (i + 1 < C.d → s1m.mem (levelMeta + (i + 1)) = s1.regs 7 ∧
          s1m.mem (levelMeta + C.d + (i + 1)) = s1.regs 6) ∧
        (∀ a, (i + 1 < C.d → a ≠ levelMeta + (i + 1) ∧ a ≠ levelMeta + C.d + (i + 1)) →
          s1m.mem a = s1.mem a) := by
      by_cases hNextLt : i + 1 < C.d
      · let s1a := { s1 with mem := Function.update s1.mem (levelMeta + (i + 1)) (s1.regs 7) }
        let s1m := { s1a with mem := Function.update s1a.mem (levelMeta + C.d + (i + 1)) (s1.regs 6) }
        have rSt1 : Runs w p ω
            (.store (.bin .add (.reg 58) (.bin .add (.reg 19) (.const 1))) (.reg 7))
            s1 .normal s1a 7 :=
          runs_store_iff.mpr ⟨levelMeta + (i + 1), s1.regs 7,
            by simp [Expr.eval, BinOp.eval, hs1_58, hs1_19, show 1 < 2 ^ w by omega,
              show i + 1 < 2 ^ w by omega, show levelMeta + (i + 1) < 2 ^ w by omega],
            by simp [Expr.eval], rfl, rfl, rfl⟩
        have rSt2 : Runs w p ω
            (.store (.bin .add (.bin .add (.reg 58) (.reg 21))
              (.bin .add (.reg 19) (.const 1))) (.reg 6))
            s1a .normal s1m 9 :=
          runs_store_iff.mpr ⟨levelMeta + C.d + (i + 1), s1.regs 6,
            by simp [Expr.eval, BinOp.eval, s1a, hs1_58, hs1_21, hs1_19,
              show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by omega,
              show levelMeta + C.d < 2 ^ w by omega,
              show levelMeta + C.d + (i + 1) < 2 ^ w by omega],
            by simp [Expr.eval, s1a], rfl, rfl, rfl⟩
        have rC : Runs w p ω condStmt s1 .normal s1m 23 :=
          runs_cond_iff.mpr ⟨1, 7 + 9 + 1,
            by simp [Expr.eval, BinOp.eval, hs1_19, hs1_21, show 1 < 2 ^ w by omega,
              show i + 1 < 2 ^ w by omega, hNextLt],
            by simpa using runs_seq_iff.mpr (Or.inr ⟨s1a, 7, 9, rSt1, rSt2, rfl⟩),
            by simp [Expr.size]⟩
        exact ⟨s1m, 23, rC, by omega, rfl,
          fun _ => ⟨by simp [s1m, s1a, Function.update_of_ne
              (by omega : levelMeta + (i + 1) ≠ levelMeta + C.d + (i + 1))],
            by simp [s1m]⟩,
          fun a hne => by
            obtain ⟨h1, h2⟩ := hne hNextLt
            simp [s1m, s1a, Function.update_of_ne h1, Function.update_of_ne h2]⟩
      · have rC : Runs w p ω condStmt s1 .normal s1 7 :=
          runs_cond_iff.mpr ⟨0, 1,
            by simp [Expr.eval, BinOp.eval, hs1_19, hs1_21, show 1 < 2 ^ w by omega,
              show i + 1 < 2 ^ w by omega, hNextLt],
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, by simp [Expr.size]⟩
        exact ⟨s1, 7, rC, by omega, rfl, fun h => absurd h hNextLt, fun _ _ => rfl⟩
    obtain ⟨s1m, cCond, rCond, hcCond, hs1m_regs, hs1m_meta, hs1m_frame⟩ := hCondStep
    have hs1m_geStart (a : ℕ) (ha : levelsStart ≤ a) : s1m.mem a = s1.mem a :=
      hs1m_frame a (fun _ => ⟨by omega, by omega⟩)
    -- Increment loop counter `reg 19 := i + 1`
    let s2 : State := { s1m with regs := Function.update s1m.regs 19 (i + 1) }
    have rInc : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) s1m .normal s2 4 :=
      runs_assign_iff.mpr ⟨i + 1, by
        simp [Expr.eval, BinOp.eval, hs1m_regs, hs1_19, show 1 < 2 ^ w by omega, show i + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    let yCore1 : ∀ j, j < i + 1 → Rcore.τ := fun j hj =>
      if h : j < i then yCore0 j h else y_i
    have hs1m_hCell : s1m.mem (levelTable + i) = st.regs 4 :=
      (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans hs1_hCell
    have hs1m_bCell : s1m.mem (branchTable + i) = 0 :=
      (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans hs1_bCell
    have hNewCoreLoc := hlocal (st.regs 4) (chainLevelOrdAbs chain i) y_i s1.mem s1m.mem
      (fun a ha => (hs1m_geStart a (hInv.heapLo.trans (hfoot_i a ha).1)).symm)
    -- Preserve earlier cores `j < i` across body (footprints `< st.regs 4`, `≥ levelsStart`)
    have hOldCore (j : ℕ) (hj : j < i) :
        s2.mem (levelTable + j) = st.mem (levelTable + j) ∧
        s2.mem (branchTable + j) = chain.bran j ∧
        Rcore.rep (s2.mem (levelTable + j)) (chainLevelOrdAbs chain j) (yCore0 j hj) s2.mem ∧
        Rcore.phi (s2.mem (levelTable + j)) (yCore0 j hj) s2.mem =
          Rcore.phi (st.mem (levelTable + j)) (yCore0 j hj) st.mem ∧
        (∀ a, Rcore.foot (s2.mem (levelTable + j)) (yCore0 j hj) a → levelsStart ≤ a ∧ a < st.regs 4) := by
      obtain ⟨hbrJ, hrepJ, hfootJ, _⟩ := hInv.cores j hj
      have hlvJ : s1m.mem (levelTable + j) = st.mem (levelTable + j) :=
        (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
          (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
      have hbrJ' : s1m.mem (branchTable + j) = chain.bran j :=
        ((hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
          (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))).trans hbrJ
      have hlocJ := hlocal (st.mem (levelTable + j)) (chainLevelOrdAbs chain j) (yCore0 j hj)
        st.mem s1m.mem (fun a ha => by
          obtain ⟨hlo, hhi⟩ := hfootJ a ha
          exact ((hs1m_geStart a hlo).trans (hs1_frame a hhi (by omega) (by omega))).symm)
      refine ⟨hlvJ, hbrJ', ?_, ?_, fun a ha => hfootJ a (by rwa [hlvJ] at ha)⟩
      · change Rcore.rep (s1m.mem (levelTable + j)) _ _ s1m.mem; rw [hlvJ]; exact hlocJ.1 hrepJ
      · change Rcore.phi (s1m.mem (levelTable + j)) _ s1m.mem = _; rw [hlvJ]; exact hlocJ.2.symm
    have hInvNext : InitLevelsLoopInv (w := w) Rcore chain L fmt.precision depth vc_i ec_i capExp
        capLimit levelTable branchTable levelsStart lvlMTable levelMeta coreInitSpace lvlM nextM
        N₀ ℓ₀ g₀ initMem (i + 1) s2 yCore1 := by
      refine ⟨by simp [s2, hs1m_regs, hs1_regs 1 (by omega), hInv.reg1],
        by simp [s2],
        by simp [s2, hs1m_regs, hs1_21],
        by simp [s2, hs1m_regs, hs1_51, Nat.add_assoc],
        by simp [s2, hs1m_regs, hs1_52, Nat.add_assoc],
        by simp [s2, hs1m_regs, hs1_regs 56 (by omega), hInv.reg56],
        by simp [s2, hs1m_regs, hs1_regs 57 (by omega), hInv.reg57],
        by simp [s2, hs1m_regs, hs1_58],
        by simp [s2, hs1m_regs, hs1_regs 67 (by omega), hInv.reg67],
        by simp [s2, hs1m_regs, hs1_regs 68 (by omega), hInv.reg68],
        by simp [s2, hs1m_regs, hs1_regs 98 (by omega), hInv.reg98],
        by simp [s2, hs1m_regs]; exact hInv.heapLo.trans h4Lo_i,
        by simp [s2, hs1m_regs, Finset.sum_range_succ]; have := hInv.heapHi; omega,
        fun a ha => by
          have ha' : s1.regs 4 ≤ a := by simpa [s2, hs1m_regs] using ha
          exact (hs1m_geStart a ((hInv.heapLo.trans h4Lo_i).trans ha')).trans (hz1 a ha'),
        fun a ha hL' hB' hML' hMG' => by
          change s1m.mem a = initMem a
          rw [hs1m_frame a (fun hlt' => ⟨by rcases hML' with h | h <;> omega,
                by rcases hMG' with h | h <;> omega⟩),
            hs1_frame a (ha.trans_le hInv.heapLo) (by rcases hL' with h | h <;> omega)
              (by rcases hB' with h | h <;> omega)]
          exact hInv.frameBelow a ha (by rcases hL' with h | h <;> omega)
            (by rcases hB' with h | h <;> omega) hML' hMG',
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨vcH, ecH, hvcH, hecH, hcapH, ?_, by simpa [s2, hs1m_regs] using hHEnd_i,
          ?_, ?_, ?_, ?_, by simpa [s2, hs1m_regs] using hLenNextEnd_i, ?_, ?_, ?_, ?_,
          by simpa [s2, hs1m_regs, hs1_8] using hLenNextEnd_i⟩
        · change DynGraphAt s1m.mem (s1m.regs 6) vcH ecH (chain.G (i + 1))
          rw [hs1m_regs, hGsucc_i]; rw [ha0Eq] at hH_i
          exact dynGraphAt_of_agree hH_i (fun a hlo _ => hs1m_geStart a (hInv.heapLo.trans (h6Lo_i.trans hlo)))
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (6 : ℕ) ≠ 19)] at hlo; omega)
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (6 : ℕ) ≠ 19)] at hlo; omega)
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (6 : ℕ) ≠ 19)] at hlo; omega)
        · change EdgeValuesAt s1m.mem (s1m.regs 7) 4 L fmt.precision (chain.G (i + 1)).E
            (chain.toTreeChain.chainLen ℓ₀ (i + 1))
          rw [hs1m_regs, hGsucc_i, ← hChainLenSucc]; rw [ha0Eq] at hLenNext_i
          exact hLenNext_i.congr (fun _ _ _ _ => hs1m_geStart _ (by have := hInv.heapLo; omega))
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (7 : ℕ) ≠ 19)] at hlo; omega)
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (7 : ℕ) ≠ 19)] at hlo; omega)
        · intro a hlo _
          exact Or.inr (by have := hInv.heapLo; simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (7 : ℕ) ≠ 19)] at hlo; omega)
        · change EdgeValuesAt s1m.mem (s1m.regs 8) 4 L fmt.precision (chain.G (i + 1)).E
            (fun e => if i + 1 = 0 then g₀ e else chain.toTreeChain.chainLen ℓ₀ (i + 1) e)
          simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
          rw [hs1m_regs, hs1_8, hGsucc_i, ← hChainLenSucc]; rw [ha0Eq] at hLenNext_i
          exact hLenNext_i.congr (fun _ _ _ _ => hs1m_geStart _ (by have := hInv.heapLo; omega))
      · intro hi1
        refine ⟨nextOrdW, ?_, ?_, by simpa [s2, hs1m_regs] using hOrdNextEnd_i, ?_⟩
        · change OrdListAt s1m.mem (s1m.regs 9) (chain.levelOrd (i + 1)) nextOrdW
          rw [hs1m_regs, hOrdSucc_i]; rw [ha0Eq] at hOrdNext_i
          exact ordListAt_of_agree hOrdNext_i (fun j _ =>
            hs1m_geStart _ (by have := hInv.heapLo; omega))
        · rw [ha0Eq] at hOrdNextLe_i
          have hnm := hNextLe_i hi1
          omega
        · intro j hj
          change s1m.mem (s1m.regs 9 + j) < 2 ^ w
          rw [hs1m_regs, hs1m_geStart _ (by have := hInv.heapLo; omega)]
          exact hOrdNextW_i j hj
      · intro j hj
        by_cases hjlt : j < i
        · simp only [yCore1, hjlt, ↓reduceDIte]
          obtain ⟨hlvJ, hbrJ', hrepJ', _, hfootJ'⟩ := hOldCore j hjlt
          refine ⟨hbrJ', hrepJ',
            fun a ha => ⟨(hfootJ' a ha).1, by simp [s2, hs1m_regs]; exact (hfootJ' a ha).2.trans_le h4Lo_i⟩,
            fun j' hj' hne a ha hfj' => ?_⟩
          by_cases hj'lt : j' < i
          · simp only [hj'lt, ↓reduceDIte] at hfj'
            have h1 := (hInv.cores j hjlt).2.2.2 j' hj'lt hne a (by rwa [hlvJ] at ha)
            rw [(hOldCore j' hj'lt).1] at hfj'
            exact h1 hfj'
          · have hj'i : j' = i := by omega
            subst hj'i
            simp only [hj'lt, ↓reduceDIte] at hfj'
            change Rcore.foot (s1m.mem (levelTable + j')) y_i a at hfj'
            rw [hs1m_hCell] at hfj'
            have h1 := (hfootJ' a ha).2
            have h2 := (hfoot_i a hfj').1
            omega
        · have hji : j = i := by omega
          subst hji
          simp only [yCore1, hjlt, ↓reduceDIte]
          refine ⟨by change s1m.mem (branchTable + j) = _; rw [hs1m_bCell, hbr_i],
            by change Rcore.rep (s1m.mem (levelTable + j)) _ _ s1m.mem
               rw [hs1m_hCell]; exact hNewCoreLoc.1 (ha0Eq ▸ hrep_i),
            fun a ha => by
              change Rcore.foot (s1m.mem (levelTable + j)) y_i a at ha
              rw [hs1m_hCell] at ha
              have := hfoot_i a ha
              simp only [s2, hs1m_regs, Function.update_of_ne (by decide : (4 : ℕ) ≠ 19)]
              exact ⟨hInv.heapLo.trans this.1, this.2⟩,
            fun j' hj' hne a ha hfj' => by
              have hj'lt : j' < j := by omega
              simp only [hj'lt, ↓reduceDIte] at hfj'
              change Rcore.foot (s1m.mem (levelTable + j)) y_i a at ha
              rw [hs1m_hCell] at ha
              have h1 := (hfoot_i a ha).1
              have h2 := ((hOldCore j' hj'lt).2.2.2.2 a hfj').2
              omega⟩
      · intro j hj1 hjle hjLt
        by_cases hjOld : j ≤ i
        · obtain ⟨hDGJ, hGLoJ, hGHiJ, hLenJ, hLLoJ, hLHiJ, hDisjJ⟩ := hInv.metaLevels j hj1 hjOld hjLt
          have hLCell : s1m.mem (levelMeta + j) = st.mem (levelMeta + j) :=
            (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
              (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
          have hGCell : s1m.mem (levelMeta + C.d + j) = st.mem (levelMeta + C.d + j) :=
            (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
              (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
          have hAgreeOld (a : ℕ) (hlo : levelsStart ≤ a) (hhi : a < st.regs 4) :
              s1m.mem a = st.mem a :=
            (hs1m_geStart a hlo).trans (hs1_frame a hhi (by omega) (by omega))
          refine ⟨by change DynGraphAt s1m.mem (s1m.mem (levelMeta + C.d + j)) _ _ _
                     rw [hGCell]; exact dynGraphAt_of_agree hDGJ (fun a ha1 ha2 => hAgreeOld a (by omega) (by omega)),
            by change levelsStart ≤ s1m.mem (levelMeta + C.d + j); rw [hGCell]; exact hGLoJ,
            by change s1m.mem (levelMeta + C.d + j) + _ ≤ s2.regs 4
               rw [hGCell]; simp [s2, hs1m_regs]; exact hGHiJ.trans h4Lo_i,
            by change EdgeValuesAt s1m.mem (s1m.mem (levelMeta + j)) _ _ _ _ _
               rw [hLCell]; exact hLenJ.congr (fun e he t ht => by
                 have heLt := hDGJ.2.2.1 e he
                 have hmul : e * L + L ≤ ec_i * L := by
                   have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
                 exact hAgreeOld _ (by omega) (by omega)),
            by change levelsStart ≤ s1m.mem (levelMeta + j); rw [hLCell]; exact hLLoJ,
            by change s1m.mem (levelMeta + j) + _ ≤ s2.regs 4
               rw [hLCell]; simp [s2, hs1m_regs]; exact hLHiJ.trans h4Lo_i,
            fun r hr => ?_⟩
          by_cases hrOld : r < i
          · simp only [yCore1, hrOld, ↓reduceDIte]
            refine ⟨fun a ha1 ha2 hf => ?_, fun a ha1 ha2 hf => ?_⟩
            · rw [hLCell] at ha1 ha2; rw [(hOldCore r hrOld).1] at hf
              exact (hDisjJ r hrOld).1 a ha1 ha2 hf
            · rw [hGCell] at ha1 ha2; rw [(hOldCore r hrOld).1] at hf
              exact (hDisjJ r hrOld).2 a ha1 ha2 hf
          · have hri : r = i := by omega
            subst hri
            simp only [yCore1, hrOld, ↓reduceDIte]
            refine ⟨fun a ha1 ha2 hf => ?_, fun a ha1 ha2 hf => ?_⟩
            · rw [hLCell] at ha1 ha2
              change Rcore.foot (s1m.mem (levelTable + r)) y_i a at hf
              rw [hs1m_hCell] at hf; have := (hfoot_i a hf).1; omega
            · rw [hGCell] at ha1 ha2
              change Rcore.foot (s1m.mem (levelTable + r)) y_i a at hf
              rw [hs1m_hCell] at hf; have := (hfoot_i a hf).1; omega
        · have hji1 : j = i + 1 := by omega
          subst hji1
          obtain ⟨hLPtr, hGPtr⟩ := hs1m_meta hjLt
          have hG1 : DynGraphAt s1m.mem (s1.regs 6) vc_i ec_i (chain.G (i + 1)) := by
            rw [hvcH] at hH_i; rw [hecH] at hH_i; rw [hGsucc_i]; rw [ha0Eq] at hH_i
            exact dynGraphAt_of_agree hH_i (fun a hlo _ => hs1m_geStart a (hInv.heapLo.trans (h6Lo_i.trans hlo)))
          have hL1 : EdgeValuesAt s1m.mem (s1.regs 7) 4 L fmt.precision (chain.G (i + 1)).E
              (chain.toTreeChain.chainLen ℓ₀ (i + 1)) := by
            rw [hGsucc_i, ← hChainLenSucc]; rw [ha0Eq] at hLenNext_i
            exact hLenNext_i.congr (fun _ _ _ _ => hs1m_geStart _ (by have := hInv.heapLo; omega))
          refine ⟨by change DynGraphAt s1m.mem (s1m.mem (levelMeta + C.d + (i + 1))) _ _ _
                     rw [hGPtr]; exact hG1,
            by change levelsStart ≤ s1m.mem (levelMeta + C.d + (i + 1)); rw [hGPtr]; exact hInv.heapLo.trans h6Lo_i,
            by change s1m.mem (levelMeta + C.d + (i + 1)) + _ ≤ s2.regs 4
               rw [hGPtr]; simp [s2, hs1m_regs]; rwa [hvcH, hecH] at hHEnd_i,
            by change EdgeValuesAt s1m.mem (s1m.mem (levelMeta + (i + 1))) _ _ _ _ _
               rw [hLPtr]; exact hL1,
            by change levelsStart ≤ s1m.mem (levelMeta + (i + 1)); rw [hLPtr]; exact hInv.heapLo.trans h7Lo_i,
            by change s1m.mem (levelMeta + (i + 1)) + _ ≤ s2.regs 4
               rw [hLPtr]; simp [s2, hs1m_regs]; rwa [hecH] at hLenNextEnd_i,
            fun r hr => ?_⟩
          by_cases hrOld : r < i
          · simp only [yCore1, hrOld, ↓reduceDIte]
            refine ⟨fun a ha1 _ hf => ?_, fun a ha1 _ hf => ?_⟩
            · rw [hLPtr] at ha1; have := ((hOldCore r hrOld).2.2.2.2 a hf).2; omega
            · rw [hGPtr] at ha1; have := ((hOldCore r hrOld).2.2.2.2 a hf).2; omega
          · have hri : r = i := by omega
            subst hri
            simp only [yCore1, hrOld, ↓reduceDIte]
            refine ⟨fun a ha1 ha2 hf => ?_, fun a ha1 ha2 hf => ?_⟩
            · rw [hLPtr] at ha1 ha2
              change Rcore.foot (s1m.mem (levelTable + r)) y_i a at hf
              rw [hs1m_hCell] at hf; exact h7Disj_i a ha1 (by rwa [← hecH] at ha2) hf
            · rw [hGPtr] at ha1 ha2
              change Rcore.foot (s1m.mem (levelTable + r)) y_i a at hf
              rw [hs1m_hCell] at hf; exact h6Disj_i a ha1 (by rwa [← hvcH, ← hecH] at ha2) hf
      · refine ⟨fun j hj1 hjle hjLt => ?_, fun j₁ j₂ hj1 hlt hj2le hj2Lt => ?_⟩
        · by_cases hjOld : j ≤ i
          · have hLCell : s1m.mem (levelMeta + j) = st.mem (levelMeta + j) :=
              (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
                (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
            have hGCell : s1m.mem (levelMeta + C.d + j) = st.mem (levelMeta + C.d + j) :=
              (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
                (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
            change s1m.mem (levelMeta + C.d + j) + dynGraphSize vc_i ec_i ≤ s1m.mem (levelMeta + j)
            rw [hGCell, hLCell]; exact hInv.metaOrd.1 j hj1 hjOld hjLt
          · have hji1 : j = i + 1 := by omega
            subst hji1
            obtain ⟨hLPtr, hGPtr⟩ := hs1m_meta hjLt
            change s1m.mem (levelMeta + C.d + (i + 1)) + dynGraphSize vc_i ec_i ≤ s1m.mem (levelMeta + (i + 1))
            rw [hGPtr, hLPtr]; rwa [hvcH, hecH] at h6Le7_i
        · have hLCell₁ : s1m.mem (levelMeta + j₁) = st.mem (levelMeta + j₁) :=
            (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
              (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
          by_cases hj2Old : j₂ ≤ i
          · have hGCell₂ : s1m.mem (levelMeta + C.d + j₂) = st.mem (levelMeta + C.d + j₂) :=
              (hs1m_frame _ (fun _ => ⟨by omega, by omega⟩)).trans
                (hs1_frame _ (by have := hInv.heapLo; omega) (by omega) (by omega))
            change s1m.mem (levelMeta + j₁) + ec_i * L ≤ s1m.mem (levelMeta + C.d + j₂)
            rw [hLCell₁, hGCell₂]; exact hInv.metaOrd.2 j₁ j₂ hj1 hlt hj2Old hj2Lt
          · have hj2i1 : j₂ = i + 1 := by omega
            subst hj2i1
            obtain ⟨_, hGPtr⟩ := hs1m_meta hj2Lt
            have hLHi₁ := (hInv.metaLevels j₁ hj1 (by omega) (by omega)).2.2.2.2.2.1
            change s1m.mem (levelMeta + j₁) + ec_i * L ≤ s1m.mem (levelMeta + C.d + (i + 1))
            rw [hLCell₁, hGPtr]; omega
      · intro j hj
        by_cases hjlt : j < i
        · rw [(hOldCore j hjlt).1]; simp [s2, hs1m_regs]
          exact ⟨(hInv.handlesLe j hjlt).1, (hInv.handlesLe j hjlt).2.trans h4Lo_i⟩
        · have hji : j = i := by omega
          subst hji; change levelsStart ≤ s1m.mem (levelTable + j) ∧ s1m.mem (levelTable + j) ≤ s2.regs 4
          rw [hs1m_hCell]; simp [s2, hs1m_regs]; exact ⟨hInv.heapLo, h4Lo_i⟩
    obtain ⟨out, cRest, yCoreFin, rRest, hInvFin, hOutRegs, hcRest⟩ :=
      ih (i + 1) (by omega) s2 yCore1 hInvNext
    have rBodyStore : Runs w p ω
        (ordRebuildLevelBodyKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5))
        st .normal s1m (cBody + cCond + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, cBody, cCond, rBody, rCond, rfl⟩)
    have rCondTrue :
        Runs w p ω (forUp 19 (.reg 21)
            (ordRebuildLevelBodyKFBLStore init (opCore 3) (opCore 2) coreLenProc (opCore 5)))
          st .normal out (3 + ((cBody + cCond + 1) + 4 + 1) + cRest + 1) := by
      refine runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s2, (cBody + cCond + 1) + 4 + 1, cRest,
        by simp [Expr.eval, BinOp.eval, hInv.reg19, hInv.reg21, hi, show 1 < 2 ^ w by omega],
        by decide,
        runs_seq_iff.mpr (Or.inr ⟨s1m, cBody + cCond + 1, 4, rBodyStore, rInc, rfl⟩),
        rRest, by simp [Expr.size]⟩))
    refine ⟨out, _, yCoreFin, rCondTrue, hInvFin, fun r hr => by
      rw [hOutRegs r hr]
      simp only [s2, hs1m_regs, Function.update_of_ne (show r ≠ 19 by omega)]
      exact hs1_regs r (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))), ?_⟩
    -- Telescope potential sum across iteration `i`
    have hSumPhi1 :
        (∑ j : Fin (i + 1), Rcore.phi (s2.mem (levelTable + j.val)) (yCore1 j.val j.isLt) s2.mem) =
        (∑ j : Fin i, Rcore.phi (st.mem (levelTable + j.val)) (yCore0 j.val j.isLt) st.mem) +
          Rcore.phi (st.regs 4) y_i s1.mem := by
      rw [Fin.sum_univ_castSucc]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Fin.val_castSucc, yCore1, j.isLt, ↓reduceDIte]
        exact (hOldCore j.val j.isLt).2.2.2.1
      · simp only [Fin.val_last, yCore1, lt_irrefl, ↓reduceDIte]
        change Rcore.phi (s1m.mem (levelTable + i)) y_i s1m.mem = _
        rw [hs1m_hCell]; exact hNewCoreLoc.2.symm
    have hSumBoundSplit :
        (∑ j ∈ Finset.range C.d, if i ≤ j then
            P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35
          else 0) =
        (P.mul * T.cost (chain.scState i) +
          ordLevelFixedCost L capExp capLimit P (lvlM i) N₀ (nextM i) + 35) +
        (∑ j ∈ Finset.range C.d, if i + 1 ≤ j then
            P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35
          else 0) := by
      have hterm : ∀ j ∈ Finset.range C.d,
          (if i ≤ j then P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35 else 0) =
          (if j = i then P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35 else 0) +
          (if i + 1 ≤ j then P.mul * T.cost (chain.scState j) +
              ordLevelFixedCost L capExp capLimit P (lvlM j) N₀ (nextM j) + 35 else 0) := by
        intro j _; by_cases h1 : j = i <;> by_cases h2 : i + 1 ≤ j <;> simp [h1, h2] <;> omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [hi]
    dsimp only at hcBody
    rw [ha0St] at hcBody
    have hcBody' : cBody + Rcore.phi (st.regs 4) y_i s1.mem ≤
        P.mul * T.cost (chain.scState i) +
          ordLevelFixedCost L capExp capLimit P (lvlM i) N₀ (nextM i) := hcBody
    rw [hSumPhi1] at hcRest
    rw [hSumBoundSplit]
    omega

end MinCostFlow.MinRatio
