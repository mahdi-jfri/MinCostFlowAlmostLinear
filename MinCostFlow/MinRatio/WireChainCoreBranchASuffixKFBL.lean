module

public import MinCostFlow.MinRatio.WireShiftDeepCollectKFBL
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreBranchA
public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBL
import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBLOrd
import MinCostFlow.MinRatio.WireShiftDeepPhase3
import MinCostFlow.MinRatio.WireShiftDeepPrep
import WordRAM.Tactic

/-!
# Branch A suffix execution under `KFBL` (`WireChainCoreBranchASuffixKFBL`)

Runs the Branch A suffix under `sparseCoreOrdMachineContractKFBL`
(`ordRebuildSuffixProgramKFBLStore_runs` + `shiftDeepCollectNewKFBL_runs`):
1. Increments `rebuildCount[0]` via `incrementLevelCounter`.
2. Rebuilds all chain levels `0 .. d` via `ordRebuildSuffixProgramKFBLStore_runs` with uniform
   caps `(vCap, eCap)` (`vCap = n`, `eCap = rootECap`).
3. Zeroes `updCount[0 .. d - 1]` via `wireZeroUpdCountLoop_runs`.
4. Collects the rebuilt active forest pointers into `newPtrs[0 .. d]` via
   `shiftDeepCollectNewKFBL_runs`.

Branch A rebuilds every level, so the select part reads no slot (`firstReb = 0`), and the suffix
writes none. It takes no companion of the core beyond `UpdateCoreCoreKFBL`, whose
`SparseCoreReadoutFootAt` places the forests that the collection reads.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle

/-- Suffix of Branch A under `KFBL`: increments `rebuildCount[0]`, sets up suffix-rebuild
registers (keeping `reg 98 = depth`), calls `ordRebuildSuffixProgramKFBLStore` on `0 .. d`,
zeroes `updCount[0 .. d - 1]`, and collects the new forests into `newPtrs[0 .. d]`. -/
@[expose] def wireBranchASuffixStmtKFBL
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
  .assign 56 (.load (.bin .sub (.reg 82) (.const 1))) ;;
  .assign 57 (.reg 82) ;;
  .assign 58 (.reg 83) ;;
  .assign 67 (.reg 94) ;;
  .assign 68 (.reg 95) ;;
  ordRebuildSuffixProgramKFBLStore initCore readGraph readLSF coreLenProc readOrd lastInit ;;
  .assign 20 (.const 0) ;;
  wireZeroUpdCountLoop ;;
  (.assign 20 (.reg 71) ;;
   collectLSFForestsLoop readLSF 81 ;;
   collectTermForestStmt 81)

theorem wireBranchASuffixStmtKFBL_noRand
    (initCore readGraph readLSF coreLenProc readOrd lastInit : ℕ) :
    (wireBranchASuffixStmtKFBL initCore readGraph readLSF coreLenProc readOrd lastInit).NoRand := by
  simp [wireBranchASuffixStmtKFBL, incrementLevelCounter_noRand,
    ordRebuildSuffixProgramKFBLStore_noRand, wireZeroUpdCountLoop_noRand,
    collectLSFForestsLoop_noRand, collectTermForestStmt_noRand, Stmt.NoRand]

set_option maxHeartbeats 800000 in
/-- Execute `wireBranchASuffixStmtKFBL` starting from the post-prefix state `st` (where `reg 28 =
newLen0`, `reg 29 = newLvlGraph0`, `reg 30 = ordPtr0`, `reg 4 = heap3`, and
`reg 98 = Expander.chosenL (cfg.P.M₀ ^ 2)`). -/
theorem wireBranchASuffixKFBL_runs
    {w L P m capExp capLimit fcap lastMul intCapMax forestEdgeCap drainUnit edMul mThresh
      wordExp stretchPrec vCap eCap
      initCore coreLenProc edgeProc signExt mul intDiv copy lastInit
      intCap ordW
      handleBase branchBase lvlMTable levelMeta rebuildCountBase updCountBase
      newPtrs newLen0 newLvlGraph0 ordPtr0 heap0 heap1 heap3 : ℕ}
    {coreSpace coreFixed : ℕ → ℕ} {toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {G : MGraph} {Psc : SparseCoreOrdParams}
    {levelSpace : ℕ → ℕ} {levelCost : ChainState cfg.T cfg.P → ℕ → ℕ}
    {updStepSpace : ℕ → ℕ → ℕ} {lastSpace termUpdSpace : ℕ}
    {allocation lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {st : State}
    (st0 : ChainState cfg.T cfg.P) (Gstart : MGraph) (ℓstart gstart : ℕ → ℝ) (extraEnc : ℕ)
    (hCoreLocal : Rcore.Local)
    (hFour : fmt.limbBits = 4) (hPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hLWord : L < 2 ^ w) (hPWord : P < 2 ^ w)
    (hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w)
    (hdPos : 0 < cfg.P.d) (hdW : cfg.P.d < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hNW : st0.N₀ < 2 ^ w)
    (hw18 : 18 < 2 ^ w)
    (hCapLim : vCap + eCap + 2 ≤ capLimit)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T) (hWordExpEq : Psc.wordExp = wordExp)
    (hCoreImpl : UpdateCoreCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hLastImpl : ∀ H : MGraph,
      H.m ≤ m → H.m ≤ levelM cfg.TP cfg.P cfg.P.d → H.n ≤ H.m + 1 →
      (∀ u ∈ H.V, ∀ v ∈ H.V, H.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision H.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L H vCap eCap lastMul stretchPrec lastAlloc))
    {stepCap : ℕ → ℕ → ℕ}
    (hOps : UpdateCoreOpsHypKFBL (w := w) (L := L) (P := P) (m := m) (capExp := capExp)
      (capLimit := capLimit) (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (drainUnit := drainUnit) (edMul := edMul)
      (mThresh := mThresh) (coreSpace := coreSpace) (coreFixed := coreFixed) (toolMul := toolMul)
      (fmt := fmt) (cfg := cfg) (G := G) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) levelSpace levelCost updStepSpace lastSpace termUpdSpace stepCap)
    (hRebInv : UpdateRebuildModelInv w L P wordExp stretchPrec st0 0 Gstart ℓstart gstart extraEnc)
    (hGstartM : Gstart.m ≤ m)
    (hNextFacts :
      let stLG : ChainState cfg.T cfg.P := { st0 with ℓ := ℓstart, g := gstart }
      let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 Gstart extraEnc).1
      ShiftLoopLevelFacts cfg next ∧
      (∀ j ≤ cfg.P.d, (next.G j).IsValid ∧ (next.G j).n ≤ next.N₀) ∧
      (∀ j < cfg.P.d,
        ordRotWords (chainLevelOrdAbs next j) (next.bran j) ≤
          1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m) ∧
      (∀ j < cfg.P.d, (cfg.T.lsfs (next.scState j) (next.bran j)).F.F.E ⊆ Gstart.E) ∧
      (next.lastLSFs next.lastBran).F.F.E ⊆ Gstart.E ∧
      (∀ j ≤ cfg.P.d, (next.G j).m ≤ levelM cfg.TP cfg.P j) ∧
      (∀ u ∈ (next.G cfg.P.d).V, ∀ v ∈ (next.G cfg.P.d).V, (next.G cfg.P.d).Connected u v))
    (hRegs :
      st.regs 4 = heap3 ∧ st.regs 28 = newLen0 ∧ st.regs 29 = newLvlGraph0 ∧
      st.regs 30 = ordPtr0 ∧ st.regs 71 = 0 ∧
      st.regs 75 = cfg.P.d ∧ st.regs 76 = cfg.P.k ∧ st.regs 77 = handleBase ∧
      st.regs 78 = branchBase ∧ st.regs 81 = newPtrs ∧ st.regs 82 = lvlMTable ∧
      st.regs 83 = levelMeta ∧ st.regs 85 = updCountBase ∧ st.regs 86 = rebuildCountBase ∧
      st.regs 94 = L ∧ st.regs 95 = P ∧ st.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2))
    (hN0Cell : st.mem (lvlMTable - 1) = st0.N₀)
    (hRC0 : st.mem rebuildCountBase = st0.rebuildCount 0)
    (hLvlM : ∀ j < cfg.P.d, st.mem (lvlMTable + j) = st0.lvlM j)
    (hG0 : DynGraphAt st.mem newLvlGraph0 vCap eCap Gstart)
    (hLen0 : EdgeValuesAt st.mem newLen0 4 L P Gstart.E ℓstart)
    (hOrd0 : OrdListAt st.mem ordPtr0 (sortedEnds Gstart) ordW)
    (hOrdW : ∀ t < ordW, st.mem (ordPtr0 + t) < 2 ^ w)
    (hOrdWLe : ordW ≤ 2 * Gstart.n + 2 * Gstart.m + 1)
    (hLMd0 : st.mem (levelMeta + cfg.P.d) = newLvlGraph0)
    (hIntCap : ∀ e ∈ Gstart.E, e < intCap)
    (hBounds :
      1 ≤ lvlMTable ∧ handleBase + cfg.P.d < heap0 ∧ branchBase + cfg.P.d < heap0 ∧
      lvlMTable + cfg.P.d ≤ heap0 ∧ levelMeta + 2 * cfg.P.d ≤ heap0 ∧
      rebuildCountBase < heap0 ∧ updCountBase + cfg.P.d ≤ heap0 ∧
      newPtrs + (cfg.P.d + 1) ≤ heap0 ∧
      heap0 ≤ heap1 ∧ heap1 ≤ heap3 ∧
      heap1 ≤ newLen0 ∧ newLen0 + eCap * L ≤ heap3 ∧
      heap1 ≤ newLvlGraph0 ∧ newLvlGraph0 + dynGraphSize vCap eCap ≤ heap3 ∧
      heap1 ≤ ordPtr0 ∧ ordPtr0 + ordW ≤ heap3)
    (hSep :
      let d := cfg.P.d
      (handleBase + d < branchBase ∨ branchBase + d < handleBase) ∧
      (handleBase + d < lvlMTable ∨ lvlMTable + d ≤ handleBase) ∧
      (branchBase + d < lvlMTable ∨ lvlMTable + d ≤ branchBase) ∧
      (handleBase + d < levelMeta ∨ levelMeta + 2 * d ≤ handleBase) ∧
      (branchBase + d < levelMeta ∨ levelMeta + 2 * d ≤ branchBase) ∧
      (lvlMTable + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ lvlMTable) ∧
      rebuildCountBase ≠ lvlMTable - 1 ∧
      (rebuildCountBase < lvlMTable ∨ lvlMTable + d ≤ rebuildCountBase) ∧
      (rebuildCountBase < handleBase ∨ handleBase + d < rebuildCountBase) ∧
      (rebuildCountBase < branchBase ∨ branchBase + d < rebuildCountBase) ∧
      (rebuildCountBase < levelMeta ∨ levelMeta + 2 * d ≤ rebuildCountBase) ∧
      (rebuildCountBase < updCountBase ∨ updCountBase + d ≤ rebuildCountBase) ∧
      (updCountBase + d ≤ handleBase ∨ handleBase + d < updCountBase) ∧
      (updCountBase + d ≤ branchBase ∨ branchBase + d < updCountBase) ∧
      (updCountBase + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ updCountBase) ∧
      (handleBase + d < newPtrs ∨ newPtrs + (d + 1) ≤ handleBase) ∧
      (branchBase + d < newPtrs ∨ newPtrs + (d + 1) ≤ branchBase) ∧
      (levelMeta + 2 * d ≤ newPtrs ∨ newPtrs + (d + 1) ≤ levelMeta) ∧
      (updCountBase + d ≤ newPtrs ∨ newPtrs + (d + 1) ≤ updCountBase) ∧
      (rebuildCountBase < newPtrs ∨ newPtrs + (d + 1) ≤ rebuildCountBase))
    (hz : ZeroFrom st.mem heap3)
    (hRoom : heap3 + (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d < 2 ^ w)
    (hTok0 : Rcore.τ) :
    let d := cfg.P.d
    let stLG : ChainState cfg.T cfg.P := { st0 with ℓ := ℓstart, g := gstart }
    let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 Gstart extraEnc).1
    ∃ (out : State) (cost termTok : ℕ) (coreTok : ℕ → Rcore.τ),
      Runs w p ω
        (wireBranchASuffixStmtKFBL initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
        st .normal out cost ∧
      heap3 ≤ out.regs 4 ∧
      out.regs 4 ≤ heap3 + (Finset.range d).sum levelSpace + lastSpace + 5 * d ∧
      ZeroFrom out.mem (out.regs 4) ∧
      (∀ r, 70 ≤ r → out.regs r = st.regs r) ∧
      ForestPtrListAt out.mem newPtrs (chainSuffixForests next 0) intCap (out.regs 4) ∧
      (∀ j < d,
        out.mem (branchBase + j) = next.bran j ∧
        heap3 ≤ out.mem (handleBase + j) ∧ out.mem (handleBase + j) ≤ out.regs 4 ∧
        Rcore.rep (out.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok j) out.mem ∧
        (∀ a, Rcore.foot (out.mem (handleBase + j)) (coreTok j) a → heap3 ≤ a ∧ a < out.regs 4)) ∧
      (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
        ∀ a, Rcore.foot (out.mem (handleBase + j₁)) (coreTok j₁) a →
          ¬ Rcore.foot (out.mem (handleBase + j₂)) (coreTok j₂) a) ∧
      (∀ j, 1 ≤ j → j < d →
        DynGraphAt out.mem (out.mem (levelMeta + d + j)) vCap eCap (next.G j) ∧
        heap3 ≤ out.mem (levelMeta + d + j) ∧
        out.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ out.regs 4 ∧
        EdgeValuesAt out.mem (out.mem (levelMeta + j)) 4 L P (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        heap3 ≤ out.mem (levelMeta + j) ∧
        out.mem (levelMeta + j) + eCap * L ≤ out.regs 4 ∧
        (∀ r < d,
          (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + eCap * L →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a) ∧
          (∀ a, out.mem (levelMeta + d + j) ≤ a →
            a < out.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (out.mem (handleBase + r)) (coreTok r) a)) ∧
        (∀ a, out.mem (levelMeta + j) ≤ a → a < out.mem (levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).foot
            (out.mem (handleBase + d)) termTok a) ∧
        (∀ a, out.mem (levelMeta + d + j) ≤ a →
          a < out.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).foot
            (out.mem (handleBase + d)) termTok a)) ∧
      out.mem (branchBase + d) = next.lastBran ∧
      heap3 ≤ out.mem (handleBase + d) ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).rep
        (out.mem (handleBase + d)) (next.lastK, next.lastLSFs) termTok out.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).foot
          (out.mem (handleBase + d)) termTok a →
        heap3 ≤ a ∧ a < out.regs 4 ∧ ∀ j < d, ¬ Rcore.foot (out.mem (handleBase + j)) (coreTok j) a) ∧
      out.mem rebuildCountBase = st0.rebuildCount 0 + 1 ∧
      (∀ j < d, out.mem (updCountBase + j) = 0) ∧
      (∀ a < heap3,
        (a < handleBase ∨ handleBase + d < a) →
        (a < branchBase ∨ branchBase + d < a) →
        ((a < levelMeta + 1 ∨ levelMeta + d ≤ a) ∧
         (a < levelMeta + d + 1 ∨ levelMeta + 2 * d ≤ a)) →
        a ≠ rebuildCountBase →
        (a < updCountBase ∨ updCountBase + d ≤ a) →
        (a < newPtrs ∨ newPtrs + (d + 1) ≤ a) →
        out.mem a = st.mem a) ∧
      cost + (Finset.range d).sum (fun j => Rcore.phi (out.mem (handleBase + j)) (coreTok j) out.mem) ≤
        (Finset.range d).sum (fun j => levelCost next j + 9) +
          lastMul * (cfg.L.cost (next.G d) + 1) +
          d * (Psc.readout + 68) + 15 * d + 270 ∧
      ((∀ j, 1 ≤ j → j < d →
          out.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ out.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
          out.mem (levelMeta + j₁) + eCap * L ≤ out.mem (levelMeta + d + j₂))) := by
  dsimp only
  set d := cfg.P.d
  let stLG : ChainState cfg.T cfg.P := { st0 with ℓ := ℓstart, g := gstart }
  let next := (Chain.Ordered.algorithm1_rebuild cfg.T cfg.L cfg.P stLG 0 Gstart extraEnc).1
  obtain ⟨hr4, hr28, hr29, hr30, hr71, hr75, hr76, hr77, hr78, hr81, hr82, hr83, hr85,
    hr86, hr94, hr95, hr98⟩ := hRegs
  obtain ⟨hH0, hHB0, hBB0, hM0, hLM0, hRC0Lt, hUC0, hNP0, h01, h13,
    hL1, hL3, hG1, hG3, hO1, hO3⟩ := hBounds
  obtain ⟨hSepHB, hSepHM, hSepBM, hSepHL, hSepBL, hSepML, hRCH, hRCM, hRCHB, hRCBB, hRCLM, hRCUC,
    hUCHB, hUCBB, hUCLM, hNPHB, hNPBB, hNPLM, hNPUC, hNPRC⟩ := hSep
  obtain ⟨hRCNext, hLastKPos, hRebLvls, hLastAgree, hLastPos, hLastStr⟩ := hRebInv
  obtain ⟨hSFLNext, hValidNext, hRotNext, hFSubNext, hLastFSubNext, hMLeNext, hConnNext⟩ :=
    hNextFacts
  obtain ⟨_, hExG0, hExLvls, hExLast, hExLastBr, _, hExEll, _, hExLvlM, hExN0, _⟩ :=
    ordAlgorithm1_rebuild_exact cfg.T cfg.L cfg.P stLG hdPos Gstart extraEnc
  have hNextN0 : next.N₀ = st0.N₀ := hExN0
  have hNextLvlM : ∀ j, next.lvlM j = st0.lvlM j := fun j => congrFun hExLvlM j
  have hNextEll : next.ℓ = ℓstart := hExEll
  have hRangeEq : Finset.Ico 0 d = Finset.range d := by ext x; simp
  -- Step 1: `rebuildCount[0]++` and setup registers for `ordRebuildSuffixProgramKFBLStore`
  let s1 := { st with regs := Function.update st.regs 0 rebuildCountBase }
  let s2 := { s1 with regs := Function.update s1.regs 1 0 }
  have r1 : Runs w p ω (.assign 0 (.reg 86)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨rebuildCountBase, by simp [Expr.eval, hr86], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 1 (.const 0)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s3, r3, hs3Mem, hs3Regs, _⟩ :=
    incrementLevelCounter_runs (w := w) (base := rebuildCountBase) (level := 0)
      (count := st0.rebuildCount 0) (p := p) (st := s2) (ω := ω)
      (by simp [s2, s1]) (by simp [s2]) (by simpa [s2, s1] using hRC0)
      (by omega) hRCNext
  have hs3_eq (a : ℕ) (hne : a ≠ rebuildCountBase) : s3.mem a = st.mem a := by
    rw [hs3Mem]; simp [s2, s1, Function.update_of_ne hne]
  have hs3_rc : s3.mem rebuildCountBase = st0.rebuildCount 0 + 1 := by
    rw [hs3Mem]; simp
  have hs3_r (r : ℕ) (h0 : r ≠ 0) (h1 : r ≠ 1) : s3.regs r = st.regs r := by
    rw [hs3Regs]; simp [s2, s1, Function.update_of_ne h0, Function.update_of_ne h1]
  have goA {s : State} {r : ℕ} {e : Expr} {v : ℕ} {rest : Stmt} {sOut : State} {cRest : ℕ}
      (he : e.eval w s = some v)
      (hr : Runs w p ω rest { s with regs := Function.update s.regs r v } .normal sOut cRest) :
      Runs w p ω (.assign r e ;; rest) s .normal sOut (e.size + 1 + cRest + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨_, e.size + 1, cRest,
      runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩, hr, rfl⟩)
  let regs4 : ℕ → ℕ :=
    Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update s3.regs
      1 cfg.P.k) 6 newLvlGraph0) 7 newLen0) 8 newLen0) 9 ordPtr0) 20 0) 21 d)
      51 handleBase) 52 branchBase) 56 st0.N₀) 57 lvlMTable) 58 levelMeta) 67 L) 68 P
  let s4 : State := { s3 with regs := regs4 }
  have hs4_ge70 (r : ℕ) (hr : 70 ≤ r) : s4.regs r = st.regs r := by
    have hne : ∀ k < 70, r ≠ k := fun k hk => by omega
    simp only [s4, regs4,
      Function.update_of_ne (hne 68 (by decide)), Function.update_of_ne (hne 67 (by decide)),
      Function.update_of_ne (hne 58 (by decide)), Function.update_of_ne (hne 57 (by decide)),
      Function.update_of_ne (hne 56 (by decide)), Function.update_of_ne (hne 52 (by decide)),
      Function.update_of_ne (hne 51 (by decide)), Function.update_of_ne (hne 21 (by decide)),
      Function.update_of_ne (hne 20 (by decide)), Function.update_of_ne (hne 9 (by decide)),
      Function.update_of_ne (hne 8 (by decide)), Function.update_of_ne (hne 7 (by decide)),
      Function.update_of_ne (hne 6 (by decide)), Function.update_of_ne (hne 1 (by decide))]
    exact hs3_r r (by omega) (by omega)
  have hs4_4 : s4.regs 4 = heap3 := by
    simp only [s4, regs4, Function.update_of_ne (by decide : (4 : ℕ) ≠ 68),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 67), Function.update_of_ne (by decide : (4 : ℕ) ≠ 58),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 57), Function.update_of_ne (by decide : (4 : ℕ) ≠ 56),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 52), Function.update_of_ne (by decide : (4 : ℕ) ≠ 51),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 21), Function.update_of_ne (by decide : (4 : ℕ) ≠ 20),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 9), Function.update_of_ne (by decide : (4 : ℕ) ≠ 8),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 7), Function.update_of_ne (by decide : (4 : ℕ) ≠ 6),
      Function.update_of_ne (by decide : (4 : ℕ) ≠ 1)]
    exact (hs3_r 4 (by decide) (by decide)).trans hr4
  -- Step 2: `ordRebuildSuffixProgramKFBLStore_runs` on `[0, d]`
  have hModelLevel : ∀ j, 0 ≤ j → j < d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = cfg.T.initOrd cfg.P.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (next.levelOrd j) ∧
      next.G (j + 1) = cfg.T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧
      (next.G j).m ≤ next.lvlM j ∧ (next.G j).n ≤ next.N₀ ∧
      next.lvlM j < 2 ^ w ∧ (next.lvlM j + next.N₀ + 2) ^ Psc.wordExp * (L + 1) < 2 ^ w ∧
      IsRotationOrder (next.G j) (next.levelOrd j) ∧
      (∀ e ∈ (next.G j).E, 0 < ℓj e) ∧
      (next.G (j + 1)).E ⊆ (next.G j).E ∧
      (∀ e ∈ (next.G (j + 1)).E,
        ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ fmt.precision =
          next.toTreeChain.chainLen next.ℓ (j + 1) e) ∧
      (next.G (j + 1)).m ≤ (next.G (j + 1)).m ∧
      (next.G (j + 1)).n ≤ next.N₀ ∧
      ordRotWords (chainLevelOrdAbs next j) 0 ≤
        1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m ∧
      (j + 1 < d → (next.G (j + 1)).m ≤ next.lvlM (j + 1)) := by
    intro j _ hj
    obtain ⟨hScJ, hGJ1, hBrJ, hUpdJ⟩ := hExLvls j (Nat.zero_le j) hj
    obtain ⟨hmLe, hnLe, hMW, hWordE, hRot, hPos, hSub, hFits⟩ := hRebLvls j (Nat.zero_le j) hj
    refine ⟨?_, hGJ1, hBrJ, hUpdJ, hmLe, hnLe, hMW, hWordExpEq ▸ hWordE, hRot, hPos, hSub,
      hPrec ▸ hFits, le_rfl, (hValidNext (j + 1) (by omega)).2,
      hBrJ ▸ hRotNext j hj, fun hj1 => (hRebLvls (j + 1) (Nat.zero_le _) hj1).1⟩
    rw [hScJ, hNextLvlM j, hNextN0, hNextEll]
    exact hInitOrdEq cfg.P.k (st0.lvlM j) st0.N₀ (next.G j) _ _ _ _ (next.levelOrd j)
      (fun e he => by simp [he, stLG, next])
  have hs4_6 : s4.regs 6 = newLvlGraph0 := by simp [s4, regs4]
  have hs4_7 : s4.regs 7 = newLen0 := by simp [s4, regs4]
  have hs4_9 : s4.regs 9 = ordPtr0 := by simp [s4, regs4]
  have hOrd0Eq : next.levelOrd 0 = sortedEnds Gstart := by
    simp only [ChainState.levelOrd, Chain.Ordered.chainLevelOrd, ↓reduceIte]
    exact congrArg sortedEnds hExG0
  have hLen0Eq : next.toTreeChain.chainLen next.ℓ 0 = ℓstart := by
    simp [TreeChain.chainLen, hNextEll]
  have hCoreImplNext : ∀ j, 0 ≤ j → j < d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (next.G j)
          cfg.P.k (next.lvlM j) next.N₀ vCap eCap capExp Psc allocation) ∧
      SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (next.G j) cfg.P.k
        (next.lvlM j) next.N₀ vCap eCap capExp Psc allocation Rcore p opCore := fun j _ hj => by
    rw [hSFLNext.2.1, hSFLNext.2.2.1]
    exact hCoreImpl j hj (next.G j) (hSFLNext.1 j (le_of_lt hj))
      ((hSFLNext.2.2.2 j (le_of_lt hj)).trans (by rw [hExG0]; exact hGstartM))
  let restSp : ℕ → ℕ := fun j =>
    ordLevelSpace L capExp capLimit 0 (next.lvlM j) next.N₀ (next.G (j + 1)).m
  let coreInitSpace : ℕ → ℕ := fun j => levelSpace j - restSp j
  have hOrdSpaceAdd : ∀ x j,
      ordLevelSpace L capExp capLimit x (next.lvlM j) next.N₀ (next.G (j + 1)).m =
        x + restSp j := fun x j => by
    unfold restSp ordLevelSpace
    simp only [Nat.zero_add, Nat.add_assoc]
  have hInitSpaceLe : ∀ j, 0 ≤ j → j < d → ∀ gB lB grB oB h,
      allocation 6 [gB, lB, grB, oB, cfg.P.k, next.lvlM j, next.N₀, L, fmt.precision,
        Expander.chosenL (cfg.P.M₀ ^ 2), h] ≤ coreInitSpace j := fun j _ hj gB lB grB oB h => by
    have hdom := hOps.levelSpaceDom next j gB lB grB oB h hj hSFLNext (hMLeNext (j + 1) (by omega))
    rw [hOrdSpaceAdd] at hdom
    dsimp only [coreInitSpace]; omega
  have hLvlSpaceLe : ∀ j, 0 ≤ j → j < d →
      ordLevelSpace L capExp capLimit (coreInitSpace j) (next.lvlM j) next.N₀ (next.G (j + 1)).m ≤
        levelSpace j := fun j _ hj => by
    have hdom := hOps.levelSpaceDom next j 0 0 0 0 0 hj hSFLNext (hMLeNext (j + 1) (by omega))
    rw [hOrdSpaceAdd] at hdom ⊢
    dsimp only [coreInitSpace]; omega
  obtain ⟨s5, cReb, termTok, coreTok5, rReb, hs5_lo, hs5_hi, hz5, hCores5,
      hCoreDisj5, hMeta5, hMetaOrd5, hTermB5, hTermHLo5, hTermRep5, hTermFoot5, hTermDisj5, hs5_frame, hcReb⟩ :=
    ordRebuildSuffixProgramKFBLStore_runs_ord (w := w) (L := L)
      (depth := Expander.chosenL (cfg.P.M₀ ^ 2)) (vCap := vCap) (eCap := eCap) (capExp := capExp)
      (capLimit := capLimit) (init := initCore) (coreLenProc := coreLenProc) (edgeProc := edgeProc)
      (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy) (lastInit := lastInit)
      (first := 0) (handleBase := handleBase) (branchBase := branchBase) (lvlMTable := lvlMTable)
      (levelLens := levelMeta) (heapFloor := heap3) (lastMul := lastMul)
      (stretchPrec := stretchPrec) (fmt := fmt) (T := cfg.T) (LT := cfg.L) (CP := cfg.P)
      (P := Psc) (allocation := allocation) (lastAlloc := lastAlloc)
      (coreInitSpace := coreInitSpace) (nextM := fun j => (next.G (j + 1)).m)
      (Rcore := Rcore) (p := p) (op := opCore) (opLast := opLast) (st := s4) (ω := ω)
      next levelSpace (levelCost next) lastSpace (Nat.zero_le d) hCoreLocal
      hFour (hPrec ▸ hWidth) hLWord (hPrec ▸ hPWord) hDepthW hdW hkPos hkW
      (hNextN0.symm ▸ hNW) (by omega)
      (by simp [s4, regs4]) (by omega) (by simp [s4, regs4]) (by simp [s4, regs4, d])
      (by simp [s4, regs4]) (by simp [s4, regs4]) (by simp [s4, regs4, hNextN0])
      (by simp [s4, regs4]) (by simp [s4, regs4]) (by simp [s4, regs4]) (by simp [s4, regs4, hPrec])
      ((hs4_ge70 98 (by decide)).trans hr98)
      (by omega) (by omega) (by omega) (by omega)
      hSepHB hSepHM hSepBM hSepHL hSepBL hSepML
      (fun j _ hj => (hs3_eq (lvlMTable + j) (by rcases hRCM with h | h <;> omega)).trans
        ((hLvlM j hj).trans (hNextLvlM j).symm))
      (by rw [hs4_6, hExG0]; exact dynGraphAt_of_agree hG0 (fun a ha1 _ => hs3_eq a (by omega)))
      (by rw [hs4_7, hExG0, hLen0Eq, hPrec]; exact hLen0.congr (fun e he t ht => hs3_eq _ (by omega)))
      (by simp [s4, regs4])
      (fun _ => ⟨ordW, by
          rw [hs4_9, hOrd0Eq]
          exact MinCostFlow.MinRatio.ordListAt_of_agree hOrd0 (fun t ht => hs3_eq _ (by omega)),
        fun t ht => by rw [hs4_9, hs3_eq _ (by omega)]; exact hOrdW t ht,
        by rw [hs4_9, hs4_4]; exact hO3, by rw [hExG0]; exact hOrdWLe⟩)
      (by rw [hs4_6, hs4_4]; exact hG3)
      (by rw [hs4_7, hs4_4]; exact hL3)
      (fun a ha1 _ => by rw [hs4_6] at ha1; exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩)
      (fun a ha1 _ => by rw [hs4_7] at ha1; exact ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩)
      (fun a ha => (hs3_eq a (by omega)).trans (hz a (by omega)))
      hCoreImplNext hCapLim hInitSpaceLe hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (hLastImpl (next.G d)
        ((hSFLNext.2.2.2 d le_rfl).trans (by rw [hExG0]; exact hGstartM))
        (hMLeNext d le_rfl) (hSFLNext.1 d le_rfl) hConnNext)
      hModelLevel
      ⟨hExLast.trans (by rw [hNextEll]), hExLastBr, hLastAgree, hLastPos, hLastStr⟩
      hLvlSpaceLe
      (fun j _ hj => hOps.levelCostDom next j hj)
      (fun gB lB h => hOps.lastSpaceDom gB lB h)
      (by rw [hs4_4, hRangeEq]; omega) hTok0
  rw [hs4_4] at hs5_lo hs5_hi
  rw [hRangeEq] at hs5_hi hcReb
  have hs5_ge70 (r : ℕ) (hr : 70 ≤ r) : s5.regs r = st.regs r :=
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 rReb r hr).trans (hs4_ge70 r hr)
  -- Step 3: zero `updCount[0 .. d - 1]`
  let s5a := { s5 with regs := Function.update s5.regs 20 0 }
  have r5a : Runs w p ω (.assign 20 (.const 0)) s5 .normal s5a 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨s6, cZero, rZero, hcZero, hUCZero6, hUCFr6, hs6_regs⟩ :=
    wireZeroUpdCountLoop_runs (w := w) (first := 0) (d := d) (updCountBase := updCountBase)
      (p := p) (ω := ω) (st := s5a)
      (by simp [s5a]) (by simp [s5a, hs5_ge70 75 (by decide), hr75])
      (by simp [s5a, hs5_ge70 85 (by decide), hr85])
      (Nat.zero_le d) (by omega) (by omega)
  have hs6_r4 : s6.regs 4 = s5.regs 4 := by
    rw [hs6_regs 4 (by decide)]; simp [s5a]
  have hs6_ge70 (r : ℕ) (hr : 70 ≤ r) : s6.regs r = st.regs r := by
    rw [hs6_regs r (by omega)]; simp [s5a, Function.update_of_ne (by omega : r ≠ 20), hs5_ge70 r hr]
  have hs6_eq5 (a : ℕ) (h : a < updCountBase ∨ updCountBase + d ≤ a) : s6.mem a = s5.mem a :=
    hUCFr6 a (by simpa using h)
  have hs6_eq5_ge3 (a : ℕ) (ha : heap3 ≤ a) : s6.mem a = s5.mem a := hs6_eq5 a (Or.inr (by omega))
  -- Step 4: `shiftDeepCollectNewKFBL_runs` on `0 .. d`
  let coreHandle6 : ℕ → ℕ := fun j => s5.mem (handleBase + j)
  set termH := s5.mem (handleBase + d)
  have hTermRep6 :
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L P (next.G d).E).rep
        termH (next.lastK, next.lastLSFs) termTok s6.mem :=
    (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P (next.G d).E
      termH (next.lastK, next.lastLSFs) termTok s5.mem s6.mem
      (fun a ha => (hs6_eq5_ge3 a (hTermFoot5 a (hPrec.symm ▸ ha)).1).symm)).1 (hPrec ▸ hTermRep5)
  obtain ⟨hTLo, _, hTK, hTBr⟩ := hTermRep6
  have hLastBrLt : next.lastBran < next.lastK := by rw [hExLastBr]; exact hLastKPos
  obtain ⟨hTBrHdr, hTLSF⟩ := hTBr next.lastBran hLastBrLt
  have hTBrLo := hTBrHdr.1
  have hTBrHi := hTBrHdr.2.1
  set lsfHdr := s6.mem (termH + 1 + next.lastBran)
  set forestPtr := s6.mem (lsfHdr + 1)
  have hTermEndLe : termTok ≤ s5.regs 4 := by
    have hlt := (hTermFoot5 (termTok - 1) ⟨by omega, by omega⟩).2; omega
  have hCoreRep6 (j : ℕ) (hj : j < d) :
      Rcore.rep (coreHandle6 j) (chainLevelOrdAbs next j) (coreTok5 j) s6.mem ∧
      Rcore.phi (coreHandle6 j) (coreTok5 j) s6.mem =
        Rcore.phi (coreHandle6 j) (coreTok5 j) s5.mem := by
    have hloc := hCoreLocal (coreHandle6 j) (chainLevelOrdAbs next j) (coreTok5 j) s5.mem s6.mem
      (fun a ha => (hs6_eq5_ge3 a ((hCores5 j (Nat.zero_le j) hj).2.2.2.2 a ha).1).symm)
    exact ⟨hloc.1 (hCores5 j (Nat.zero_le j) hj).2.2.2.1, hloc.2.symm⟩
  have hS6Room : s6.regs 4 + 5 * (d - 0) < 2 ^ w := by rw [hs6_r4]; omega
  obtain ⟨s7, cCol, coreTok7, rCol, hs7_lo, hs7_hi, hz7, hNewForests7, hCores7, hCoreDisj7,
      hs7_frame, hs7_regs, hcCol⟩ :=
    shiftDeepCollectNewKFBL_runs (w := w) (L := L)
      (depth := Expander.chosenL (cfg.P.M₀ ^ 2)) (vCap := vCap) (eCap := eCap) (capExp := capExp)
      (i0 := 0) (handleBase := handleBase) (branchBase := branchBase)
      (levelMeta := levelMeta) (newPtrs := newPtrs) (intCap := intCap)
      (termHandle := termH) (vcLast := vCap) (ecLast := eCap) (lsfHdr := lsfHdr)
      (forestPtr := forestPtr) (p := p) (ω := ω) (st := s6) next coreHandle6 coreTok5 hCoreLocal
      hdPos
      (hs6_ge70 71 (by decide) |>.trans hr71)
      (hs6_ge70 75 (by decide) |>.trans hr75) (hs6_ge70 77 (by decide) |>.trans hr77)
      (hs6_ge70 78 (by decide) |>.trans hr78) (hs6_ge70 81 (by decide) |>.trans hr81)
      (hs6_ge70 83 (by decide) |>.trans hr83)
      hkW hdW (by omega) (by omega) (by omega) (by omega) (by omega)
      hS6Room
      (fun a ha => (hs6_eq5_ge3 a (by omega)).trans (hz5 a (by omega)))
      (fun j _ hj => (hCoreImplNext j (Nat.zero_le j) hj).2)
      (fun j _ hj => by
        obtain ⟨hBrJ, hHLoJ, hHHiJ, _, hFootJ⟩ := hCores5 j (Nat.zero_le j) hj
        obtain ⟨hScJ, _, hBrNJ, hUpdNJ, hmLeJ, hnLeJ, _, _, hRotJ, hPosJ, _, _, _, _, _, _⟩ :=
          hModelLevel j (Nat.zero_le j) hj
        have hDGJ :
            DynGraphAt s6.mem (s6.mem (levelMeta + d + j)) vCap eCap (next.G j) ∧
            s6.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s6.regs 4 ∧
            ∀ a, s6.mem (levelMeta + d + j) ≤ a →
              a < s6.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
              (∀ r < d, ¬ Rcore.foot (coreHandle6 r) (coreTok5 r) a) ∧
              (a < newPtrs ∨ newPtrs + (d + 1) ≤ a) := by
          by_cases hj0 : j = 0
          · subst hj0
            have hLMd6 : s6.mem (levelMeta + d + 0) = newLvlGraph0 := by
              rw [Nat.add_zero, hs6_eq5 _ (by rcases hUCLM with h | h <;> omega),
                hs5_frame (levelMeta + d) (by omega)
                  (by rcases hSepHL with h | h <;> omega) (by rcases hSepBL with h | h <;> omega)
                  ⟨Or.inr (by omega), Or.inl (by omega)⟩,
                hs3_eq _ (by rcases hRCLM with h | h <;> omega), hLMd0]
            refine ⟨?_, by rw [hLMd6, hs6_r4]; omega, fun a ha1 ha2 => by
              rw [hLMd6] at ha1 ha2
              exact ⟨fun r hr hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 a hf).1; omega,
                Or.inr (by omega)⟩⟩
            rw [hLMd6, hExG0]
            exact dynGraphAt_of_agree hG0 (fun a ha1 ha2 => by
              rw [hs6_eq5 _ (Or.inr (by omega)),
                hs5_frame a (by omega) (Or.inr (by omega)) (Or.inr (by omega))
                  ⟨Or.inr (by omega), Or.inr (by omega)⟩,
                hs3_eq a (by omega)])
          · obtain ⟨hDG, hGLo, hGHi, _, _, _, hDisjC, _, _⟩ := hMeta5 j (by omega) hj
            have hLMdj : s6.mem (levelMeta + d + j) = s5.mem (levelMeta + d + j) :=
              hs6_eq5 _ (by rcases hUCLM with h | h <;> omega)
            refine ⟨?_, by rw [hLMdj, hs6_r4]; exact hGHi, fun a ha1 ha2 => by
              rw [hLMdj] at ha1 ha2
              exact ⟨fun r hr => (hDisjC r (Nat.zero_le r) hr).2 a ha1 ha2,
                Or.inr (le_trans (by omega : newPtrs + (d + 1) ≤ heap3) (le_trans hGLo ha1))⟩⟩
            rw [hLMdj]
            exact dynGraphAt_of_agree hDG (fun a ha1 _ => hs6_eq5_ge3 a (le_trans hGLo ha1))
        obtain ⟨hDGJ', hDGEndJ, hDGDisjJ⟩ := hDGJ
        have hInJ : SparseCoreOrdInput cfg.T cfg.P.k (next.lvlM j) next.N₀ (next.scState j)
            (next.G j) (next.levelOrd j) (next.updCount j) := by
          rw [hScJ, hUpdNJ]
          exact SparseCoreOrdInput.init (next.G j) _ _ (next.levelOrd j) hDGJ'.1 hmLeJ hnLeJ
            (fun e he => by simp [he, hPosJ e he]) hRotJ
        exact ⟨hs6_eq5 _ (by rcases hUCHB with h | h <;> omega),
          (hs6_eq5 _ (by rcases hUCBB with h | h <;> omega)).trans hBrJ,
          by rw [hBrNJ]; exact hkPos, lt_of_le_of_lt hHHiJ (by omega), (hCoreRep6 j hj).1, hInJ,
          fun a ha => by rw [hs6_r4]; exact (hFootJ a ha).2,
          fun r _ hr => ⟨fun hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 _ hf).1; omega,
            fun hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 _ hf).1; omega⟩,
          by rcases hNPHB with h | h <;> omega, by rcases hNPBB with h | h <;> omega,
          by rcases hNPLM with h | h <;> omega,
          fun t ht hf => by have := (hFootJ _ hf).1; omega,
          ⟨hDGJ', hDGEndJ, fun a ha1 ha2 =>
            ⟨fun r _ hr => (hDGDisjJ a ha1 ha2).1 r hr, (hDGDisjJ a ha1 ha2).2⟩⟩⟩)
      hCoreDisj5
      (hs6_eq5 _ (by rcases hUCHB with h | h <;> omega))
      ((hs6_eq5 _ (by rcases hUCBB with h | h <;> omega)).trans hTermB5)
      rfl rfl hTLSF.2.1 (by rw [hs6_r4]; exact le_trans hTBrHdr.2.2.2.2.2.1 hTermEndLe)
      (fun e he => hIntCap e (hLastFSubNext he))
      ⟨by rcases hNPHB with h | h <;> omega, by rcases hNPBB with h | h <;> omega,
       Or.inr (by omega), Or.inr (by omega),
       by rw [hs6_r4]; exact (hTermFoot5 _ ⟨by omega, by omega⟩).2,
       by rw [hs6_r4]; exact (hTermFoot5 _ ⟨by omega, by omega⟩).2,
       fun r _ hr => ⟨fun hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 _ hf).1; omega,
         fun hf => by have := ((hCores5 r (Nat.zero_le r) hr).2.2.2.2 _ hf).1; omega,
         hTermDisj5 r (Nat.zero_le r) hr _ ⟨by omega, by omega⟩,
         hTermDisj5 r (Nat.zero_le r) hr _ ⟨by omega, by omega⟩⟩,
       fun a ha1 ha2 => by
         have haIn : termH ≤ a ∧ a < termTok :=
           ⟨by have := hTBrHdr.2.2.2.2.1; omega, by have := hTBrHdr.2.2.2.2.2.1; omega⟩
         exact ⟨fun r _ hr => hTermDisj5 r (Nat.zero_le r) hr a haIn,
           Or.inr (by omega)⟩⟩
      (fun j _ hj e he => hIntCap e (hFSubNext j hj he))
  rw [hs6_r4] at hs7_lo hs7_hi
  rw [hRangeEq] at hcCol
  -- Compose all steps of `wireBranchASuffixStmtKFBL`
  have rTail : Runs w p ω
      (ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
       .assign 20 (.const 0) ;; wireZeroUpdCountLoop ;;
       (.assign 20 (.reg 71) ;; collectLSFForestsLoop (opCore 2) 81 ;;
         collectTermForestStmt 81))
      s4 .normal s7 (cReb + (2 + (cZero + cCol + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s5, cReb, _, rReb,
      runs_seq_iff.mpr (Or.inr ⟨s5a, 2, _, r5a,
        runs_seq_iff.mpr (Or.inr ⟨s6, cZero, cCol, rZero, rCol, rfl⟩), rfl⟩), rfl⟩)
  have rSetup : Runs w p ω
      (.assign 1 (.reg 76) ;; .assign 6 (.reg 29) ;; .assign 7 (.reg 28) ;; .assign 8 (.reg 28) ;;
       .assign 9 (.reg 30) ;; .assign 20 (.const 0) ;; .assign 21 (.reg 75) ;; .assign 51 (.reg 77) ;;
       .assign 52 (.reg 78) ;; .assign 56 (.load (.bin .sub (.reg 82) (.const 1))) ;;
       .assign 57 (.reg 82) ;; .assign 58 (.reg 83) ;; .assign 67 (.reg 94) ;; .assign 68 (.reg 95) ;;
       ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit ;;
       .assign 20 (.const 0) ;; wireZeroUpdCountLoop ;;
       (.assign 20 (.reg 71) ;; collectLSFForestsLoop (opCore 2) 81 ;;
         collectTermForestStmt 81))
      s3 .normal s7 _ :=
    goA (by simp [Expr.eval, hs3_r 76 (by decide) (by decide), hr76])
    (goA (by simp [Expr.eval, hs3_r 29 (by decide) (by decide), hr29])
    (goA (by simp [Expr.eval, hs3_r 28 (by decide) (by decide), hr28])
    (goA (by simp [Expr.eval, hs3_r 28 (by decide) (by decide), hr28])
    (goA (by simp [Expr.eval, hs3_r 30 (by decide) (by decide), hr30])
    (goA (by simp [Expr.eval, show 0 < 2 ^ w by omega])
    (goA (by simp [Expr.eval, hs3_r 75 (by decide) (by decide), hr75])
    (goA (by simp [Expr.eval, hs3_r 77 (by decide) (by decide), hr77])
    (goA (by simp [Expr.eval, hs3_r 78 (by decide) (by decide), hr78])
    (goA (by simp [Expr.eval, BinOp.eval, hs3_r 82 (by decide) (by decide), hr82,
      show 1 < 2 ^ w by omega, show lvlMTable - 1 < 2 ^ w by omega,
      hs3_eq (lvlMTable - 1) (Ne.symm hRCH), hN0Cell])
    (goA (by simp [Expr.eval, hs3_r 82 (by decide) (by decide), hr82])
    (goA (by simp [Expr.eval, hs3_r 83 (by decide) (by decide), hr83])
    (goA (by simp [Expr.eval, hs3_r 94 (by decide) (by decide), hr94])
    (goA (by simp [Expr.eval, hs3_r 95 (by decide) (by decide), hr95]) rTail)))))))))))))
  have rAll := runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 10, _, r3, rSetup, rfl⟩), rfl⟩), rfl⟩)
  -- Memory framing helpers
  have hS7_eq6 (a : ℕ) (ha : a < s5.regs 4)
      (hnc : ∀ j < d, ¬ Rcore.foot (coreHandle6 j) (coreTok5 j) a)
      (hnp : a < newPtrs ∨ newPtrs + (d + 1) ≤ a) : s7.mem a = s6.mem a :=
    hs7_frame a (by rw [hs6_r4]; exact ha) (fun j _ hj => hnc j hj) (by simpa using hnp)
  have hS7_lt3 (a : ℕ) (ha : a < heap3) (hnp : a < newPtrs ∨ newPtrs + (d + 1) ≤ a) :
      s7.mem a = s6.mem a :=
    hS7_eq6 a (lt_of_lt_of_le ha hs5_lo)
      (fun j hj hf => by have := ((hCores5 j (Nat.zero_le j) hj).2.2.2.2 a hf).1; omega) hnp
  have hHandle7 (j : ℕ) (hj : j ≤ d) : s7.mem (handleBase + j) = s5.mem (handleBase + j) :=
    (hS7_lt3 _ (by omega) (by rcases hNPHB with h | h <;> omega)).trans
      (hs6_eq5 _ (by rcases hUCHB with h | h <;> omega))
  have hBranch7 (j : ℕ) (hj : j ≤ d) : s7.mem (branchBase + j) = s5.mem (branchBase + j) :=
    (hS7_lt3 _ (by omega) (by rcases hNPBB with h | h <;> omega)).trans
      (hs6_eq5 _ (by rcases hUCBB with h | h <;> omega))
  have hMeta7 (j : ℕ) (hj : j < 2 * d) : s7.mem (levelMeta + j) = s5.mem (levelMeta + j) :=
    (hS7_lt3 _ (by omega) (by rcases hNPLM with h | h <;> omega)).trans
      (hs6_eq5 _ (by rcases hUCLM with h | h <;> omega))
  have hPhi6Eq5 :
      (Finset.range d).sum (fun j => Rcore.phi (coreHandle6 j) (coreTok5 j) s6.mem) =
      (Finset.range d).sum (fun j => Rcore.phi (s5.mem (handleBase + j)) (coreTok5 j) s5.mem) :=
    Finset.sum_congr rfl (fun j hj => (hCoreRep6 j (Finset.mem_range.mp hj)).2)
  have hPhi7Eq :
      (Finset.range d).sum (fun j => Rcore.phi (s7.mem (handleBase + j)) (coreTok7 j) s7.mem) =
      (Finset.range d).sum (fun j => Rcore.phi (coreHandle6 j) (coreTok7 j) s7.mem) :=
    Finset.sum_congr rfl (fun j hj => by rw [hHandle7 j (le_of_lt (Finset.mem_range.mp hj))])
  refine ⟨s7, _, termTok, coreTok7, rAll, le_trans hs5_lo hs7_lo, by omega, hz7,
    fun r hr => (hs7_regs r hr).trans (hs6_ge70 r hr), hNewForests7, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    rw [hBranch7 j (le_of_lt hj), hHandle7 j (le_of_lt hj)]
    obtain ⟨hBr, hHLo, hHHi, _, hFoot5⟩ := hCores5 j (Nat.zero_le j) hj
    obtain ⟨hRep7, hFoot7⟩ := hCores7 j (Nat.zero_le j) hj
    refine ⟨hBr, hHLo, le_trans hHHi hs7_lo, hRep7, fun a ha => ?_⟩
    rcases hFoot7 a ha with h5 | ⟨hlo, hhi⟩
    · exact ⟨(hFoot5 a h5).1, lt_of_lt_of_le (hFoot5 a h5).2 hs7_lo⟩
    · rw [hs6_r4] at hlo; exact ⟨le_trans hs5_lo hlo, hhi⟩
  · intro j₁ h1 j₂ h2 hne a ha1 ha2
    rw [hHandle7 j₁ (le_of_lt h1)] at ha1; rw [hHandle7 j₂ (le_of_lt h2)] at ha2
    exact hCoreDisj7 j₁ j₂ (Nat.zero_le j₁) h1 (Nat.zero_le j₂) h2 hne a ha1 ha2
  · intro j hj1 hj2
    obtain ⟨hDG, hGLo, hGHi, hLen, hLLo, hLHi, hDisjC, hDisjTL, hDisjTG⟩ := hMeta5 j hj1 hj2
    have hML : s7.mem (levelMeta + j) = s5.mem (levelMeta + j) := hMeta7 j (by omega)
    have hMG : s7.mem (levelMeta + d + j) = s5.mem (levelMeta + d + j) := by
      simpa [Nat.add_assoc] using hMeta7 (d + j) (by omega)
    refine ⟨?_, by rw [hMG]; exact hGLo, by rw [hMG]; exact le_trans hGHi hs7_lo,
      ?_, by rw [hML]; exact hLLo, by rw [hML]; exact le_trans hLHi hs7_lo, ?_, ?_, ?_⟩
    · rw [hMG]
      exact dynGraphAt_of_agree hDG (fun a ha1 ha2 =>
        (hS7_eq6 a (lt_of_lt_of_le ha2 hGHi) (fun r hr => (hDisjC r (Nat.zero_le r) hr).2 a ha1 ha2)
          (Or.inr (le_trans (by omega : newPtrs + (d + 1) ≤ heap3) (le_trans hGLo ha1)))).trans
          (hs6_eq5_ge3 a (le_trans hGLo ha1)))
    · rw [hML]
      exact (hPrec ▸ hLen).congr (fun e he t ht => by
        have heL : e * L + L ≤ eCap * L := by
          have := hDG.2.2.1 e he
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right L (Nat.succ_le_of_lt this)
        have hlt : s5.mem (levelMeta + j) + e * L + t < s5.mem (levelMeta + j) + eCap * L := by omega
        exact (hS7_eq6 _ (lt_of_lt_of_le hlt hLHi)
          (fun r hr => (hDisjC r (Nat.zero_le r) hr).1 _ (by omega) hlt)
          (Or.inr (by omega))).trans (hs6_eq5_ge3 _ (by omega)))
    · intro r hr
      rw [hML, hMG, hHandle7 r (le_of_lt hr)]
      refine ⟨fun a ha1 ha2 hf => ?_, fun a ha1 ha2 hf => ?_⟩
      · rcases (hCores7 r (Nat.zero_le r) hr).2 a hf with h5 | ⟨hlo, _⟩
        · exact (hDisjC r (Nat.zero_le r) hr).1 a ha1 ha2 h5
        · rw [hs6_r4] at hlo; omega
      · rcases (hCores7 r (Nat.zero_le r) hr).2 a hf with h5 | ⟨hlo, _⟩
        · exact (hDisjC r (Nat.zero_le r) hr).2 a ha1 ha2 h5
        · rw [hs6_r4] at hlo; exact absurd (lt_of_lt_of_le ha2 hGHi) (not_lt_of_ge hlo)
    · intro a ha1 ha2; rw [hML] at ha1 ha2; rw [hHandle7 d le_rfl]; exact hPrec ▸ hDisjTL a ha1 ha2
    · intro a ha1 ha2; rw [hMG] at ha1 ha2; rw [hHandle7 d le_rfl]; exact hPrec ▸ hDisjTG a ha1 ha2
  · rw [hBranch7 d le_rfl]; exact hTermB5
  · rw [hHandle7 d le_rfl]; exact hTermHLo5
  · rw [hHandle7 d le_rfl]
    exact (LastLevelProgram.lastLevelRepresentation_local vCap eCap 4 L P (next.G d).E
      termH (next.lastK, next.lastLSFs) termTok s5.mem s7.mem
      (fun a ha => by
        have hF := hTermFoot5 a (hPrec.symm ▸ ha)
        exact ((hS7_eq6 a hF.2 (fun r hr => hTermDisj5 r (Nat.zero_le r) hr a (hPrec.symm ▸ ha))
          (Or.inr (by omega))).trans (hs6_eq5_ge3 a hF.1)).symm)).1 (hPrec ▸ hTermRep5)
  · intro a ha
    rw [hHandle7 d le_rfl] at ha
    have hF := hTermFoot5 a (hPrec.symm ▸ ha)
    refine ⟨hF.1, lt_of_lt_of_le hF.2 hs7_lo, fun r hr hf => ?_⟩
    rw [hHandle7 r (le_of_lt hr)] at hf
    rcases (hCores7 r (Nat.zero_le r) hr).2 a hf with h5 | ⟨hlo, _⟩
    · exact hTermDisj5 r (Nat.zero_le r) hr a (hPrec.symm ▸ ha) h5
    · rw [hs6_r4] at hlo; omega
  · exact (hS7_lt3 rebuildCountBase (by omega) (by rcases hNPRC with h | h <;> omega)).trans
      ((hs6_eq5 rebuildCountBase (by rcases hRCUC with h | h <;> omega)).trans
        ((hs5_frame rebuildCountBase (by omega) (by rcases hRCHB with h | h <;> omega)
          (by rcases hRCBB with h | h <;> omega)
          (by rcases hRCLM with h | h <;> [exact ⟨Or.inl (by omega), Or.inl (by omega)⟩; exact ⟨Or.inr (by omega), Or.inr (by omega)⟩])).trans hs3_rc))
  · intro j hj
    exact (hS7_lt3 (updCountBase + j) (by omega) (by rcases hNPUC with h | h <;> omega)).trans
      (hUCZero6 j (Nat.zero_le j) hj)
  · intro a ha hH hB hM hRC hUC hNP
    exact (hS7_lt3 a ha hNP).trans ((hs6_eq5 a hUC).trans ((hs5_frame a ha hH hB hM).trans (hs3_eq a hRC)))
  · rw [hPhi7Eq]; rw [hPhi6Eq5] at hcCol
    simp only [Expr.size, Nat.sub_zero] at hcCol hcZero ⊢
    change cReb + (Finset.range d).sum (fun j => Rcore.phi (s5.mem (handleBase + j)) (coreTok5 j) s5.mem) ≤
      (Finset.range d).sum (fun j => levelCost next j + 9) + lastMul * (cfg.L.cost (next.G d) + 1) + 28 at hcReb
    change cCol + (Finset.range d).sum (fun j => Rcore.phi (coreHandle6 j) (coreTok7 j) s7.mem) ≤
      d * (Psc.readout + 48) + 50 +
        (Finset.range d).sum (fun j => Rcore.phi (s5.mem (handleBase + j)) (coreTok5 j) s5.mem) at hcCol
    change _ + (Finset.range d).sum (fun j => Rcore.phi (coreHandle6 j) (coreTok7 j) s7.mem) ≤
      (Finset.range d).sum (fun j => levelCost next j + 9) +
        lastMul * (cfg.L.cost (next.G d) + 1) + d * (Psc.readout + 68) + 15 * d + 270
    clear rAll rSetup rTail rReb rZero rCol hCores5 hMeta5 hCores7 hCoreDisj7 hNewForests7 hTermRep5
      hModelLevel
    have hRd : d * (Psc.readout + 48) ≤ d * (Psc.readout + 68) :=
      Nat.mul_le_mul_left d (by omega)
    omega
  · refine ⟨fun j hj1 hj2 => ?_, fun j₁ j₂ hj1 hlt hj2 => ?_⟩
    · have hML : s7.mem (levelMeta + j) = s5.mem (levelMeta + j) := hMeta7 j (by omega)
      have hMG : s7.mem (levelMeta + d + j) = s5.mem (levelMeta + d + j) := by
        simpa [Nat.add_assoc] using hMeta7 (d + j) (by omega)
      rw [hMG, hML]; exact hMetaOrd5.1 j hj1 hj2
    · have hML : s7.mem (levelMeta + j₁) = s5.mem (levelMeta + j₁) := hMeta7 j₁ (by omega)
      have hMG : s7.mem (levelMeta + d + j₂) = s5.mem (levelMeta + d + j₂) := by
        simpa [Nat.add_assoc] using hMeta7 (d + j₂) (by omega)
      rw [hML, hMG]; exact hMetaOrd5.2 j₁ j₂ hj1 hlt hj2

end MinCostFlow.MinRatio
