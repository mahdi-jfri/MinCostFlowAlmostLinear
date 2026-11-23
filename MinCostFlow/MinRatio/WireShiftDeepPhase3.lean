module

public import MinCostFlow.MinRatio.WireShiftDeepPrepKFBL
public import MinCostFlow.MinRatio.WireRebuildSuffixLoopKFBL
import WordRAM.Tactic

/-!
# Deep shift Phases 0–3 composition (`WireShiftDeepPhase3`)

Composes `shiftDeepKFBL_phases_0_to_2_runs` (`WireShiftDeepPrepKFBL.lean`) with Phase 3
(`ordRebuildSuffixProgramKFBLStore_runs`) under the layout contract, and preserves `yI0_3` across
Phase 3, producing the pre-Phase-4a state `s4` for `WireShiftDeepAux.lean`. Every level graph
that Phases 2 and 3 store, and the last level, have the caps `(vCap, eCap)` of the module.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- The deep shift body under the layout contract `sparseCoreOrdMachineContractKFBL`. It uses
`shiftDeepInitRegsKFBL` in Phase 0, `shiftDeepCollectOldKFBL` in Phase 1,
`shiftDeepRestartAndReadoutKFBL` in Phase 2, and `ordRebuildSuffixProgramKFBLStore` in Phase 3
(all using the live-list graph copy `copyGraphLiveFromHeader`). -/
@[expose] def shiftDeepChainBodyKFBL
    (init restart readGraph readLSF coreLenProc readOrd lastInit packEditsProc
      readTree cutTree linkTree bind canonCopy isNeg : ℕ) : Stmt :=
  shiftDeepInitRegsKFBL ;;
  shiftDeepCollectOldKFBL readLSF ;;
  shiftDeepRestartAndReadoutKFBL restart readGraph readLSF coreLenProc readOrd ;;
  ordRebuildSuffixProgramKFBLStore init readGraph readLSF coreLenProc readOrd lastInit ;;
  shiftDeepCollectNewAndSync readLSF packEditsProc readTree cutTree linkTree bind canonCopy isNeg

theorem shiftDeepChainBodyKFBL_noRand
    (init restart readGraph readLSF coreLenProc readOrd lastInit packEditsProc
      readTree cutTree linkTree bind canonCopy isNeg : ℕ) :
    (shiftDeepChainBodyKFBL init restart readGraph readLSF coreLenProc readOrd lastInit
      packEditsProc readTree cutTree linkTree bind canonCopy isNeg).NoRand := by
  simp [shiftDeepChainBodyKFBL, shiftDeepInitRegsKFBL_noRand, shiftDeepCollectOldKFBL_noRand,
    shiftDeepRestartAndReadoutKFBL_noRand, ordRebuildSuffixProgramKFBLStore_noRand,
    shiftDeepCollectNewAndSync_noRand, Stmt.NoRand]

/-- Two nonempty memory intervals with distinct constant tags are disjoint. -/
theorem interval_disj_of_tags {tag : ℕ → ℕ} {b1 n1 v1 b2 n2 v2 : ℕ}
    (hn1 : 0 < n1) (hn2 : 0 < n2)
    (h1 : ∀ j < n1, tag (b1 + j) = v1) (h2 : ∀ j < n2, tag (b2 + j) = v2) (hne : v1 ≠ v2) :
    b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 := by
  by_contra hcon; push Not at hcon
  by_cases hle : b1 ≤ b2
  · have hA := h1 (b2 - b1) (by omega)
    rw [show b1 + (b2 - b1) = b2 by omega] at hA
    have hB := h2 0 hn2; simp only [Nat.add_zero] at hB
    exact hne (hA.symm.trans hB)
  · have hB := h2 (b1 - b2) (by omega)
    rw [show b2 + (b1 - b2) = b1 by omega] at hB
    have hA := h1 0 hn1; simp only [Nat.add_zero] at hA
    exact hne (hA.symm.trans hB)

/-- An address whose tag differs from `v` lies outside any interval `[b + lo, b + hi)` tagged `v`. -/
theorem not_mem_interval_of_tag_ne {tag : ℕ → ℕ} {b lo hi v a : ℕ}
    (h : ∀ j, lo ≤ j → j < hi → tag (b + j) = v) (hne : tag a ≠ v) :
    a < b + lo ∨ b + hi ≤ a := by
  by_contra hcon; push Not at hcon
  have h1 := h (a - b) (by omega) (by omega)
  rw [show b + (a - b) = a by omega] at h1
  exact hne h1

/-- The space of a level splits into the space of the init and the rest. -/
theorem ordLevelSpace_eq_add (L capExp capLimit initSp M N nextM : ℕ) :
    ordLevelSpace L capExp capLimit initSp M N nextM =
      initSp + ordLevelSpace L capExp capLimit 0 M N nextM := by
  simp only [ordLevelSpace]; omega

theorem ordRebuildSuffixProgramKFBLStore_preserves_ge70
    {w init readGraph readLSF coreLenProc readOrd lastInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {c : ℕ}
    (hr : Runs w p ω
      (ordRebuildSuffixProgramKFBLStore init readGraph readLSF coreLenProc readOrd lastInit)
      st .normal out c)
    (r : ℕ) (h70 : 70 ≤ r) : out.regs r = st.regs r :=
  runs_preserves_above
    (s := ordRebuildSuffixProgramKFBLStore init readGraph readLSF coreLenProc readOrd lastInit)
    h70 rfl hr

set_option maxHeartbeats 800000 in
/-- Execute Phases 0–3 of `shiftDeepChainBodyKFBL` on a non-terminal shift `i < d`, under the
layout contract. -/
theorem shiftDeep_phases_0_to_3_runs
    {w L P m V psi k epsExp drainUnit capExp wordExp stretchPrec lastMul
      intCapMax forestEdgeCap deepSpace deepFixed toolMul vCap eCap capLimit fcap restartSpace
      lastSpace initCore coreLenProc edgeProc signExt mul intDiv copy lastInit root heap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore opLast : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {i : Fin (cfg.P.d + 1)}
    (levelSpace : ℕ → ℕ) (levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ)
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hFmtPrec : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hL4W : 4 * L + 2 < 2 ^ w) (hw17 : 17 < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hdW : cfg.P.d < 2 ^ w) (hN0W : cfg.N₀ < 2 ^ w)
    (hDepthW : Expander.chosenL (cfg.P.M₀ ^ 2) < 2 ^ w)
    (hInitOrdEq : ToolInitOrdEqOnE cfg.T)
    (hCore : DeepShiftCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hForestCap : DeepShiftForestCapKFBL fmt L vCap eCap capExp cfg Psc allocation fcap Rcore p
      opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
    (hLastImpl : ∀ G : MGraph, G.m ≤ m → G.m ≤ levelM cfg.TP cfg.P cfg.P.d → G.n ≤ G.m + 1 →
      (∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) →
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision G.E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L cfg.L G vCap eCap lastMul stretchPrec lastAlloc))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hOps : DeepShiftOpsHypKFBL (w := w) (L := L) (capExp := capExp) (capLimit := capLimit)
      (fcap := fcap) (lastMul := lastMul) (intCapMax := intCapMax)
      (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace) (deepFixed := deepFixed)
      (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc) (allocation := allocation)
      (lastAlloc := lastAlloc) restartSpace levelSpace levelCost lastSpace)
    (hiLt : i.val < cfg.P.d)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hCaps0 : SolverLevelCapsAt vCap eCap model tok mem0)
    (hMemEq : ∀ a, tok.tag a ≠ 5 → mem a = mem0 a)
    (hBranLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hModelInv : ShiftDeepModelInv w L P wordExp stretchPrec model i)
    (hModelK : ShiftDeepModelInvKFBL model i)
    (hWordExpEq : Psc.wordExp = wordExp)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < heap)
    (hzHeap : ZeroFrom mem heap)
    (hHeapRoom : heap + deepSpace < 2 ^ w) :
    let d := cfg.P.d
    let i0 := i.val
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i0).1
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let levelMeta := solverLevelMetaAddr tok.table d
    let cnt := d - i0 + 1
    let heap1 := heap + 2 * cnt
    let forestSafe : ℕ → Prop := fun a =>
      (a < heap → tok.tag a ≠ 4 ∧ tok.tag a ≠ 22 + d) ∧ (a < heap ∨ heap1 ≤ a)
    let phase03 : Stmt :=
      shiftDeepInitRegsKFBL ;;
      shiftDeepCollectOldKFBL (opCore 2) ;;
      shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5) ;;
      ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5)
        lastInit
    ∃ (s2 s3 s4 : State) (c03 newTermTok : ℕ)
      (yI0_2 yI0_3 : Rcore.τ) (coreTok4 : ℕ → Rcore.τ),
      Runs w p ω phase03 (startState [root, i0, heap] mem pos) .normal s4 c03 ∧
      heap1 ≤ s2.regs 4 ∧ s2.regs 4 ≤ s3.regs 4 ∧ s3.regs 4 ≤ s4.regs 4 ∧
      s4.regs 4 ≤ heap + 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace +
        (Finset.range d).sum levelSpace + lastSpace ∧
      ZeroFrom s4.mem (s4.regs 4) ∧
      -- Phase 1 old forests + frame
      (∀ t (ht : t < (chainSuffixForests model.chain i0).length),
        ∃ vc ec,
          DynGraphAt s2.mem (s2.mem (heap + t)) vc ec (chainSuffixForests model.chain i0)[t] ∧
          s2.mem (heap + t) + dynGraphSize vc ec ≤ s2.regs 4 ∧
          (∀ e ∈ (chainSuffixForests model.chain i0)[t].E, e < tok.intCap) ∧
          (∀ a, s2.mem (heap + t) ≤ a → a < s2.mem (heap + t) + dynGraphSize vc ec →
            ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a ∧ forestSafe a)) ∧
      (∀ a, Rcore.foot (tok.coreHandle i0) yI0_2 a →
        Rcore.foot (tok.coreHandle i0) (tok.coreTok i0) a ∨ (heap1 ≤ a ∧ a < s2.regs 4)) ∧
      (∀ a < heap1,
        (∀ j, i0 ≤ j → j < d → ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) →
        (a < heap ∨ heap + cnt ≤ a) → s2.mem a = mem a) ∧
      -- Phase 2 outputs for `i0` and `i0 + 1`
      s3.mem (branchBase + i0) = (model.chain.bran i0 + 1) % cfg.P.k ∧
      (∀ a, Rcore.foot (tok.coreHandle i0) yI0_3 a →
        Rcore.foot (tok.coreHandle i0) yI0_2 a ∨ (s2.regs 4 ≤ a ∧ a < s3.regs 4)) ∧
      DynGraphAt s3.mem (s3.regs 6) vCap eCap (next.G (i0 + 1)) ∧
      EdgeValuesAt s3.mem (s3.regs 7) 4 L fmt.precision (next.G (i0 + 1)).E
        (next.toTreeChain.chainLen model.chain.ℓ (i0 + 1)) ∧
      s2.regs 4 ≤ s3.regs 6 ∧ s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 4 ∧
      (∀ a, s3.regs 6 ≤ a → a < s3.regs 6 + dynGraphSize vCap eCap →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s2.regs 4 ≤ s3.regs 7 ∧ s3.regs 7 + eCap * L ≤ s3.regs 4 ∧
      (∀ a, s3.regs 7 ≤ a → a < s3.regs 7 + eCap * L →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 7 ∧
      (i0 + 1 < d → s3.mem (levelMeta + (i0 + 1)) = s3.regs 7 ∧
        s3.mem (levelMeta + d + (i0 + 1)) = s3.regs 6) ∧
      (∀ a < s2.regs 4, ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a →
        a ≠ branchBase + i0 →
        (i0 + 1 < d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + d + (i0 + 1)) →
        s3.mem a = s2.mem a) ∧
      -- Preserved `yI0_3` at `s4`
      Rcore.rep (tok.coreHandle i0) (chainLevelOrdAbs next i0) yI0_3 s4.mem ∧
      Rcore.phi (tok.coreHandle i0) yI0_3 s4.mem = Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem ∧
      -- Phase 3 outputs on `[i0 + 1, d)` and terminal `d`
      (∀ j, i0 + 1 ≤ j → j < d →
        s4.mem (branchBase + j) = next.bran j ∧
        s3.regs 4 ≤ s4.mem (handleBase + j) ∧ s4.mem (handleBase + j) ≤ s4.regs 4 ∧
        Rcore.rep (s4.mem (handleBase + j)) (chainLevelOrdAbs next j) (coreTok4 j) s4.mem ∧
        (∀ a, Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a →
          s3.regs 4 ≤ a ∧ a < s4.regs 4)) ∧
      (∀ j₁ j₂, i0 + 1 ≤ j₁ → j₁ < d → i0 + 1 ≤ j₂ → j₂ < d → j₁ ≠ j₂ →
        ∀ a, Rcore.foot (s4.mem (handleBase + j₁)) (coreTok4 j₁) a →
          ¬ Rcore.foot (s4.mem (handleBase + j₂)) (coreTok4 j₂) a) ∧
      (∀ j, i0 + 1 + 1 ≤ j → j < d →
        DynGraphAt s4.mem (s4.mem (levelMeta + d + j)) vCap eCap (next.G j) ∧
        s3.regs 4 ≤ s4.mem (levelMeta + d + j) ∧
        s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.regs 4 ∧
        EdgeValuesAt s4.mem (s4.mem (levelMeta + j)) 4 L fmt.precision (next.G j).E
          (next.toTreeChain.chainLen next.ℓ j) ∧
        s3.regs 4 ≤ s4.mem (levelMeta + j) ∧
        s4.mem (levelMeta + j) + eCap * L ≤ s4.regs 4 ∧
        (∀ r, i0 + 1 ≤ r → r < d →
          (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
            ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a) ∧
          (∀ a, s4.mem (levelMeta + d + j) ≤ a →
            a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
            ¬ Rcore.foot (s4.mem (handleBase + r)) (coreTok4 r) a)) ∧
        (∀ a, s4.mem (levelMeta + j) ≤ a → a < s4.mem (levelMeta + j) + eCap * L →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
              (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a) ∧
        (∀ a, s4.mem (levelMeta + d + j) ≤ a →
          a < s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          ¬ (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
              (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a)) ∧
      ((∀ j, i0 + 1 + 1 ≤ j → j < d →
          s4.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s4.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, i0 + 1 + 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
          s4.mem (levelMeta + j₁) + eCap * L ≤ s4.mem (levelMeta + d + j₂))) ∧
      s4.mem (branchBase + d) = next.lastBran ∧
      (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision (next.G d).E).rep
        (s4.mem (handleBase + d)) (next.lastK, next.lastLSFs) newTermTok s4.mem ∧
      (∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
          (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a →
        s3.regs 4 ≤ a ∧ a < s4.regs 4) ∧
      (∀ j, i0 + 1 ≤ j → j < d →
        ∀ a, (LastLevelProgram.lastLevelRepresentation vCap eCap 4 L fmt.precision
            (next.G d).E).foot (s4.mem (handleBase + d)) newTermTok a →
          ¬ Rcore.foot (s4.mem (handleBase + j)) (coreTok4 j) a) ∧
      (∀ a < s3.regs 4,
        (a < handleBase + (i0 + 1) ∨ handleBase + d < a) →
        (a < branchBase + (i0 + 1) ∨ branchBase + d < a) →
        ((a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + d ≤ a) ∧
         (a < levelMeta + d + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a)) →
        s4.mem a = s3.mem a) ∧
      -- Preserved registers `70..83` at `s4`
      s4.regs 70 = root ∧ s4.regs 71 = i0 ∧ s4.regs 73 = tok.handle ∧
      s4.regs 75 = d ∧ s4.regs 77 = handleBase ∧ s4.regs 78 = branchBase ∧
      s4.regs 79 = cnt ∧ s4.regs 80 = heap ∧ s4.regs 81 = heap + cnt ∧
      s4.regs 83 = levelMeta ∧
      -- Cost + potential bound through Phase 3
      c03 + Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem +
        (Finset.Ico (i0 + 1) d).sum
          (fun j => Rcore.phi (s4.mem (handleBase + j)) (coreTok4 j) s4.mem) ≤
        copyGraphLiveCost (cfg.T.lsfs (model.chain.scState i0) (model.chain.bran i0)).F.F.n
          (cfg.T.lsfs (model.chain.scState i0) (model.chain.bran i0)).F.F.m +
        (d - i0) * (Psc.readout + 48) +
        Psc.mul * (cfg.T.cost (next.scState i0) - cfg.T.cost (model.chain.scState i0) + 1) +
        Psc.mul * (2 * (next.G (i0 + 1)).n + 2 * (next.G (i0 + 1)).m + 2) *
          SparseCore.bundleLogFactor (model.chain.lvlM i0) model.chain.N₀ +
        2 * Psc.readout + copyGraphLiveCost (next.G (i0 + 1)).n (next.G (i0 + 1)).m +
        (next.G (i0 + 1)).m *
          (wireCoreLenEdgeCost (ordLevelLwMax L capExp (model.chain.lvlM i0) model.chain.N₀) +
            30) +
        (Finset.Ico (i0 + 1) d).sum (fun j => levelCost model i j + 9) +
        lastMul * (cfg.L.cost (next.G d) + 1) + 600 +
        (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
  dsimp only
  let d := cfg.P.d
  let i0 := i.val
  let chain := model.chain
  let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1
  have hChain' : (alg2LoopShiftStep cfg model i).chain = next := by
    simp [alg2LoopShiftStep, next, chain, i0]
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let lvlMTable := solverLvlMAddr tok.table d
  let levelMeta := solverLevelMetaAddr tok.table d
  let cnt := d - i0 + 1
  let heap1 := heap + 2 * cnt
  -- Run Phases 0–2
  obtain ⟨s2, s3, c012, ordW3, yI0_2, yI0_3, r012, hs2_lo, h4Lo3, hs3_heapLe, hz3,
      hOldForestsSafe2, hFootI0_2, hs2_frame, hBr3, hRepI0_3, hFootI0_3, hH3, hLen3, hGrad3,
      hOrd3, hOrdLe3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3, h7Disj3, h6Le7_3, hMeta3, hs3_frame,
      h3_1, h3_20, h3_21, h3_51, h3_52, h3_56, h3_57, h3_58, h3_67, h3_68,
      h3_70, h3_71, h3_73, h3_75, h3_77, h3_78, h3_79, h3_80, h3_81, h3_83, h3_98, hc012⟩ :=
    shiftDeepKFBL_phases_0_to_2_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi)
      (k := k) (epsExp := epsExp) (drainUnit := drainUnit) (capExp := capExp)
      (wordExp := wordExp) (stretchPrec := stretchPrec) (lastMul := lastMul)
      (intCapMax := intCapMax) (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace)
      (deepFixed := deepFixed) (toolMul := toolMul) (vCap := vCap) (eCap := eCap)
      (capLimit := capLimit) (fcap := fcap) (restartSpace := restartSpace)
      (lastSpace := lastSpace) (initCore := initCore) (coreLenProc := coreLenProc)
      (edgeProc := edgeProc) (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy)
      (root := root) (heap := heap) (pos := pos) (fmt := fmt) (cfg := cfg) (Psc := Psc)
      (allocation := allocation) (lastAlloc := lastAlloc) (Rcore := Rcore) (p := p)
      (opCore := opCore) (ω := ω) (mem0 := mem0) (mem := mem) (model := model) (tok := tok)
      (i := i)
      levelSpace levelCost hCoreLocal hFmtBits hFmtPrec hw17 hkPos hkW hdW hCore hForestCap
      hcapLim hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hOps hiLt hRep0 hMeta0 hCaps0
      hMemEq hBranLt hModelInv hModelK hFootLt hzHeap hHeapRoom
  -- Unpack tags, metadata, and exact shift characterization
  obtain ⟨_, _, _, _, hFresh0, _, hExtM0, _, _, _, _, _, _, _, _, _, _, _, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, _, _, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hT21⟩ := hTags0
  obtain ⟨_, _, hLvlM0, hTagM0, hTagMeta0, _⟩ := hMeta0
  obtain ⟨_, _, _, _, _, hNextLvls, hLastAgree, hLastPos, hLastStr, _, _, _, _, _, _, _⟩ :=
    hModelInv
  obtain ⟨_, _, _, hExBr, _, _, _, _, hExLvls, hExLast, hExLastBr, _, _,
      hExEll, _, hExLvlM, hExN0⟩ := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
  have hdPos : 0 < d := Nat.zero_lt_of_lt hiLt
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hmem0_eq {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 5) : mem a = mem0 a :=
    hMemEq a (ht ▸ hv)
  have hTagHandle (j : ℕ) (hj : j ≤ d) : tok.tag (handleBase + j) = 4 :=
    hT4 j (lt_of_le_of_lt hj (by change d < 2 * (d + 1); exact Nat.lt_of_lt_of_le (Nat.lt_succ_self d) (Nat.le_mul_of_pos_left _ (by decide))))
  have hTagBranch (j : ℕ) (hj : j ≤ d) : tok.tag (branchBase + j) = 4 := by
    have hlt : d + 1 + j < 2 * (d + 1) := by
      rw [two_mul]; exact Nat.add_lt_add_left (Nat.lt_succ_of_le hj) (d + 1)
    have := hT4 ((d + 1) + j) hlt
    rwa [← Nat.add_assoc] at this
  have hTagMetaG (j : ℕ) (hj : j < d) : tok.tag (levelMeta + d + j) = 22 + d := by
    have hlt : d + j < 2 * d := by rw [two_mul]; exact Nat.add_lt_add_left hj d
    have := hTagMeta0 (d + j) hlt
    rwa [← Nat.add_assoc] at this
  have hTagMetaL (j : ℕ) (hj : j < d) : tok.tag (levelMeta + j) = 22 + d :=
    hTagMeta0 j (lt_of_lt_of_le hj (Nat.le_mul_of_pos_left d (by decide)))
  have hLevelEnd : branchBase + d < heap := htagLt (by rw [hTagBranch d le_rfl]; decide)
  have hMEnd : lvlMTable + d ≤ heap := by
    have h1 := hTagM0 (d - 1) (Nat.sub_lt hdPos Nat.one_pos)
    have h3 := htagLt (by rw [h1]; exact Nat.ne_of_gt (Nat.add_pos_left (by decide) _))
    have h4 : lvlMTable + (d - 1) + 1 = lvlMTable + d := by
      rw [Nat.add_assoc, Nat.sub_add_cancel hdPos]
    exact h4 ▸ Nat.succ_le_of_lt h3
  have hMetaEnd : levelMeta + 2 * d ≤ heap := by
    have h2d : 0 < 2 * d := Nat.mul_pos (by decide) hdPos
    have h1 := hTagMeta0 (2 * d - 1) (Nat.sub_lt h2d Nat.one_pos)
    have h3 := htagLt (by rw [h1]; exact Nat.ne_of_gt (Nat.add_pos_left (by decide) _))
    have h4 : levelMeta + (2 * d - 1) + 1 = levelMeta + 2 * d := by
      rw [Nat.add_assoc, Nat.sub_add_cancel h2d]
    exact h4 ▸ Nat.succ_le_of_lt h3
  have hCoreFootLt (j : ℕ) (hj : j < d) (a : ℕ)
      (ha : Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) : a < heap :=
    htagLt (by rw [hT21 j hj a ha]; exact Nat.ne_of_gt (Nat.add_pos_left (by decide) _))
  have hNotFoot2 {a : ℕ} (ha : a < heap) (hne : tok.tag a ≠ 21 + i0) :
      ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a := fun hf => by
    rcases hFootI0_2 a hf with h0 | ⟨hlo, _⟩
    · exact hne (hT21 i0 hiLt a h0)
    · exact absurd (lt_of_lt_of_le ha ((Nat.le_add_right heap _).trans hlo)) (lt_irrefl _)
  have hs2_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv5 : v ≠ 5)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s2.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs2_frame a (lt_of_lt_of_le hlt (Nat.le_add_right heap _))
      (fun j hj1 hj2 hf => hvC j hj1 hj2 (ht.symm.trans (hT21 j hj2 a hf)))
      (Or.inl hlt), hmem0_eq ht hv5]
  have hs3_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv4 : v ≠ 4) (hv5 : v ≠ 5)
      (hv22 : v ≠ 22 + d) (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s3.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs3_frame a (lt_of_lt_of_le hlt ((Nat.le_add_right heap _).trans hs2_lo))
      (hNotFoot2 hlt (ht ▸ hvC i0 le_rfl hiLt))
      (fun h => hv4 (ht.symm.trans (h ▸ hTagBranch i0 (le_of_lt hiLt))))
      (fun hlt1 => ⟨fun h => hv22 (ht.symm.trans (h ▸ hTagMetaL (i0 + 1) hlt1)),
        fun h => hv22 (ht.symm.trans (h ▸ hTagMetaG (i0 + 1) hlt1))⟩)]
    exact hs2_eq_mem0 ht hv0 hv5 hvC
  have hs3_geHeap1 : heap1 ≤ s3.regs 4 := hs2_lo.trans h4Lo3
  have hSpaceTot := hOps.spaceTotal
  -- Disjointness between table blocks
  have hSepHB : handleBase + d < branchBase ∨ branchBase + d < handleBase :=
    Or.inl (Nat.add_lt_add_left (Nat.lt_succ_self d) handleBase)
  have h4ne21d : (4 : ℕ) ≠ 21 + d := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 4 < 21) (Nat.le_add_right 21 d))
  have h4ne22d : (4 : ℕ) ≠ 22 + d := Nat.ne_of_lt (lt_of_lt_of_le (by decide : 4 < 22) (Nat.le_add_right 22 d))
  have hSepHM : handleBase + d < lvlMTable ∨ lvlMTable + d ≤ handleBase :=
    (interval_disj_of_tags (Nat.succ_pos d) hdPos
      (fun j hj => hTagHandle j (Nat.lt_succ_iff.mp hj)) hTagM0 h4ne21d).imp
      (fun h => Nat.lt_of_succ_le h) id
  have hSepBM : branchBase + d < lvlMTable ∨ lvlMTable + d ≤ branchBase :=
    (interval_disj_of_tags (Nat.succ_pos d) hdPos
      (fun j hj => hTagBranch j (Nat.lt_succ_iff.mp hj)) hTagM0 h4ne21d).imp
      (fun h => Nat.lt_of_succ_le h) id
  have hSepHL : handleBase + d < levelMeta ∨ levelMeta + 2 * d ≤ handleBase :=
    (interval_disj_of_tags (Nat.succ_pos d) (Nat.mul_pos (by decide) hdPos)
      (fun j hj => hTagHandle j (Nat.lt_succ_iff.mp hj)) hTagMeta0 h4ne22d).imp
      (fun h => Nat.lt_of_succ_le h) id
  have hSepBL : branchBase + d < levelMeta ∨ levelMeta + 2 * d ≤ branchBase :=
    (interval_disj_of_tags (Nat.succ_pos d) (Nat.mul_pos (by decide) hdPos)
      (fun j hj => hTagBranch j (Nat.lt_succ_iff.mp hj)) hTagMeta0 h4ne22d).imp
      (fun h => Nat.lt_of_succ_le h) id
  have hSepML : lvlMTable + d ≤ levelMeta ∨ levelMeta + 2 * d ≤ lvlMTable :=
    Or.inl le_rfl
  -- The module and the model facts at the levels of `next`
  have hLvlN := hModelK.2.1
  rw [hChain'] at hLvlN
  have hCoreNext : ∀ j, i0 + 1 ≤ j → j < d →
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T
          (next.G j) cfg.P.k (next.lvlM j) next.N₀ vCap eCap capExp Psc allocation) ∧
      SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (next.G j) cfg.P.k
        (next.lvlM j) next.N₀ vCap eCap capExp Psc allocation Rcore p opCore := by
    intro j _ hj
    rw [hLvlN.2.1, hLvlN.2.2.1]
    have hM0_le_m : (next.G 0).m ≤ m := by
      have hG0Eq : next.G 0 = model.chain.G 0 :=
        (ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt).1 0 (Nat.zero_le _)
      rw [hG0Eq, hFresh0.m_eq]
      exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
        (Finset.card_range m)
    exact hCore j hj (next.G j) (hLvlN.1 j (le_of_lt hj))
      ((hLvlN.2.2.2 j (le_of_lt hj)).trans hM0_le_m)
  have hModelLevel3 : ∀ j, i0 + 1 ≤ j → j < d →
      let Gj := next.G j
      let ℓj := next.toTreeChain.chainLen next.ℓ j
      next.scState j = cfg.T.initOrd cfg.P.k (next.lvlM j) next.N₀ Gj
        (fun e => if e ∈ Gj.E then ℓj e else 0)
        (fun e => if e ∈ Gj.E then ℓj e else 0) (next.levelOrd j) ∧
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
      ordRotWords (chainLevelOrdAbs next j) 0 ≤ 1 + 2 * (next.G (j + 1)).n + 2 * (next.G (j + 1)).m ∧
      (j + 1 < d → (next.G (j + 1)).m ≤ next.lvlM (j + 1)) := by
    intro j hj1 hj2
    obtain ⟨_, hGSucc, hBr, hUpd, _, _⟩ := hExLvls j hj1 hj2
    have hNL := hNextLvls j hj1 hj2
    rw [hChain'] at hNL
    obtain ⟨hmLe, hnLe, hMiW, hWExp, hRot, hPosJ, hSubJ, hFitsJ⟩ := hNL
    have hZeroExt :=
      ordAlgorithm1_shift_coreAt_eq_zeroExtension hInitOrdEq cfg.L cfg.P chain hiLt hj1 hj2
    have hGradSc :
        cfg.T.initOrd cfg.P.k (next.lvlM j) next.N₀ (next.G j)
          (fun e => if e ∈ (next.G j).E then next.toTreeChain.chainLen next.ℓ j e else 0)
          (fun e => if e ∈ (next.G j).E then next.toTreeChain.chainLen next.ℓ j e else 0)
          (next.levelOrd j) = next.scState j := by
      rw [hExLvlM, hExN0, hExEll]
      exact (hZeroExt.trans (hInitOrdEq _ _ _ _ _ _ _ _ _ (fun _ _ => rfl))).symm
    have hRW := hModelK.2.2.1 j (Nat.le_of_succ_le hj1) hj2
    rw [hChain', hBr] at hRW
    have hHnNext : (next.G (j + 1)).n ≤ next.N₀ := by
      have := hModelK.2.2.2.1 (j + 1) (by omega); rwa [hChain'] at this
    refine ⟨hGradSc.symm, hGSucc, hBr, hUpd, hmLe, hnLe, hMiW, hWordExpEq ▸ hWExp, hRot, hPosJ,
      hSubJ, fun e he => by
        obtain ⟨q, hq, hqEq⟩ := hFitsJ e he; exact ⟨q, hq, by rw [hFmtPrec]; exact hqEq⟩,
      le_rfl, hHnNext, hRW, fun hlt => ?_⟩
    have hNL1 := hNextLvls (j + 1) (Nat.le_succ_of_le hj1) hlt
    rw [hChain'] at hNL1
    exact hNL1.1
  have hOrdW3 : i0 + 1 < d → ordW3 ≤ 2 * (next.G (i0 + 1)).n + 2 * (next.G (i0 + 1)).m + 1 := by
    intro hlt
    have hRW := hModelK.2.2.1 i0 le_rfl hiLt
    rw [hChain', hExBr] at hRW
    dsimp only [next, chain, i0] at hOrdLe3 hRW ⊢
    omega
  rw [hChain'] at hLastAgree hLastPos hLastStr
  have hMidRoom : s3.regs 4 + (Finset.range d).sum levelSpace + lastSpace < 2 ^ w := by
    have h2 : 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace +
        (Finset.range d).sum levelSpace + lastSpace ≤ deepSpace :=
      ((Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))).trans hSpaceTot
    have h3 : s3.regs 4 + (Finset.range d).sum levelSpace + lastSpace ≤ heap + deepSpace := by
      have hA := Nat.add_le_add_right (Nat.add_le_add_right hs3_heapLe ((Finset.range d).sum levelSpace)) lastSpace
      have hB : heap + 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace +
          (Finset.range d).sum levelSpace + lastSpace =
          heap + (2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace +
            (Finset.range d).sum levelSpace + lastSpace) := by
        simp only [Nat.add_assoc]
      exact hA.trans (hB ▸ Nat.add_le_add_left h2 heap)
    exact lt_of_le_of_lt h3 hHeapRoom
  have hNextN0W : next.N₀ < 2 ^ w := hLvlN.2.2.1.symm ▸ hN0W
  have h3_56' : s3.regs 56 = next.N₀ := h3_56.trans hExN0.symm
  have hL_lt_w : L < 2 ^ w :=
    lt_of_le_of_lt ((Nat.le_mul_of_pos_left L (by decide : 0 < 4)).trans (Nat.le_add_right _ 2)) hL4W
  have hP_lt_w : fmt.precision < 2 ^ w :=
    hFmtPrec.symm ▸ lt_of_le_of_lt (hWidth.trans (Nat.le_add_right _ 2)) hL4W
  have hw9 : 9 < 2 ^ w := lt_trans (by decide : 9 < 17) hw17
  have hhb_lt : handleBase + d < branchBase + d :=
    Nat.add_lt_add_right (Nat.lt_add_of_pos_right (Nat.succ_pos d)) d
  have hh_lt_s3 : handleBase + d < s3.regs 4 :=
    lt_trans hhb_lt (lt_of_lt_of_le hLevelEnd ((Nat.le_add_right heap _).trans hs3_geHeap1))
  have hb_lt_s3 : branchBase + d < s3.regs 4 :=
    lt_of_lt_of_le hLevelEnd ((Nat.le_add_right heap _).trans hs3_geHeap1)
  have hM_le_s3 : lvlMTable + d ≤ s3.regs 4 :=
    hMEnd.trans ((Nat.le_add_right heap _).trans hs3_geHeap1)
  have hMeta_le_s3 : levelMeta + 2 * d ≤ s3.regs 4 :=
    hMetaEnd.trans ((Nat.le_add_right heap _).trans hs3_geHeap1)
  have hS3_disj {a : ℕ} (ha : s2.regs 4 ≤ a) :
      (a < handleBase + (i0 + 1) ∨ handleBase + d < a) ∧
      (a < branchBase + (i0 + 1) ∨ branchBase + d < a) ∧
      (a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a) :=
    have hge : heap ≤ a := (Nat.le_add_right heap _).trans (hs2_lo.trans ha)
    ⟨Or.inr (lt_of_lt_of_le (lt_trans hhb_lt hLevelEnd) hge),
     Or.inr (lt_of_lt_of_le hLevelEnd hge),
     Or.inr (hMetaEnd.trans hge)⟩
  have hLvlM3 : ∀ j, i0 + 1 ≤ j → j < d → s3.mem (lvlMTable + j) = next.lvlM j := by
    intro j _ hj2
    have hne : 21 + d ≠ 0 ∧ 21 + d ≠ 4 ∧ 21 + d ≠ 5 ∧ 21 + d ≠ 22 + d ∧
        ∀ r, i0 ≤ r → r < d → 21 + d ≠ 21 + r :=
      ⟨Nat.ne_of_gt (Nat.add_pos_left (by decide) _),
       Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 21) (Nat.le_add_right 21 d)),
       Nat.ne_of_gt (lt_of_lt_of_le (by decide : 5 < 21) (Nat.le_add_right 21 d)),
       Nat.ne_of_lt (Nat.add_lt_add_right (by decide : 21 < 22) d),
       fun r _ hr h => absurd (Nat.add_left_cancel h) (Nat.ne_of_gt hr)⟩
    rw [hs3_eq_mem0 (hTagM0 j hj2) hne.1 hne.2.1 hne.2.2.1 hne.2.2.2.1 hne.2.2.2.2,
      hLvlM0 j hj2, hExLvlM]
  have hRoom3 : s3.regs 4 + (Finset.Ico (i0 + 1) d).sum levelSpace + lastSpace < 2 ^ w := by
    have hSumLe := sum_Ico_le_sum_range (a := i0 + 1) (b := d) (d := d) le_rfl levelSpace
    exact lt_of_le_of_lt (Nat.add_le_add_right (Nat.add_le_add_left hSumLe _) _) hMidRoom
  -- Phase 3: `ordRebuildSuffixProgramKFBLStore` on `[i0 + 1, d]`
  let restSp : ℕ → ℕ := fun j =>
    ordLevelSpace L capExp capLimit 0 (next.lvlM j) next.N₀ (next.G (j + 1)).m
  obtain ⟨s4, c3, newTermTok, coreTok4, r3, hs4_lo, hs4_hi, hz4, hCores4,
      hCoreDisj4, hMeta4, hMetaOrd4, hTermB4, _, hTermRep4, hTermFoot4, hTermDisj4, hs4_frame, hc3⟩ :=
    ordRebuildSuffixProgramKFBLStore_runs_ord (w := w) (L := L)
      (depth := Expander.chosenL (cfg.P.M₀ ^ 2)) (vCap := vCap) (eCap := eCap)
      (capExp := capExp) (capLimit := capLimit) (init := initCore)
      (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
      (intDiv := intDiv) (copy := copy) (lastInit := lastInit) (first := i0 + 1)
      (handleBase := handleBase) (branchBase := branchBase) (lvlMTable := lvlMTable)
      (levelLens := levelMeta) (heapFloor := s3.regs 4) (lastMul := lastMul)
      (stretchPrec := stretchPrec) (fmt := fmt) (T := cfg.T) (LT := cfg.L) (CP := cfg.P)
      (P := Psc) (allocation := allocation) (lastAlloc := lastAlloc)
      (coreInitSpace := fun j => levelSpace j - restSp j)
      (nextM := fun j => (next.G (j + 1)).m) (Rcore := Rcore) (p := p) (op := opCore)
      (opLast := opLast) (st := s3) (ω := ω) next levelSpace (levelCost model i) lastSpace
      (Nat.succ_le_of_lt hiLt) hCoreLocal hFmtBits (by rw [hFmtPrec]; exact hWidth) hL_lt_w
      hP_lt_w hDepthW hdW hkPos hkW hNextN0W hw9 h3_1
      le_rfl h3_20 h3_21 h3_51 h3_52 h3_56' h3_57 h3_58 h3_67 h3_68 h3_98
      hh_lt_s3 hb_lt_s3 hM_le_s3 hMeta_le_s3
      hSepHB hSepHM hSepBM hSepHL hSepBL hSepML hLvlM3
      hH3 (by rw [hExEll]; exact hLen3) hGrad3
      (fun hlt => ⟨ordW3, (hOrd3 hlt).1, (hOrd3 hlt).2.1, (hOrd3 hlt).2.2, hOrdW3 hlt⟩)
      hHEnd3 hLenEnd3
      (fun _ ha1 _ => hS3_disj (h6Lo3.trans ha1))
      (fun _ ha1 _ => hS3_disj (h7Lo3.trans ha1))
      hz3 hCoreNext hcapLim
      (fun j hj1 hj2 g l gr o h => by
        have hSp := hOps.levelSpaceDom model i j g l gr o h hiLt hj1 hj2
          hModelK.1.2.2.1 (fun r _ => congrFun hModelK.1.2.1 r) hModelK
        dsimp only at hSp
        rw [ordLevelSpace_eq_add] at hSp
        dsimp only [restSp, next, chain, i0] at hSp ⊢
        omega)
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy
      (hLastImpl (next.G d)
        (le_trans (by simpa [hChain'] using hModelK.2.2.2.2.2.2.2.2.2.2)
          (by
            rw [hFresh0.m_eq]
            exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
              (Finset.card_range m)))
        (by simpa [hChain'] using hModelK.2.2.2.2.2.2.2.2.1 d le_rfl)
        (hLvlN.1 d le_rfl) (by simpa [hChain'] using hModelK.2.2.2.2.2.2.2.2.2.1))
      hModelLevel3
      ⟨hExLast.trans (by rw [hExEll]), hExLastBr, hLastAgree, hLastPos, hLastStr⟩
      (fun j hj1 hj2 => by
        have hSp := hOps.levelSpaceDom model i j 0 0 0 0 0 hiLt hj1 hj2
          hModelK.1.2.2.1 (fun r _ => congrFun hModelK.1.2.1 r) hModelK
        dsimp only at hSp
        rw [ordLevelSpace_eq_add] at hSp ⊢
        exact Nat.sub_add_cancel (Nat.le_of_add_left_le hSp) |>.le)
      (fun j hj1 hj2 => hOps.levelCostDom model i j hiLt hj1 hj2)
      hOps.lastSpaceDom hRoom3 (tok.coreTok i0)
  have hs4_heapLe : s4.regs 4 ≤ heap + 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace +
      (Finset.range d).sum levelSpace + lastSpace := by
    have hSumLe := sum_Ico_le_sum_range (a := i0 + 1) (b := d) (d := d) le_rfl levelSpace
    exact le_trans hs4_hi (Nat.add_le_add_right (Nat.add_le_add hs3_heapLe hSumLe) _)
  clear hCore hForestCap hLastImpl hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hInitOrdEq hOps
    hModelK hCoreNext hModelLevel3 hOrdW3 hLastAgree hLastPos hLastStr hExLvls hExLast
    hExLastBr hExEll hExLvlM hExN0 hExBr hLvlN hNextLvls hCaps0 hMemEq hBranLt
    hSepHB hSepHM hSepBM hSepHL hSepBL hSepML hMidRoom hSpaceTot hMEnd hLvlM0 hTagM0
  -- Preserve `yI0_3` across Phase 3
  have hY3FootLt (a : ℕ) (ha : Rcore.foot (tok.coreHandle i0) yI0_3 a) : a < s3.regs 4 := by
    rcases hFootI0_3 a ha with h2 | ⟨_, hhi⟩
    · rcases hFootI0_2 a h2 with h0 | ⟨_, hhi2⟩
      · exact (hCoreFootLt i0 hiLt a h0).trans_le
          (le_trans (Nat.le_add_right heap _) hs3_geHeap1)
      · exact hhi2.trans_le h4Lo3
    · exact hhi
  have hH_end : handleBase + d < heap := lt_trans hhb_lt hLevelEnd
  have hMetaD_le : levelMeta + d ≤ levelMeta + 2 * d :=
    Nat.add_le_add_left (Nat.le_mul_of_pos_left d (by decide)) levelMeta
  have hY3Pres4 : Rcore.rep (tok.coreHandle i0) (chainLevelOrdAbs next i0) yI0_3 s4.mem ∧
      Rcore.phi (tok.coreHandle i0) yI0_3 s4.mem = Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem := by
    have hneMeta : 21 + i0 ≠ 22 + d :=
      Nat.ne_of_lt (Nat.add_lt_add (by decide : 21 < 22) hiLt)
    have hne4 : 21 + i0 ≠ 4 :=
      Nat.ne_of_gt (lt_of_lt_of_le (by decide : 4 < 21) (Nat.le_add_right 21 i0))
    have hloc := hCoreLocal (tok.coreHandle i0) (chainLevelOrdAbs next i0) yI0_3 s3.mem s4.mem
      (fun a ha => by
        have hlt3 := hY3FootLt a ha
        have hne : (a < handleBase + (i0 + 1) ∨ handleBase + d < a) ∧
            (a < branchBase + (i0 + 1) ∨ branchBase + d < a) ∧
            ((a < levelMeta + (i0 + 1 + 1) ∨ levelMeta + d ≤ a) ∧
             (a < levelMeta + d + (i0 + 1 + 1) ∨ levelMeta + 2 * d ≤ a)) := by
          rcases hFootI0_3 a ha with h2 | ⟨hlo, _⟩
          · rcases hFootI0_2 a h2 with h0 | ⟨hlo2, _⟩
            · have ht := hT21 i0 hiLt a h0
              have hm := not_mem_interval_of_tag_ne (b := levelMeta) (lo := 0) (hi := 2 * d)
                (fun j _ hj => hTagMeta0 j hj) (ht ▸ hneMeta)
              exact ⟨(not_mem_interval_of_tag_ne (b := handleBase) (lo := i0 + 1) (hi := d + 1)
                  (fun j _ hj => hTagHandle j (Nat.lt_succ_iff.mp hj)) (ht ▸ hne4)).imp
                  id (fun h => Nat.lt_of_succ_le h),
                (not_mem_interval_of_tag_ne (b := branchBase) (lo := i0 + 1) (hi := d + 1)
                  (fun j _ hj => hTagBranch j (Nat.lt_succ_iff.mp hj)) (ht ▸ hne4)).imp
                  id (fun h => Nat.lt_of_succ_le h),
                hm.elim
                  (fun h =>
                    have h0' : a < levelMeta := Nat.add_zero levelMeta ▸ h
                    ⟨Or.inl (lt_of_lt_of_le h0' (Nat.le_add_right _ _)),
                     Or.inl (lt_of_lt_of_le h0' ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))⟩)
                  (fun h => ⟨Or.inr (hMetaD_le.trans h), Or.inr h⟩)⟩
            · have hge := le_trans (Nat.le_add_right heap _) hlo2
              exact ⟨Or.inr (lt_of_lt_of_le hH_end hge), Or.inr (lt_of_lt_of_le hLevelEnd hge),
                ⟨Or.inr (hMetaD_le.trans (hMetaEnd.trans hge)),
                  Or.inr (hMetaEnd.trans hge)⟩⟩
          · have hge := le_trans (Nat.le_add_right heap _) (le_trans hs2_lo hlo)
            exact ⟨Or.inr (lt_of_lt_of_le hH_end hge), Or.inr (lt_of_lt_of_le hLevelEnd hge),
              ⟨Or.inr (hMetaD_le.trans (hMetaEnd.trans hge)),
                Or.inr (hMetaEnd.trans hge)⟩⟩
        exact (hs4_frame a hlt3 hne.1 hne.2.1 hne.2.2).symm)
    exact ⟨hloc.1 hRepI0_3, hloc.2.symm⟩
  -- Compose `r012` and `r3`
  have r03 : Runs w p ω
      (shiftDeepInitRegsKFBL ;; shiftDeepCollectOldKFBL (opCore 2) ;;
        shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5) ;;
        ordRebuildSuffixProgramKFBLStore initCore (opCore 3) (opCore 2) coreLenProc (opCore 5)
          lastInit)
      (startState [root, i0, heap] mem pos) .normal s4 (c012 + c3 + 1) := by
    rcases runs_seq_iff.mp r012 with ⟨_, _, _, hne, _⟩ | ⟨s1', ca, cbc, ra, rbc, hcEq⟩
    · exact absurd hne (by simp)
    · rcases runs_seq_iff.mp rbc with ⟨_, _, _, hne2, _⟩ | ⟨s2', cb, cc, rb, rc, hcEq2⟩
      · exact absurd hne2 (by simp)
      · exact runs_seq_iff.mpr (Or.inr ⟨s1', ca, cb + (cc + c3 + 1) + 1, ra,
          runs_seq_iff.mpr (Or.inr ⟨s2', cb, cc + c3 + 1, rb,
            runs_seq_iff.mpr (Or.inr ⟨s3, cc, c3, rc, r3, rfl⟩), rfl⟩),
          by omega⟩)
  refine ⟨s2, s3, s4, c012 + c3 + 1, newTermTok, yI0_2, yI0_3,
    coreTok4, r03, hs2_lo, h4Lo3, hs4_lo, hs4_heapLe, hz4, hOldForestsSafe2, hFootI0_2,
    hs2_frame, hBr3, hFootI0_3, hH3, hLen3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3, h7Disj3, h6Le7_3,
    hMeta3, hs3_frame, hY3Pres4.1, hY3Pres4.2, hCores4, hCoreDisj4, hMeta4, hMetaOrd4, hTermB4, hTermRep4,
    hTermFoot4, hTermDisj4, hs4_frame,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 70 (by decide)).trans h3_70,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 71 (by decide)).trans h3_71,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 73 (by decide)).trans h3_73,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 75 (by decide)).trans h3_75,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 77 (by decide)).trans h3_77,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 78 (by decide)).trans h3_78,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 79 (by decide)).trans h3_79,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 80 (by decide)).trans h3_80,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 81 (by decide)).trans h3_81,
    (ordRebuildSuffixProgramKFBLStore_preserves_ge70 r3 83 (by decide)).trans h3_83, ?_⟩
  clear r03 r3 r012 hCores4 hCoreDisj4 hMeta4 hTermRep4 hTermFoot4 hTermDisj4
    hH3 hLen3 hGrad3 hOrd3 hOldForestsSafe2 hY3Pres4 hRepI0_3
  dsimp only [d, i0, chain, next, handleBase] at hc012 hc3 ⊢
  omega

end MinCostFlow.MinRatio
