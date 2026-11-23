module

public import MinCostFlow.MinRatio.WireShiftDeepSpecKFBL
public import MinCostFlow.MinRatio.WireShiftDeepStepsKFBL
public import MinCostFlow.MinRatio.WireShiftDeepRestartKFBL
public import MinCostFlow.MinRatio.WireShiftDeepInitKFBL
public import MinCostFlow.MinRatio.WireShiftDeepPrep
import WordRAM.Tactic

/-!
# Phases 0 to 2 of the deep shift under the layout contract (`WireShiftDeepPrepKFBL`)

`shiftDeepKFBL_phases_0_to_2_runs` is the `KFBL` copy of `shiftDeep_phases_0_to_2_runs`
(`WireShiftDeepPrep.lean`). It runs Phase 0 (`shiftDeepInitRegsKFBL`, which also loads the depth
of the solver header into register `98`), Phase 1 (`shiftDeepCollectOldKFBL_runs`) and Phase 2
(`shiftDeepRestartAndReadoutKFBL_runs`) of a deep shift `i < d`.

The hypotheses differ from the `K` version in three ways.
* The module meets the layout contract at every level (`DeepShiftCoreKFBL`), and the forest of
  op `2` has caps of size at most `fcap` (`DeepShiftForestCapKFBL`). The placement fields of
  `DeepShiftOpsHyp` are gone.
* The stored level graphs have the caps `(vCap, eCap)` (`SolverLevelCapsAt`).
* The model meets `ShiftDeepModelInvKFBL`: its level graphs have `n ≤ m + 1`, its level sizes are
  those of the configuration, and the order of the new branch has the right number of words.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

set_option maxHeartbeats 1600000 in
/-- **Phases 0 to 2 of the deep shift under the layout contract** (`i < d`). The graph of level
`i + 1` that Phase 2 reads has the caps `(vCap, eCap)`, the old forest of level `i` that Phase 1
copies has size at most `fcap`, and register `98` holds the depth of the solver header. -/
theorem shiftDeepKFBL_phases_0_to_2_runs
    {w L P m V psi k epsExp drainUnit capExp wordExp stretchPrec lastMul
      intCapMax forestEdgeCap deepSpace deepFixed toolMul vCap eCap capLimit fcap restartSpace
      lastSpace initCore coreLenProc edgeProc signExt mul intDiv copy root heap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {i : Fin (cfg.P.d + 1)}
    (levelSpace : ℕ → ℕ) (levelCost : Alg2State cfg → Fin (cfg.P.d + 1) → ℕ → ℕ)
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hFmtPrec : fmt.precision = P) (hw17 : 17 < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hdW : cfg.P.d < 2 ^ w)
    (hCore : DeepShiftCoreKFBL fmt L m vCap eCap capExp cfg Psc allocation Rcore p initCore opCore)
    (hForestCap : DeepShiftForestCapKFBL fmt L vCap eCap capExp cfg Psc allocation fcap Rcore p
      opCore)
    (hcapLim : vCap + eCap + 2 ≤ capLimit)
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
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a →
      a < heap)
    (hzHeap : ZeroFrom mem heap)
    (hHeapRoom : heap + deepSpace < 2 ^ w) :
    let d := cfg.P.d
    let i0 := i.val
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i0).1
    let newBran := (model.chain.bran i0 + 1) % cfg.P.k
    let handleBase := tok.handle + 18
    let branchBase := handleBase + (d + 1)
    let lvlMTable := solverLvlMAddr tok.table d
    let levelMeta := solverLevelMetaAddr tok.table d
    let cnt := d - i0 + 1
    let heap1 := heap + 2 * cnt
    let Fi0 := (cfg.T.lsfs (model.chain.scState i0) (model.chain.bran i0)).F.F
    let H1 := next.G (i0 + 1)
    let LwMax := ordLevelLwMax L capExp (model.chain.lvlM i0) model.chain.N₀
    let forestSafe : ℕ → Prop := fun a =>
      (a < heap → tok.tag a ≠ 4 ∧ tok.tag a ≠ 22 + d) ∧ (a < heap ∨ heap1 ≤ a)
    ∃ (s2 s3 : State) (c012 ordW3 : ℕ) (yI0_2 yI0_3 : Rcore.τ),
      Runs w p ω
        (shiftDeepInitRegsKFBL ;; shiftDeepCollectOldKFBL (opCore 2) ;;
          shiftDeepRestartAndReadoutKFBL (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5))
        (startState [root, i0, heap] mem pos) .normal s3 c012 ∧
      heap1 ≤ s2.regs 4 ∧ s2.regs 4 ≤ s3.regs 4 ∧
      s3.regs 4 ≤ heap + 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace ∧
      ZeroFrom s3.mem (s3.regs 4) ∧
      -- Phase 1 preserved old forests with safety predicates
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
      -- Phase 2 outputs for level `i0` and next level `i0 + 1`
      s3.mem (branchBase + i0) = newBran ∧
      Rcore.rep (tok.coreHandle i0) (chainLevelOrdAbs next i0) yI0_3 s3.mem ∧
      (∀ a, Rcore.foot (tok.coreHandle i0) yI0_3 a →
        Rcore.foot (tok.coreHandle i0) yI0_2 a ∨ (s2.regs 4 ≤ a ∧ a < s3.regs 4)) ∧
      DynGraphAt s3.mem (s3.regs 6) vCap eCap (next.G (i0 + 1)) ∧
      EdgeValuesAt s3.mem (s3.regs 7) 4 L fmt.precision (next.G (i0 + 1)).E
        (next.toTreeChain.chainLen model.chain.ℓ (i0 + 1)) ∧
      s3.regs 8 = s3.regs 7 ∧
      (i0 + 1 < d →
        OrdListAt s3.mem (s3.regs 9) (next.levelOrd (i0 + 1)) ordW3 ∧
        (∀ t < ordW3, s3.mem (s3.regs 9 + t) < 2 ^ w) ∧
        s3.regs 9 + ordW3 ≤ s3.regs 4) ∧
      ordW3 ≤ ordRotWords (chainLevelOrdAbs next i0) newBran ∧
      s2.regs 4 ≤ s3.regs 6 ∧ s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 4 ∧
      (∀ a, s3.regs 6 ≤ a → a < s3.regs 6 + dynGraphSize vCap eCap →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s2.regs 4 ≤ s3.regs 7 ∧ s3.regs 7 + eCap * L ≤ s3.regs 4 ∧
      (∀ a, s3.regs 7 ≤ a → a < s3.regs 7 + eCap * L →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s3.regs 6 + dynGraphSize vCap eCap ≤ s3.regs 7 ∧
      (i0 + 1 < d → s3.mem (levelMeta + (i0 + 1)) = s3.regs 7 ∧
        s3.mem (levelMeta + d + (i0 + 1)) = s3.regs 6) ∧
      (∀ a < s2.regs 4, ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a → a ≠ branchBase + i0 →
        (i0 + 1 < d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + d + (i0 + 1)) →
        s3.mem a = s2.mem a) ∧
      -- Registers set up for Phase 3 and preserved high registers
      s3.regs 1 = cfg.P.k ∧ s3.regs 20 = i0 + 1 ∧ s3.regs 21 = d ∧
      s3.regs 51 = handleBase + (i0 + 1) ∧ s3.regs 52 = branchBase + (i0 + 1) ∧
      s3.regs 56 = model.chain.N₀ ∧ s3.regs 57 = lvlMTable ∧ s3.regs 58 = levelMeta ∧
      s3.regs 67 = L ∧ s3.regs 68 = fmt.precision ∧
      s3.regs 70 = root ∧ s3.regs 71 = i0 ∧ s3.regs 73 = tok.handle ∧
      s3.regs 75 = d ∧ s3.regs 77 = handleBase ∧ s3.regs 78 = branchBase ∧
      s3.regs 79 = cnt ∧ s3.regs 80 = heap ∧ s3.regs 81 = heap + cnt ∧
      s3.regs 83 = levelMeta ∧ s3.regs 98 = Expander.chosenL (cfg.P.M₀ ^ 2) ∧
      -- Cost + `Rcore.phi` bound
      c012 + Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem ≤
        copyGraphLiveCost Fi0.n Fi0.m + (d - i0) * (Psc.readout + 48) +
        Psc.mul * (cfg.T.cost (next.scState i0) - cfg.T.cost (model.chain.scState i0) + 1) +
        Psc.mul * (2 * H1.n + 2 * H1.m + 2) *
          SparseCore.bundleLogFactor (model.chain.lvlM i0) model.chain.N₀ +
        2 * Psc.readout + copyGraphLiveCost H1.n H1.m +
        H1.m * (wireCoreLenEdgeCost LwMax + 30) + 570 +
        (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) := by
  dsimp only
  let d := cfg.P.d
  let i0 := i.val
  let chain := model.chain
  let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P chain i0).1
  let newBran := (chain.bran i0 + 1) % cfg.P.k
  let handleBase := tok.handle + 18
  let branchBase := handleBase + (d + 1)
  let n0Cell := solverN0Addr tok.table d
  let lvlMTable := solverLvlMAddr tok.table d
  let levelMeta := solverLevelMetaAddr tok.table d
  let cnt := d - i0 + 1
  let heap1 := heap + 2 * cnt
  let forestSafe : ℕ → Prop := fun a =>
    (a < heap → tok.tag a ≠ 4 ∧ tok.tag a ≠ 22 + d) ∧ (a < heap ∨ heap1 ≤ a)
  have hChain' : (alg2LoopShiftStep cfg model i).chain = next := by
    simp [alg2LoopShiftStep, next, chain, i0]
  -- The module at the levels of `model.chain`
  have hLvl0 := hModelK.1
  have hM0_le_m : (model.chain.G 0).m ≤ m := by
    obtain ⟨_, _, _, _, hFresh0, _, hExtM0, _⟩ := hRep0
    rw [hFresh0.m_eq]
    exact (Finset.card_le_card fun e he => Finset.mem_range.mpr (hExtM0 e he)).trans_eq
      (Finset.card_range m)
  have hCoreAt : ∀ j < cfg.P.d,
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractKFBL fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T
          (model.chain.G j) cfg.P.k (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc
          allocation) ∧
      SparseCoreReadoutFootAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T (model.chain.G j)
        cfg.P.k (model.chain.lvlM j) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p
        opCore := by
    intro j hj
    rw [hLvl0.2.1, hLvl0.2.2.1]
    exact hCore j hj (model.chain.G j) (hLvl0.1 j (le_of_lt hj))
      ((hLvl0.2.2.2 j (le_of_lt hj)).trans hM0_le_m)
  have hForestCapI0 : SparseCoreForestCapAt fmt L (Expander.chosenL (cfg.P.M₀ ^ 2)) cfg.T
      (model.chain.G i0) cfg.P.k (model.chain.lvlM i0) model.chain.N₀ vCap eCap capExp Psc
      allocation fcap Rcore p opCore := by
    rw [hLvl0.2.1, hLvl0.2.2.1]
    exact hForestCap i0 hiLt (model.chain.G i0) (hLvl0.1 i0 (le_of_lt hiLt))
  have hMetaCaps := SolverLevelMetaAt.atCaps hMeta0 hCaps0
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, _, _, _, ⟨hG0Cap, _, _, _⟩, _, _, _, _, _, _,
    hCores0, hTermPtr0, hTermBran0, hTermRep0, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, hT21⟩ :=
    hTags0
  obtain ⟨⟨hN0Val, hTagN0, _, _⟩, hCoreOwn0, _, hTagM0, hTagMeta0, _⟩ := hMeta0
  have hTagN0' : tok.tag (lvlMTable - 1) = 21 + d := by
    simpa [lvlMTable, solverLvlMAddr, solverN0Addr] using hTagN0
  obtain ⟨⟨hLastBranLt, _⟩, hScIn0, _, hNextSub1, hNextFits1, _, _, _, _, _, _, _, hLsfSub,
    hLastSubOld, _, _⟩ := hModelInv
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hmem0_eq {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 5) : mem a = mem0 a :=
    hMemEq a (ht ▸ hv)
  have hTagHandle (j : ℕ) (hj : j ≤ d) : tok.tag (handleBase + j) = 4 := hT4 j (by omega)
  have hTagBranch (j : ℕ) (hj : j ≤ d) : tok.tag (branchBase + j) = 4 := by
    have := hT4 ((d + 1) + j) (by omega)
    rwa [show tok.handle + 18 + ((d + 1) + j) = branchBase + j by
      dsimp [branchBase, handleBase]; omega] at this
  have hTagMetaG (j : ℕ) (hj : j < d) : tok.tag (levelMeta + d + j) = 22 + d := by
    have := hTagMeta0 (d + j) (by omega)
    rwa [show levelMeta + (d + j) = levelMeta + d + j by omega] at this
  have hTagMetaL (j : ℕ) (hj : j < d) : tok.tag (levelMeta + j) = 22 + d := hTagMeta0 j (by omega)
  have hRootW : root + 16 ≤ heap := by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ heap := by
    have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hLevelEnd : branchBase + d < heap := htagLt (by rw [hTagBranch d le_rfl]; decide)
  have hMetaEnd : levelMeta + 2 * d ≤ heap := by
    have := htagLt (by rw [hTagMeta0 (2 * d - 1) (by omega)]; omega); dsimp only [levelMeta, d] at *; omega
  have hTermTokLe : tok.termTok ≤ heap := by
    by_cases hlt : tok.termHandle < tok.termTok
    · have := htagLt (by rw [hT19 (tok.termTok - 1) ⟨by omega, by omega⟩]; decide); omega
    · have := hTermRep0.1; omega
  have hSpaceTot := hOps.spaceTotal
  -- Phase 0: `shiftDeepInitRegsKFBL`
  obtain ⟨s1, c0, r0, hc0, hs1Mem, h1_70, h1_71, _, h1_73, _, h1_75, h1_76, h1_77, h1_78,
      h1_79, h1_80, h1_81, h1_82, h1_83, h1_4, h1_98⟩ :=
    shiftDeepInitRegsKFBL_runs (w := w) (root := root) (i := i0) (heap0 := heap)
      (handle := tok.handle) (table := tok.table) (d := d) (k := cfg.P.k) (pos := pos) (p := p)
      (ω := ω) (mem := mem)
      ((hmem0_eq (hT1 0 (by omega)) (by decide)).trans (by simpa using hRootDir0 0 (by simp)))
      ((hmem0_eq (hT1 1 (by omega)) (by decide)).trans (by simpa using hRootDir0 1 (by simp)))
      ((hmem0_eq (hT2 11 (by omega)) (by decide)).trans
        (by have := hInitPar0 2 (by simp); simpa [Nat.add_assoc] using this))
      ((hmem0_eq (hT2 12 (by omega)) (by decide)).trans
        (by have := hInitPar0 3 (by simp); simpa [Nat.add_assoc] using this))
      ((hmem0_eq (hT2 17 (by omega)) (by decide)).trans hInitPar0.coreDepth_eq)
      hiLt (by omega) (by omega) (by dsimp [branchBase, handleBase] at hLevelEnd; omega)
      (by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr] at hMetaEnd ⊢; omega)
      (by dsimp [cnt] at *; omega) hw17
  -- Phase 1: `shiftDeepCollectOld`
  have hTermH1 : s1.mem (handleBase + d) = tok.termHandle := by
    rw [hs1Mem, hmem0_eq (hTagHandle d le_rfl) (by decide)]; exact hTermPtr0
  have hTermB1 : s1.mem (branchBase + d) = chain.lastBran := by
    rw [hs1Mem, hmem0_eq (hTagBranch d le_rfl) (by decide)]; exact hTermBran0
  obtain ⟨hOldTermBW, hOldTermLSF⟩ := hTermRep0.2.2.2 chain.lastBran hLastBranLt
  have hMem1_term (a : ℕ) (ha1 : tok.termHandle ≤ a) (ha2 : a < tok.termTok) :
      s1.mem a = mem0 a := by
    rw [hs1Mem, hmem0_eq (hT19 a ⟨ha1, ha2⟩) (by decide)]
  set oldTermLsfHdr := mem0 (tok.termHandle + 1 + chain.lastBran)
  set oldTermFPtr := mem0 (oldTermLsfHdr + 1)
  have hCoreFootLt (j : ℕ) (hj : j < d) (a : ℕ)
      (ha : Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) : a < heap :=
    htagLt (by rw [hT21 j hj a ha]; omega)
  have hCoreDisj0 (j₁ j₂ : ℕ) (h1 : j₁ < d) (h2 : j₂ < d) (hne : j₁ ≠ j₂) (a : ℕ)
      (ha1 : Rcore.foot (tok.coreHandle j₁) (tok.coreTok j₁) a)
      (ha2 : Rcore.foot (tok.coreHandle j₂) (tok.coreTok j₂) a) : False := by
    have := (hT21 j₁ h1 a ha1).symm.trans (hT21 j₂ h2 a ha2); omega
  have hCores1 : ∀ j, i0 ≤ j → j < d →
      s1.mem (handleBase + j) = tok.coreHandle j ∧
      s1.mem (branchBase + j) = chain.bran j ∧
      chain.bran j < cfg.P.k ∧ tok.coreHandle j < 2 ^ w ∧
      Rcore.rep (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) s1.mem ∧
      SparseCoreOrdInput cfg.T cfg.P.k (chain.lvlM j) chain.N₀ (chain.scState j) (chain.G j)
        (chain.levelOrd j) (chain.updCount j) ∧
      (∀ a, Rcore.foot (tok.coreHandle j) (tok.coreTok j) a → a < s1.regs 4) ∧
      (∀ r, i0 ≤ r → r < d →
        ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (handleBase + j) ∧
        ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (branchBase + j) ∧
        ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) (levelMeta + d + j)) ∧
      (handleBase + j < heap ∨ heap + cnt ≤ handleBase + j) ∧
      (branchBase + j < heap ∨ heap + cnt ≤ branchBase + j) ∧
      (levelMeta + d + j < heap ∨ heap + cnt ≤ levelMeta + d + j) ∧
      (∀ t < cnt, ¬ Rcore.foot (tok.coreHandle j) (tok.coreTok j) (heap + t)) ∧
      (DynGraphAt s1.mem (s1.mem (levelMeta + d + j)) vCap eCap (chain.G j) ∧
        s1.mem (levelMeta + d + j) + dynGraphSize vCap eCap ≤ s1.regs 4 ∧
        (∀ a, s1.mem (levelMeta + d + j) ≤ a →
          a < s1.mem (levelMeta + d + j) + dynGraphSize vCap eCap →
          (∀ r, i0 ≤ r → r < d → ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) a) ∧
          (a < heap ∨ heap + cnt ≤ a))) := by
    intro j hj1 hj2
    have h4a := hTagHandle j (le_of_lt hj2)
    have h4b := hTagBranch j (le_of_lt hj2)
    have h22 := hTagMetaG j hj2
    have hloc := hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) mem0
      s1.mem (fun a ha => (hs1Mem.symm ▸ hmem0_eq (hT21 j hj2 a ha) (by omega)).symm)
    obtain ⟨hDGj, _, _, _, hTagGj⟩ := hMetaCaps j hj2
    have hPtrEq : s1.mem (levelMeta + d + j) = mem0 (levelMeta + d + j) :=
      hs1Mem.symm ▸ hmem0_eq h22 (by omega)
    have hDGEndJ : mem0 (levelMeta + d + j) + dynGraphSize vCap eCap ≤ heap := by
      have hpos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
      have h1 : mem0 (levelMeta + d + j) ≤
          mem0 (levelMeta + d + j) + dynGraphSize vCap eCap - 1 := by omega
      have h2 : mem0 (levelMeta + d + j) + dynGraphSize vCap eCap - 1 <
          mem0 (levelMeta + d + j) + dynGraphSize vCap eCap := by omega
      have := htagLt (by rw [hTagGj _ h1 h2]; split_ifs <;> omega)
      omega
    have hChW : tok.coreHandle j < 2 ^ w :=
      lt_trans (hFootLt (tok.coreHandle j) (Or.inl (hCoreOwn0 j hj2))) (by omega)
    refine ⟨(hs1Mem.symm ▸ hmem0_eq h4a (by decide)).trans (hCores0 j hj2).1,
      (hs1Mem.symm ▸ hmem0_eq h4b (by decide)).trans (hCores0 j hj2).2.1,
      hBranLt j hj2, hChW, hloc.1 (hCores0 j hj2).2.2, hScIn0 j hj1 hj2,
      fun a ha => (hCoreFootLt j hj2 a ha).trans_le (by rw [h1_4]; omega),
      fun r _ hr2 => ⟨fun hf => by have := hT21 r hr2 _ hf; rw [h4a] at this; omega,
        fun hf => by have := hT21 r hr2 _ hf; rw [h4b] at this; omega,
        fun hf => by have := hT21 r hr2 _ hf; rw [h22] at this; omega⟩,
      Or.inl (htagLt (by rw [h4a]; decide)), Or.inl (htagLt (by rw [h4b]; decide)),
      Or.inl (htagLt (by rw [h22]; omega)),
      fun t _ hf => by have := hCoreFootLt j hj2 _ hf; omega,
      ⟨hPtrEq.symm ▸ dynGraphAt_of_agree hDGj (fun a ha1 ha2 =>
          hs1Mem.symm ▸ hmem0_eq (hTagGj a ha1 ha2) (by split_ifs <;> omega)),
        by rw [hPtrEq, h1_4]; omega,
        fun a ha1 ha2 => by
          rw [hPtrEq] at ha1 ha2
          exact ⟨fun r _ hr2 hf => by
              have := hT21 r hr2 a hf; rw [hTagGj a ha1 ha2] at this; split_ifs at this <;> omega,
            Or.inl (htagLt (by rw [hTagGj a ha1 ha2]; split_ifs <;> omega))⟩⟩⟩
  have hOldTermDG1 : DynGraphAt s1.mem oldTermFPtr tok.vcLast tok.ecLast
      (chain.lastLSFs chain.lastBran).F.F :=
    dynGraphAt_of_agree hOldTermLSF.2.1 (fun a ha1 ha2 =>
      hMem1_term a (by have := hOldTermBW.2.2.2.2.1; have := hTermRep0.1; omega)
        (by have := hOldTermBW.2.2.2.2.2.1; omega))
  obtain ⟨s2, c1, vcFi0, ecFi0, yI0_2, r1, hs2_lo, hs2_hi, hFcap2, hz2, _, _, _, _,
      hOldForestsSafe2, hRepI0_2, hFootI0_2, hs2_frame, hs2_regs, hc1⟩ :=
    shiftDeepCollectOldKFBL_runs (w := w) (L := L) (capExp := capExp) (i0 := i0)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (oldPtrs := heap) (intCap := tok.intCap) (termHandle := tok.termHandle)
      (vcLast := tok.vcLast) (ecLast := tok.ecLast) (lsfHdr := oldTermLsfHdr)
      (forestPtr := oldTermFPtr) (p := p) (ω := ω) (st := s1) chain tok.coreHandle tok.coreTok
      forestSafe
      (fun a ha => ⟨fun hlt => by rw [h1_4] at ha; omega, Or.inr (by rw [h1_4] at ha; exact ha)⟩)
      (fun j _ hj2 a ha => by
        have ht := hT21 j hj2 a ha
        exact ⟨fun _ => ⟨by rw [ht]; omega, by rw [ht]; omega⟩,
          Or.inl (hCoreFootLt j hj2 a ha)⟩)
      hCoreLocal hiLt h1_71 h1_75 h1_77 h1_78 h1_80 h1_83 hkW hdW (by omega)
      (by rw [h1_4]; omega) (by rw [h1_4]; dsimp [branchBase] at hLevelEnd; omega)
      (by rw [h1_4]; omega) (by rw [h1_4]; omega)
      (fun a ha => hs1Mem.symm ▸ hzHeap a (by rw [h1_4] at ha; omega))
      (fun j _ hj2 => (hCoreAt j hj2).2) hForestCapI0
      hCores1 (fun j₁ j₂ _ h2 _ h4 => hCoreDisj0 j₁ j₂ h2 h4)
      hTermH1 hTermB1
      (hMem1_term _ (by omega) (by have := hTermRep0.1; dsimp only [chain] at *; omega))
      (hMem1_term _ (by have := hOldTermBW.1; have := hTermRep0.1; dsimp only [chain] at *; omega)
        (by have := hOldTermBW.2.1; omega))
      hOldTermDG1
      (by have := hOldTermBW.2.2.2.2.2.1; rw [h1_4]; omega)
      (fun e he => hG0Cap e (hLastSubOld he))
      ⟨Or.inl (htagLt (by rw [hTagHandle d le_rfl]; decide)),
        Or.inl (htagLt (by rw [hTagBranch d le_rfl]; decide)),
        Or.inl (by have := hTermRep0.1; dsimp only [chain] at *; omega),
        Or.inl (by have := hOldTermBW.2.1; omega),
        by rw [h1_4]; have := hTermRep0.1; dsimp only [chain] at *; omega,
        by rw [h1_4]; have := hOldTermBW.2.1; omega,
        fun r _ hr2 => ⟨fun hf => by
            have := hT21 r hr2 _ hf; rw [hTagHandle d le_rfl] at this; omega,
          fun hf => by have := hT21 r hr2 _ hf; rw [hTagBranch d le_rfl] at this; omega,
          fun hf => by
            have := hT21 r hr2 _ hf
            rw [hT19 _ ⟨by omega, by have := hTermRep0.1; dsimp only [chain] at *; omega⟩] at this
            omega,
          fun hf => by
            have := hT21 r hr2 _ hf
            rw [hT19 _ ⟨by have := hOldTermBW.1; have := hTermRep0.1; dsimp only [chain] at *; omega,
              by have := hOldTermBW.2.1; omega⟩] at this
            omega⟩,
        fun a ha1 ha2 => by
          have h19 : tok.tag a = 19 := hT19 a ⟨by
              have := hOldTermBW.2.2.2.2.1; have := hTermRep0.1; omega,
            by have := hOldTermBW.2.2.2.2.2.1; omega⟩
          exact ⟨fun r _ hr2 hf => by have := hT21 r hr2 a hf; rw [h19] at this; omega,
            Or.inl (htagLt (by rw [h19]; decide)),
            ⟨fun _ => ⟨by rw [h19]; decide, by rw [h19]; omega⟩,
              Or.inl (htagLt (by rw [h19]; decide))⟩⟩⟩
      (by rw [h1_4]; omega)
      (fun j hj1 hj2 e he => hG0Cap e ((hLsfSub j hj1 hj2).1 he))
  have hs2_heapLe : s2.regs 4 ≤ heap + 2 * (d + 1) + (5 + fcap + 5 * d) := by
    rw [h1_4] at hs2_hi; omega
  -- Phase 2: `shiftDeepRestartAndReadout`
  have hs2_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv5 : v ≠ 5)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s2.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs2_frame a (by rw [h1_4]; omega)
      (fun j hj1 hj2 hf => hvC j hj1 hj2 (ht.symm.trans (hT21 j hj2 a hf)))
      (Or.inl hlt), hs1Mem, hmem0_eq ht hv5]
  obtain ⟨hGI0, hLenI0, hLenOwnI0, hTagLenI0, hTagGI0⟩ := hMetaCaps i0 hiLt
  have hGI0_ptr : s2.mem (levelMeta + d + i0) = mem0 (levelMeta + d + i0) :=
    hs2_eq_mem0 (hTagMetaG i0 hiLt) (by omega) (by omega) (fun _ _ _ => by omega)
  have hLenI0_ptr : s2.mem (levelMeta + i0) = mem0 (levelMeta + i0) :=
    hs2_eq_mem0 (hTagMetaL i0 hiLt) (by omega) (by omega) (fun _ _ _ => by omega)
  have hGI0_end : mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap ≤ heap := by
    have hpos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
    have h1 : mem0 (levelMeta + d + i0) ≤
        mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap - 1 := by omega
    have h2 : mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap - 1 <
        mem0 (levelMeta + d + i0) + dynGraphSize vCap eCap := by omega
    have := htagLt (by rw [hTagGI0 _ h1 h2]; split_ifs <;> omega); omega
  have hLenI0_end : mem0 (levelMeta + i0) + eCap * L ≤ heap := by
    by_cases h0 : eCap * L = 0
    · rw [h0, add_zero]; exact le_of_lt (hFootLt _ (Or.inl hLenOwnI0))
    · have h1 : mem0 (levelMeta + i0) ≤ mem0 (levelMeta + i0) + eCap * L - 1 := by omega
      have h2 : mem0 (levelMeta + i0) + eCap * L - 1 < mem0 (levelMeta + i0) + eCap * L := by
        omega
      have := htagLt (by rw [hTagLenI0 _ h1 h2]; omega); omega
  have hNotFoot2 {a : ℕ} (ha : a < heap) (hne : tok.tag a ≠ 21 + i0) :
      ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a := fun hf => by
    rcases hFootI0_2 a hf with h0 | ⟨hlo, _⟩
    · exact hne (hT21 i0 hiLt a h0)
    · rw [h1_4] at hlo; omega
  have hRestartSp := hOps.restartSpaceDom model i (tok.coreHandle i0) (s2.regs 4) hiLt
    hLvl0.2.2.1 (fun r _ => congrFun hLvl0.2.1 r) hModelK
  have hRotWLive : ordRotWords (chainLevelOrdAbs next i0) newBran ≤
      1 + 2 * (next.G (i0 + 1)).n + 2 * (next.G (i0 + 1)).m := by
    have hRW := hModelK.2.2.1 i0 le_rfl hiLt
    have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
    rw [hChain', hEx.2.2.2.1] at hRW
    exact hRW
  have hRotW : ordRotWords (chainLevelOrdAbs next i0) newBran ≤
      1 + 2 * chain.N₀ + 2 * (next.G (i0 + 1)).m := by
    have hHn : (next.G (i0 + 1)).n ≤ next.N₀ := by
      have := hModelK.2.2.2.1 (i0 + 1) (by omega); rwa [hChain'] at this
    have hEx := ordAlgorithm1_shift_exact cfg.T cfg.L cfg.P chain hiLt
    have hN0Eq : next.N₀ = chain.N₀ := hEx.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    omega
  obtain ⟨s3, ordW3, c2, yI0_3, r2, hBr3, hRepI0_3, hH3, hLen3, hGrad3, hOrd3, hOrdLe3, h6Lo3,
      hHEnd3, h6Disj3, h7Lo3, hLenEnd3, h7Disj3, h6Le7_3, hMeta3, h4Lo3, h4Hi3, hz3, hFootI0_3,
      hs3_frame, h3_1, h3_20, h3_21, h3_51, h3_52, h3_56, h3_57, h3_58, h3_67, h3_68,
      hs3_regs, hc2⟩ :=
    shiftDeepRestartAndReadoutKFBL_runs (w := w) (L := L) (capExp := capExp)
      (capLimit := capLimit) (coreLenProc := coreLenProc) (edgeProc := edgeProc)
      (signExt := signExt) (mul := mul) (intDiv := intDiv) (copy := copy) (i0 := i0)
      (handle := tok.handle) (handleBase := handleBase) (branchBase := branchBase)
      (lvlMTable := lvlMTable) (levelMeta := levelMeta) (N0 := model.chain.N₀)
      (coreH := tok.coreHandle i0) (nextM := (next.G (i0 + 1)).m) (LT := cfg.L) (p := p)
      (ω := ω) (st := s2) chain yI0_2 hCoreLocal hFmtBits
      (hCoreAt i0 hiLt).1 (hCoreAt i0 hiLt).2 hcapLim
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hiLt hkPos hkW hdW (by omega)
      ((hs2_regs 71 (by decide)).trans h1_71) ((hs2_regs 73 (by decide)).trans h1_73)
      ((hs2_regs 75 (by decide)).trans h1_75) ((hs2_regs 76 (by decide)).trans h1_76)
      ((hs2_regs 77 (by decide)).trans h1_77) ((hs2_regs 78 (by decide)).trans h1_78)
      ((hs2_regs 82 (by decide)).trans h1_82) ((hs2_regs 83 (by decide)).trans h1_83)
      ((hs2_eq_mem0 (hTagHandle i0 (le_of_lt hiLt)) (by decide) (by decide)
        (fun _ _ _ => by omega)).trans (hCores0 i0 hiLt).1)
      (lt_trans (hFootLt (tok.coreHandle i0) (Or.inl (hCoreOwn0 i0 hiLt))) (by omega))
      ((hs2_eq_mem0 (hTagBranch i0 (le_of_lt hiLt)) (by decide) (by decide)
        (fun _ _ _ => by omega)).trans (hCores0 i0 hiLt).2.1)
      (hBranLt i0 hiLt)
      ((hs2_eq_mem0 (hT2 5 (by omega)) (by decide) (by decide) (fun _ _ _ => by omega)).trans
        (by simpa using hDetHdr0 5 (by simp)))
      ((hs2_eq_mem0 (hT2 8 (by omega)) (by decide) (by decide) (fun _ _ _ => by omega)).trans
        (by have := hNumHdr0 3 (by simp); rw [hFmtPrec]; simpa [Nat.add_assoc] using this))
      (by dsimp only [lvlMTable, n0Cell, solverLvlMAddr, solverN0Addr]; omega)
      (by dsimp only [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr] at hMetaEnd ⊢; omega)
      ((hs2_eq_mem0 hTagN0' (by omega) (by omega) (fun _ _ _ => by omega)).trans hN0Val)
      ⟨by rw [h1_4] at hs2_lo; omega,
        by rw [h1_4] at hs2_lo; dsimp only [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr] at hMetaEnd ⊢; omega,
        by rw [h1_4] at hs2_lo; dsimp [branchBase] at hLevelEnd; omega,
        by rw [h1_4] at hs2_lo; omega,
        by rw [h1_4] at hs2_lo; omega⟩
      ⟨hNotFoot2 (htagLt (by rw [hTagBranch i0 (le_of_lt hiLt)]; decide))
          (by rw [hTagBranch i0 (le_of_lt hiLt)]; omega),
        hNotFoot2 (htagLt (by rw [hT2 5 (by omega)]; decide)) (by rw [hT2 5 (by omega)]; omega),
        hNotFoot2 (htagLt (by rw [hT2 8 (by omega)]; decide)) (by rw [hT2 8 (by omega)]; omega),
        hNotFoot2 (htagLt (by rw [hTagN0']; omega)) (by rw [hTagN0']; omega),
        hNotFoot2 (htagLt (by rw [hTagMetaL i0 hiLt]; omega)) (by rw [hTagMetaL i0 hiLt]; omega),
        hNotFoot2 (htagLt (by rw [hTagMetaG i0 hiLt]; omega)) (by rw [hTagMetaG i0 hiLt]; omega),
        fun hlt => ⟨hNotFoot2 (htagLt (by rw [hTagMetaL (i0 + 1) hlt]; omega))
            (by rw [hTagMetaL (i0 + 1) hlt]; omega),
          hNotFoot2 (htagLt (by rw [hTagMetaG (i0 + 1) hlt]; omega))
            (by rw [hTagMetaG (i0 + 1) hlt]; omega)⟩⟩
      ⟨fun h => by have := hT2 5 (by omega); rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hT2 8 (by omega); rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hTagN0'; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by
          have := hTagMetaL i0 hiLt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by
          have := hTagMetaG i0 hiLt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun hlt => ⟨fun h => by
            have := hTagMetaL (i0 + 1) hlt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
          fun h => by
            have := hTagMetaG (i0 + 1) hlt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
          fun h => by have := hT2 8 (by omega); rw [h, hTagMetaL (i0 + 1) hlt] at this; omega,
          fun h => by have := hT2 8 (by omega); rw [h, hTagMetaG (i0 + 1) hlt] at this; omega,
          by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr]; omega,
          by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr]; omega⟩⟩
      (hGI0_ptr.symm ▸ dynGraphAt_of_agree hGI0 (fun a ha1 ha2 =>
        hs2_eq_mem0 (hTagGI0 a ha1 ha2) (by split_ifs <;> omega) (by split_ifs <;> omega) (fun _ _ _ => by split_ifs <;> omega)))
      (by rw [hGI0_ptr]; rw [h1_4] at hs2_lo; omega)
      (fun a ha1 ha2 => by
        rw [hGI0_ptr] at ha1 ha2
        exact ⟨hNotFoot2 (htagLt (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega))
            (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega),
          fun h => by
            have := hTagGI0 a ha1 ha2; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; split_ifs at this <;> omega⟩)
      (hLenI0_ptr.symm ▸ hFmtPrec.symm ▸ hLenI0.congr (fun e he t ht => by
        have heLt := hGI0.2.2.1 e he
        have hmul : e * L + L ≤ eCap * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
        exact hs2_eq_mem0 (hTagLenI0 _ (by omega) (by omega)) (by omega) (by omega)
          (fun _ _ _ => by omega)))
      (by rw [hLenI0_ptr]; rw [h1_4] at hs2_lo; omega)
      (fun a ha1 ha2 => by
        rw [hLenI0_ptr] at ha1 ha2
        exact ⟨hNotFoot2 (htagLt (by rw [hTagLenI0 a ha1 ha2]; omega))
            (by rw [hTagLenI0 a ha1 ha2]; omega),
          fun h => by
            have := hTagLenI0 a ha1 ha2; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega⟩)
      hRepI0_2 (hScIn0 i0 le_rfl hiLt)
      (fun a ha => by
        rcases hFootI0_2 a ha with h0 | ⟨_, hhi⟩
        · exact (hCoreFootLt i0 hiLt a h0).trans_le (by rw [h1_4] at hs2_lo; omega)
        · exact hhi)
      hz2
      ⟨by dsimp only [next, chain, i0] at hChain' ⊢; rw [← hChain']; exact hNextSub1,
        fun e he => by
          have hhe : e ∈ ((alg2LoopShiftStep cfg model i).chain.G (i0 + 1)).E := by
            dsimp only [next, chain, i0] at hChain' ⊢; rwa [hChain']
          obtain ⟨q, hq, hEq⟩ := hNextFits1 e hhe
          exact ⟨q, hq, by
            dsimp only [next, chain, i0] at hChain' ⊢; rw [← hChain', hFmtPrec]; exact hEq⟩⟩
      le_rfl hRotW
      (by dsimp only [d, i0, chain, next, newBran] at hRestartSp hs2_heapLe hRotW ⊢; omega)
  have hs3_heapLe : s3.regs 4 ≤ heap + 2 * (d + 1) + (5 + fcap + 5 * d) + restartSpace := by
    dsimp only [d, i0, chain, next, newBran] at hRestartSp h4Hi3 hs2_heapLe ⊢
    omega
  have hPhi1Eq :
      (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) s1.mem) =
      (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) :=
    Finset.sum_congr rfl (fun j hj => by
      obtain ⟨_, hj2⟩ := Finset.mem_Ico.mp hj
      exact (hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) mem0 s1.mem
        (fun a ha => (hs1Mem.symm ▸ hmem0_eq (hT21 j hj2 a ha) (by omega)).symm)).2.symm)
  refine ⟨s2, s3, c0 + (c1 + c2 + 1) + 1, ordW3, yI0_2, yI0_3,
    runs_seq_iff.mpr (Or.inr ⟨s1, c0, c1 + c2 + 1, r0,
      runs_seq_iff.mpr (Or.inr ⟨s2, c1, c2, r1, r2, rfl⟩), rfl⟩),
    h1_4 ▸ hs2_lo, h4Lo3, hs3_heapLe, hz3, hOldForestsSafe2, h1_4 ▸ hFootI0_2,
    fun a ha hnf hout => (hs2_frame a (h1_4.symm ▸ ha) hnf hout).trans (congrFun hs1Mem a),
    hBr3, hRepI0_3, hFootI0_3, hH3, hLen3, hGrad3, hOrd3, hOrdLe3, h6Lo3, hHEnd3, h6Disj3,
    h7Lo3, hLenEnd3, h7Disj3, h6Le7_3, hMeta3, hs3_frame,
    h3_1, h3_20, h3_21, h3_51, h3_52, h3_56, h3_57, h3_58, h3_67, h3_68,
    ((hs3_regs 70 (by decide)).trans (hs2_regs 70 (by decide))).trans h1_70,
    ((hs3_regs 71 (by decide)).trans (hs2_regs 71 (by decide))).trans h1_71,
    ((hs3_regs 73 (by decide)).trans (hs2_regs 73 (by decide))).trans h1_73,
    ((hs3_regs 75 (by decide)).trans (hs2_regs 75 (by decide))).trans h1_75,
    ((hs3_regs 77 (by decide)).trans (hs2_regs 77 (by decide))).trans h1_77,
    ((hs3_regs 78 (by decide)).trans (hs2_regs 78 (by decide))).trans h1_78,
    ((hs3_regs 79 (by decide)).trans (hs2_regs 79 (by decide))).trans h1_79,
    ((hs3_regs 80 (by decide)).trans (hs2_regs 80 (by decide))).trans h1_80,
    ((hs3_regs 81 (by decide)).trans (hs2_regs 81 (by decide))).trans h1_81,
    ((hs3_regs 83 (by decide)).trans (hs2_regs 83 (by decide))).trans h1_83,
    ((hs3_regs 98 (by decide)).trans (hs2_regs 98 (by decide))).trans h1_98, ?_⟩
  rw [hPhi1Eq] at hc1
  have hRotMulLe :
      Psc.mul * (ordRotWords (chainLevelOrdAbs next i0) newBran + 1) *
        SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ ≤
      Psc.mul * (2 * (next.G (i0 + 1)).n + 2 * (next.G (i0 + 1)).m + 2) *
        SparseCore.bundleLogFactor (chain.lvlM i0) chain.N₀ :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  dsimp only [d, i0, chain, next, newBran] at hc1 hc2 hRotMulLe ⊢
  omega

end MinCostFlow.MinRatio
