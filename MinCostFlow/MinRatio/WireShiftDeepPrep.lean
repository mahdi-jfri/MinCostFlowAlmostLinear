module

public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.MinRatio.WireShiftDeepRestart
import WordRAM.Tactic

/-!
# Deep shift operational bounds and Phases 0–2 (`WireShiftDeepPrep`)

Provides:
1. `DeepShiftOpsHyp`: bundles the implementation-level readout placement, allocation, and cost
   domination bounds for sparse-core ops `1, 2, 3, 5`, `init`, and terminal `lastInit`.
2. Helper lemmas (`sum_Ico_le_sum_range`, `sum_Fin_eq_range_plus_Ico`,
   `ordRebuildSuffixProgramKStore_preserves_ge70`, `shiftDeep_chainLen_le`).
3. `shiftDeep_phases_0_to_2_runs`: composes Phase 0 (`shiftDeepInitRegs`), Phase 1
   (`shiftDeepCollectOld`), and Phase 2 (`shiftDeepRestartAndReadout`) for a non-terminal shift
   `i < d`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program SparseCore.Program Bundle

/-- Implementation-level readout placement, space, and cost domination hypotheses for the
sparse-core and last-level machines during a non-terminal deep shift `i < d`. -/
structure DeepShiftOpsHyp
    {w L P capExp lastMul intCapMax forestEdgeCap deepSpace deepFixed toolMul : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (dgCap ecCap restartSpace : ℕ) (levelSpace levelCost : ℕ → ℕ) (lastSpace : ℕ) : Prop where
  /-- Op `2` (`readLSF`) forest & stretch pointer placement and graph-size cap. -/
  op2Placement : ∀ (G : MGraph) (handle : ℕ) (x : Rcore.τ) (m : ℕ → ℕ)
    (h ret vcF ecF Lw : ℕ) (forest : LSF),
    LSFAt m h vcF ecF 4 Lw fmt.precision G.E forest →
    h ≤ ret → ret ≤ h + 5 →
    m (h + 1) + dynGraphSize vcF ecF ≤ ret ∧
    dynGraphSize vcF ecF ≤ dgCap ∧
    (∀ a, m (h + 1) ≤ a → a < m (h + 1) + dynGraphSize vcF ecF → Rcore.foot handle x a ∨ h ≤ a) ∧
    m (h + 3) + 2 ≤ ret ∧
    (∀ e ∈ G.E, m (m (h + 3)) + e * Lw + Lw ≤ ret ∧ m (m (h + 3) + 1) + e * Lw + Lw ≤ ret)
  /-- Op `3` (`readGraph`) pointer placement and size caps. -/
  op3Placement : ∀ (H : MGraph) (m1 : ℕ → ℕ) (h0 h1 rawGraph vcH ecH : ℕ),
    DynGraphAt m1 rawGraph vcH ecH H → h0 ≤ h1 → h1 ≤ h0 + 1 →
    rawGraph + dynGraphSize vcH ecH ≤ h1 ∧ dynGraphSize vcH ecH ≤ dgCap ∧ ecH ≤ ecCap
  /-- Op `5` (`readOrd`) output placement inside `[heapFloor, h)` with in-range words. -/
  op5Placement : ∀ (ord : ℕ → List End) (m : ℕ → ℕ) (oPtr oWords heapFloor h : ℕ),
    OrdListAt m oPtr ord oWords → ZeroFrom m h → heapFloor ≤ h →
    heapFloor ≤ oPtr ∧ oPtr + oWords ≤ h ∧ (∀ t < oWords, m (oPtr + t) < 2 ^ w)
  /-- Restart + readout allocation envelope at level `i`. -/
  restartSpaceDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (coreH h : ℕ),
    i.val < cfg.P.d →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (model.chain.lvlM i.val + model.chain.N₀ + 2) + 1)
    allocation i.val 1 [coreH, newBran, h] + 7 + dgCap + ecCap * L +
      (next.G (i.val + 1)).m * wireCoreLenEdgeSpace (max L LwMax) +
      ordRotWords (chainLevelOrdAbs next i.val) newBran ≤ restartSpace
  /-- Suffix level rebuild allocation envelope for `j ∈ [i + 1, d)`. -/
  levelSpaceDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j gB lB oB h : ℕ),
    i.val < cfg.P.d → i.val + 1 ≤ j → j < cfg.P.d →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)
    allocation j 6 [gB, lB, lB, oB, cfg.P.k, next.lvlM j, next.N₀, h] + 7 + dgCap + ecCap * L +
      (next.G (j + 1)).m * wireCoreLenEdgeSpace (max L LwMax) +
      ordRotWords (chainLevelOrdAbs next j) 0 ≤ levelSpace j
  /-- Terminal level rebuild allocation envelope. -/
  lastSpaceDom : ∀ (gB lB h : ℕ),
    lastAlloc 1 [gB, lB, L, fmt.precision, h] ≤ lastSpace
  /-- Total space budget domination. -/
  spaceTotal :
    2 * (cfg.P.d + 1) + (5 + dgCap + 5 * cfg.P.d) + restartSpace +
      (Finset.range cfg.P.d).sum levelSpace + lastSpace + 5 * cfg.P.d +
      3 * intCapMax + forestEdgeCap * (2 + wireTreeSyncEditSpace L) ≤ deepSpace
  /-- Per-level rebuild cost domination for `ordRebuildSuffixProgramKStore_runs`. -/
  levelCostDom : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)) (j vcH ecH oWords : ℕ),
    i.val < cfg.P.d → i.val + 1 ≤ j → j < cfg.P.d →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (next.lvlM j + next.N₀ + 2) + 1)
    dynGraphSize vcH ecH ≤ dgCap →
    (j = i.val + 1 → oWords ≤ ordRotWords (chainLevelOrdAbs next i.val) newBran) →
    (i.val + 1 < j → oWords ≤ ordRotWords (chainLevelOrdAbs next (j - 1)) 0) →
    Psc.mul * (cfg.T.cost (next.scState j) + (next.G j).n + (next.G j).m + oWords + 1) +
      Psc.mul * (ordRotWords (chainLevelOrdAbs next j) 0 + 1) *
        SparseCore.bundleLogFactor (next.lvlM j) next.N₀ +
      2 * Psc.readout + 17 * dynGraphSize vcH ecH +
      (next.G (j + 1)).m * (wireCoreLenEdgeCost (max L LwMax) + 30) + 265 ≤ levelCost j
  /-- Total non-tree-update cost domination by `deepFixed + toolMul * Δ totalRuntime`. -/
  costTotal : ∀ (model : Alg2State cfg) (i : Fin (cfg.P.d + 1)),
    i.val < cfg.P.d →
    let next := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P model.chain i.val).1
    let newBran := (model.chain.bran i.val + 1) % cfg.P.k
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (model.chain.lvlM i.val + model.chain.N₀ + 2) + 1)
    17 * dgCap +
      Psc.mul * (cfg.T.cost (next.scState i.val) - cfg.T.cost (model.chain.scState i.val) + 1) +
      Psc.mul * (ordRotWords (chainLevelOrdAbs next i.val) newBran + 1) *
        SparseCore.bundleLogFactor (model.chain.lvlM i.val) model.chain.N₀ +
      2 * Psc.readout + 17 * dgCap +
      (next.G (i.val + 1)).m * (wireCoreLenEdgeCost (max L LwMax) + 30) +
      (Finset.Ico (i.val + 1) cfg.P.d).sum (fun j => levelCost j + 9) +
      lastMul * (cfg.L.cost (next.G cfg.P.d) + 1) +
      2 * cfg.P.d * (Psc.readout + 48) + 210 * (cfg.P.d + 1) + 85 * forestEdgeCap + 1100 ≤
      deepFixed + toolMul * (next.totalRuntime - model.chain.totalRuntime)

theorem sum_Ico_le_sum_range {a b d : ℕ} (hb : b ≤ d) (f : ℕ → ℕ) :
    (Finset.Ico a b).sum f ≤ (Finset.range d).sum f :=
  Finset.sum_le_sum_of_subset (fun x hx => by
    simp only [Finset.mem_Ico] at hx; exact Finset.mem_range.mpr (by omega))

theorem sum_Fin_eq_range_plus_Ico {d i : ℕ} (hi : i < d) (f : ℕ → ℕ) :
    (∑ j : Fin d, f j.val) = (Finset.range i).sum f + (Finset.Ico i d).sum f := by
  rw [Fin.sum_univ_eq_sum_range f d, ← Finset.sum_union]
  · congr 1; ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega

theorem ordRebuildSuffixProgramKStore_preserves_ge70
    {w init readGraph readLSF coreLenProc readOrd lastInit : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State} {c : ℕ}
    (hr : Runs w p ω (ordRebuildSuffixProgramKStore init readGraph readLSF coreLenProc readOrd lastInit)
      st .normal out c)
    (r : ℕ) (h70 : 70 ≤ r) : out.regs r = st.regs r :=
  runs_preserves_above
    (s := ordRebuildSuffixProgramKStore init readGraph readLSF coreLenProc readOrd lastInit)
    h70 rfl hr

theorem shiftDeep_chainLen_le {T : SparseCoreRestartTool} {LT : LastLevelTool}
    {CP : ChainParams} (chain : ChainState T CP) {i0 : ℕ} (hiLt : i0 < CP.d) :
    let next := (Chain.Ordered.algorithm1_shift T LT CP chain i0).1
    ∀ j ≤ i0, next.toTreeChain.chainLen next.ℓ j = chain.toTreeChain.chainLen chain.ℓ j := by
  dsimp only
  obtain ⟨_, hExPre, _, _, _, _, _, _, _, _, _, _, _, hExEll, _, _, _⟩ :=
    ordAlgorithm1_shift_exact T LT CP chain hiLt
  intro j
  induction j with
  | zero => intro _; rw [hExEll]; rfl
  | succ k ih =>
    intro hk
    obtain ⟨hsc, hbr, _⟩ := hExPre k (by omega)
    simp only [TreeChain.chainLen]
    rw [ih (by omega)]
    simp only [ChainState.toTreeChain, TreeChain.activeLSF, show k < CP.d by omega, ↓reduceIte,
      hsc, hbr]

set_option maxHeartbeats 1600000 in
/-- Execute Phases 0–2 of `shiftDeepChainBody` (`shiftDeepInitRegs ;; shiftDeepCollectOld ;;
shiftDeepRestartAndReadout`) for a non-terminal shift `i < d`. -/
theorem shiftDeep_phases_0_to_2_runs
    {w L P m V psi k epsExp drainUnit capExp wordExp stretchPrec lastMul
      intCapMax forestEdgeCap deepSpace deepFixed toolMul dgCap ecCap restartSpace lastSpace
      initCore coreLenProc edgeProc signExt mul intDiv copy root heap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Psc : SparseCoreOrdParams}
    {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {opCore : ℕ → ℕ}
    {ω : ℕ → Bool} {mem0 mem : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {i : Fin (cfg.P.d + 1)}
    (levelSpace levelCost : ℕ → ℕ)
    (hCoreLocal : Rcore.Local)
    (hFmtBits : fmt.limbBits = 4) (hFmtPrec : fmt.precision = P) (hw17 : 17 < 2 ^ w)
    (hkPos : 0 < cfg.P.k) (hkW : cfg.P.k < 2 ^ w) (hdW : cfg.P.d < 2 ^ w)
    (hCoreImpl : ∀ j < cfg.P.d, ∀ (G : MGraph) (M vc ec : ℕ),
      Rcore.Implements w p initCore opCore
        (sparseCoreOrdMachineContractK fmt L cfg.T G cfg.P.k M model.chain.N₀ vc ec capExp Psc (allocation j)))
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hCopy : MeetsContract w p copy (copyWordsContract w))
    (hOps : DeepShiftOpsHyp (w := w) (L := L) (P := P) (capExp := capExp) (lastMul := lastMul)
      (intCapMax := intCapMax) (forestEdgeCap := forestEdgeCap) (deepSpace := deepSpace)
      (deepFixed := deepFixed) (toolMul := toolMul) (fmt := fmt) (cfg := cfg) (Psc := Psc)
      (allocation := allocation) (lastAlloc := lastAlloc) Rcore dgCap ecCap restartSpace
      levelSpace levelCost lastSpace)
    (hiLt : i.val < cfg.P.d)
    (hRep0 : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hMeta0 : SolverLevelMetaAt P V model tok mem0)
    (hMemEq : ∀ a, tok.tag a ≠ 5 → mem a = mem0 a)
    (hBranLt : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k)
    (hModelInv : ShiftDeepModelInv w L P wordExp stretchPrec model i)
    (hFootLt : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
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
    let LwMax := L + (capExp + sparseCoreReadout2LimbConst) *
      (Nat.log 2 (model.chain.lvlM i0 + model.chain.N₀ + 2) + 1)
    let forestSafe : ℕ → Prop := fun a =>
      (a < heap → tok.tag a ≠ 4 ∧ tok.tag a ≠ 22 + d) ∧ (a < heap ∨ heap1 ≤ a)
    ∃ (s2 s3 : State) (c012 vcH3 ecH3 ordW3 : ℕ) (yI0_2 yI0_3 : Rcore.τ),
      Runs w p ω
        (shiftDeepInitRegs ;; shiftDeepCollectOld (opCore 2) ;;
          shiftDeepRestartAndReadout (opCore 1) (opCore 3) (opCore 2) coreLenProc (opCore 5))
        (startState [root, i0, heap] mem pos) .normal s3 c012 ∧
      heap1 ≤ s2.regs 4 ∧ s2.regs 4 ≤ s3.regs 4 ∧
      s3.regs 4 ≤ heap + 2 * (d + 1) + (5 + dgCap + 5 * d) + restartSpace ∧
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
      DynGraphAt s3.mem (s3.regs 6) vcH3 ecH3 (next.G (i0 + 1)) ∧
      EdgeValuesAt s3.mem (s3.regs 7) 4 L fmt.precision (next.G (i0 + 1)).E
        (next.toTreeChain.chainLen model.chain.ℓ (i0 + 1)) ∧
      s3.regs 8 = s3.regs 7 ∧
      (i0 + 1 < d →
        OrdListAt s3.mem (s3.regs 9) (next.levelOrd (i0 + 1)) ordW3 ∧
        (∀ t < ordW3, s3.mem (s3.regs 9 + t) < 2 ^ w) ∧
        s3.regs 9 + ordW3 ≤ s3.regs 4) ∧
      ordW3 ≤ ordRotWords (chainLevelOrdAbs next i0) newBran ∧
      s2.regs 4 ≤ s3.regs 6 ∧ s3.regs 6 + dynGraphSize vcH3 ecH3 ≤ s3.regs 4 ∧
      (∀ a, s3.regs 6 ≤ a → a < s3.regs 6 + dynGraphSize vcH3 ecH3 →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      s2.regs 4 ≤ s3.regs 7 ∧ s3.regs 7 + ecH3 * L ≤ s3.regs 4 ∧
      (∀ a, s3.regs 7 ≤ a → a < s3.regs 7 + ecH3 * L →
        ¬ Rcore.foot (tok.coreHandle i0) yI0_3 a) ∧
      (i0 + 1 < d → s3.mem (levelMeta + (i0 + 1)) = s3.regs 7 ∧
        s3.mem (levelMeta + d + (i0 + 1)) = s3.regs 6) ∧
      (∀ a < s2.regs 4, ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a → a ≠ branchBase + i0 →
        (i0 + 1 < d → a ≠ levelMeta + (i0 + 1) ∧ a ≠ levelMeta + d + (i0 + 1)) →
        s3.mem a = s2.mem a) ∧
      -- Registers set up for Phase 3 and preserved high registers `70..83`
      s3.regs 1 = cfg.P.k ∧ s3.regs 20 = i0 + 1 ∧ s3.regs 21 = d ∧
      s3.regs 51 = handleBase + (i0 + 1) ∧ s3.regs 52 = branchBase + (i0 + 1) ∧
      s3.regs 56 = model.chain.N₀ ∧ s3.regs 57 = lvlMTable ∧ s3.regs 58 = levelMeta ∧
      s3.regs 67 = L ∧ s3.regs 68 = fmt.precision ∧
      s3.regs 70 = root ∧ s3.regs 71 = i0 ∧ s3.regs 73 = tok.handle ∧
      s3.regs 75 = d ∧ s3.regs 77 = handleBase ∧ s3.regs 78 = branchBase ∧
      s3.regs 79 = cnt ∧ s3.regs 80 = heap ∧ s3.regs 81 = heap + cnt ∧
      s3.regs 83 = levelMeta ∧
      -- Cost + `Rcore.phi` bound
      c012 + Rcore.phi (tok.coreHandle i0) yI0_3 s3.mem ≤
        17 * dgCap + (d - i0) * (Psc.readout + 48) +
        Psc.mul * (cfg.T.cost (next.scState i0) - cfg.T.cost (model.chain.scState i0) + 1) +
        Psc.mul * (ordRotWords (chainLevelOrdAbs next i0) newBran + 1) *
          SparseCore.bundleLogFactor (model.chain.lvlM i0) model.chain.N₀ +
        2 * Psc.readout + 17 * dgCap +
        (next.G (i0 + 1)).m * (wireCoreLenEdgeCost (max L LwMax) + 30) + 565 +
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
  obtain ⟨hRootDir0, hDetHdr0, hNumHdr0, hInitPar0, _, _, _, ⟨hG0Cap, _, _, _⟩, _, _, _, _, _, _,
    hCores0, hTermPtr0, hTermBran0, hTermRep0, _, hTags0⟩ := hRep0
  obtain ⟨hOwnOfTag, hT1, hT2, _, hT4, _, _, _, _, _, _, _, _, _, _, _, _, _, hT19, _, hT21⟩ := hTags0
  obtain ⟨⟨hN0Val, hTagN0, _, _⟩, hCoreOwn0, _, hTagM0, hTagMeta0, hMetaLvls0⟩ := hMeta0
  have hTagN0' : tok.tag (lvlMTable - 1) = 21 + d := by
    simpa [lvlMTable, solverLvlMAddr, solverN0Addr] using hTagN0
  obtain ⟨⟨hLastBranLt, _⟩, hScIn0, _, hNextSub1, hNextFits1, _, _, _, _, _, _, _, hLsfSub, hLastSubOld, _, _⟩ := hModelInv
  have htagLt {a : ℕ} (h : tok.tag a ≠ 0) : a < heap := hFootLt a (Or.inl (hOwnOfTag a h))
  have hmem0_eq {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 5) : mem a = mem0 a :=
    hMemEq a (ht ▸ hv)
  have hTagHandle (j : ℕ) (hj : j ≤ d) : tok.tag (handleBase + j) = 4 := hT4 j (by omega)
  have hTagBranch (j : ℕ) (hj : j ≤ d) : tok.tag (branchBase + j) = 4 := by
    have := hT4 ((d + 1) + j) (by omega)
    rwa [show tok.handle + 18 + ((d + 1) + j) = branchBase + j by dsimp [branchBase, handleBase]; omega] at this
  have hTagMetaG (j : ℕ) (hj : j < d) : tok.tag (levelMeta + d + j) = 22 + d := by
    have := hTagMeta0 (d + j) (by omega)
    rwa [show levelMeta + (d + j) = levelMeta + d + j by omega] at this
  have hTagMetaL (j : ℕ) (hj : j < d) : tok.tag (levelMeta + j) = 22 + d := hTagMeta0 j (by omega)
  have hRootW : root + 16 ≤ heap := by have := htagLt (by rw [hT1 15 (by omega)]; decide); omega
  have hHandleW : tok.handle + 18 ≤ heap := by have := htagLt (by rw [hT2 17 (by omega)]; decide); omega
  have hLevelEnd : branchBase + d < heap := htagLt (by rw [hTagBranch d le_rfl]; decide)
  have hMetaEnd : levelMeta + 2 * d ≤ heap := by
    have := htagLt (by rw [hTagMeta0 (2 * d - 1) (by omega)]; omega); dsimp only [levelMeta, d] at *; omega
  have hTermTokLe : tok.termTok ≤ heap := by
    by_cases hlt : tok.termHandle < tok.termTok
    · have := htagLt (by rw [hT19 (tok.termTok - 1) ⟨by omega, by omega⟩]; decide); omega
    · have := hTermRep0.1; omega
  have hSpaceTot := hOps.spaceTotal
  -- Phase 0: `shiftDeepInitRegs`
  obtain ⟨s1, c0, r0, hc0, hs1Mem, h1_70, h1_71, _, h1_73, _, h1_75, h1_76, h1_77, h1_78,
      h1_79, h1_80, h1_81, h1_82, h1_83, h1_4⟩ :=
    shiftDeepInitRegs_runs (w := w) (root := root) (i := i0) (heap0 := heap) (handle := tok.handle)
      (table := tok.table) (d := d) (k := cfg.P.k) (pos := pos) (p := p) (ω := ω) (mem := mem)
      ((hmem0_eq (hT1 0 (by omega)) (by decide)).trans (by simpa using hRootDir0 0 (by simp)))
      ((hmem0_eq (hT1 1 (by omega)) (by decide)).trans (by simpa using hRootDir0 1 (by simp)))
      ((hmem0_eq (hT2 11 (by omega)) (by decide)).trans
        (by have := hInitPar0 2 (by simp); simpa [Nat.add_assoc] using this))
      ((hmem0_eq (hT2 12 (by omega)) (by decide)).trans
        (by have := hInitPar0 3 (by simp); simpa [Nat.add_assoc] using this))
      hiLt (by omega) (by omega) (by dsimp [branchBase, handleBase] at hLevelEnd; omega)
      (by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr] at hMetaEnd ⊢; omega)
      (by dsimp [cnt] at *; omega) hw17
  -- Phase 1: `shiftDeepCollectOld`
  have hTermH1 : s1.mem (handleBase + d) = tok.termHandle := by
    rw [hs1Mem, hmem0_eq (hTagHandle d le_rfl) (by decide)]; exact hTermPtr0
  have hTermB1 : s1.mem (branchBase + d) = chain.lastBran := by
    rw [hs1Mem, hmem0_eq (hTagBranch d le_rfl) (by decide)]; exact hTermBran0
  obtain ⟨hOldTermBW, hOldTermLSF⟩ := hTermRep0.2.2.2 chain.lastBran hLastBranLt
  have hMem1_term (a : ℕ) (ha1 : tok.termHandle ≤ a) (ha2 : a < tok.termTok) : s1.mem a = mem0 a := by
    rw [hs1Mem, hmem0_eq (hT19 a ⟨ha1, ha2⟩) (by decide)]
  set oldTermLsfHdr := mem0 (tok.termHandle + 1 + chain.lastBran)
  set oldTermFPtr := mem0 (oldTermLsfHdr + 1)
  have hCoreFootLt (j : ℕ) (hj : j < d) (a : ℕ) (ha : Rcore.foot (tok.coreHandle j) (tok.coreTok j) a) :
      a < heap := htagLt (by rw [hT21 j hj a ha]; omega)
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
      (∃ vc ec,
        DynGraphAt s1.mem (s1.mem (levelMeta + d + j)) vc ec (chain.G j) ∧
        s1.mem (levelMeta + d + j) + dynGraphSize vc ec ≤ s1.regs 4 ∧
        (∀ a, s1.mem (levelMeta + d + j) ≤ a →
          a < s1.mem (levelMeta + d + j) + dynGraphSize vc ec →
          (∀ r, i0 ≤ r → r < d → ¬ Rcore.foot (tok.coreHandle r) (tok.coreTok r) a) ∧
          (a < heap ∨ heap + cnt ≤ a))) := by
    intro j hj1 hj2
    have h4a := hTagHandle j (le_of_lt hj2)
    have h4b := hTagBranch j (le_of_lt hj2)
    have h22 := hTagMetaG j hj2
    have hloc := hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) mem0 s1.mem
      (fun a ha => (hs1Mem.symm ▸ hmem0_eq (hT21 j hj2 a ha) (by omega)).symm)
    obtain ⟨vcJ, ecJ, hDGj, _, _, _, hTagGj⟩ := hMetaLvls0 j hj2
    have hPtrEq : s1.mem (levelMeta + d + j) = mem0 (levelMeta + d + j) :=
      hs1Mem.symm ▸ hmem0_eq h22 (by omega)
    have hDGEndJ : mem0 (levelMeta + d + j) + dynGraphSize vcJ ecJ ≤ heap := by
      have hpos : 0 < dynGraphSize vcJ ecJ := by unfold dynGraphSize; omega
      have h1 : mem0 (levelMeta + d + j) ≤ mem0 (levelMeta + d + j) + dynGraphSize vcJ ecJ - 1 := by omega
      have h2 : mem0 (levelMeta + d + j) + dynGraphSize vcJ ecJ - 1 <
          mem0 (levelMeta + d + j) + dynGraphSize vcJ ecJ := by omega
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
      ⟨vcJ, ecJ, hPtrEq.symm ▸ dynGraphAt_of_agree hDGj (fun a ha1 ha2 =>
          hs1Mem.symm ▸ hmem0_eq (hTagGj a ha1 ha2) (by split_ifs <;> omega)),
        by rw [hPtrEq, h1_4]; omega,
        fun a ha1 ha2 => by
          rw [hPtrEq] at ha1 ha2
          exact ⟨fun r _ hr2 hf => by have := hT21 r hr2 a hf; rw [hTagGj a ha1 ha2] at this; split_ifs at this <;> omega,
            Or.inl (htagLt (by rw [hTagGj a ha1 ha2]; split_ifs <;> omega))⟩⟩⟩
  have hOldTermDG1 : DynGraphAt s1.mem oldTermFPtr tok.vcLast tok.ecLast
      (chain.lastLSFs chain.lastBran).F.F :=
    dynGraphAt_of_agree hOldTermLSF.2.1 (fun a ha1 ha2 =>
      hMem1_term a (by have := hOldTermBW.2.2.2.2.1; have := hTermRep0.1; omega)
        (by have := hOldTermBW.2.2.2.2.2.1; omega))
  obtain ⟨s2, c1, vcFi0, ecFi0, yI0_2, r1, hs2_lo, hs2_hi, hz2, hCopyDG2, _, _,
      _, hOldForestsSafe2, hRepI0_2, hFootI0_2, hs2_frame, hs2_regs, hc1⟩ :=
    shiftDeepCollectOld_runs (w := w) (L := L) (capExp := capExp) (init := initCore) (i0 := i0)
      (handleBase := handleBase) (branchBase := branchBase) (levelMeta := levelMeta)
      (oldPtrs := heap) (intCap := tok.intCap) (termHandle := tok.termHandle)
      (vcLast := tok.vcLast) (ecLast := tok.ecLast) (lsfHdr := oldTermLsfHdr)
      (forestPtr := oldTermFPtr) (p := p) (ω := ω) (st := s1) chain tok.coreHandle tok.coreTok
      forestSafe (fun a ha => ⟨fun hlt => by rw [h1_4] at ha; omega, Or.inr (by rw [h1_4] at ha; exact ha)⟩)
      hCoreLocal hiLt h1_71 h1_75 h1_77 h1_78 h1_80 h1_83 hkW hdW (by omega)
      (by rw [h1_4]; omega) (by rw [h1_4]; dsimp [branchBase] at hLevelEnd; omega)
      (by rw [h1_4]; omega) (by rw [h1_4]; omega)
      (fun a ha => hs1Mem.symm ▸ hzHeap a (by rw [h1_4] at ha; omega))
      (fun j _ hj2 vc ec => hCoreImpl j hj2 (chain.G j) (chain.lvlM j) vc ec)
      hCores1 (fun j₁ j₂ _ h2 _ h4 => hCoreDisj0 j₁ j₂ h2 h4)
      hTermH1 hTermB1
      (hMem1_term _ (by omega) (by have := hTermRep0.1; dsimp only [chain] at *; omega))
      (hMem1_term _ (by have := hOldTermBW.1; have := hTermRep0.1; dsimp only [chain] at *; omega) (by have := hOldTermBW.2.1; omega))
      hOldTermDG1
      (by have := hOldTermBW.2.2.2.2.2.1; rw [h1_4]; omega)
      (fun e he => hG0Cap e (hLastSubOld he))
      ⟨Or.inl (htagLt (by rw [hTagHandle d le_rfl]; decide)),
        Or.inl (htagLt (by rw [hTagBranch d le_rfl]; decide)),
        Or.inl (by have := hTermRep0.1; dsimp only [chain] at *; omega),
        Or.inl (by have := hOldTermBW.2.1; omega),
        by rw [h1_4]; have := hTermRep0.1; dsimp only [chain] at *; omega,
        by rw [h1_4]; have := hOldTermBW.2.1; omega,
        fun r _ hr2 => ⟨fun hf => by have := hT21 r hr2 _ hf; rw [hTagHandle d le_rfl] at this; omega,
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
          have h19 : tok.tag a = 19 := hT19 a ⟨by have := hOldTermBW.2.2.2.2.1; have := hTermRep0.1; omega,
            by have := hOldTermBW.2.2.2.2.2.1; omega⟩
          exact ⟨fun r _ hr2 hf => by have := hT21 r hr2 a hf; rw [h19] at this; omega,
            Or.inl (htagLt (by rw [h19]; decide)),
            ⟨fun _ => ⟨by rw [h19]; decide, by rw [h19]; omega⟩, Or.inl (htagLt (by rw [h19]; decide))⟩⟩⟩
      ⟨by rw [h1_4]; omega, fun m ret vcF ecF Lw hLSF hLo hHi => by
        obtain ⟨hEnd, hDg, _, _, _⟩ := hOps.op2Placement (chain.G i0) (tok.coreHandle i0)
          (tok.coreTok i0) m (s1.regs 4) ret vcF ecF Lw _ (hFmtBits ▸ hLSF) hLo hHi
        exact ⟨hEnd, by rw [h1_4] at hHi; omega,
          fun e he => hG0Cap e ((hLsfSub i0 le_rfl hiLt).1 he)⟩⟩
      (fun j hj1 hj2 m h ret vcF ecF Lw hLSF hGe hLo hHi => by
        obtain ⟨hEnd, _, hIn, _, _⟩ := hOps.op2Placement (chain.G j) (tok.coreHandle j)
          (tok.coreTok j) m h ret vcF ecF Lw _ (hFmtBits ▸ hLSF) hLo hHi
        refine ⟨hEnd, fun r hr1 hr2 a ha1 ha2 hf => ?_, fun a ha1 ha2 => ?_,
          fun e he => hG0Cap e ((hLsfSub j (by omega) hj2).1 he)⟩
        · rcases hIn a ha1 ha2 with hfj | hgeH
          · exact hCoreDisj0 j r hj2 hr2 (by omega) a hfj hf
          · have := hCoreFootLt r hr2 a hf; rw [h1_4] at hGe; omega
        · rcases hIn a ha1 ha2 with hfj | hgeH
          · have hltH := hCoreFootLt j hj2 a hfj
            have ht := hT21 j hj2 a hfj
            exact ⟨Or.inl hltH, ⟨fun _ => ⟨by rw [ht]; omega, by rw [ht]; omega⟩, Or.inl hltH⟩,
              fun _ hf0 => hCoreDisj0 i0 j hiLt hj2 (by omega) a hf0 hfj,
              fun hge => by rw [h1_4] at hge; omega⟩
          · rw [h1_4] at hGe
            exact ⟨Or.inr (by omega),
              ⟨fun hlt => by omega, Or.inr (by omega)⟩,
              fun hlt => by omega, fun _ => hgeH⟩)
  have hDgFi0Le : dynGraphSize vcFi0 ecFi0 ≤ dgCap :=
    (hOps.op3Placement _ s2.mem (s2.regs 4) (s2.regs 4) (s2.mem heap) vcFi0 ecFi0 hCopyDG2 le_rfl (by omega)).2.1
  have hs2_heapLe : s2.regs 4 ≤ heap + 2 * (d + 1) + (5 + dgCap + 5 * d) := by
    rw [h1_4] at hs2_hi; omega
  -- Phase 2: `shiftDeepRestartAndReadout`
  have hs2_eq_mem0 {a v : ℕ} (ht : tok.tag a = v) (hv0 : v ≠ 0) (hv5 : v ≠ 5)
      (hvC : ∀ j, i0 ≤ j → j < d → v ≠ 21 + j) : s2.mem a = mem0 a := by
    have hlt := htagLt (ht ▸ hv0)
    rw [hs2_frame a (by rw [h1_4]; omega)
      (fun j hj1 hj2 hf => hvC j hj1 hj2 (ht.symm.trans (hT21 j hj2 a hf)))
      (Or.inl hlt), hs1Mem, hmem0_eq ht hv5]
  obtain ⟨vcI0, ecI0, hGI0, hLenI0, hLenOwnI0, hTagLenI0, hTagGI0⟩ := hMetaLvls0 i0 hiLt
  have hGI0_ptr : s2.mem (levelMeta + d + i0) = mem0 (levelMeta + d + i0) :=
    hs2_eq_mem0 (hTagMetaG i0 hiLt) (by omega) (by omega) (fun _ _ _ => by omega)
  have hLenI0_ptr : s2.mem (levelMeta + i0) = mem0 (levelMeta + i0) :=
    hs2_eq_mem0 (hTagMetaL i0 hiLt) (by omega) (by omega) (fun _ _ _ => by omega)
  have hGI0_end : mem0 (levelMeta + d + i0) + dynGraphSize vcI0 ecI0 ≤ heap := by
    have hpos : 0 < dynGraphSize vcI0 ecI0 := by unfold dynGraphSize; omega
    have h1 : mem0 (levelMeta + d + i0) ≤ mem0 (levelMeta + d + i0) + dynGraphSize vcI0 ecI0 - 1 := by omega
    have h2 : mem0 (levelMeta + d + i0) + dynGraphSize vcI0 ecI0 - 1 <
        mem0 (levelMeta + d + i0) + dynGraphSize vcI0 ecI0 := by omega
    have := htagLt (by rw [hTagGI0 _ h1 h2]; split_ifs <;> omega); omega
  have hLenI0_end : mem0 (levelMeta + i0) + ecI0 * L ≤ heap := by
    by_cases h0 : ecI0 * L = 0
    · rw [h0, add_zero]; exact le_of_lt (hFootLt _ (Or.inl hLenOwnI0))
    · have h1 : mem0 (levelMeta + i0) ≤ mem0 (levelMeta + i0) + ecI0 * L - 1 := by omega
      have h2 : mem0 (levelMeta + i0) + ecI0 * L - 1 < mem0 (levelMeta + i0) + ecI0 * L := by omega
      have := htagLt (by rw [hTagLenI0 _ h1 h2]; omega); omega
  have hNotFoot2 {a : ℕ} (ha : a < heap) (hne : tok.tag a ≠ 21 + i0) :
      ¬ Rcore.foot (tok.coreHandle i0) yI0_2 a := fun hf => by
    rcases hFootI0_2 a hf with h0 | ⟨hlo, _⟩
    · exact hne (hT21 i0 hiLt a h0)
    · rw [h1_4] at hlo; omega
  have hRestartSp := hOps.restartSpaceDom model i (tok.coreHandle i0) (s2.regs 4) hiLt
  dsimp only at hRestartSp
  obtain ⟨s3, vcH3, ecH3, ordW3, Lw3, c2, yI0_3, r2, hLw3, hBr3, hRepI0_3, hH3, hLen3, hGrad3,
      hOrd3, hOrdLe3, h6Lo3, hHEnd3, h6Disj3, h7Lo3, hLenEnd3, h7Disj3, hMeta3, h4Lo3, h4Hi3, hz3,
      hFootI0_3, hs3_frame, h3_1, h3_20, h3_21, h3_51, h3_52, h3_56, h3_57, h3_58, h3_67, h3_68,
      hs3_regs, hc2⟩ :=
    shiftDeepRestartAndReadout_runs (w := w) (L := L) (capExp := capExp) (init := initCore)
      (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt) (mul := mul)
      (intDiv := intDiv) (copy := copy) (i0 := i0) (handle := tok.handle) (handleBase := handleBase)
      (branchBase := branchBase) (lvlMTable := lvlMTable) (levelMeta := levelMeta) (N0 := model.chain.N₀)
      (vcI := vcI0) (ecI := ecI0) (coreH := tok.coreHandle i0) (LT := cfg.L) (p := p) (ω := ω)
      (st := s2) chain yI0_2 hCoreLocal hFmtBits
      (hCoreImpl i0 hiLt (chain.G i0) (chain.lvlM i0) vcI0 ecI0)
      hCoreLenProc hEdgeProc hSign hMul hDiv hCopy hiLt hkPos hkW hdW (by omega)
      ((hs2_regs 71 (by decide)).trans h1_71) ((hs2_regs 73 (by decide)).trans h1_73)
      ((hs2_regs 75 (by decide)).trans h1_75) ((hs2_regs 76 (by decide)).trans h1_76)
      ((hs2_regs 77 (by decide)).trans h1_77) ((hs2_regs 78 (by decide)).trans h1_78)
      ((hs2_regs 82 (by decide)).trans h1_82) ((hs2_regs 83 (by decide)).trans h1_83)
      ((hs2_eq_mem0 (hTagHandle i0 (le_of_lt hiLt)) (by decide) (by decide) (fun _ _ _ => by omega)).trans
        (hCores0 i0 hiLt).1)
      (lt_trans (hFootLt (tok.coreHandle i0) (Or.inl (hCoreOwn0 i0 hiLt))) (by omega))
      ((hs2_eq_mem0 (hTagBranch i0 (le_of_lt hiLt)) (by decide) (by decide) (fun _ _ _ => by omega)).trans
        (hCores0 i0 hiLt).2.1)
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
      ⟨hNotFoot2 (htagLt (by rw [hTagBranch i0 (le_of_lt hiLt)]; decide)) (by rw [hTagBranch i0 (le_of_lt hiLt)]; omega),
        hNotFoot2 (htagLt (by rw [hT2 5 (by omega)]; decide)) (by rw [hT2 5 (by omega)]; omega),
        hNotFoot2 (htagLt (by rw [hT2 8 (by omega)]; decide)) (by rw [hT2 8 (by omega)]; omega),
        hNotFoot2 (htagLt (by rw [hTagN0']; omega)) (by rw [hTagN0']; omega),
        hNotFoot2 (htagLt (by rw [hTagMetaL i0 hiLt]; omega)) (by rw [hTagMetaL i0 hiLt]; omega),
        hNotFoot2 (htagLt (by rw [hTagMetaG i0 hiLt]; omega)) (by rw [hTagMetaG i0 hiLt]; omega),
        fun hlt => ⟨hNotFoot2 (htagLt (by rw [hTagMetaL (i0 + 1) hlt]; omega)) (by rw [hTagMetaL (i0 + 1) hlt]; omega),
          hNotFoot2 (htagLt (by rw [hTagMetaG (i0 + 1) hlt]; omega)) (by rw [hTagMetaG (i0 + 1) hlt]; omega)⟩⟩
      ⟨fun h => by have := hT2 5 (by omega); rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hT2 8 (by omega); rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hTagN0'; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hTagMetaL i0 hiLt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun h => by have := hTagMetaG i0 hiLt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
        fun hlt => ⟨fun h => by have := hTagMetaL (i0 + 1) hlt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
          fun h => by have := hTagMetaG (i0 + 1) hlt; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega,
          fun h => by have := hT2 8 (by omega); rw [h, hTagMetaL (i0 + 1) hlt] at this; omega,
          fun h => by have := hT2 8 (by omega); rw [h, hTagMetaG (i0 + 1) hlt] at this; omega,
          by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr]; omega,
          by dsimp [levelMeta, lvlMTable, n0Cell, solverLevelMetaAddr, solverLvlMAddr, solverN0Addr]; omega⟩⟩
      (hGI0_ptr.symm ▸ dynGraphAt_of_agree hGI0 (fun a ha1 ha2 =>
        hs2_eq_mem0 (hTagGI0 a ha1 ha2) (by split_ifs <;> omega) (by split_ifs <;> omega) (fun _ _ _ => by split_ifs <;> omega)))
      (by rw [hGI0_ptr]; rw [h1_4] at hs2_lo; omega)
      (fun a ha1 ha2 => by
        rw [hGI0_ptr] at ha1 ha2
        exact ⟨hNotFoot2 (htagLt (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega)) (by rw [hTagGI0 a ha1 ha2]; split_ifs <;> omega),
          fun h => by have := hTagGI0 a ha1 ha2; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; split_ifs at this <;> omega⟩)
      (hLenI0_ptr.symm ▸ hFmtPrec.symm ▸ hLenI0.congr (fun e he t ht => by
        have heLt := hGI0.2.2.1 e he
        have hmul : e * L + L ≤ ecI0 * L := by
          have := Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt); rwa [Nat.succ_mul] at this
        exact hs2_eq_mem0 (hTagLenI0 _ (by omega) (by omega)) (by omega) (by omega) (fun _ _ _ => by omega)))
      (by rw [hLenI0_ptr]; rw [h1_4] at hs2_lo; omega)
      (fun a ha1 ha2 => by
        rw [hLenI0_ptr] at ha1 ha2
        exact ⟨hNotFoot2 (htagLt (by rw [hTagLenI0 a ha1 ha2]; omega)) (by rw [hTagLenI0 a ha1 ha2]; omega),
          fun h => by have := hTagLenI0 a ha1 ha2; rw [h, hTagBranch i0 (le_of_lt hiLt)] at this; omega⟩)
      hRepI0_2 (hScIn0 i0 le_rfl hiLt)
      (fun a ha => by
        rcases hFootI0_2 a ha with h0 | ⟨_, hhi⟩
        · exact (hCoreFootLt i0 hiLt a h0).trans_le (by rw [h1_4] at hs2_lo; omega)
        · exact hhi)
      hz2 (by dsimp only [d, i0, chain, next] at hRestartSp ⊢; omega)
      ⟨by dsimp only [next, chain, i0] at hChain' ⊢; rw [← hChain']; exact hNextSub1, fun e he => by
        have hhe : e ∈ ((alg2LoopShiftStep cfg model i).chain.G (i0 + 1)).E := by
          dsimp only [next, chain, i0] at hChain' ⊢; rwa [hChain']
        obtain ⟨q, hq, hEq⟩ := hNextFits1 e hhe
        exact ⟨q, hq, by dsimp only [next, chain, i0] at hChain' ⊢; rw [← hChain', hFmtPrec]; exact hEq⟩⟩
      (fun ret1 _ hret1Hi =>
        ⟨fun m1 h1 raw vcH ecH hDG hh1 hh2 => by
          obtain ⟨hE, hDg, _⟩ := hOps.op3Placement _ m1 ret1 h1 raw vcH ecH hDG hh1 hh2
          dsimp only [d, i0, chain, next] at hRestartSp hret1Hi ⊢
          exact ⟨hE, by omega⟩,
        fun m2 vcH ecH vcF ecF h2 h3 Lw hDGEx hLSF hLw _ hh2Hi hh2 hh3 => by
          obtain ⟨m1, rawG, hDG⟩ := hDGEx
          obtain ⟨_, hDgH, hEcH⟩ := hOps.op3Placement _ m1 h2 h2 rawG vcH ecH hDG le_rfl (by omega)
          obtain ⟨_, _, _, hS2, hSE⟩ := hOps.op2Placement (chain.G i0) (tok.coreHandle i0)
            yI0_2 m2 h2 h3 vcF ecF Lw _ hLSF hh2 hh3
          have hMonoSp := wireCoreLenEdgeSpace_mono (max_le_max_left L hLw)
          have hMulSp := Nat.mul_le_mul_left (next.G (i0 + 1)).m hMonoSp
          have hEcMul := Nat.mul_le_mul_right L hEcH
          have hSub1 : (next.G (i0 + 1)).E ⊆ (chain.G i0).E := by
            dsimp only [next, chain, i0] at hChain' ⊢; rw [← hChain']; exact hNextSub1
          dsimp only [d, i0, chain, next] at hRestartSp hret1Hi hMulSp ⊢
          exact ⟨hS2, fun e he => (hSE e (hSub1 he)).1,
            fun e he => (hSE e (hSub1 he)).2, by omega⟩⟩)
      (fun hi1Lt m oPtr oWords h hOrd _ hz hGe => by
        obtain ⟨hLo, hEnd, hW⟩ := hOps.op5Placement _ m oPtr oWords (s2.regs 4) h hOrd hz hGe
        exact ⟨fun a ha1 _ => ⟨by rw [h1_4] at hs2_lo; omega,
            by rw [h1_4] at hs2_lo; omega⟩, hEnd, hW⟩)
  obtain ⟨_, hDgH3, hEcH3⟩ :=
    hOps.op3Placement _ s3.mem (s3.regs 4) (s3.regs 4) (s3.regs 6) vcH3 ecH3 hH3 le_rfl (by omega)
  have hs3_heapLe : s3.regs 4 ≤ heap + 2 * (d + 1) + (5 + dgCap + 5 * d) + restartSpace := by
    have hMonoSp := wireCoreLenEdgeSpace_mono (max_le_max_left L hLw3)
    have hMulSp := Nat.mul_le_mul_left (next.G (i0 + 1)).m hMonoSp
    have hEcMul := Nat.mul_le_mul_right L hEcH3
    dsimp only [d, i0, chain, next] at hRestartSp h4Hi3 hMulSp ⊢
    omega
  have hPhi1Eq :
      (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) s1.mem) =
      (Finset.Ico i0 d).sum (fun j => Rcore.phi (tok.coreHandle j) (tok.coreTok j) mem0) :=
    Finset.sum_congr rfl (fun j hj => by
      obtain ⟨_, hj2⟩ := Finset.mem_Ico.mp hj
      exact (hCoreLocal (tok.coreHandle j) (chainLevelOrdAbs chain j) (tok.coreTok j) mem0 s1.mem
        (fun a ha => (hs1Mem.symm ▸ hmem0_eq (hT21 j hj2 a ha) (by omega)).symm)).2.symm)
  have hMonoCL := wireCoreLenEdgeCost_mono (max_le_max_left L hLw3)
  have hMulCL := Nat.mul_le_mul_left (next.G (i0 + 1)).m (Nat.add_le_add_right hMonoCL 30)
  refine ⟨s2, s3, c0 + (c1 + c2 + 1) + 1, vcH3, ecH3, ordW3, yI0_2, yI0_3,
    runs_seq_iff.mpr (Or.inr ⟨s1, c0, c1 + c2 + 1, r0,
      runs_seq_iff.mpr (Or.inr ⟨s2, c1, c2, r1, r2, rfl⟩), rfl⟩),
    h1_4 ▸ hs2_lo, h4Lo3, hs3_heapLe, hz3, hOldForestsSafe2, h1_4 ▸ hFootI0_2,
    fun a ha hnf hout => (hs2_frame a (h1_4.symm ▸ ha) hnf hout).trans (congrFun hs1Mem a),
    hBr3, hRepI0_3, hFootI0_3, hH3, hLen3, hGrad3, hOrd3, hOrdLe3, h6Lo3, hHEnd3, h6Disj3,
    h7Lo3, hLenEnd3, h7Disj3, hMeta3, hs3_frame,
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
    ((hs3_regs 83 (by decide)).trans (hs2_regs 83 (by decide))).trans h1_83, ?_⟩
  rw [hPhi1Eq] at hc1
  dsimp only [d, i0, chain, next] at hc1 hc2 hMulCL ⊢
  omega

end MinCostFlow.MinRatio
