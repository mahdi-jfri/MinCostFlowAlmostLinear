module

public import MinCostFlow.MinRatio.WireInitPrefix
import MinCostFlow.MinRatio.WireInitConcreteArith

/-!
# End-to-end concrete ordered initializer theorem (`WireInitConcreteCore`)

Composes `initConcreteStage1_runs` and `initConcreteStage2D_runs` (`WireInitPrefix`) with
`ordRebuildSuffixProgramKFBL_init_runs` (`WireInitLevelsK`), `finishSolverInitBody_runs`
(`InitTail`), and `solverInitPostTailBodyK_runs` (`WireInitPostTailK`) to prove
`initConcreteBody_runs`. The sparse core meets `sparseCoreOrdMachineContractKFBL` at depth
`coreDepth` and at the caps `(G.n, m)` of the input graph, so every level has these caps.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program LastLevelProgram

set_option maxHeartbeats 500000 in
/-- End-to-end execution of `initConcreteBody` against the K-contract ordered sparse core,
`lastLevelRuntimeMachineContract` + `LastLevelProgram.readoutBody`, and `pathTreeMachineContract`. -/
theorem initConcreteBody_runs
    {w graphPack paramSetup sortedEnds coreInit coreLenProc edgeProc signExt mul intDiv
      lastInit treeInit bind shift divide negate copy
      L P m V psi k epsExp coreDepth capExp capLimit lastMult stretchP lastSpace
      paramSpace paramCost treeConst treeInitSpace linkSpace
      graph gradient lengths root pos : ℕ}
    {fmt : Num.Format w} {T : SparseCoreRestartTool} {lastTool : LastLevelTool}
    {C : ChainParams} {P_sc : SparseCoreOrdParams}
    {coreAlloc : ℕ → List ℕ → ℕ} {lastAlloc : ℕ → List ℕ → ℕ}
    {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs T)} {Rtree : DSRep PathTreeState}
    {opCore opLast opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {G : MGraph} {B_tree : ℤ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    (hFour : fmt.limbBits = 4) (hPeq : fmt.precision = P) (hWidth : P ≤ 4 * L)
    (hEq : ToolInitOrdEqOnE T) (hLastEq : LastLevelBuildEqOnE lastTool)
    (hlocalCore : Rcore.Local)
    (hpack : MeetsContract w p graphPack
      (dgInitFromListsContract w G.n (initRootECap N₀ C.k m) G (G.V.sort (· ≤ ·))
        ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))))
    (hparam : MeetsContract w p paramSetup
      (initParamSetupContract w m V L P C.d C.k psi k epsExp N₀ coreDepth lvlM paramSpace
        paramCost))
    (hsortAt : p.procs[sortedEnds]? = some buildSortedEndsBody)
    (hCoreLenProc : p.procs[coreLenProc]? = some (wireCoreLenBody edgeProc))
    (hEdgeProc : p.procs[edgeProc]? = some (wireCoreLenEdgeBody signExt mul intDiv copy))
    (hSign : MeetsContract w p signExt (Num.signExtendContract w 4))
    (hMul : MeetsContract w p mul (Num.multiplyContract w 4))
    (hIntDiv : MeetsContract w p intDiv (Num.integerDivideContract w 4))
    (hshift : MeetsContract w p shift (Num.shiftLeftContract w 4))
    (hdiv : MeetsContract w p divide (Num.fixedDivideContract w 4))
    (hneg : MeetsContract w p negate (Num.negateContract w 4))
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hbind : MeetsContract w p bind (pathSlotBindContract w))
    (hLastReadout : p.procs[opLast 0]? = some LastLevelProgram.readoutBody)
    (htreeImpl : Rtree.Implements w p treeInit opTree (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hCoreImpl : ∀ i < C.d,
      Rcore.Implements w p coreInit opCore
        (sparseCoreOrdMachineContractKFBL fmt L coreDepth T
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
            (IPM.Machine.readVector mem lengths 4 L P m)
            (IPM.Machine.readVector mem gradient 4 L P m)).1.G i)
          C.k (lvlM i) N₀ G.n (initRootECap N₀ C.k m) capExp P_sc coreAlloc) ∧
      SparseCoreReadoutFootAt fmt L coreDepth T
        ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
          (IPM.Machine.readVector mem lengths 4 L P m)
          (IPM.Machine.readVector mem gradient 4 L P m)).1.G i)
        C.k (lvlM i) N₀ G.n (initRootECap N₀ C.k m) capExp P_sc coreAlloc Rcore p opCore)
    (hLastImpl : ∀ vc ec, vc + ec + 2 ≤ capLimit →
      (lastLevelRepresentation vc ec 4 L P
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
            (IPM.Machine.readVector mem lengths 4 L P m)
            (IPM.Machine.readVector mem gradient 4 L P m)).1.G C.d).E).Implements
        w p lastInit opLast
        (lastLevelRuntimeMachineContract fmt L lastTool
          ((Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
            (IPM.Machine.readVector mem lengths 4 L P m)
            (IPM.Machine.readVector mem gradient 4 L P m)).1.G C.d)
          vc ec lastMult stretchP lastAlloc))
    (hLastSpaceLe : ∀ args, lastAlloc 1 args ≤ lastSpace)
    (hInitSpaceLe : ∀ i < C.d, ∀ g l gr o h,
      coreAlloc 6 [g, l, gr, o, C.k, lvlM i, N₀, L, P, coreDepth, h] ≤ coreInitSpace i)
    (htreeInitLe : ∀ heap, treeAlloc 7 G.n [G.n, L, heap] ≤ treeInitSpace)
    (htreeLinkLe : ∀ args, treeAlloc 0 G.n args ≤ linkSpace)
    (hGE : G.E = Finset.range m) (hGV : G.IsValid)
    (hVlt : ∀ v ∈ G.V, v < G.n) (hGnLeN : G.n ≤ N₀) (hGmLeM0 : m ≤ lvlM 0)
    (hcap0 : G.n + initRootECap N₀ C.k m + 2 ≤ capLimit)
    (hGraphAt : GraphAt mem graph G)
    (hGraphBelow : graph + (graphWords G).length ≤ root)
    (hLenBelow : lengths + G.m * L ≤ root) (hGradBelow : gradient + G.m * L ≤ root)
    (hVecValid : ∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧
      0 < Num.intVal mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L)
    (hz : ZeroFrom mem root)
    (hk : 0 < C.k) (hdPos : 0 < C.d) (hwk : C.k < 2 ^ w) (hN3w : N₀ + 3 < 2 ^ w)
    (hVW : V < 2 ^ w) (hPW : P < 2 ^ w) (hDW : coreDepth < 2 ^ w) (hsearchW : 20 * (4 * L + 8) + 100 < 2 ^ w)
    (hPdiv : 4 ∣ P) (hLpos : 0 < L) (hleEps : epsExp ≤ P) (hfitEps : P - epsExp + 1 < 4 * L)
    (hvw : 2 * G.n + 1 < 2 ^ w) (hwidthN : Nat.log 2 (2 * G.n + 1) ≤ 4 * L)
    (hw17 : 17 < 2 ^ w)
    (hMw : ∀ i < C.d, lvlM i < 2 ^ w)
    (hWord : ∀ i < C.d, (lvlM i + N₀ + 2) ^ P_sc.wordExp * (L + 1) < 2 ^ w)
    (hH : (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
      (IPM.Machine.readVector mem lengths 4 L P m)
      (IPM.Machine.readVector mem gradient 4 L P m)).1.toTreeChain.Holds G
      (IPM.Machine.readVector mem lengths 4 L P m) σ σ_mwu γ_ℓ γ_c)
    (hCoreInput : ∀ i < C.d,
      let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G
        (IPM.Machine.readVector mem lengths 4 L P m)
        (IPM.Machine.readVector mem gradient 4 L P m)).1
      SparseCoreOrdInput T C.k (lvlM i) N₀ (chain.scState i) (chain.G i) (chain.levelOrd i) (chain.updCount i))
    (hModel :
      let ℓ₀ := IPM.Machine.readVector mem lengths 4 L P m
      let g₀ := IPM.Machine.readVector mem gradient 4 L P m
      let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G ℓ₀ g₀).1
      (∀ i < C.d,
        (chain.G i).m ≤ lvlM i ∧ (chain.G i).n ≤ N₀ ∧
        (∀ e ∈ (chain.G i).E, 0 < chain.toTreeChain.chainLen ℓ₀ i e) ∧
        IsRotationOrder (chain.G i) (chain.levelOrd i) ∧
        (chain.G (i + 1)).E ⊆ (chain.G i).E ∧
        (chain.G (i + 1)).m ≤ nextM i ∧
        (i + 1 < C.d → nextM i ≤ lvlM (i + 1)) ∧
        ordRotWords (chainLevelOrdAbs chain i) 0 ≤ 1 + 2 * N₀ + 2 * nextM i ∧
        (∀ e ∈ (chain.G (i + 1)).E,
          ∃ q : ℤ, Num.Fits 4 L q ∧ (q : ℝ) / (2 : ℝ) ^ P =
            chain.toTreeChain.chainLen ℓ₀ (i + 1) e)) ∧
      (∀ e ∈ (chain.G C.d).E, 0 < chain.toTreeChain.chainLen ℓ₀ C.d e) ∧
      (∀ e ∈ (chain.G C.d).E,
        2 * (2 : ℝ) ^ stretchP *
          lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen ℓ₀ C.d) e <
        Num.capacity 4 L))
    (hValFits :
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
      let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
      ∀ e < m,
        let v := initialPathEdgeValue P ε (gradInt e) (lenInt e)
        let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
        |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree ∧
        Num.Fits 4 L (-th) ∧ Num.Fits 4 L th)
    (hB : 0 ≤ B_tree)
    (hcapB : 2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B_tree + 0) < (Num.capacity 4 L : ℤ))
    (hroom : root + initConcreteSpace m G.n L C.d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ < 2 ^ w) :
    let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
    let len₀ := IPM.Machine.readVector mem lengths 4 L P m
    let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
    let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
    let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
    let chain := (Chain.Ordered.algorithm1_initialize T lastTool C lvlM N₀ G len₀ grad₀).1
    let d := C.d
    let eCap := initRootECap N₀ C.k m
    ∃ (mid : State) (cInit rootGraph table levelsEnd treeEnd finalHeap vcLast ecLast : ℕ)
      (sFin : PathTreeState) (yTree : Rtree.τ)
      (slotFin nameFin : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
      let len0Buf := table - eCap * L
      let n0Cell := solverN0Addr table d
      let lvlMTable := solverLvlMAddr table d
      let levelMeta := solverLevelMetaAddr table d
      let handle := solverHandleAddr table d
      let levelTable := handle + 18
      let branchTable := levelTable + (d + 1)
      let freshCounter := levelsEnd + (4 * (d + 1) + 1)
      let forward := freshCounter + 1
      let inverse := forward + m
      let edgeThresholds := inverse + m
      let treeHeap := edgeThresholds + m
      let slots := treeEnd
      let names := treeEnd + m
      let slotThresholds := treeEnd + m + 2 * G.n
      let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
      let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
      let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
      let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
      let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
      let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
      let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
      let metaStatic := fun a => ∃ j, 1 ≤ j ∧ j < d ∧
        ((mid.mem (levelMeta + j) ≤ a ∧ a < mid.mem (levelMeta + j) + eCap * L) ∨
         (mid.mem (levelMeta + d + j) ≤ a ∧ a < mid.mem (levelMeta + d + j) + dynGraphSize G.n eCap))
      let extraStatic := fun a => a < branchTable + (d + 1) ∨ metaStatic a ∨
        (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
      Runs w p ω
        (initConcreteBody graphPack paramSetup sortedEnds coreInit (opCore 3) (opCore 2) coreLenProc
          (opCore 5) lastInit (opLast 0) treeInit (opTree 0) bind shift divide negate copy)
        (startState [graph, gradient, lengths, L, P, V, root] mem pos) (.returned finalHeap) mid cInit ∧
      SolverRootDirAt mid.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
      DetectHeaderAt mid.mem handle treeHeap names inverse slotThresholds m L
        (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      MinRatioNumericHeaderAt mid.mem handle L P (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      SolverChainHeaderAt mid.mem handle m V d C.k psi (root + 16) k epsExp coreDepth ∧
      FreshTablesAt mid.mem forward inverse freshCounter m m id id m ∧
      (∀ a, levelsEnd ≤ a → a < levelsEnd + (4 * (d + 1) + 1) → mid.mem a = 0) ∧
      (∀ e < m, mid.mem (inOffReady + e) = 0) ∧
      (∀ e < m,
        mid.mem (edgeThresholds + e) = thPtr e ∧
        mid.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt mid.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt mid.mem (recPtr e) 4 L (some (initialPathEdgeValue P ε (gradInt e) (lenInt e)))) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree
        (fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)) B_tree
        slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap mid.mem ∧
      ZeroFrom mid.mem finalHeap ∧
      root ≤ finalHeap ∧
      (∀ a < root, mid.mem a = mem a) ∧
      DynGraphAt mid.mem rootGraph G.n eCap G ∧
      root + 16 + (L + 1) + 6 ≤ rootGraph ∧
      rootGraph + dynGraphSize G.n eCap ≤ len0Buf ∧
      len0Buf + eCap * L = table ∧
      branchTable + (d + 1) ≤ levelsEnd ∧
      treeHeap ≤ treeEnd ∧
      afterThresh ≤ finalHeap ∧
      finalHeap < 2 ^ w ∧
      (mid.mem (solverSelectHeapAddr table d) = 0 ∧
       mid.mem (solverSelectBlocksAddr table d) = 0) ∧
      (mid.mem n0Cell = chain.N₀ ∧
       (∀ j < d, mid.mem (lvlMTable + j) = chain.lvlM j) ∧
       (∀ j < d, branchTable + (d + 1) ≤ mid.mem (levelTable + j) ∧
         mid.mem (levelTable + j) ≤ levelsEnd) ∧
       mid.mem (levelMeta + 0) = len0Buf ∧
       mid.mem (levelMeta + d + 0) = rootGraph ∧
       EdgeValuesAt mid.mem len0Buf 4 L P (chain.G 0).E (chain.toTreeChain.chainLen len₀ 0) ∧
       (∀ j, 1 ≤ j → j < d →
         DynGraphAt mid.mem (mid.mem (levelMeta + d + j)) G.n eCap (chain.G j) ∧
         EdgeValuesAt mid.mem (mid.mem (levelMeta + j)) 4 L P (chain.G j).E (chain.toTreeChain.chainLen len₀ j) ∧
         branchTable + (d + 1) ≤ mid.mem (levelMeta + j) ∧
         mid.mem (levelMeta + j) + eCap * L ≤ levelsEnd ∧
         branchTable + (d + 1) ≤ mid.mem (levelMeta + d + j) ∧
         mid.mem (levelMeta + d + j) + dynGraphSize G.n eCap ≤ levelsEnd)) ∧
      ((∀ j, 1 ≤ j → j < d → mid.mem (levelMeta + d + j) + dynGraphSize G.n eCap ≤ mid.mem (levelMeta + j)) ∧
       (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < d → mid.mem (levelMeta + j₁) + eCap * L ≤ mid.mem (levelMeta + d + j₂))) ∧
      (∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds m G.n a ∧
        ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
            d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
      OrdInitChainCoresK Rcore
        (lastLevelRepresentation vcLast ecLast 4 L P (chain.G d).E)
        Rtree chain treeHeap levelTable branchTable rootGraph edgeRecords edgeThresholds
        slots names slotThresholds m L finalHeap G recPtr extraStatic yCore yTerm yTree mid.mem ∧
      finalHeap ≤ root + initConcreteSpace m G.n L d paramSpace capExp capLimit lastSpace
        treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ ∧
      cInit + Rtree.phi treeHeap yTree mid.mem +
          (∑ i : Fin d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) mid.mem) ≤
        initConcreteFixed m G.n L d paramCost capExp capLimit lastMult treeConst P_sc lvlM nextM N₀ +
          max P_sc.mul lastMult * chain.totalRuntime := by
  subst hPeq
  intro grad₀ len₀ lenInt gradInt ε chain d eCap
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hELtM : ∀ e ∈ G.E, e < m := fun e he => Finset.mem_range.mp (hGE ▸ he)
  have hmLeECap : m ≤ eCap := initRootECap_ge_m N₀ C.k m
  have hELtECap : ∀ e ∈ G.E, e < eCap := fun e he => lt_of_lt_of_le (hELtM e he) hmLeECap
  have heCapLe : eCap ≤ capLimit := by omega
  have hNw : N₀ < 2 ^ w := by omega
  let pBase := root + 16 + (L + 1) + 6
  have hA12 := mkCCStage12Arith heCapLe hroom
  -- Stage 1: save caller args, parameter setup, compute `eCap`
  obtain ⟨s1, rootGraph, c1, r1, hrgLo, hrgHi, hs1_6, hs1_7, hs1_56, hs1_57, hs1_61,
      hs1_67, hs1_68, hs1_69, hs1_70, hs1_71, hs1_72, hs1_73, hs1_75, hs1_76,
      hs1_92, hs1_93, hs1_94, hs1_95, hs1_97, hlvl1, hdep1, hframe1, hz1, hc1⟩ :=
    initConcreteStage1_runs (w := w) (paramSetup := paramSetup) (graph := graph)
      (gradient := gradient) (lengths := lengths) (L := L) (P := fmt.precision) (V := V)
      (root := root) (pos := pos) (d := C.d) (branch := C.k) (psi := psi) (k := k)
      (epsExp := epsExp) (N₀ := N₀) (coreDepth := coreDepth) (paramSpace := paramSpace)
      (paramCost := paramCost) (lvlM := lvlM) (G := G) (p := p) (ω := ω) (mem := mem)
      (hGm.symm ▸ hparam) hGraphAt hGraphBelow hz hk hVW hPW hN3w (hGm.symm ▸ hA12.eCap_lt_w)
      hw17 hA12.room1
  have hGraph1 : GraphAt s1.mem graph G := fun j hj =>
    (hframe1 _ (by omega)).trans (hGraphAt j hj)
  -- Stage 2: pack `rootGraph` at `(G.n, eCap)`, sortedEnds, metadata + select ptrs, header
  let ordBase := rootGraph + dynGraphSize G.n eCap
  let len0Buf := ordBase + 1 + 4 * G.n + 2 * eCap
  let table := len0Buf + eCap * L
  obtain ⟨s2, c2, r2, hs2_9, hs2_56, hs2_57, hs2_58, hs2_59, hs2_60, hs2_67, hs2_68, hs2_70,
      hs2_71, hs2_74, hs2_75, hs2_76, hs2_77, hs2_96, hs2_98, hDG2, _, -,
      hn0_2, hlvlCopy2, hmeta0_2, hmetaG0_2, hsh_2, hsb_2, hlenCopy2,
      hOrd2, hOrdW2, hchain2, hnum2, hframe2, hz2, hc2⟩ :=
    initConcreteStage2D_runs (w := w) (graphPack := graphPack) (sortedEnds := sortedEnds)
      (copy := copy) (root := root) (pBase := pBase) (rootGraph := rootGraph) (graph := graph)
      (gradient := gradient) (lengths := lengths) (m := m) (eCap := eCap) (V := V) (L := L)
      (P := fmt.precision) (d := C.d) (branch := C.k) (psi := psi) (k := k) (epsExp := epsExp)
      (N₀ := N₀) (coreDepth := coreDepth) (lvlM := lvlM) (G := G) (p := p) (ω := ω) (st := s1)
      hpack hsortAt hcopy hs1_6 hs1_7 hs1_56 hs1_57 (by simpa [eCap, hGm] using hs1_61) hs1_67 hs1_68 hs1_69 hs1_70
      hs1_71 hs1_72 hs1_73 hs1_75 hs1_76 hs1_93 (hGm ▸ hs1_94) hs1_95 hs1_97
      hGraph1 hGV hGm hVlt hELtECap hmLeECap hGraphBelow (hGm ▸ hLenBelow)
      hA12.root16_le_pBase hrgLo hlvl1 hdep1 hz1 hNw hdPos hsearchW hw17 (hA12.room2 rootGraph hrgHi)
  have hA3 := mkCCStage3Arith hrgLo hrgHi rfl rfl rfl hmLeECap heCapLe hGnLeN hGmLeM0 hw17 hroom
  let n0Cell := solverN0Addr table C.d; let lvlMTable := solverLvlMAddr table C.d
  let levelMeta := solverLevelMetaAddr table C.d; let handle := solverHandleAddr table C.d
  let levelTable := handle + 18; let branchTable := levelTable + (C.d + 1)
  let levelsStart := branchTable + (C.d + 1)
  have hs2_9' : s2.regs 9 = ordBase := hs2_9; have hs2_58' : s2.regs 58 = levelMeta := hs2_58
  have hs2_59' : s2.regs 59 = len0Buf := hs2_59; have hs2_60' : s2.regs 60 = lvlMTable := hs2_60
  have hs2_74' : s2.regs 74 = handle := hs2_74; have hs2_77' : s2.regs 77 = levelTable := hs2_77
  have ⟨hn0D, hlmD, hmetD, hshD, hsbD⟩ : n0Cell = table + (C.d + 1) ∧ lvlMTable = n0Cell + 1 ∧
      levelMeta = lvlMTable + C.d ∧ solverSelectHeapAddr table C.d = levelMeta + 2 * C.d ∧
      solverSelectBlocksAddr table C.d = levelMeta + 2 * C.d + 1 := ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hhD : handle = table + (4 * C.d + 4) := by
    unfold handle solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hMetaLayout : lvlMTable + C.d = levelMeta ∧ levelMeta + 2 * C.d ≤ levelTable :=
    ⟨rfl, by dsimp only [levelTable]; omega⟩
  -- Stage 3: stage registers + run `ordRebuildSuffixProgramKFBLStore`
  let t0 := { s2 with regs := Function.update s2.regs 57 lvlMTable }
  let t1 := { t0 with regs := Function.update t0.regs 51 levelTable }
  let t2 := { t1 with regs := Function.update t1.regs 52 branchTable }
  let t3 := { t2 with regs := Function.update t2.regs 4 levelsStart }
  let t4 := { t3 with regs := Function.update t3.regs 1 C.k }
  let t5 := { t4 with regs := Function.update t4.regs 6 rootGraph }
  let t6 := { t5 with regs := Function.update t5.regs 7 len0Buf }
  let t7 := { t6 with regs := Function.update t6.regs 8 gradient }
  let t8 := { t7 with regs := Function.update t7.regs 20 0 }
  let t9 := { t8 with regs := Function.update t8.regs 21 C.d }
  have rt0 : Runs w p ω (.assign 57 (.reg 60)) s2 .normal t0 2 :=
    runs_assign_iff.mpr ⟨lvlMTable, by simp [Expr.eval, hs2_60'], rfl, rfl, rfl⟩
  have rt1 : Runs w p ω (.assign 51 (.reg 77)) t0 .normal t1 2 :=
    runs_assign_iff.mpr ⟨levelTable, by simp [Expr.eval, t0, hs2_77'], rfl, rfl, rfl⟩
  have rt2 : Runs w p ω (.assign 52 (.bin .add (.reg 77) (.bin .add (.reg 75) (.const 1)))) t1 .normal t2 6 :=
    runs_assign_iff.mpr ⟨branchTable, by
      have hbr : solverHandleAddr table C.d + 18 + (C.d + 1) < 2 ^ w := hA3.br_lt_w
      simp [Expr.eval, BinOp.eval, t1, t0, hs2_77', hs2_75, branchTable, levelTable, handle,
        hA3.one_lt_w, hA3.d1_lt_w, hbr],
      rfl, rfl, rfl⟩
  have rt3 : Runs w p ω (.assign 4 (.bin .add (.reg 52) (.bin .add (.reg 75) (.const 1)))) t2 .normal t3 6 :=
    runs_assign_iff.mpr ⟨levelsStart, by
      have hlv : solverHandleAddr table C.d + 18 + (C.d + 1) + (C.d + 1) < 2 ^ w := hA3.lvlStart_lt_w
      simp [Expr.eval, BinOp.eval, t2, t1, t0, hs2_75, levelsStart, branchTable, levelTable, handle,
        hA3.one_lt_w, hA3.d1_lt_w, hlv],
      rfl, rfl, rfl⟩
  have rt4 : Runs w p ω (.assign 1 (.reg 76)) t3 .normal t4 2 :=
    runs_assign_iff.mpr ⟨C.k, by simp [Expr.eval, t3, t2, t1, t0, hs2_76], rfl, rfl, rfl⟩
  have rt5 : Runs w p ω (.assign 6 (.reg 96)) t4 .normal t5 2 :=
    runs_assign_iff.mpr ⟨rootGraph, by simp [Expr.eval, t4, t3, t2, t1, t0, hs2_96], rfl, rfl, rfl⟩
  have rt6 : Runs w p ω (.assign 7 (.reg 59)) t5 .normal t6 2 :=
    runs_assign_iff.mpr ⟨len0Buf, by simp [Expr.eval, t5, t4, t3, t2, t1, t0, hs2_59'], rfl, rfl, rfl⟩
  have rt7 : Runs w p ω (.assign 8 (.reg 70)) t6 .normal t7 2 :=
    runs_assign_iff.mpr ⟨gradient, by simp [Expr.eval, t6, t5, t4, t3, t2, t1, t0, hs2_70], rfl, rfl, rfl⟩
  have rt8 : Runs w p ω (.assign 20 (.const 0)) t7 .normal t8 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, hA3.zero_lt_w], rfl, rfl, rfl⟩
  have rt9 : Runs w p ω (.assign 21 (.reg 75)) t8 .normal t9 2 :=
    runs_assign_iff.mpr ⟨C.d, by simp [Expr.eval, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_75], rfl, rfl, rfl⟩
  have hmem2_root (a : ℕ) (ha : a < root) : s2.mem a = mem a :=
    (hframe2 a (lt_of_lt_of_le ha hA3.root_le_rootG)).trans (hframe1 a (lt_of_lt_of_le ha hA3.root_le_pBase))
  have hLen2 : EdgeValuesAt s2.mem len0Buf 4 L fmt.precision G.E len₀ := by
    intro e he
    have hem : e < m := Finset.mem_range.mp (hGE ▸ he)
    have hmul : e * L + L ≤ m * L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem)
    have hltM (j : ℕ) (hj : j < L) : e * L + j < m * L :=
      lt_of_lt_of_le (Nat.add_lt_add_left hj (e * L)) hmul
    have hltR (j : ℕ) (hj : j < L) : lengths + (e * L + j) < root :=
      lt_of_lt_of_le (Nat.add_lt_add_left (hltM j hj) lengths) (hGm ▸ hLenBelow)
    have hcopyAt (j : ℕ) (hj : j < L) : s2.mem (len0Buf + e * L + j) = mem (lengths + e * L + j) := by
      rw [Nat.add_assoc, hlenCopy2 (e * L + j) (hltM j hj),
        hframe1 _ (lt_of_lt_of_le (hltR j hj) hA3.root_le_pBase), ← Nat.add_assoc]
    have hval : Num.Valid s2.mem (len0Buf + e * L) 4 L :=
      fun j hj => by rw [hcopyAt j hj]; exact (hVecValid e hem).1 j hj
    refine ⟨hval, ?_⟩
    have hfix : Num.fixVal s2.mem (len0Buf + e * L) 4 L fmt.precision =
        Num.fixVal mem (lengths + e * L) 4 L fmt.precision := by
      unfold Num.fixVal; rw [Num.intVal_congr hcopyAt]
    simp [len₀, IPM.Machine.readVector, hem, hfix]
  have hGrad2 : EdgeValuesAt s2.mem gradient 4 L fmt.precision G.E grad₀ := by
    intro e he
    have hem : e < m := Finset.mem_range.mp (hGE ▸ he)
    have hmul : e * L + L ≤ G.m * L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (hGm.symm ▸ Nat.succ_le_of_lt hem)
    have hltR (j : ℕ) (hj : j < L) : gradient + e * L + j < root :=
      lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hj (e * L)) gradient)
        ((Nat.add_le_add_left hmul gradient).trans hGradBelow)
    have hval : Num.Valid s2.mem (gradient + e * L) 4 L :=
      fun j hj => by rw [hmem2_root _ (hltR j hj)]; exact (hVecValid e hem).2.2 j hj
    refine ⟨hval, ?_⟩
    have hfix : Num.fixVal s2.mem (gradient + e * L) 4 L fmt.precision =
        Num.fixVal mem (gradient + e * L) 4 L fmt.precision := by
      unfold Num.fixVal; rw [Num.intVal_congr (fun j hj => hmem2_root _ (hltR j hj))]
    simp [grad₀, IPM.Machine.readVector, hem, hfix]
  have hGradEnd3 : gradient + eCap * L ≤ levelTable := by
    have hgrRoot : gradient ≤ root := le_trans (Nat.le_add_right _ _) hGradBelow
    have hrootLen0 : root ≤ len0Buf := hA3.root_le_rootG.trans ((Nat.le_add_right _ _).trans hA3.rootG_end_le_len0)
    have htbLvl : table ≤ levelTable := by dsimp only [levelTable]; omega
    exact (Nat.add_le_add_right (hgrRoot.trans hrootLen0) (eCap * L)).trans htbLvl
  obtain ⟨s3, levelsEnd, vcLast, ecLast, cLevels, yCore0, yTerm0, rLevels,
      hs3_4, hlevLo, hlevHi, hcapLast, hz3, hframe3, hcores3, hmetaLevels3, hmetaOrd3, hlastBr3, hrepTerm3, hfootTerm3,
      hhandlesLe3, hs3_regs, hcLevels⟩ :=
    ordRebuildSuffixProgramKFBL_init_runs (w := w) (L := L) (depth := coreDepth) (capExp := capExp)
      (capLimit := capLimit)
      (init := coreInit) (coreLenProc := coreLenProc) (edgeProc := edgeProc) (signExt := signExt)
      (mul := mul) (intDiv := intDiv) (copy := copy) (lastInit := lastInit)
      (rootGraph := rootGraph) (lenBase := len0Buf) (gradBase := gradient)
      (ordBase := ordBase) (ordWords := 1 + 2 * G.n + 2 * m) (vc0 := G.n) (ec0 := eCap)
      (levelTable := levelTable) (branchTable := branchTable) (levelsStart := levelsStart)
      (lvlMTable := lvlMTable) (levelMeta := levelMeta)
      (lastMult := lastMult) (stretchP := stretchP) (lastSpace := lastSpace)
      (fmt := fmt) (T := T) (lastTool := lastTool) (C := C) (P := P_sc)
      (allocation := coreAlloc) (lastAllocation := lastAlloc)
      (coreInitSpace := coreInitSpace) (lvlM := lvlM) (nextM := nextM) (N₀ := N₀)
      (Rcore := Rcore) (p := p) (opCore := opCore) (opLast := opLast) (st := t9) (ω := ω)
      (G₀ := G) (ℓ₀ := len₀) (g₀ := grad₀)
      hFour hWidth hEq hLastEq hlocalCore hCoreImpl hLastImpl hLastSpaceLe hInitSpaceLe
      hCoreLenProc hEdgeProc hSign hMul hIntDiv hcopy
      (by simp [t9, t8, t7, t6, t5, t4]) (by simp [t9, t8, t7, t6, t5, t4, t3])
      (by simp [t9, t8, t7, t6, t5]) (by simp [t9, t8, t7, t6])
      (by simp [t9, t8, t7]) (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_9'])
      (by simp [t9, t8]) (by simp [t9])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1]) (by simp [t9, t8, t7, t6, t5, t4, t3, t2])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_56])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_58'])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_67])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_68])
      (by simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0, hs2_98])
      ⟨rfl, le_rfl⟩ hMetaLayout hlvlCopy2
      hcap0 hDG2 hA3.rootG_end_le_meta
      hLen2 hA3.len0_end_le_meta
      hGrad2 hGradEnd3
      hOrd2 (fun _ => hA3.ordWords_le) hA3.ordEnd_le_lvl hOrdW2
      (fun a ha => hz2 a (hA3.handle18_le_lvlStart.trans ha))
      hk hdPos hwk hNw hA3.d_lt_w hA3.L_lt_w hPW hDW hA3.nine_lt_w
      hMw hWord hModel hA3.room3
  have rStage3 : Runs w p ω
      (initConcreteStage3 coreInit (opCore 3) (opCore 2) coreLenProc (opCore 5) lastInit)
      s2 .normal s3
      (2 + (2 + (6 + (6 + (2 + (2 + (2 + (2 + (2 + (2 + cLevels + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨t0, 2, _, rt0,
    runs_seq_iff.mpr (Or.inr ⟨t1, 2, _, rt1,
    runs_seq_iff.mpr (Or.inr ⟨t2, 6, _, rt2,
    runs_seq_iff.mpr (Or.inr ⟨t3, 6, _, rt3,
    runs_seq_iff.mpr (Or.inr ⟨t4, 2, _, rt4,
    runs_seq_iff.mpr (Or.inr ⟨t5, 2, _, rt5,
    runs_seq_iff.mpr (Or.inr ⟨t6, 2, _, rt6,
    runs_seq_iff.mpr (Or.inr ⟨t7, 2, _, rt7,
    runs_seq_iff.mpr (Or.inr ⟨t8, 2, _, rt8,
    runs_seq_iff.mpr (Or.inr ⟨t9, 2, cLevels, rt9, rLevels, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  let s3' := { s3 with regs := Function.update s3.regs 69 rootGraph }
  have hs3_r (r : ℕ) (hr : r = 67 ∨ r = 68 ∨ 70 ≤ r) : s3.regs r = s2.regs r := by
    obtain ⟨h21, h20, h8, h7, h6, h1, h4, h52, h51, h57⟩ := reg_ne_stage3 hr
    exact (hs3_regs r hr).trans (by
      simp [t9, t8, t7, t6, t5, t4, t3, t2, t1, t0,
        Function.update_of_ne h21, Function.update_of_ne h20,
        Function.update_of_ne h8, Function.update_of_ne h7,
        Function.update_of_ne h6, Function.update_of_ne h1,
        Function.update_of_ne h4, Function.update_of_ne h52,
        Function.update_of_ne h51, Function.update_of_ne h57])
  have rRest69 : Runs w p ω (.assign 69 (.reg 96)) s3 .normal s3' 2 :=
    runs_assign_iff.mpr ⟨rootGraph, by simp [Expr.eval, hs3_r 96 (Or.inr (Or.inr (by decide))), hs2_96], rfl, rfl, rfl⟩
  have hA4 := mkCCStage4Arith hrgHi rfl rfl rfl heCapLe hlevLo hlevHi hroom
  -- Stage 4: `finishSolverInitBody`
  have hmem3_preMeta (a : ℕ) (ha : a ≤ levelMeta) : s3.mem a = s2.mem a :=
    hframe3 a (by dsimp only [levelsStart, branchTable, levelTable]; omega)
      (Or.inl (by dsimp only [levelTable]; omega))
      (Or.inl (by dsimp only [branchTable, levelTable]; omega))
      (Or.inl (by omega)) (Or.inl (by omega))
  have hmem3_sel : s3.mem (solverSelectHeapAddr table C.d) = s2.mem (solverSelectHeapAddr table C.d) ∧
      s3.mem (solverSelectBlocksAddr table C.d) = s2.mem (solverSelectBlocksAddr table C.d) :=
    ⟨hframe3 _ (by dsimp only [levelsStart, branchTable, levelTable]; omega)
      (Or.inl (by dsimp only [levelTable]; omega))
      (Or.inl (by dsimp only [branchTable, levelTable]; omega))
      (Or.inr (by omega)) (Or.inr (by omega)),
     hframe3 _ (by dsimp only [levelsStart, branchTable, levelTable]; omega)
      (Or.inl (by dsimp only [levelTable]; omega))
      (Or.inl (by dsimp only [branchTable, levelTable]; omega))
      (Or.inr (by omega)) (Or.inr (by omega))⟩
  have hmem3_hdr (a : ℕ) (hlo : handle ≤ a) (hhi : a < levelTable) : s3.mem a = s2.mem a :=
    hframe3 a (lt_of_lt_of_le hhi hA4.handle18_lt_lvlStart) (Or.inl hhi)
      (Or.inl (lt_of_lt_of_le hhi hA4.handle18_le_br))
      (Or.inr (by omega)) (Or.inr (by omega))
  have hmem3_metaG0 : s3.mem (levelMeta + C.d) = s2.mem (levelMeta + C.d) :=
    hframe3 _ (by dsimp only [levelsStart, branchTable, levelTable]; omega)
      (Or.inl (by dsimp only [levelTable]; omega))
      (Or.inl (by dsimp only [branchTable, levelTable]; omega))
      (Or.inr le_rfl) (Or.inl (Nat.lt_succ_self _))
  have hnum3 : MinRatioNumericHeaderAt s3.mem handle L fmt.precision (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) := by
    intro j hj
    have hj4 : j < 4 := by simpa [List.length] using hj
    rw [hmem3_hdr (handle + 5 + j) (by omega) (by omega)]; exact hnum2 j hj
  have hchain3 : SolverChainHeaderAt s3.mem handle m V C.d C.k psi (root + 16) k epsExp coreDepth := by
    intro j hj
    have hj8 : j < 9 := by simpa [List.length] using hj
    rw [hmem3_hdr (handle + 9 + j) (by omega) (by omega)]; exact hchain2 j hj
  have hDG3 : DynGraphAt s3.mem rootGraph G.n eCap G :=
    dynGraphAt_of_agree hDG2 (fun a _ hhi => hmem3_preMeta a (by have := hA3.rootG_end_le_meta; change _ ≤ levelMeta at this; omega))
  let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
  let forward := freshCounter + 1
  let inverse := forward + m
  let edgeThresholds := inverse + m
  let treeHeap := edgeThresholds + m
  obtain ⟨s4, cTail, sTree0, xTree0, treeEnd, rTail,
      hs4_74, hs4_80, hs4_81, hs4_82, hs4_83, hs4_84, hs4_85, hs4_99,
      hdetect4, hnum4, hsched4, hfresh4, hrepTree4, hinitTreePost4, hz4, htreeLo, htreeHi,
      hfootTree4, hframe4, hcTail⟩ :=
    finishSolverInitBody_runs (w := w) (handle := handle) (rootGraph := rootGraph) (d := C.d)
      (m := m) (n := G.n) (L := L) (P := fmt.precision)
      (searchSpace := 20 * (4 * L + 8) + 100) (readSpace := 20 * (4 * L + 8) + 100)
      (levelsEnd := levelsEnd) (treeInit := treeInit) (treeConst := treeConst)
      (fmt := fmt) (treeAlloc := treeAlloc) (Rtree := Rtree) (treeOp := opTree)
      (p := p) (ω := ω) (st := s3')
      (by simp [s3', hs3_r 74 (Or.inr (Or.inr (by decide))), hs2_74'])
      (by simp [s3', hs3_r 75 (Or.inr (Or.inr (by decide))), hs2_75])
      (by simp [s3'])
      (by simp [s3', hs3_r 67 (Or.inl rfl), hs2_67])
      (by simp [s3', hs3_4])
      (by simpa [s3', Nat.add_assoc] using hchain3 0 (by simp))
      (by simpa [s3', dgNOff] using hDG3.2.2.2.2.2.1)
      hnum3 hz3
      (lt_of_lt_of_le (by unfold handle solverHandleAddr; omega : handle + 16 < handle + 18) hA4.handle18_le_levEnd)
      hA4.rootG2_lt_levEnd htreeImpl hA3.L_lt_w hPW hvw (hFour.symm ▸ hwidthN)
      (lt_of_le_of_lt (Nat.add_le_add_left (htreeInitLe treeHeap) _) hA4.treeHeap_plus_init_lt_w)
      (lt_trans (by decide : 16 < 17) hw17)
  have hs4_r (r : ℕ) (hr1 : 1 ≤ r) (hr79 : r ≤ 79) : s4.regs r = s3'.regs r :=
    finishSolverInitBody_preserves_regs hr1 hr79 rTail
  have hmem4_below (a : ℕ) (ha : a < levelsEnd) (hnot : a < handle ∨ handle + 4 < a) :
      s4.mem a = s3.mem a := hframe4 a ha hnot
  have hroot16_le_rootG : root + 16 ≤ rootGraph := hA12.root16_le_pBase.trans (by omega)
  have hrootG_le_len0 : rootGraph + dynGraphSize G.n eCap ≤ len0Buf := hA4.rootG_end_le_len0
  have hrootG_le_table : rootGraph + dynGraphSize G.n eCap ≤ table := hA4.rootG_end_le_table
  have htable_le_handle : table ≤ handle := by omega
  have hroot_le_handle : root ≤ handle :=
    (Nat.le_add_right root 16).trans (hroot16_le_rootG.trans ((Nat.le_add_right _ _).trans
      (hrootG_le_table.trans htable_le_handle)))
  have hhandle_le_lvl : handle ≤ levelTable := Nat.le_add_right _ _
  have hlvlEnd_le_br : levelTable + (C.d + 1) ≤ branchTable := le_rfl
  have hbrEnd_le_levEnd : branchTable + (C.d + 1) ≤ levelsEnd := hlevLo
  have hlvl_le_levEnd : levelTable ≤ levelsEnd := hA4.handle18_le_levEnd
  have hhandle_le_levEnd : handle ≤ levelsEnd := hhandle_le_lvl.trans hlvl_le_levEnd
  have hroot_le_levEnd : root ≤ levelsEnd := hroot_le_handle.trans hhandle_le_levEnd
  have htreeHiLe : treeEnd ≤ treeHeap + treeInitSpace :=
    htreeHi.trans (Nat.add_le_add_left (htreeInitLe treeHeap) _)
  have ⟨hfinSpaceLe, hroomPost⟩ := initConcrete_roomPost_and_space
    (w := w) (root := root) (rootGraph := rootGraph) (L := L) (m := m) (n := G.n) (eCap := eCap)
    (d := C.d) (paramSpace := paramSpace) (capExp := capExp) (capLimit := capLimit)
    (lastSpace := lastSpace) (treeInitSpace := treeInitSpace) (linkSpace := linkSpace)
    (ordBase := ordBase) (len0Buf := len0Buf) (table := table) (levelsEnd := levelsEnd) (treeEnd := treeEnd)
    (coreInitSpace := coreInitSpace) (lvlM := lvlM) (nextM := nextM) (N₀ := N₀)
    hrgHi rfl rfl rfl heCapLe hlevHi htreeHiLe hroom
  have hlevEnd_lt_w : levelsEnd < 2 ^ w := hA4.levEnd_lt_w
  have hd_lt_w : C.d < 2 ^ w := hA3.d_lt_w
  have hCore4 (i : ℕ) (hi : i < C.d) :
      s4.mem (levelTable + i) = s3.mem (levelTable + i) ∧
      s4.mem (branchTable + i) = chain.bran i ∧
      Rcore.rep (s4.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCore0 i) s4.mem ∧
      Rcore.phi (s4.mem (levelTable + i)) (yCore0 i) s4.mem =
        Rcore.phi (s3.mem (levelTable + i)) (yCore0 i) s3.mem := by
    obtain ⟨hbr, hrep, hfoot, _, _⟩ := hcores3 i hi
    have hlvLt : levelTable + i < levelsEnd :=
      lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_lt hi) levelTable)
        (hlvlEnd_le_br.trans ((Nat.le_add_right _ _).trans hbrEnd_le_levEnd))
    have hbrLt : branchTable + i < levelsEnd :=
      lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_lt hi) branchTable) hbrEnd_le_levEnd
    have hlvGt : handle + 4 < levelTable + i :=
      lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle) (Nat.le_add_right _ _)
    have hbrGt : handle + 4 < branchTable + i :=
      lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle)
        ((Nat.le_add_right _ _).trans (hlvlEnd_le_br.trans (Nat.le_add_right _ _)))
    have hlv := hmem4_below (levelTable + i) hlvLt (Or.inr hlvGt)
    have hloc := hlocalCore (s3.mem (levelTable + i)) (chainLevelOrdAbs chain i) (yCore0 i)
      s3.mem s4.mem (fun a ha =>
        have hgt : handle + 4 < a :=
          lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle)
            ((Nat.le_add_right _ _).trans (hlvlEnd_le_br.trans ((Nat.le_add_right _ _).trans (hfoot a ha).1)))
        (hmem4_below a (hfoot a ha).2 (Or.inr hgt)).symm)
    exact ⟨hlv, (hmem4_below (branchTable + i) hbrLt (Or.inr hbrGt)).trans hbr,
      by rw [hlv]; exact hloc.1 hrep, by rw [hlv]; exact hloc.2.symm⟩
  have hTermLoc4 := (lastLevelRepresentation_local vcLast ecLast 4 L fmt.precision (chain.G C.d).E)
    (s3.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm0 s3.mem s4.mem (fun a ha =>
      have hgt : handle + 4 < a :=
        lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle)
          ((Nat.le_add_right _ _).trans (hlvlEnd_le_br.trans ((Nat.le_add_right _ _).trans (hfootTerm3 a ha).1)))
      (hmem4_below a (hfootTerm3 a ha).2 (Or.inr hgt)).symm)
  have hlvTermLt : levelTable + C.d < levelsEnd :=
    lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_self C.d) levelTable)
      (hlvlEnd_le_br.trans ((Nat.le_add_right _ _).trans hbrEnd_le_levEnd))
  have hbrTermLt : branchTable + C.d < levelsEnd :=
    lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_self C.d) branchTable) hbrEnd_le_levEnd
  have hlvTerm4 : s4.mem (levelTable + C.d) = s3.mem (levelTable + C.d) :=
    hmem4_below (levelTable + C.d) hlvTermLt
      (Or.inr (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle) (Nat.le_add_right _ _)))
  have hmem4_root (a : ℕ) (ha : a < root) : s4.mem a = mem a :=
    (hmem4_below a (lt_of_lt_of_le ha hroot_le_levEnd) (Or.inl (lt_of_lt_of_le ha hroot_le_handle))).trans
      ((hmem3_preMeta a (by have := hA3.root_le_rootG; have h2 := hA3.rootG_end_le_meta; change _ ≤ levelMeta at h2; omega)).trans (hmem2_root a ha))
  -- Stage 5: `solverInitPostTailBodyK_runs`
  have hlenAt4 : ∀ e < m, 0 < lenInt e ∧ PathIntAt s4.mem (lengths + e * L) 4 L (lenInt e) := by
    intro e he
    have hmul : e * L + L ≤ G.m * L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (hGm.symm ▸ Nat.succ_le_of_lt he)
    have hlPos := (hVecValid e he).2.1
    have htoNat : ((lenInt e : ℕ) : ℤ) = Num.intVal mem (lengths + e * L) 4 L := Int.toNat_of_nonneg hlPos.le
    have hmemEq : ∀ j < L, s4.mem (lengths + e * L + j) = mem (lengths + e * L + j) := fun j hj =>
      hmem4_root _ (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hj (e * L)) lengths)
        ((Nat.add_le_add_left hmul lengths).trans hLenBelow))
    refine ⟨Int.lt_toNat.mpr hlPos,
      fun j hj => by rw [hmemEq j hj]; exact (hVecValid e he).1 j hj,
      (Num.intVal_congr hmemEq).trans htoNat.symm⟩
  have hgradAt4 : ∀ e < m, PathIntAt s4.mem (gradient + e * L) 4 L (gradInt e) := by
    intro e he
    have hmul : e * L + L ≤ G.m * L := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (hGm.symm ▸ Nat.succ_le_of_lt he)
    have hmemEq : ∀ j < L, s4.mem (gradient + e * L + j) = mem (gradient + e * L + j) := fun j hj =>
      hmem4_root _ (lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hj (e * L)) gradient)
        ((Nat.add_le_add_left hmul gradient).trans hGradBelow))
    exact ⟨fun j hj => by rw [hmemEq j hj]; exact (hVecValid e he).2.2 j hj, Num.intVal_congr hmemEq⟩
  have hTG : chain.toTreeChain.chainTree.E ⊆ G.E := by
    have hs := chain.toTreeChain.chainTree_isSubgraph hH
      (chain.toTreeChain.forestsAreSubgraphs_of_holds hH)
    rw [hH.1] at hs; exact hs.2.1
  have hDG4 : DynGraphAt s4.mem rootGraph G.n eCap G :=
    dynGraphAt_of_agree hDG3 (fun a _ hhi =>
      have hltH : a < handle := lt_of_lt_of_le hhi (hrootG_le_table.trans htable_le_handle)
      hmem4_below a (lt_of_lt_of_le hltH hhandle_le_levEnd) (Or.inl hltH))
  have hchain4 : SolverChainHeaderAt s4.mem handle m V C.d C.k psi (root + 16) k epsExp coreDepth := fun j hj => by
    have hj8 : j < 9 := by simpa [List.length] using hj
    have hlt : handle + 9 + j < levelsEnd :=
      lt_of_lt_of_le (by rw [Nat.add_assoc]; exact Nat.add_lt_add_left (lt_of_lt_of_le (Nat.add_lt_add_left hj8 9) (by decide : 9 + 9 ≤ 18)) handle)
        hlvl_le_levEnd
    have hgt : handle + 4 < handle + 9 + j :=
      lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 9) handle) (Nat.le_add_right _ _)
    rw [hmem4_below _ hlt (Or.inr hgt)]
    exact hchain3 j hj
  let metaStatic3 : ℕ → Prop := fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
    ((s3.mem (levelMeta + j) ≤ a ∧ a < s3.mem (levelMeta + j) + eCap * L) ∨
     (s3.mem (levelMeta + C.d + j) ≤ a ∧ a < s3.mem (levelMeta + C.d + j) + dynGraphSize G.n eCap))
  have hmetaStatic4 : ∀ a, metaStatic3 a →
      handle + 18 + (C.d + 1) + (C.d + 1) ≤ a ∧ a < levelsEnd ∧
      (∀ i < C.d, ¬ Rcore.foot (s4.mem (handle + 18 + i)) (yCore0 i) a) ∧
      ¬ (lastLevelRepresentation vcLast ecLast 4 L fmt.precision (chain.G C.d).E).foot
          (s4.mem (handle + 18 + C.d)) yTerm0 a := by
    rintro a ⟨j, hj1, hjLt, ⟨hlo, hhi⟩ | ⟨hlo, hhi⟩⟩
    · obtain ⟨_, _, _, _, hLLo, hLHi, hDisjC, hDisjTL, _⟩ := hmetaLevels3 j hj1 hjLt
      refine ⟨hLLo.trans hlo, lt_of_lt_of_le hhi hLHi, fun i hi hf => ?_, fun hf => ?_⟩
      · rw [(hCore4 i hi).1] at hf; exact (hDisjC i hi).1 a hlo hhi hf
      · rw [hlvTerm4] at hf; exact hDisjTL a hlo hhi hf
    · obtain ⟨_, hGLo, hGHi, _, _, _, hDisjC, _, hDisjTG⟩ := hmetaLevels3 j hj1 hjLt
      refine ⟨hGLo.trans hlo, lt_of_lt_of_le hhi hGHi, fun i hi hf => ?_, fun hf => ?_⟩
      · rw [(hCore4 i hi).1] at hf; exact (hDisjC i hi).2 a hlo hhi hf
      · rw [hlvTerm4] at hf; exact hDisjTG a hlo hhi hf
  obtain ⟨s5, finalHeap, cPost, sFin, yTree, slotFin, nameFin, yCore, yTerm,
      rPost, hs5_99, hrootDir5, hdetect5, hnum5, hchain5, hfresh5, hsched5, hoff5, hedges5,
      hinv5, hz5, hafterLe5, hfinHi5, hframe5, hframePreH5, hframeLvl5, hframeMeta5, hDG5, htreeOut5, hcores5, hcPost⟩ :=
    solverInitPostTailBodyK_runs (w := w) (shift := shift) (divide := divide) (negate := negate)
      (copy := copy) (bind := bind) (initCore := coreInit) (initTree := treeInit)
      (root := root) (table := table) (handle := handle) (levelsEnd := levelsEnd)
      (rootGraph := rootGraph) (gradient := gradient) (lengths := lengths)
      (forward := forward) (inverse := inverse) (edgeThresholds := edgeThresholds)
      (freshCounter := freshCounter) (treeHeap := treeHeap) (treeEnd := treeEnd)
      (m := m) (ec0 := eCap) (V := V) (Ψ := psi) (k := k) (epsExp := epsExp) (L := L) (P := fmt.precision)
      (searchSpace := 20 * (4 * L + 8) + 100) (readSpace := 20 * (4 * L + 8) + 100)
      (treeConst := treeConst) (linkSpace := linkSpace) (capExp := capExp) (capLimit := capLimit)
      (vcLast := vcLast) (ecLast := ecLast)
      (fmt := fmt) (T := T) (C := C) (P_sc := P_sc) (coreAlloc := coreAlloc)
      (depth := coreDepth) (lvlM := lvlM) (treeAlloc := treeAlloc) (N₀ := N₀)
      (Rcore := Rcore) (Rtree := Rtree) (opCore := opCore) (opLast := opLast) (opTree := opTree)
      (p := p) (ω := ω) (st := s4) (G := G) (len₀ := len₀) (chain := chain) (B := B_tree)
      (xCore := yCore0) (xTerm := yTerm0) (sTree := sTree0) (xTree := xTree0)
      (metaStatic := metaStatic3)
      lenInt gradInt hFour rfl hlocalCore hH hshift hdiv hneg hcopy hbind hCoreImpl
      hLastReadout htreeImpl hCoreInput
      ((hs4_r 67 (by decide) (by decide)).trans (by simp [s3', hs3_r 67 (Or.inl rfl), hs2_67]))
      ((hs4_r 68 (by decide) (by decide)).trans (by simp [s3', hs3_r 68 (Or.inr (Or.inl rfl)), hs2_68]))
      ((hs4_r 69 (by decide) (by decide)).trans (by simp [s3']))
      ((hs4_r 70 (by decide) (by decide)).trans (by simp [s3', hs3_r 70 (Or.inr (Or.inr (by decide))), hs2_70]))
      ((hs4_r 71 (by decide) (by decide)).trans (by simp [s3', hs3_r 71 (Or.inr (Or.inr (by decide))), hs2_71]))
      hs4_74
      ((hs4_r 75 (by decide) (by decide)).trans (by simp [s3', hs3_r 75 (Or.inr (Or.inr (by decide))), hs2_75]))
      hs4_80 hs4_81 hs4_82 hs4_83 hs4_84 hs4_85 hs4_99
      hhD rfl hroot16_le_rootG hrootG_le_table hlevLo rfl rfl rfl rfl htreeLo
      (by rw [← hGm]; exact hLenBelow) (by rw [← hGm]; exact hGradBelow)
      hDG4 hELtM hcap0 hdetect4 hnum4 hchain4
      hfresh4 hsched4 hrepTree4 hinitTreePost4 hfootTree4
      (fun i hi => by
        obtain ⟨hlv, hbr, hrep, _⟩ := hCore4 i hi
        obtain ⟨_, _, hfoot, hdisjC, hdisjT⟩ := hcores3 i hi
        refine ⟨hbr, hrep, fun a ha => ?_⟩
        rw [hlv] at ha
        exact ⟨(hfoot a ha).1, (hfoot a ha).2,
          fun j hj hne hfj => hdisjC j hj hne a ha (by rwa [(hCore4 j hj).1] at hfj),
          fun hft => hdisjT a ha (by rwa [hlvTerm4] at hft)⟩)
      ((hmem4_below (branchTable + C.d) hbrTermLt
        (Or.inr (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle)
          ((Nat.le_add_right _ _).trans (hlvlEnd_le_br.trans (Nat.le_add_right _ _)))))).trans hlastBr3)
      (by rw [hlvTerm4]; exact hTermLoc4.1 hrepTerm3)
      (fun a ha => by
        rw [hlvTerm4] at ha
        exact ⟨(hfootTerm3 a ha).1, (hfootTerm3 a ha).2, fun j hj hfj => by
          rw [(hCore4 j hj).1] at hfj
          exact (hcores3 j hj).2.2.2.2 a hfj ha⟩)
      (fun i hi => ⟨by
          have hlvLt : levelTable + i < levelsEnd :=
            lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hi) levelTable)
              (hlvlEnd_le_br.trans ((Nat.le_add_right _ _).trans hbrEnd_le_levEnd))
          rw [hmem4_below (levelTable + i) hlvLt
            (Or.inr (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle) (Nat.le_add_right _ _)))]
          exact lt_of_le_of_lt (hhandlesLe3 i hi).2 hlevEnd_lt_w,
        by
          have hbrLt : branchTable + i < levelsEnd :=
            lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hi) branchTable) hbrEnd_le_levEnd
          rw [hmem4_below (branchTable + i) hbrLt
            (Or.inr (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 18) handle)
              ((Nat.le_add_right _ _).trans (hlvlEnd_le_br.trans (Nat.le_add_right _ _)))))]
          by_cases hlt : i < C.d
          · rw [(hcores3 i hlt).1, (ordAlgorithm1_initialize_level_facts hEq lastTool C lvlM N₀ G len₀ grad₀).2.2.2.2 i hlt |>.1]
            exact Nat.pos_of_ne_zero (by positivity)
          · have hieq : i = C.d := Nat.le_antisymm hi (Nat.le_of_not_lt hlt)
            subst hieq
            rw [hlastBr3, (ordAlgorithm1_initialize_level_facts hEq lastTool C lvlM N₀ G len₀ grad₀).2.2.1]
            exact Nat.pos_of_ne_zero (by positivity)⟩)
      hlenAt4 hgradAt4
      (fun e he => ⟨(hValFits e he).2.2.2.2.1, (hValFits e he).2.2.2.2.2⟩)
      (fun e he => by
        have hem : e < m := Finset.mem_range.mp (hGE ▸ hTG he)
        have hv := hValFits e hem
        exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1⟩)
      hB hcapB hPdiv hPW hLpos hleEps hfitEps hvw hwidthN hd_lt_w hw17 hz4
      (fun e _ cur _ _ => htreeLinkLe _) hroomPost hmetaStatic4
  have rRet : Runs w p ω (.ret (.reg 99)) s5 (.returned finalHeap) s5 2 :=
    runs_ret_iff.mpr ⟨finalHeap, by simp [Expr.eval, hs5_99], rfl, rfl, rfl⟩
  have rFull : Runs w p ω
      (initConcreteBody graphPack paramSetup sortedEnds coreInit (opCore 3) (opCore 2) coreLenProc
        (opCore 5) lastInit (opLast 0) treeInit (opTree 0) bind shift divide negate copy)
      (startState [graph, gradient, lengths, L, fmt.precision, V, root] mem pos)
      (.returned finalHeap) s5
      (c1 + (c2 + ((2 + (2 + (6 + (6 + (2 + (2 + (2 + (2 + (2 + (2 + cLevels + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) +
        (2 + (cTail + (cPost + 2 + 1) + 1) + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1, _, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, c2, _, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, _, _, rStage3,
    runs_seq_iff.mpr (Or.inr ⟨s3', 2, _, rRest69,
    runs_seq_iff.mpr (Or.inr ⟨s4, cTail, _, rTail,
    runs_seq_iff.mpr (Or.inr ⟨s5, cPost, 2, rPost, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hSumPhi4 :
      (∑ i : Fin C.d, Rcore.phi (s4.mem (levelTable + i.val)) (yCore0 i.val) s4.mem) =
      (∑ i : Fin C.d, Rcore.phi (s3.mem (levelTable + i.val)) (yCore0 i.val) s3.mem) :=
    Finset.sum_congr rfl fun i _ => (hCore4 i.val i.isLt).2.2.2
  have hfinLeSp : finalHeap ≤ root + initConcreteSpace m G.n L C.d paramSpace capExp capLimit
      lastSpace treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ :=
    hfinHi5.trans hfinSpaceLe
  have hrootLeFin : root ≤ finalHeap :=
    initConcrete_root_le_fin hroot_le_levEnd htreeLo hafterLe5
  let cInit :=
    c1 + (c2 + ((2 + (2 + (6 + (6 + (2 + (2 + (2 + (2 + (2 + (2 + cLevels + 1) + 1) + 1) + 1) +
      1) + 1) + 1) + 1) + 1) + 1) +
      (2 + (cTail + (cPost + 2 + 1) + 1) + 1) + 1) + 1) + 1
  have hcostFinal :
      cInit + Rtree.phi treeHeap yTree s5.mem +
          (∑ i : Fin C.d, Rcore.phi (s5.mem (levelTable + i.val)) (yCore i.val) s5.mem) ≤
        initConcreteFixed m G.n L C.d paramCost capExp capLimit lastMult treeConst P_sc lvlM nextM N₀ +
          max P_sc.mul lastMult * chain.totalRuntime := by
    rw [hSumPhi4] at hcPost
    exact initConcrete_totalCost_le heCapLe hc1 hc2 hcLevels hcTail hcPost
  have hmem5_preH (a : ℕ) (h1 : root + 16 ≤ a) (h2 : a < handle) : s5.mem a = s3.mem a :=
    (hframePreH5 a h1 h2).trans (hmem4_below a (lt_of_lt_of_le h2 hhandle_le_levEnd) (Or.inl h2))
  have hmem5_meta (a : ℕ) (hms : metaStatic3 a) : s5.mem a = s3.mem a := by
    obtain ⟨hlo, hhi, _, _⟩ := hmetaStatic4 a hms
    have hgt : handle + 4 < a :=
      lt_of_lt_of_le (by omega : handle + 4 < handle + 18 + (C.d + 1) + (C.d + 1)) hlo
    exact (hframeMeta5 a hms).trans (hmem4_below a hhi (Or.inr hgt))
  have hlen0Sub : table - eCap * L = len0Buf := Nat.add_sub_cancel len0Buf (eCap * L)
  obtain ⟨hmetaStaticEq, hSel5, hMeta5, hMetaOrd5⟩ := initConcrete_packMeta5
    (m2 := s2.mem) (m3 := s3.mem) (m5 := s5.mem) (lvlM := lvlM) (N₀ := N₀)
    hH.1 hGE hmLeECap rfl (fun _ _ => rfl) hroot16_le_rootG hrootG_le_len0 rfl hmem5_preH
    hmem3_preMeta hmem3_sel hmem5_meta
    hn0_2 hlvlCopy2 hmeta0_2 hmetaG0_2 ⟨hsh_2, hsb_2⟩ hmem3_metaG0 hLen2
    (fun j hj => by rw [hframeLvl5 j hj, (hCore4 j hj).1]; exact hhandlesLe3 j (Nat.le_of_lt hj))
    (fun j hj1 hjLt => by
      obtain ⟨hDG3J, hGLo3, hGHi3, hLen3J, hLLo3, hLHi3, _, _, _⟩ := hmetaLevels3 j hj1 hjLt
      exact ⟨hDG3J, hGLo3, hGHi3, hLen3J, hLLo3, hLHi3⟩) hmetaOrd3
  have hmetaStaticEq' :
      (fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
        ((s5.mem (solverLevelMetaAddr table C.d + j) ≤ a ∧
            a < s5.mem (solverLevelMetaAddr table C.d + j) + eCap * L) ∨
         (s5.mem (solverLevelMetaAddr table C.d + C.d + j) ≤ a ∧
            a < s5.mem (solverLevelMetaAddr table C.d + C.d + j) + dynGraphSize G.n eCap))) =
      metaStatic3 := hmetaStaticEq
  have hExtraEq :
      (fun a => a < solverHandleAddr table C.d + 18 + (C.d + 1) + (C.d + 1) ∨
        (∃ j, 1 ≤ j ∧ j < C.d ∧
          ((s5.mem (solverLevelMetaAddr table C.d + j) ≤ a ∧ a < s5.mem (solverLevelMetaAddr table C.d + j) + eCap * L) ∨
           (s5.mem (solverLevelMetaAddr table C.d + C.d + j) ≤ a ∧ a < s5.mem (solverLevelMetaAddr table C.d + C.d + j) + dynGraphSize G.n eCap))) ∨
        (levelsEnd ≤ a ∧ a < levelsEnd + (4 * (C.d + 1) + 1) + 1 + m + m + m) ∨
        (treeEnd + m + 2 * G.n + 2 * G.n + m ≤ a ∧
          a < treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L)) =
      (fun a => a < handle + 18 + (C.d + 1) + (C.d + 1) ∨ metaStatic3 a ∨
        (levelsEnd ≤ a ∧ a < treeHeap) ∨
        (treeEnd + m + 2 * G.n + 2 * G.n + m ≤ a ∧
          a < treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L)) := by
    funext a; rw [← hmetaStaticEq']
  refine ⟨s5, cInit, rootGraph, table, levelsEnd, treeEnd, finalHeap, vcLast, ecLast, sFin, yTree,
    slotFin, nameFin, yCore, yTerm, ?_⟩
  refine ⟨rFull, hrootDir5, hdetect5, hnum5, hchain5, hfresh5, hsched5, hoff5, hedges5, hinv5,
    hz5, hrootLeFin, fun a ha => (hframe5 a ha).trans (hmem4_root a ha),
    hDG5, by omega, hlen0Sub.symm ▸ hrootG_le_len0, by omega, hlevLo, htreeLo, hafterLe5,
    lt_of_le_of_lt hfinLeSp hroom, hSel5, by simpa only [hlen0Sub] using hMeta5, hMetaOrd5,
    by rwa [hExtraEq], by rwa [hExtraEq], hfinLeSp, hcostFinal⟩

end MinCostFlow.MinRatio
