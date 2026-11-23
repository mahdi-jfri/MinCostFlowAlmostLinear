module

public import MinCostFlow.MinRatio.SolverInitWiredBase
public import MinCostFlow.MinRatio.WireSpecBase
public import MinCostFlow.MinRatio.InitRootECap
public import MinCostFlow.IPM.MinRatioSpec

/-!
# Corrected spec of the concrete initializer

`OrdInitConcreteSpec` (`SolverInitWiredBase.lean`) is false for every program.
It asks `root ≤ finalHeap < 2 ^ w`, and no
hypothesis bounds `root`. It also lacks the word-size condition that the sparse-core contract asks
at the initialization of every level, and it bounds neither the space nor the cost of Init.

`OrdInitConcreteSpecW` is the corrected spec. It has a space parameter `initSpace'` and three more
hypotheses, all about the input of the call:
* `root + initSpace' < 2 ^ w`;
* the word-size condition `(lvlM i + N₀ + 2) ^ wordExp < 2 ^ w` at every level `i < d`, with the
  exponent `wordExp` of the sparse-core program;
* the cap and limb facts `WireCapFacts` of the sparse-core contract on the initial state.
It has two more conclusions:
* `finalHeap ≤ root + initSpace'`, so that `finalHeap < 2 ^ w` follows;
* the cost: the steps of Init plus the potentials of the path tree and of the sparse-core levels
  are at most `initFixed + initMul · totalRuntime`, where `totalRuntime` is the cumulative runtime
  of the initial chain (`ChainState.totalRuntime`). The sparse-core initialization of level `i`
  costs `P.mul` times the tool cost of its new state plus its input size, so Init pays the tool
  cost of the whole chain once. The credit of the solver potential for later rebuilds starts
  from this value.
The rest of the statement is that of `OrdInitConcreteSpec`, word for word.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine SparseCore.Program DynSpanner.Program

/-- **The corrected concrete initializer spec.** It is `OrdInitConcreteSpec` with the space
parameter `initSpace'`, the hypotheses `root + initSpace' < 2 ^ w`, the word-size condition of the
sparse-core contract at every level, and `WireCapFacts` on the initial state, and with two more
conclusions: `finalHeap ≤ root + initSpace'` and the cost bound
`cInit + Φ_tree + Σ_i Φ_core,i ≤ initFixed + initMul · totalRuntime`. -/
@[expose] def OrdInitConcreteSpecW (w L P E m V psi k epsExp : ℕ) (cfg : Alg2Config)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (G : MGraph) (p : Program)
    (initConcreteProc : ℕ) (B_tree : ℤ)
    (capExp limbMul capLimit wordExp initSpace' initFixed initMul : ℕ) : Prop :=
  ∃ body, p.procs[initConcreteProc]? = some body ∧
    ∀ (graph gradient lengths root pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ),
      let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
      let len₀ := IPM.Machine.readVector mem lengths 4 L P m
      let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
      let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
      let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
      let chain := s0.chain
      let d := cfg.P.d
      let eCap := initRootECap cfg.N₀ cfg.P.k m
      let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
      root + initSpace' < 2 ^ w →
      (∀ i < d, (chain.lvlM i + chain.N₀ + 2) ^ wordExp * (L + 1) < 2 ^ w) →
      WireCapFacts capExp limbMul L capLimit s0 →
      IPM.Machine.GraphAt mem graph G →
      graph + (IPM.Machine.graphWords G).length ≤ root →
      lengths + G.m * L ≤ root →
      gradient + G.m * L ≤ root →
      (∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧ 0 < Num.intVal mem (lengths + e * L) 4 L ∧
        Num.Valid mem (gradient + e * L) 4 L) →
      IPM.LengthsWithin G E len₀ →
      (∀ e ∈ G.E, |grad₀ e| ≤ (2 : ℝ) ^ E) →
      ZeroFrom mem root →
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
        Runs w p ω body (startState [graph, gradient, lengths, L, P, V, root] mem pos)
          (.returned finalHeap) mid cInit ∧
        SolverRootDirAt mid.mem root handle table levelsEnd forward inverse freshCounter
          slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
        DetectHeaderAt mid.mem handle treeHeap names inverse slotThresholds m L
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        MinRatioNumericHeaderAt mid.mem handle L P (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        SolverChainHeaderAt mid.mem handle m V d cfg.P.k psi (root + 16) k epsExp
          (Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
        FreshTablesAt mid.mem forward inverse freshCounter m m id id m ∧
        (∀ a, levelsEnd ≤ a → a < levelsEnd + (4 * (d + 1) + 1) → mid.mem a = 0) ∧
        (∀ e < m, mid.mem (inOffReady + e) = 0) ∧
        (∀ e < m,
          mid.mem (edgeThresholds + e) = thPtr e ∧
          mid.mem (edgeRecords + e) = recPtr e ∧
          PathIntAt mid.mem (thPtr e) 4 L (detectorThreshold P cfg.ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
          PathEdgeAt mid.mem (recPtr e) 4 L (some (initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)))) ∧
        InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree
          (fun e => initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)) B_tree
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
        ((∀ j, 1 ≤ j → j < d →
            mid.mem (levelMeta + d + j) + dynGraphSize G.n eCap ≤ mid.mem (levelMeta + j)) ∧
         (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < d →
            mid.mem (levelMeta + j₁) + eCap * L ≤ mid.mem (levelMeta + d + j₂))) ∧
        (∀ a, Rtree.foot treeHeap yTree a →
          OutsideInitSlotTables slots names slotThresholds m G.n a ∧
          ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
              d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
        OrdInitChainCoresAt Rcore
          (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G d).E)
          Rtree chain treeHeap levelTable branchTable rootGraph edgeRecords edgeThresholds
          slots names slotThresholds m L finalHeap G recPtr extraStatic yCore yTerm yTree mid.mem ∧
        finalHeap ≤ root + initSpace' ∧
        cInit + Rtree.phi treeHeap yTree mid.mem +
            (∑ i : Fin d, Rcore.phi (mid.mem (levelTable + i.val)) (yCore i.val) mid.mem) ≤
          initFixed + initMul * chain.totalRuntime

end MinCostFlow.MinRatio
