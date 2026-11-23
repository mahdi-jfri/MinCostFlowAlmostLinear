module

public import MinCostFlow.MinRatio.InitConcreteModules
public import MinCostFlow.MinRatio.InitConcretePostTailRuns
public import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# End-to-end concrete wired Algorithm 2 initialization

Discharges every concrete submodule hypothesis of `solverInitFullPrefix_runs`,
`buildSolverInitLevels_fixedPoint_capIndexed_runs`, `finishSolverInitBody_runs`, and
`solverInitPostTailBody_runs` using `initConcreteHelperProcs`,
`LinkCut.PathProg.pathTree_implements`, and `LastLevelProgram.packedLastLevelProgram_implements`
(relocated via `dsRep_implements_shift`).

Leaves only the three external interfaces parameterized:
- `quality` (`IPM.Machine.solverQualityContract`, supplied by the host solver program),
- `degreeSetup` (temporary `degCap` envelope), and
- `Rcore` (`sparseCoreMachineContract`).
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program

/-- Complete concrete deterministic Algorithm 2 Init program taking the seven-word IPM entry
`[graph, gradient, lengths, L, P, V, root]` and returning the fresh heap pointer `finalHeap`.
Reserves `[root, root + 16)` for `SolverRootDirAt`, runs the full concrete Init prefix,
builds all `C.d` sparse cores and the packed last-level structure, initializes the Section 6
path tree, populates all Detect thresholds and initial `PathEdgeAt` records, inserts every
edge of `chain.toTreeChain.chainTree` into the path tree, and writes `SolverRootDirAt`. -/
@[expose] def solverInitConcreteFullProgram
    (base quality threshold lsstConstant decK thr cDeg witnessDen coefficient
      initCore readCore forestCore : ℕ)
    (retry degreeSetup inconclusive : Stmt) : Stmt :=
  let lay := initConcreteLayout base
  .assign 6 (.bin .add (.reg 6) (.const 16)) ;;
  solverInitFullProgram lay.alpha lay.precisionSelect quality lay.dgInitFromLists threshold
    lay.depth lay.clog lsstConstant lay.factors decK thr cDeg witnessDen coefficient
    lay.power lay.extendCopy lay.multiply lay.shiftLeft lay.add retry degreeSetup
    (buildSolverInitLevels initCore readCore forestCore lay.copy lay.heapSort lay.writeGradCell
        (lay.lastLevel + 15) ;;
      finishSolverInitBody lay.pathTree ;;
      solverInitPostTailBody lay.shiftLeft lay.fixedDivide lay.negate lay.copy
        forestCore readCore (lay.lastLevel + 16) (lay.pathTree + 1) lay.slotBind)
    inconclusive ;;
  .ret (.reg 99)

private theorem startState_add16_step {w a0 a1 a2 a3 a4 a5 root pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (h16 : 16 < 2 ^ w) (hroot : root + 16 < 2 ^ w) :
    Runs w p ω (.assign 6 (.bin .add (.reg 6) (.const 16)))
      (startState [a0, a1, a2, a3, a4, a5, root] mem pos) .normal
      (startState [a0, a1, a2, a3, a4, a5, root + 16] mem pos) 4 := by
  refine runs_assign_iff.mpr ⟨root + 16, ?_, rfl, ?_, rfl⟩
  · simp [Expr.eval, BinOp.eval, startState, h16, hroot]
  · simp only [startState, State.mk.injEq, true_and, and_true]
    funext r
    rcases r with _ | _ | _ | _ | _ | _ | _ | n <;> simp [Function.update]

private theorem root_add16_pow_bound {B root dh : ℕ} (hB : 2 ≤ B) (hroot : root ≤ B ^ dh) :
    root + 16 ≤ B ^ (dh + 5) := by
  have h32 : 32 ≤ B ^ 5 :=
    le_trans (by decide : 32 ≤ 2 ^ 5) (Nat.pow_le_pow_left hB 5)
  have h1 : 1 ≤ B ^ dh := Nat.one_le_pow dh B (by omega)
  have hmul : 32 * B ^ dh ≤ B ^ 5 * B ^ dh := Nat.mul_le_mul_right (B ^ dh) h32
  rw [← Nat.pow_add, Nat.add_comm 5 dh] at hmul
  omega

private theorem ipmQuality_precision_arith (m V k : ℕ) :
    let L := IPM.Machine.ipmQualityLimbs m V k
    let P := IPM.Machine.ipmQualityPrecision m V k
    let epsExp := Num.IPM.alphaExponent m V + k + 10
    4 ∣ P ∧ 0 < L ∧ epsExp ≤ P ∧ P - epsExp + 1 < 4 * L := by
  have hk : k ≤ IPM.Machine.qualitySlackExponent m V k :=
    IPM.Machine.qualityExponent_le_qualitySlackExponent m V k
  have hα : Num.IPM.alphaExponent m V ≤ Num.IPM.alphaScale m V := by
    unfold Num.IPM.alphaExponent Num.IPM.alphaScale
    have hc : Nat.clog 2 (1000 * (m.size + V.size)) ≤ 1000 * (m.size + V.size) :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
    omega
  dsimp only [IPM.Machine.ipmQualityLimbs, IPM.Machine.ipmQualityPrecision,
    IPM.Machine.ipmQualityErrorBits, IPM.Machine.ipmQualityRangeExponent]
  refine ⟨Nat.dvd_mul_right 4 _, by omega, by omega, by omega⟩

private theorem wired_cont_arith {root L dg table d lev endT finalHeap w : ℕ}
    (htable : root + 16 + (L + 1) + 6 + dg ≤ table) (hdg3 : 3 ≤ dg)
    (hlev : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev)
    (hroom : table + (d + 1) + 17 + (d + 1) + (d + 1) < 2 ^ w)
    (hle : lev ≤ endT) (hfin : endT ≤ finalHeap) :
    let handle := table + (d + 1)
    let levelTable := handle + 17
    let rootGraph := root + 16 + (L + 1) + 6
    root + 16 < 2 ^ w ∧ root ≤ finalHeap ∧
    root + 16 ≤ rootGraph ∧ rootGraph + dg ≤ table ∧
    handle + 9 < levelTable ∧ rootGraph + 2 < levelTable ∧
    handle + 16 < lev ∧ rootGraph + 2 < lev ∧
    (∀ j < 4, handle + 5 + j < levelTable) ∧
    (∀ j < 8, handle + 9 + j < levelTable ∧ handle + 9 + j < lev ∧ handle + 4 < handle + 9 + j) ∧
    (∀ i ≤ d, levelTable + i < lev ∧ handle + 4 < levelTable + i ∧
      levelTable + (d + 1) + i < lev ∧ handle + 4 < levelTable + (d + 1) + i) ∧
    (∀ x, rootGraph ≤ x → x < rootGraph + dg → x < levelTable ∧ x < handle) ∧
    (∀ x < root, x < levelTable ∧ x < handle) ∧
    (∀ j ≤ d, table + j < levelTable ∧ table + j < handle) := by
  dsimp only
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    fun j hj => by omega, fun j hj => ⟨by omega, by omega, by omega⟩,
    fun i hi => ⟨by omega, by omega, by omega, by omega⟩,
    fun x h1 h2 => ⟨by omega, by omega⟩, fun x hx => ⟨by omega, by omega⟩,
    fun j hj => ⟨by omega, by omega⟩⟩

private theorem vec_lt_root_of_le {base e L m root j : ℕ}
    (he : e < m) (hj : j < L) (hend : base + m * L ≤ root) :
    base + e * L + j < root := by
  have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hm; omega

/-- End-to-end concrete wired Algorithm 2 Init theorem: discharges every concrete helper
module, the Section 6 link-cut tree (`LinkCut.PathProg.pathRep 4`), and the canonical
packed last-level data structure (`LastLevelProgram.packedLastLevelProgram`) from a single
`p.HasAt base (initConcreteHelperProcs ...)` placement hypothesis. -/
theorem solverInitConcreteFull_runs
    (base scDepth threshold Kγ pathC Kint cw decK thr cDeg witnessDen coefficient
      quality initCore q dh : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (opCore : ℕ → ℕ)
    (hK : 1 ≤ decK) (hcDeg : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ (guest : Program) (cLast : ℕ) (KLast CfLast : ℝ)
      (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (multiplier : ℕ),
      let C_lsst := LastLevelProgram.graphCanonicalConstant KLast CfLast
      let dLast := ⌈max 1 C_lsst⌉₊
      let lastProg := LastLevelProgram.packedLastLevelProgram guest dLast cLast
      let lastTool := LastLevelProgram.fixedPointLastLevelTool oracle C_lsst
      lastTool.IsSpec (SparseCore.lastLevelParams (128 * max 1 C_lsst)) ∧
      ∀ (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
        {Rcore : DSRep (sparseCoreRestartTool oracle C_lsst scDepth sparsify).State}
        {costs : SparseCoreMachineCosts}
        {coreAlloc : ℕ → ℕ → List ℕ → ℕ}
        {Mcap Ncap scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
        {c graph gradient lengths root pos levelSpace linkSpace : ℕ}
        {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
        {qualityExponent qualityCharge : ℕ → ℕ}
        {retry degreeSetup inconclusive : Stmt}
        (B_tree : ℤ),
        let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
        let w := wordSize c J.solverWords
        let I := IPM.Machine.solverConnectedAugmented J
        let V := IPM.Machine.solverPenalty J.m
        let G := IPM.namedInstance I
        let k := qualityExponent G.m
        let L := IPM.Machine.ipmQualityLimbs I.m V k
        let P := IPM.Machine.ipmQualityPrecision I.m V k
        let M := max I.m threshold
        let T := sparseCoreRestartTool oracle C_lsst scDepth sparsify
        let len₀ := IPM.Machine.readVector mem lengths 4 L P I.m
        let grad₀ := IPM.Machine.readVector mem gradient 4 L P I.m
        let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
        let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
        J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) → I.IsValid →
        2 ^ k ≤ (J.n + J.m + 2) ^ q →
        root ≤ B ^ dh →
        ∀ (hqw : IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w),
        multiplier ≤ c →
        ∀ (hM : 1 ≤ M),
        let fmt := (IPM.Machine.ipmQualityMinRatioFormat I.m V k hqw).fmt
        let C := Chain.concreteChainParams M hM
        let chain := (algorithm1_initialize T lastTool C Mcap (Ncap 0) G len₀ grad₀).1
        let Ψ := IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6
        let den := Expander.maxPhiDenOf decK thr (M ^ 2)
        let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
        let growth := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
          (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
        let epsExp := Num.IPM.alphaExponent I.m V + k + 10
        let stretchP := (1024 * dLast).size + 3 * ((chain.G C.d).m + 1).size
        let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
        -- Concrete helper bundle + three external parameters (`quality`, `degreeSetup`, `Rcore`)
        p.HasAt base (initConcreteHelperProcs base Kγ pathC Kint lastProg) →
        MeetsContract w p quality (IPM.Machine.solverQualityContract w qualityExponent qualityCharge) →
        IPM.Machine.GraphAt mem graph G →
        graph + (IPM.Machine.graphWords G).length ≤ root →
        lengths + G.m * L ≤ root →
        gradient + G.m * L ≤ root →
        (∀ e < I.m, Num.Valid mem (lengths + e * L) 4 L ∧ 0 < Num.intVal mem (lengths + e * L) 4 L ∧
          Num.Valid mem (gradient + e * L) 4 L) →
        ZeroFrom mem root →
        E.L = Expander.chosenL (M ^ 2) →
        (E.P_fn (M ^ 2)).γ_ℓ = growth →
        1 ≤ (E.P_fn (M ^ 2)).K_s → (E.P_fn (M ^ 2)).p_s = 1 →
        (E.P_fn (M ^ 2)).K_s = 1 + coefficient / Real.log 2 →
        (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M →
        (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ C.k →
        E.B_fn (M ^ 2) = Chain.concreteBucketCap dLast Ψ C.k C.d (4 * M) →
        (∀ factors,
          factors.regs 22 = M → factors.regs 44 = E.L → factors.regs 47 = E.B_fn (M ^ 2) →
          factors.regs 50 = growth → factors.regs 4 = 1 →
          ∃ capped degCost,
            Runs w p ω degreeSetup factors .normal capped degCost ∧
            capped.regs 48 = E.d_fn (M ^ 2) ∧ capped.mem = factors.mem ∧
            ∀ r ≠ 48, capped.regs r = factors.regs r) →
        -- Sparse-core implementation and chain structural/space bounds
        Rcore.Local → C.d < 2 ^ w → C.k < 2 ^ w →
        2 * G.n + 1 < 2 ^ w → Nat.log 2 (2 * G.n + 1) ≤ 4 * L →
        (∀ i, i < C.d → Ncap i = Ncap 0) →
        (chain.G C.d).IsValid →
        (∀ a ∈ (chain.G C.d).V, ∀ b ∈ (chain.G C.d).V, (chain.G C.d).Connected a b) →
        (chain.G C.d).n ≤ (chain.G C.d).m + 1 →
        (∀ i < C.d, ∀ vc ec,
          Rcore.Implements w p initCore opCore
            (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (coreAlloc i))) →
        (∀ i < C.d,
          SparseCoreInput T.toSparseCoreTool T.restart C.k (chain.scState i) (chain.G i)) →
        (∃ σ σ_mwu γ_ℓ γ_c, chain.toTreeChain.Holds G len₀ σ σ_mwu γ_ℓ γ_c) →
        (∀ i < C.d,
          let Gi := chain.G i
          let Hi := chain.G (i + 1)
          let leni := chain.toTreeChain.chainLen len₀ i
          let gradi := chain.toTreeChain.chainGrad grad₀ i
          let forest := T.lsfs (chain.scState i) 0
          Gi.m ≤ Mcap i ∧ Gi.n ≤ Ncap i ∧ (∀ e ∈ Gi.E, 0 < leni e) ∧
          forest.T.IsForest ∧ forest.T.E ⊆ Gi.E ∧ Gi.V ⊆ forest.T.V ∧ Hi.E ⊆ Gi.E ∧
          2 * forest.T.n + 2 < 2 ^ w ∧
          P + scanExponent i + 2 ≤ 4 * L ∧
          0 ≤ gradientBound i ∧ (∀ e ∈ Gi.E, |gradi e| ≤ gradientBound i) ∧
          (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
        (∀ (ω' : ℕ → Bool) levelTable i, i < C.d → ∀ vc ec before,
          let Gi := chain.G i
          let Hi := chain.G (i + 1)
          let leni := chain.toTreeChain.chainLen len₀ i
          let forest := T.lsfs (chain.scState i) 0
          RebuildSuffixAt Rcore chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 i vc ec
            4 L P before →
          InitLevelTablesSeparated levelTable C.d (before.regs 6) vc ec (before.regs 8) L →
          levelTable + (C.d + 1) + (C.d + 1) ≤ before.regs 4 →
          before.regs 4 + coreAlloc i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
          ∀ args,
            Runs w p ω' prepareRebuildGraphArgs
              { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
              .normal args 36 →
            (∀ mid top v e cost,
              Runs w p ω' (rebuildInstallReadGraph initCore (opCore 3)) args .normal mid cost →
              mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e Hi →
              mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
            (∀ mid c fv fe,
              Runs w p ω' (rebuildReadForest initCore (opCore 3) (opCore 2)) args .normal mid c →
              LSFAt mid.mem (mid.regs 9) fv fe 4 L P Gi.E forest →
              EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1)) 4 L P Gi.E leni) ∧
            (∀ s v e fv fe c,
              Runs w p ω' (rebuildReadForestLengths initCore (opCore 3) (opCore 2)) args .normal s c →
              DynGraphAt s.mem (s.regs 6) v e Hi →
              LSFAt s.mem (s.regs 9) fv fe 4 L P Gi.E forest →
              dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
              s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
              s.regs 7 + e * L ≤ s.regs 5 ∧ e ≤ ec ∧
              s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
              s.regs 5 + forest.T.n + fv * L + L + fv + fv +
                3 * L * forest.T.vol forest.T.V + ec * L + 3 * L * Hi.m < 2 ^ w)) →
        (∀ e ∈ (chain.G C.d).E, 2 * (2 : ℝ) ^ stretchP *
          lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen len₀ C.d) e <
            Num.capacity 4 L) →
        (∀ e ∈ (chain.G C.d).E, 0 < chain.toTreeChain.chainLen len₀ C.d e) →
        (∀ levelTable vc ec before,
          RebuildSuffixAt Rcore chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 C.d vc ec
            4 L P before →
          before.regs 4 +
            LastLevelProgram.packedRuntimeAllocation (chain.G C.d) guest C_lsst cLast L vc ec 1
              [before.regs 6, before.regs 7, L, P, before.regs 4] < 2 ^ w) →
        -- Numeric fit bounds for Detect thresholds and initial path-tree values
        (∀ e < I.m,
          let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
          let th := detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)
          Num.Fits 4 L (-th) ∧ Num.Fits 4 L th) →
        (∀ e ∈ chain.toTreeChain.chainTree.E,
          let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
          let v := initialPathEdgeValue P ε (gradInt e) (lenInt e)
          |v.gradient| ≤ B_tree ∧ |v.length| ≤ B_tree ∧ |v.flow| ≤ B_tree ∧ |v.detector| ≤ B_tree) →
        0 ≤ B_tree →
        2 * ((2 * G.n + 1 : ℕ) : ℤ) * (B_tree + 0) < (Num.capacity 4 L : ℤ) →
        -- Post-tail readout and room bounds
        (∀ i < C.d, 5 + (chain.toTreeChain.activeLSF i).F.F.m * linkSpace ≤ levelSpace) →
        (4 + (chain.toTreeChain.activeLSF C.d).F.F.m * linkSpace ≤ levelSpace) →
        (∀ (levelTable : ℕ) (afterLevels : State) (vcLast ecLast : ℕ),
          RebuiltCoresAt Rcore chain afterLevels.mem levelTable (levelTable + (C.d + 1)) 0 C.d (afterLevels.regs 4) →
          let treeHeap := afterLevels.regs 4 + (4 * (C.d + 1) + 1) + 1 + I.m + I.m + I.m
          let treeAlloc := LinkCut.PathProg.pathAlloc L
          treeHeap + treeAlloc 7 G.n [G.n, L, treeHeap] < 2 ^ w ∧
          ∀ treeEnd, treeHeap ≤ treeEnd → treeEnd ≤ treeHeap + treeAlloc 7 G.n [G.n, L, treeHeap] →
            let threshHeap := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m + I.m + I.m
            let afterThresh := threshHeap + 3 * L + I.m * initEdgeRecordSpace L
            afterThresh + (C.d + 1) * levelSpace < 2 ^ w ∧
            (∀ e ∈ chain.toTreeChain.chainTree.E, ∀ cur,
              afterThresh ≤ cur → cur ≤ afterThresh + (C.d + 1) * levelSpace →
              treeAlloc 0 G.n [treeHeap, G.tail e + 1, G.head e + 1,
                threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L, cur] ≤ linkSpace) ∧
            (∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret fv fe : ℕ) (yCore : Rcore.τ),
              afterThresh ≤ cur → cur ≤ ret →
              LSFAt mem' cur fv fe 4 L P (chain.G i).E (T.lsfs (chain.scState i) (chain.bran i)) →
              mem' (cur + 1) + dynGraphSize fv fe ≤ ret ∧
              ∀ a, mem' (cur + 1) ≤ a → a < mem' (cur + 1) + dynGraphSize fv fe →
                Rcore.foot (afterLevels.mem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)) ∧
            (∀ i < C.d, ∀ (mem' : ℕ → ℕ) (cur ret gv ge : ℕ) (yCore : Rcore.τ),
              afterThresh ≤ cur → cur ≤ ret →
              DynGraphAt mem' (mem' cur) gv ge (chain.G (i + 1)) →
              mem' cur + dynGraphSize gv ge ≤ ret ∧
              ∀ a, mem' cur ≤ a → a < mem' cur + dynGraphSize gv ge →
                Rcore.foot (afterLevels.mem (levelTable + i)) yCore a ∨ (cur ≤ a ∧ a < ret)) ∧
            (∀ (mem' : ℕ → ℕ) (cur ret fv fe : ℕ) (yTerm : ℕ),
              afterThresh ≤ cur → cur ≤ ret →
              LSFAt mem' cur fv fe 4 L P (chain.G C.d).E (chain.lastLSFs chain.lastBran) →
              mem' (cur + 1) + dynGraphSize fv fe ≤ ret ∧
              ∀ a, mem' (cur + 1) ≤ a → a < mem' (cur + 1) + dynGraphSize fv fe →
                (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E).foot
                  (afterLevels.mem (levelTable + C.d)) yTerm a ∨ (cur ≤ a ∧ a < ret))) →
        ∃ (out : State) (cost table a levelsEnd treeEnd finalHeap vcLast ecLast : ℕ)
          (sFin : PathTreeState) (yTree : Rtree.τ) (slotFin nameFin : ℕ → ℕ)
          (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
          let handle := table + (C.d + 1)
          let levelTable := handle + 17
          let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
          let forward := freshCounter + 1
          let inverse := forward + I.m
          let edgeThresholds := inverse + I.m
          let treeHeap := edgeThresholds + I.m
          let slots := treeEnd
          let names := treeEnd + I.m
          let slotThresholds := treeEnd + I.m + 2 * G.n
          let edgeRecords := treeEnd + I.m + 2 * G.n + 2 * G.n
          let offReadyList := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m
          let inOffReady := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m + I.m
          let threshHeap := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m + I.m + I.m
          let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
          let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
          let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
          let val := fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)
          Runs w p ω
            (solverInitConcreteFullProgram base quality threshold dLast decK thr cDeg witnessDen
              coefficient initCore (opCore 3) (opCore 2) retry degreeSetup inconclusive)
            (startState [graph, gradient, lengths, L, P, V, root] mem pos)
            (.returned finalHeap) out cost ∧
          SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
            slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady
            (root + 16 + (L + 1) + 6) I.m ∧
          DetectHeaderAt out.mem handle treeHeap names inverse slotThresholds I.m L
            (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
          MinRatioNumericHeaderAt out.mem handle L P
            (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
          ChainInitParametersAt out.mem handle I.m V C.d C.k Ψ (root + 16) k epsExp ∧
          FreshTablesAt out.mem forward inverse freshCounter I.m I.m id id I.m ∧
          (∀ j ≤ C.d, out.mem (table + j) =
              Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
            (out.mem (table + j) : ℝ) ≤
              Chain.SparseCoreTool.updateThreshold C.k
                (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
            Chain.SparseCoreTool.updateThreshold C.k
                (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
              48 * ((out.mem (table + j) : ℝ) + 1)) ∧
          (∀ addr, levelsEnd ≤ addr → addr < freshCounter → out.mem addr = 0) ∧
          (∀ e < I.m, out.mem (inOffReady + e) = 0) ∧
          (∀ e < I.m,
            out.mem (edgeThresholds + e) = thPtr e ∧
            out.mem (edgeRecords + e) = recPtr e ∧
            PathIntAt out.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
            PathEdgeAt out.mem (recPtr e) 4 L (some (val e))) ∧
          InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B_tree
            slots names slotThresholds I.m thPtr chain.toTreeChain.chainTree.E
            sFin yTree slotFin nameFin finalHeap out.mem ∧
          (∀ i < C.d, Rcore.rep (out.mem (levelTable + i)) (chain.scState i) (yCore i) out.mem ∧
            ∀ addr, Rcore.foot (out.mem (levelTable + i)) (yCore i) addr → addr < finalHeap) ∧
          (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E).rep
            (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm out.mem ∧
          (∀ addr, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E).foot
            (out.mem (levelTable + C.d)) yTerm addr → addr < finalHeap) ∧
          ZeroFrom out.mem finalHeap ∧ root ≤ finalHeap ∧
          (∀ x < root, out.mem x = mem x) ∧
          DynGraphAt out.mem (root + 16 + (L + 1) + 6) G.n I.m G ∧
          root + 16 + (L + 1) + 6 + dynGraphSize G.n I.m ≤ table ∧
          handle + 17 + (C.d + 1) + (C.d + 1) ≤ levelsEnd ∧
          treeHeap ≤ treeEnd ∧
          threshHeap + 3 * L + I.m * initEdgeRecordSpace L ≤ finalHeap ∧
          finalHeap < 2 ^ w ∧
          (∀ a, Rtree.foot treeHeap yTree a →
            OutsideInitSlotTables slots names slotThresholds I.m G.n a ∧
            ¬ InitChainStaticAddr (root + 16 + (L + 1) + 6) levelTable (levelTable + (C.d + 1))
              edgeRecords edgeThresholds C.d I.m L G chain.toTreeChain.chainTree recPtr
              (fun a => a < levelTable + (C.d + 1) + (C.d + 1) ∨
                (levelsEnd ≤ a ∧ a < treeHeap) ∨
                (edgeRecords + I.m ≤ a ∧ a < threshHeap + 3 * L + I.m * initEdgeRecordSpace L)) a) ∧
          InitChainCoresAt Rcore
            (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E) Rtree
            chain treeHeap levelTable (levelTable + (C.d + 1)) (root + 16 + (L + 1) + 6)
            edgeRecords edgeThresholds slots names slotThresholds I.m L finalHeap G recPtr
            (fun a => a < levelTable + (C.d + 1) + (C.d + 1) ∨
              (levelsEnd ≤ a ∧ a < treeHeap) ∨
              (edgeRecords + I.m ≤ a ∧ a < threshHeap + 3 * L + I.m * initEdgeRecordSpace L))
            yCore yTerm yTree out.mem := by
  obtain ⟨guest, cLast, KLast, CfLast, oracle, hSpecLast, hLastImpl⟩ :=
    LastLevelProgram.packedLastLevelProgram_implements
  let C_lsst := LastLevelProgram.graphCanonicalConstant KLast CfLast
  let dLast := ⌈max 1 C_lsst⌉₊
  let lastProg := LastLevelProgram.packedLastLevelProgram guest dLast cLast
  let lay := initConcreteLayout base
  obtain ⟨mult, hprefix⟩ :=
    solverInitFullPrefix_runs lay.alpha lay.precisionSelect quality lay.dgInitFromLists threshold
      lay.depth lay.clog dLast Kγ pathC Kint cw lay.factors decK thr cDeg witnessDen coefficient
      lay.power lay.extendCopy lay.multiply lay.shiftLeft lay.add q (dh + 5) hK hcDeg hWitness
  refine ⟨guest, cLast, KLast, CfLast, oracle, mult, hSpecLast, ?_⟩
  intro J E Rcore costs coreAlloc Mcap Ncap scanExponent nextGraphSizeCap gradientBound
    c graph gradient lengths root pos levelSpace linkSpace p ω mem qualityExponent qualityCharge
    retry degreeSetup inconclusive B_tree B w I V G k L P M T len₀ grad₀ lenInt gradInt
    hJn hJm hcap hIvalid hk hrootPow hqw hcmult hM fmt C chain Ψ den cap growth epsExp stretchP Rtree
    hbundle hqual hGraph hGraphBelow hLenEnd hGradEnd hVecValid hz
    hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree
    hlocal hdW hkW hnWord hnFit hNconst hValidLast hConnLast hnLast
    hcoreImpl hcoreInput ⟨σ, σ_mwu, γ_ℓ, γ_c, hH⟩ hmodel hreadout hstretch hposLast hspaceLast
    hfits hvalB hBnonneg hcapB hlevelCap hlastCap hpostRoom
  have hfit := IPM.Machine.ipm_quality_parameter_words_fit I.m V k hqw
  have hw14 : 14 ≤ w := hfit.1
  have hw17 : 17 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 17 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hw16 : 16 < 2 ^ w := lt_trans (by decide : 16 < 17) hw17
  have hw9 : 9 < 2 ^ w := lt_trans (by decide : 9 < 16) hw16
  obtain ⟨hPdiv, hLpos, hleEps, hfitEps⟩ := ipmQuality_precision_arith I.m V k
  have hWidth4 : P ≤ 4 * L := by
    dsimp only [L, P, IPM.Machine.ipmQualityLimbs]; omega
  have hGm : G.m = I.m := IPM.namedInstance_m I
  have hB2 : 2 ≤ B := Nat.le_add_left 2 _
  have hroot16Pow : root + 16 ≤ B ^ (dh + 5) := root_add16_pow_bound hB2 hrootPow
  -- Discharge ALL concrete helper contracts from `initConcreteHelperProcs_meetsAll`
  obtain ⟨hcopy, hadd, hneg, _, hshift, hext, hmul, hdiv, halpha, hselect, hdepthProc, hclog,
      hfactorImpl, hpower, hsort, hdgAll, hentry, hbind, htreeAll, hlastAt⟩ :=
    initConcreteHelperProcs_meetsAll (Kγ := Kγ) (pathC := pathC) (Kint := Kint) (cw := cw) hw14 hbundle
  have hpack := hdgAll G.n G.m G (G.V.sort (· ≤ ·))
    ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))
  have htreeImpl := htreeAll fmt L rfl
  have htermImpl : ∀ vc ec,
      (LastLevelProgram.lastLevelRepresentation vc ec 4 L P (chain.G C.d).E).Implements
        w p (lay.lastLevel + 15) (fun _ => lay.lastLevel + 16)
        (lastLevelRuntimeMachineContract fmt L (LastLevelProgram.fixedPointLastLevelTool oracle C_lsst)
          (chain.G C.d) vc ec
          (LastLevelProgram.packedLastLevelMultiplier guest cLast dLast KLast (chain.G C.d) L)
          stretchP
          (LastLevelProgram.packedRuntimeAllocation (chain.G C.d) guest C_lsst cLast L vc ec)) := by
    intro vc ec
    have h0 := hLastImpl (L := L) (vCap := vc) (eCap := ec) fmt (chain.G C.d) rfl hConnLast hnLast
    exact dsRep_implements_shift hlastAt h0
  have hLenMem : EdgeValuesAt mem lengths 4 L P G.E len₀ := fun e he =>
    ⟨(hVecValid e (Finset.mem_range.mp he)).1, by
      dsimp only [len₀, IPM.Machine.readVector]; simp [Finset.mem_range.mp he]⟩
  have hGradMem : EdgeValuesAt mem gradient 4 L P G.E grad₀ := fun e he =>
    ⟨(hVecValid e (Finset.mem_range.mp he)).2.2, by
      dsimp only [grad₀, IPM.Machine.readVector]; simp [Finset.mem_range.mp he]⟩
  have hlenIntMem : ∀ e < I.m, 0 < lenInt e ∧ PathIntAt mem (lengths + e * L) 4 L (lenInt e) := by
    intro e he
    obtain ⟨hv, hpos, _⟩ := hVecValid e he
    have htoNat : ((lenInt e : ℕ) : ℤ) = Num.intVal mem (lengths + e * L) 4 L :=
      Int.toNat_of_nonneg (le_of_lt hpos)
    exact ⟨by dsimp only [lenInt]; omega, ⟨hv, htoNat.symm⟩⟩
  have hgradIntMem : ∀ e < I.m, PathIntAt mem (gradient + e * L) 4 L (gradInt e) := fun e he =>
    ⟨(hVecValid e he).2.2, rfl⟩
  -- Define the final postcondition over the `solverInitFullPrefix_runs` continuation
  let Post (table a : ℕ) (out : State) : Prop :=
    ∃ (levelsEnd treeEnd finalHeap vcLast ecLast : ℕ)
      (sFin : PathTreeState) (yTree : Rtree.τ) (slotFin nameFin : ℕ → ℕ)
      (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
      let handle := table + (C.d + 1)
      let levelTable := handle + 17
      let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
      let forward := freshCounter + 1
      let inverse := forward + I.m
      let edgeThresholds := inverse + I.m
      let treeHeap := edgeThresholds + I.m
      let slots := treeEnd
      let names := treeEnd + I.m
      let slotThresholds := treeEnd + I.m + 2 * G.n
      let edgeRecords := treeEnd + I.m + 2 * G.n + 2 * G.n
      let offReadyList := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m
      let inOffReady := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m + I.m
      let threshHeap := treeEnd + I.m + 2 * G.n + 2 * G.n + I.m + I.m + I.m
      let ε := ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P
      let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
      let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
      let val := fun e => initialPathEdgeValue P ε (gradInt e) (lenInt e)
      out.regs 99 = finalHeap ∧ root + 16 < 2 ^ w ∧
      SolverRootDirAt out.mem root handle table levelsEnd forward inverse freshCounter
        slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady
        (root + 16 + (L + 1) + 6) I.m ∧
      DetectHeaderAt out.mem handle treeHeap names inverse slotThresholds I.m L
        (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      MinRatioNumericHeaderAt out.mem handle L P
        (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      ChainInitParametersAt out.mem handle I.m V C.d C.k Ψ (root + 16) k epsExp ∧
      FreshTablesAt out.mem forward inverse freshCounter I.m I.m id id I.m ∧
      (∀ j ≤ C.d, out.mem (table + j) =
          Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
        (out.mem (table + j) : ℝ) ≤
          Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
          48 * ((out.mem (table + j) : ℝ) + 1)) ∧
      (∀ addr, levelsEnd ≤ addr → addr < freshCounter → out.mem addr = 0) ∧
      (∀ e < I.m, out.mem (inOffReady + e) = 0) ∧
      (∀ e < I.m,
        out.mem (edgeThresholds + e) = thPtr e ∧
        out.mem (edgeRecords + e) = recPtr e ∧
        PathIntAt out.mem (thPtr e) 4 L (detectorThreshold P ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
        PathEdgeAt out.mem (recPtr e) 4 L (some (val e))) ∧
      InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree val B_tree
        slots names slotThresholds I.m thPtr chain.toTreeChain.chainTree.E
        sFin yTree slotFin nameFin finalHeap out.mem ∧
      (∀ i < C.d, Rcore.rep (out.mem (levelTable + i)) (chain.scState i) (yCore i) out.mem ∧
        ∀ addr, Rcore.foot (out.mem (levelTable + i)) (yCore i) addr → addr < finalHeap) ∧
      (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E).rep
        (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) yTerm out.mem ∧
      (∀ addr, (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E).foot
        (out.mem (levelTable + C.d)) yTerm addr → addr < finalHeap) ∧
      ZeroFrom out.mem finalHeap ∧ root ≤ finalHeap ∧
      (∀ x < root, out.mem x = mem x) ∧
      DynGraphAt out.mem (root + 16 + (L + 1) + 6) G.n I.m G ∧
      root + 16 + (L + 1) + 6 + dynGraphSize G.n I.m ≤ table ∧
      handle + 17 + (C.d + 1) + (C.d + 1) ≤ levelsEnd ∧
      treeHeap ≤ treeEnd ∧
      threshHeap + 3 * L + I.m * initEdgeRecordSpace L ≤ finalHeap ∧
      finalHeap < 2 ^ w ∧
      (∀ a, Rtree.foot treeHeap yTree a →
        OutsideInitSlotTables slots names slotThresholds I.m G.n a ∧
        ¬ InitChainStaticAddr (root + 16 + (L + 1) + 6) levelTable (levelTable + (C.d + 1))
          edgeRecords edgeThresholds C.d I.m L G chain.toTreeChain.chainTree recPtr
          (fun a => a < levelTable + (C.d + 1) + (C.d + 1) ∨
            (levelsEnd ≤ a ∧ a < treeHeap) ∨
            (edgeRecords + I.m ≤ a ∧ a < threshHeap + 3 * L + I.m * initEdgeRecordSpace L)) a) ∧
      InitChainCoresAt Rcore
        (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E) Rtree
        chain treeHeap levelTable (levelTable + (C.d + 1)) (root + 16 + (L + 1) + 6)
        edgeRecords edgeThresholds slots names slotThresholds I.m L finalHeap G recPtr
        (fun a => a < levelTable + (C.d + 1) + (C.d + 1) ∨
          (levelsEnd ≤ a ∧ a < treeHeap) ∨
          (edgeRecords + I.m ≤ a ∧ a < threshHeap + 3 * L + I.m * initEdgeRecordSpace L))
        yCore yTerm yTree out.mem
  obtain ⟨out, costPref, table, a, hrunPref, hpost⟩ :=
    hprefix J E (heap := root + 16) (Post := Post) hJn hJm hcap hIvalid hk hroot16Pow hqw hcmult hM
      hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
      hGraph (hGraphBelow.trans (Nat.le_add_right root 16))
      (fun x hx => hz x (le_trans (Nat.le_add_right root 16) hx))
      hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree
      (levels := buildSolverInitLevels initCore (opCore 3) (opCore 2) lay.copy lay.heapSort
          lay.writeGradCell (lay.lastLevel + 15) ;;
        finishSolverInitBody lay.pathTree ;;
        solverInitPostTailBody lay.shiftLeft lay.fixedDivide lay.negate lay.copy
          (opCore 2) (opCore 3) (lay.lastLevel + 16) (lay.pathTree + 1) lay.slotBind)
      (inconclusive := inconclusive)
      (fun table a header h74 h77 hroomH _ hzH hchainH hnumH htableH htableGe hGdgH
          _ _ _ hframeH h67H h68H h69H h70H h71H h75H => by
        let handle := table + (C.d + 1)
        let levelTable := handle + 17
        let rootGraph := root + 16 + (L + 1) + 6
        have hroot_le_lvl : root ≤ levelTable :=
          le_trans (Nat.le_add_right root 16)
            (le_trans (Nat.le_add_right _ _)
              (le_trans (Nat.le_add_right _ _)
                (le_trans (Nat.le_add_right _ _)
                  (le_trans htableGe (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))))
        have hLenH : EdgeValuesAt header.mem lengths 4 L P G.E len₀ :=
          hLenMem.congr (fun e he j hj =>
            hframeH (lengths + e * L + j) (lt_of_lt_of_le (vec_lt_root_of_le (hGm ▸ Finset.mem_range.mp he) hj hLenEnd) (Nat.le_add_right root 16)))
        have hGradH : EdgeValuesAt header.mem gradient 4 L P G.E grad₀ :=
          hGradMem.congr (fun e he j hj =>
            hframeH (gradient + e * L + j) (lt_of_lt_of_le (vec_lt_root_of_le (hGm ▸ Finset.mem_range.mp he) hj hGradEnd) (Nat.le_add_right root 16)))
        -- Step 1: build all C.d sparse cores + packed last-level structure
        obtain ⟨mid, levCost, hrLev, hcoresM, hbrM, hzeroM, hlevGe,
            ⟨vcLast, ecLast, xCoreDep, yTerm0, hdisjCoresM, htermCellLe, hrepTermM, hfootTermM⟩,
            hframeL, _⟩ :=
          buildSolverInitLevels_fixedPoint_capIndexed_runs (fmt := fmt) (ω := ω)
            (terminal := fun vc ec => LastLevelProgram.lastLevelRepresentation vc ec 4 L P (chain.G C.d).E)
            (lastAllocation := fun vc ec =>
              LastLevelProgram.packedRuntimeAllocation (chain.G C.d) guest C_lsst cLast L vc ec)
            oracle C_lsst scDepth sparsify (P := C) (R := Rcore)
            G len₀ grad₀ h77 h69H h71H h70H h75H h67H h68H hzH hroomH
            hGdgH hLenH hGradH
            (htableGe.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
            (hLenEnd.trans hroot_le_lvl) (hGradEnd.trans hroot_le_lvl)
            hfit.2.1 hfit.2.2.1 rfl hWidth4 hdW hkW hw9 hlocal hcopy hsort hentry
            hNconst hValidLast hcoreImpl htermImpl hmodel (fun ω' => hreadout ω' levelTable)
            hstretch hposLast (hspaceLast levelTable)
        have hg3 : 3 ≤ dynGraphSize G.n G.m := by unfold dynGraphSize; omega
        obtain ⟨hroot16W, _, hroot16LeG, hrootGLeTb, hh9LtLv, hrg2LtLv, hh16LtM, hrg2LtM,
            hnumLtLv, hchLt, hlvlBrLt, hrgLt, hcallerLt, htbLt⟩ :=
          wired_cont_arith htableGe hg3 hlevGe hroomH le_rfl le_rfl
        have hmMid : mid.mem (handle + 9) = I.m :=
          (hframeL (handle + 9) hh9LtLv).trans (by simpa [handle, Nat.add_assoc] using hchainH 0 (by simp))
        have hnMid : mid.mem (rootGraph + 2) = G.n :=
          (hframeL (rootGraph + 2) hrg2LtLv).trans hGdgH.2.2.2.2.2.1
        have hnumMid : MinRatioNumericHeaderAt mid.mem handle L P
            (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) := by
          intro j hj; have hj4 : j < 4 := by simpa [List.length] using hj
          exact (hframeL (handle + 5 + j) (hnumLtLv j hj4)).trans (hnumH j hj)
        have hchainMid : ChainInitParametersAt mid.mem handle I.m V C.d C.k Ψ (root + 16) k epsExp := by
          intro j hj; have hj8 : j < 8 := by simpa [List.length] using hj
          exact (hframeL (handle + 9 + j) (hchLt j hj8).1).trans (hchainH j hj)
        have h67M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h67H
        have h68M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h68H
        have h69M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h69H
        have h70M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h70H
        have h71M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h71H
        have h74M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h74
        have h75M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h75H
        -- Step 2: finishSolverInitBody (schedule, fresh tables, empty path tree, Detect header)
        obtain ⟨htreeSpaceM, hpostTailRoomM⟩ := hpostRoom levelTable mid vcLast ecLast hcoresM
        obtain ⟨mid2, tailCost, sTree, xTree, treeEnd, hrTail, h74M2, h80M2, h81M2, h82M2, h83M2,
            h84M2, h85M2, h99M2, hdetectM2, hnumM2, hschedM2, hfreshM2, hrepTreeM2, hinitTreePostM2,
            hzTreeEnd, htreeLeEnd, htreeEndLe, hfootTreeM2, hframeTail, _⟩ :=
          finishSolverInitBody_runs (fmt := fmt) (ω := ω) (st := mid)
            h74M h75M h69M h67M rfl hmMid hnMid hnumMid hzeroM
            hh16LtM hrg2LtM htreeImpl hfit.2.1 hfit.2.2.1 hnWord hnFit htreeSpaceM hw16
        obtain ⟨hpostAfterRoom, hpostLinkAlloc, hpostRF, hpostRG, hpostLastRF⟩ :=
          hpostTailRoomM treeEnd htreeLeEnd htreeEndLe
        have hlevTableLeM : levelTable ≤ mid.regs 4 :=
          le_trans (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) hlevGe
        have hmid2_keep_below (x : ℕ) (hx : x < levelTable) (hdisj : x < handle ∨ handle + 4 < x) :
            mid2.mem x = header.mem x :=
          (hframeTail x (lt_of_lt_of_le hx hlevTableLeM) hdisj).trans (hframeL x hx)
        have hmid2_lvl (i : ℕ) (hi : i ≤ C.d) : mid2.mem (levelTable + i) = mid.mem (levelTable + i) :=
          hframeTail (levelTable + i) (hlvlBrLt i hi).1 (Or.inr (hlvlBrLt i hi).2.1)
        have hmid2_br (i : ℕ) (hi : i ≤ C.d) : mid2.mem (levelTable + (C.d + 1) + i) = mid.mem (levelTable + (C.d + 1) + i) :=
          hframeTail (levelTable + (C.d + 1) + i) (hlvlBrLt i hi).2.2.1 (Or.inr (hlvlBrLt i hi).2.2.2)
        have hmid4_lt_w : mid.regs 4 < 2 ^ w :=
          lt_of_le_of_lt (le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_right _ _)
            (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _))
            (Nat.le_add_right _ _)) htreeSpaceM
        have hh4_lt_core : handle + 4 < levelTable + (C.d + 1) + (C.d + 1) :=
          lt_of_lt_of_le (lt_of_lt_of_le (Nat.add_lt_add_left (by decide : 4 < 17) handle) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)
        let xCoreFn : ℕ → Rcore.τ := fun i => if hi : i < C.d then xCoreDep i hi else xCoreDep 0 C.hd
        -- Step 3: solverInitPostTailBody (Detect thresholds, PathEdgeAt records, link chainTree, SolverRootDirAt)
        obtain ⟨out, finalHeap, postCost, sFin, yTree, slotFin, nameFin, yCore, yTerm, hrPost,
            hout99, hrootDirOut, hdetectOut, hnumOut, hchainOut, hfreshOut, hschedOut, hinOffOut,
            hedgesOut, hinvOut, hcoresOut, htermOut, htermFootOut, htableOut, hlvlBrOut, hcallerOut,
            hzFin, htreeEndLeFin, hdgOut, hafterLeFin, hfinLeRoom, htreeDisjOut, hcoresAtOut⟩ :=
          solverInitPostTailBody_runs (fmt := fmt) (ω := ω) (st := mid2)
            (Rcore := Rcore) (Rterm := LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G C.d).E)
            (Rtree := Rtree) (xCore := xCoreFn) (xTerm := yTerm0) (sTree := sTree) (xTree := xTree)
            lenInt gradInt B_tree rfl hH hshift hdiv hneg hcopy hbind hcoreImpl (htermImpl vcLast ecLast)
            htreeImpl hcoreInput
            ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h67M)
            ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h68M)
            ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h69M)
            ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h70M)
            ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h71M)
            h74M2 ((finishSolverInitBody_preserves_regs (by decide) (by decide) hrTail).trans h75M)
            h80M2 h81M2 h82M2 h83M2 h84M2 h85M2 h99M2
            rfl rfl hroot16LeG hrootGLeTb hlevGe rfl rfl rfl rfl htreeLeEnd
            (hGm ▸ hLenEnd) (hGm ▸ hGradEnd)
            (DynGraphAt.of_agree hGdgH (fun x hlo hhi =>
              hmid2_keep_below x (hrgLt x hlo hhi).1 (Or.inl (hrgLt x hlo hhi).2)))
            hGm hdetectM2 hnumM2
            (fun j hj => by
              have hj8 : j < 8 := by simpa [List.length] using hj
              exact (hframeTail (handle + 9 + j) (hchLt j hj8).2.1 (Or.inr (hchLt j hj8).2.2)).trans (hchainMid j hj))
            hfreshM2 hschedM2 hrepTreeM2 hinitTreePostM2 hfootTreeM2
            (fun i hi => by
              obtain ⟨hleI, hbrI, hrepI, hfootI⟩ := hdisjCoresM i hi
              have hxI : xCoreFn i = xCoreDep i hi := dite_eq_left hi
              rw [hmid2_lvl i hi.le, hmid2_br i hi.le, hxI]
              refine ⟨hbrI, ?_, fun a ha => ?_⟩
              · refine (hlocal _ _ _ mid.mem mid2.mem (fun a ha => ?_)).1 hrepI
                have hfa := hfootI a ha
                exact (hframeTail a hfa.2.1 (Or.inr (lt_of_lt_of_le hh4_lt_core hfa.1))).symm
              · have hfa := hfootI a ha
                refine ⟨hfa.1, hfa.2.1, fun j hj hne => ?_, ?_⟩
                · dsimp only [xCoreFn]; rw [hmid2_lvl j hj.le, dite_eq_left hj]; exact hfa.2.2.1 j hj hne
                · rw [hmid2_lvl C.d le_rfl]; exact hfa.2.2.2)
            ((hmid2_br C.d le_rfl).trans hbrM)
            (by
              rw [hmid2_lvl C.d le_rfl]
              refine ((LastLevelProgram.lastLevelRepresentation_local vcLast ecLast 4 L P (chain.G C.d).E)
                _ _ _ mid.mem mid2.mem (fun a ha => ?_)).1 hrepTermM
              have hfa := hfootTermM a ha
              exact (hframeTail a hfa.2.1 (Or.inr (lt_of_lt_of_le hh4_lt_core hfa.1))).symm)
            (fun a ha => by
              rw [hmid2_lvl C.d le_rfl] at ha
              have hfa := hfootTermM a ha
              refine ⟨hfa.1, hfa.2.1, fun j hj => ?_⟩
              dsimp only [xCoreFn]
              rw [hmid2_lvl j hj.le, dite_eq_left hj]
              exact hfa.2.2 j hj)
            (fun i hi => by
              rw [hmid2_lvl i hi, hmid2_br i hi]
              rcases Nat.lt_or_eq_of_le hi with hlt | rfl
              · obtain ⟨hleI, hbrI, _, _⟩ := hdisjCoresM i hlt
                have hbr0 : chain.bran i = 0 := (algorithm1_initialize_coreAt T (LastLevelProgram.fixedPointLastLevelTool oracle C_lsst) C Mcap (Ncap 0) G len₀ grad₀ i hlt).2.2
                exact ⟨lt_of_le_of_lt hleI hmid4_lt_w, by rw [hbrI, hbr0]; exact Nat.pos_of_ne_zero (by positivity)⟩
              · have hbr0 : chain.lastBran = 0 := rfl
                exact ⟨lt_of_le_of_lt htermCellLe hmid4_lt_w, by rw [hbrM, hbr0]; exact Nat.pos_of_ne_zero (by positivity)⟩)
            (fun e he => ⟨(hlenIntMem e he).1, (hlenIntMem e he).2.congr (fun j hj =>
              let a := lengths + e * L + j
              have ha : a < root := vec_lt_root_of_le he hj (hGm ▸ hLenEnd)
              (hmid2_keep_below a (hcallerLt a ha).1 (Or.inl (hcallerLt a ha).2)).trans
                (hframeH a (lt_of_lt_of_le ha (Nat.le_add_right root 16))))⟩)
            (fun e he => (hgradIntMem e he).congr (fun j hj =>
              let a := gradient + e * L + j
              have ha : a < root := vec_lt_root_of_le he hj (hGm ▸ hGradEnd)
              (hmid2_keep_below a (hcallerLt a ha).1 (Or.inl (hcallerLt a ha).2)).trans
                (hframeH a (lt_of_lt_of_le ha (Nat.le_add_right root 16)))))
            hfits hvalB hBnonneg hcapB hPdiv hfit.2.2.1 hLpos hleEps hfitEps
            hnWord hnFit hdW hw17 hzTreeEnd
            (fun i hi mem' cur ret fv fe yc hlo hle hlsf => by
              rw [hmid2_lvl i hi.le]; exact hpostRF i hi mem' cur ret fv fe yc hlo hle hlsf)
            (fun i hi mem' cur ret gv ge yc hlo hle hdg => by
              rw [hmid2_lvl i hi.le]; exact hpostRG i hi mem' cur ret gv ge yc hlo hle hdg)
            (fun mem' cur ret fv fe yt hlo hle hlsf => by
              rw [hmid2_lvl C.d le_rfl]; exact hpostLastRF mem' cur ret fv fe yt hlo hle hlsf)
            hlevelCap hlastCap hpostLinkAlloc hpostAfterRoom
        have hmid2_out_lvl (i : ℕ) (hi : i ≤ C.d) : out.mem (levelTable + i) = mid2.mem (levelTable + i) :=
          (hlvlBrOut i hi).1
        have hrootLeFin : root ≤ finalHeap :=
          le_trans hroot_le_lvl (le_trans hlevTableLeM
            (le_trans (le_trans (le_trans (le_trans (le_trans (Nat.le_add_right _ _)
              (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _)) (Nat.le_add_right _ _))
              (le_trans htreeLeEnd htreeEndLeFin)))
        refine ⟨out, levCost + (tailCost + postCost + 1) + 1,
          runs_seq_iff.mpr (Or.inr ⟨mid, levCost, tailCost + postCost + 1, hrLev,
            runs_seq_iff.mpr (Or.inr ⟨mid2, tailCost, postCost, hrTail, hrPost, rfl⟩), rfl⟩),
          mid.regs 4, treeEnd, finalHeap, vcLast, ecLast, sFin, yTree, slotFin, nameFin, yCore, yTerm,
          hout99, hroot16W, hrootDirOut, hdetectOut, hnumOut, hchainOut, hfreshOut, ?_,
          hschedOut, hinOffOut, hedgesOut, hinvOut, ?_, ?_, ?_, hzFin, hrootLeFin, ?_,
          hdgOut, hGm ▸ htableGe, hlevGe, htreeLeEnd, hafterLeFin,
          lt_of_le_of_lt hfinLeRoom hpostAfterRoom, htreeDisjOut, hcoresAtOut⟩
        · intro j hj
          have htj : out.mem (table + j) = header.mem (table + j) :=
            (htableOut j hj).trans (hmid2_keep_below (table + j) (htbLt j hj).1 (Or.inl (htbLt j hj).2))
          obtain ⟨h1, h2, h3⟩ := htableH j hj
          exact ⟨htj.trans h1, htj.symm ▸ h2, htj.symm ▸ h3⟩
        · intro i hi
          rw [hmid2_out_lvl i hi.le]; exact hcoresOut i hi
        · rw [hmid2_out_lvl C.d le_rfl]; exact htermOut
        · rw [hmid2_out_lvl C.d le_rfl]; exact htermFootOut
        · intro x hx
          exact (hcallerOut x hx).trans
            ((hmid2_keep_below x (hcallerLt x hx).1 (Or.inl (hcallerLt x hx).2)).trans
              (hframeH x (lt_of_lt_of_le hx (Nat.le_add_right root 16)))))
  obtain ⟨levelsEnd, treeEnd, finalHeap, vcLast, ecLast, sFin, yTree, slotFin, nameFin,
      yCore, yTerm, h99, hroot16W, hrest⟩ := hpost
  have hstep1 := startState_add16_step (w := w) (p := p) (ω := ω) (mem := mem) (pos := pos)
    (a0 := graph) (a1 := gradient) (a2 := lengths) (a3 := L) (a4 := P) (a5 := V) (root := root)
    hw16 hroot16W
  have hret : Runs w p ω (.ret (.reg 99)) out (.returned finalHeap) out 2 :=
    runs_ret_iff.mpr ⟨finalHeap, by simp [Expr.eval, h99], rfl, rfl, rfl⟩
  exact ⟨out, 4 + (costPref + 2 + 1) + 1, table, a, levelsEnd, treeEnd, finalHeap, vcLast, ecLast,
    sFin, yTree, slotFin, nameFin, yCore, yTerm,
    runs_seq_iff.mpr (Or.inr ⟨_, 4, costPref + 2 + 1, hstep1,
      runs_seq_iff.mpr (Or.inr ⟨out, costPref, 2, hrunPref, hret, rfl⟩), rfl⟩),
    hrest⟩

end MinCostFlow.MinRatio
