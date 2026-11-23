module

public import MinCostFlow.Final.AssemblyDryRunSCParamOpen
public import MinCostFlow.Final.AssemblyDryRunSCFits
public import MinCostFlow.Final.AssemblyDryRunSCConnected
public import MinCostFlow.MinRatio.LastLevelContractMono
public import MinCostFlow.MinRatio.LastLevelAllocBound
import MinCostFlow.Chain.Ordered.InitPreserves
import Mathlib.Tactic

/-!
# The second dry run with the proved fits, parameters and last level (`AssemblyDryRunSCOpen`)

`theorem_1_1_dry_run_sc` (`Final/AssemblyDryRunSC.lean`) takes the Init bridge hypotheses
`DrySCInitBridgeHyps`. This file proves five of them and states the dry run with the others.

* `hParam`: the parameter setup `dryParamProcs` meets `initParamSetupContract`
  (`dryParamSetup_discharges_hParam`). The inner code given as a parameter becomes `SolverInnerOpenNoParam`, which
  installs `dryParamProcs` at offset `0`.
* `hCoreLenFits`: the chain lengths of every level fit the fixed-point format when the input
  lengths lie on the `2 ^ (-P)` grid (`drySC_hCoreLenFits_onGrid`).
* `hLastStretchFits`: the stretch blocks of the last level fit, with the stretch precision
  `dryLastStretchP J`, which uses the edge count `I.m` (`drySC_hLastStretchFits_Im`).
* `hLastImpl` and `hLastSpaceLe`: the real last-level program `dryLastLevel_implements` meets the
  last-level contract at the last graph of the initial chain. That graph is connected and has
  `n ≤ m + 1` (`drySolver_init_level_n_le_m_add_one`) and at most `I.m` edges
  (`drySC_chainLen_bounds`). The program's multiplier, stretch precision and allocation depend on
  the graph. We replace them by bounds for every graph of this size
  (`lastLevelRuntime_implements_mono`): the multiplier by its maximum over all vertex and edge
  counts (`dryLastMultBound`), the precision by `dryLastStretchP J`, and the allocation by the
  number `dryLastSpace J`. The allocation depends on the graph only through its counts and those of
  its representative graph, and grows with them (`MinRatio/LastLevelAllocBound.lean`), so
  `dryLastSpace J` evaluates it at `I.m + 1` vertices, `I.m` edges and the cap limit
  (`drySC_lastAllocLe_proved`).

The other Init hypotheses are collected in `DrySCInitOpenHyps`: the space of the sparse-core
init (`hInitSpaceLe`), and the three size bounds into `sz`. The sparse-core contract at Init is
proved in `Final/AssemblyDryRunSCCoreKFBL.lean`, which also states the dry run with the
hypotheses `DrySCInitOpenHyps` (`theorem_1_1_dry_run_sc_open`).
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-! ## The last-level multiplier and stretch precision for every last graph -/

/-- The cost multiplier of the last-level program, maximized over all graphs with at most
`M + 1` vertices and at most `M` edges. The multiplier of a graph depends only on its vertex and
edge counts and on whether it has a non-loop edge, so a maximum over the finitely many counts
covers every such graph (`packedLastLevelMultiplier_le_dryLastMultBound`). -/
def dryLastMultBound (L M : ℕ) : ℕ :=
  ((Finset.range (M + 2)) ×ˢ (Finset.range (M + 1))).sup fun nm =>
    max (packedNonLoopDispatchMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK
        L nm.1 nm.2)
      (loopOnlyMultiplier L nm.1 nm.2 + (29 * nm.2 + 81) / 2)

/-- The last-level multiplier of a graph with at most `M + 1` vertices and at most `M` edges is at
most `dryLastMultBound L M`. -/
theorem packedLastLevelMultiplier_le_dryLastMultBound {G : MGraph} {L M : ℕ}
    (hn : G.n ≤ M + 1) (hm : G.m ≤ M) :
    packedLastLevelMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK G L ≤
      dryLastMultBound L M := by
  have hmem : (G.n, G.m) ∈ (Finset.range (M + 2)) ×ˢ (Finset.range (M + 1)) :=
    Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hle := Finset.le_sup (f := fun nm : ℕ × ℕ =>
    max (packedNonLoopDispatchMultiplier lastGuest lastWordConst ⌈max 1 lastCanonConst⌉₊ lastK
        L nm.1 nm.2)
      (loopOnlyMultiplier L nm.1 nm.2 + (29 * nm.2 + 81) / 2)) hmem
  unfold packedLastLevelMultiplier
  split_ifs
  · exact (le_max_left _ _).trans hle
  · exact (le_max_right _ _).trans hle

/-- The last-level multiplier of the dry run for the circulation `J`: the bound
`dryLastMultBound` at the limb count of the format and the terminal-level edge cap
`levelM cfg.TP cfg.P cfg.P.d` (which is subpolynomial in `I.m`). -/
def dryLastMult (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
  dryLastMultBound (ipmQualityLimbs I.m (solverPenalty J.m) k) (levelM cfg.TP cfg.P cfg.P.d)

/-- The stretch precision of the last level for the circulation `J`. It is the precision of
`dryLastLevel_implements` for a graph with `I.m` edges, so it covers every last graph with at most
`I.m` edges. It does not use the cap limit. -/
def dryLastStretchP (J : Circulation) : ℕ :=
  (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size

/-- The bound on the allocation of the last-level program: at the last graph of every
initial chain, and for every pair of capacities below the cap limit, the allocation of the
initialization is at most `lastSpace source J`. That graph is connected, has `n ≤ m + 1` and at
most `I.m` edges (see `drySC_hLastImpl_proved`). -/
def DryLastAllocLe (allocationCoefficient allocationDegree : ℕ)
    (lastSpace : Circulation → Circulation → ℕ) : Prop :=
  ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin (namedInstance I) F.rangeExponent ℓ₀ →
      let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
        (levelM cfg.TP cfg.P) cfg.N₀ (namedInstance I) ℓ₀ g₀).1
      ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
        packedRuntimeAllocation (chain.G cfg.P.d) lastGuest lastCanonConst lastWordConst F.limbs
          vc ec 1 [] ≤ lastSpace source J

/-- The space that the last level of the dry run reserves for the circulation `J`: the bound
`packedRuntimeAllocBound` at the limb count of the format, the edge count `I.m`, and the cap
limit for both capacities. -/
def dryLastSpace (J : Circulation) : ℕ :=
  let I := solverConnectedAugmented J
  let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
    (concreteQualityBudgetWithLast dryWitnessUsed) I.m
  packedRuntimeAllocBound lastGuest lastCanonConst lastWordConst
    (ipmQualityLimbs I.m (solverPenalty J.m) k) I.m (dryCapLimit dryWitnessUsed J)
    (dryCapLimit dryWitnessUsed J)

/-- **The allocation bound of the last level.** At the last graph of every initial chain, and for
every pair of capacities below the cap limit, the allocation of the last-level program is at most
`dryLastSpace J`. That graph has at most `I.m` edges (`drySC_chainLen_bounds`) and at most one
vertex more than edges (`drySolver_init_level_n_le_m_add_one`), so this is
`packedRuntimeAllocation_le_bound`. -/
theorem drySC_lastAllocLe_proved (allocationCoefficient allocationDegree : ℕ) :
    DryLastAllocLe allocationCoefficient allocationDegree (fun _ J => dryLastSpace J) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg ℓ₀ g₀ hLen chain vc ec hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ (namedInstance I).E, 0 < ℓ₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ (namedInstance I).E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  obtain ⟨-, hnm⟩ :=
    drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR cfg.P.d le_rfl
  obtain ⟨-, -, hEsub, -, -⟩ :=
    drySC_chainLen_bounds J hJn hJm hCap1 ℓ₀ g₀ hLen cfg.P.d le_rfl
  have hm : (chain.G cfg.P.d).m ≤ I.m :=
    le_trans (Finset.card_le_card hEsub) (namedInstance_m I).le
  have hnm' : (chain.G cfg.P.d).n ≤ (chain.G cfg.P.d).m + 1 := hnm
  exact packedRuntimeAllocation_le_bound (chain.G cfg.P.d) lastGuest lastCanonConst
    (by omega) hm (by omega) (by omega) 1 []

/-- **`hLastImpl` from the real last-level program.** At the last graph of the initial chain, the
last-level bodies of the dry run implement the last-level contract with the multiplier
`dryLastMult J`, the stretch precision `dryLastStretchP J` and the constant allocation
`lastSpace source J`, given the allocation bound `DryLastAllocLe`. -/
theorem drySC_hLastImpl_proved (Psc : DrySparseCorePieces) (openInner : SolverInnerOpen)
    (allocationCoefficient allocationDegree : ℕ) (lastSpace : Circulation → Circulation → ℕ)
    (hAllocLe : DryLastAllocLe allocationCoefficient allocationDegree lastSpace) :
    ForAllDryInputs dryWitnessUsed allocationCoefficient allocationDegree fun source J hw =>
      let I := solverConnectedAugmented J
      let V := solverPenalty J.m
      let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) I.m
      let F := ipmQualityMinRatioFormat I.m V k hw
      let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
      let G := namedInstance I
      let w := dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source
      let p := dryLinkedProgram dryWitnessUsed Psc.sc openInner.toInnerCode
      let lay := dryTailLay Psc.sc openInner.toInnerCode
      ∀ (ℓ₀ g₀ : ℕ → ℝ), IPM.LengthsWithin G F.rangeExponent ℓ₀ →
        let chain := (Chain.Ordered.algorithm1_initialize cfg.T cfg.L cfg.P
          (levelM cfg.TP cfg.P) cfg.N₀ G ℓ₀ g₀).1
        ∀ vc ec, vc + ec + 2 ≤ dryCapLimit dryWitnessUsed J →
          (lastLevelRepresentation vc ec 4 F.limbs F.fmt.precision (chain.G cfg.P.d).E).Implements
            w p lay.lastInit lay.lastOp
            (lastLevelRuntimeMachineContract F.fmt F.limbs dryLastTool (chain.G cfg.P.d) vc ec
              (dryLastMult J) (dryLastStretchP J) (fun _ _ => lastSpace source J)) := by
  intro source J hJn hJm hCost hCap hw I V k F cfg G w p lay ℓ₀ g₀ hLen chain vc ec hcap
  have hCap1 : ∀ e, 1 ≤ J.capacity e := fun e => (hCap e).1
  have hEΨ : (F.rangeExponent : ℝ) ≤ cfg.Ψ := by
    change ((ipmQualityRangeExponent I.m V k : ℕ) : ℝ) ≤
      ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
    exact_mod_cast (by omega)
  have hlPos : ∀ e ∈ G.E, 0 < ℓ₀ e := fun e he =>
    lt_of_lt_of_le (by positivity) (hLen e he).1
  have hlR : ∀ e ∈ G.E, |Real.log (ℓ₀ e)| ≤ cfg.Ψ := fun e he =>
    (abs_log_le_of_two_pow_bounds (hLen e he).1 (hLen e he).2).trans hEΨ
  obtain ⟨hconn, hnm⟩ :=
    drySolver_init_level_n_le_m_add_one J hJn hJm hCap1 g₀ ℓ₀ hlPos hlR cfg.P.d le_rfl
  obtain ⟨-, -, hEsub, -, -⟩ :=
    drySC_chainLen_bounds J hJn hJm hCap1 ℓ₀ g₀ hLen cfg.P.d le_rfl
  have hm : (chain.G cfg.P.d).m ≤ (solverConnectedAugmented J).m :=
    le_trans (Finset.card_le_card hEsub) (namedInstance_m I).le
  have hmD : (chain.G cfg.P.d).m ≤ levelM cfg.TP cfg.P cfg.P.d := by
    have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
    have hGV := namedInstance_valid I
      (connectedInitialInstance_valid J.toInstance (V : ℤ) J.toInstance_valid)
    obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
      (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
    have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
    have hnG : G.n ≤ cfg.N₀ := by
      have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
      rw [hInEq]; exact hIn
    have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G ℓ₀ := by
      intro e he
      have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
      rw [abs_le] at hlog
      exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
        by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
    have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G ℓ₀ g₀ hGV hmG hnG hℓ
    have hLvl := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
      hV.hTP hV.hγM₀ hV.hγk hInit.1 cfg.P.d le_rfl
    exact_mod_cast hLvl.2.2.1
  have hnm' : (chain.G cfg.P.d).n ≤ (chain.G cfg.P.d).m + 1 := hnm
  have hfmt : F.fmt.limbBits = 4 := rfl
  refine lastLevelRuntime_implements_mono
    (dryLastLevel_implements (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) _ Psc.sc openInner.toInnerCode _
      F.fmt (chain.G cfg.P.d) hfmt hconn hnm) ?_ ?_ ?_
  · exact packedLastLevelMultiplier_le_dryLastMultBound (le_trans hnm' (Nat.add_le_add_right hmD 1)) hmD
  · have hsz := Nat.size_le_size (Nat.add_le_add_right hm 1)
    change (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((chain.G cfg.P.d).m + 1).size ≤
      (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * ((solverConnectedAugmented J).m + 1).size
    omega
  · intro _
    exact hAllocLe source J hJn hJm hCost hCap hw ℓ₀ g₀ hLen vc ec hcap

/-! ## The other Init bridge hypotheses -/

/-- The Init bridge hypotheses of the second dry run other than the parameter setup,
the fits, the last level and the sparse-core contract, which are proved: the space of the sparse-core
init (`hInitSpaceLe`), and the three size bounds into `sz`. The parameter space and cost are
those of `dryParamProcs`, the last-level multiplier is `dryLastMult`, and the last-level space is
`dryLastSpace`. -/
structure DrySCInitOpenHyps (Psc : DrySparseCorePieces) (rem : SolverInnerOpenNoParam)
    (B : OrdSolverInnerBounds) (hB : InnerBoundsHyp B)
    (sz : Circulation → Circulation → WiredInnerSizes) where
  coreInitSpace : Circulation → Circulation → ℕ → ℕ
  hInitSpaceLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let depth := Expander.chosenL (max I.m (concreteEdgeThresholdWithLast dryWitnessUsed) ^ 2)
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    DrySCInitSpaceLe (drySCAlloc Psc dryCapExp limbMul J) (coreInitSpace source J) cfg.P.d
      cfg.P.k cfg.N₀ F.limbs F.fmt.precision depth (levelM cfg.TP cfg.P)
  hSpaceLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    initConcreteSpace I.m (namedInstance I).n F.limbs cfg.P.d (dryParamSpace source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (dryLastSpace J)
      (LinkCut.PathProg.arenaEnd 0 (namedInstance I).n F.limbs)
      (20 * LinkCut.PathProg.treeLimbs F.limbs + 100)
      (coreInitSpace source J) (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initSpace'
  hFixedLe : ForAllDryInputs dryWitnessUsed (dryAllocCoeffFull B hB) (dryAllocDeg B hB) fun source J hw =>
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let limbMul := concreteReadout2LimbMul dryWitnessUsed
    initConcreteFixed I.m (namedInstance I).n F.limbs cfg.P.d (dryParamCost source J) dryCapExp
      (dryCapLimit dryWitnessUsed J) (dryLastMult J) LinkCut.PathProg.pathC
      (drySCParams Psc dryCapExp limbMul)
      (levelM cfg.TP cfg.P) (fun i => levelM cfg.TP cfg.P (i + 1)) cfg.N₀ ≤
    (sz source J).initFixed
  hMulLe : ∀ source J,
    max (drySCParams Psc dryCapExp (concreteReadout2LimbMul dryWitnessUsed)).mul (dryLastMult J) ≤
      (sz source J).toolMul

end MinCostFlow.Final.DryRun

end
