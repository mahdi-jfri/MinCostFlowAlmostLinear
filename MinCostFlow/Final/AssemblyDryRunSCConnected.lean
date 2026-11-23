module

public import MinCostFlow.Final.AssemblyDryRunSC
public import MinCostFlow.MinRatio.OrdSolverReached
import MinCostFlow.Chain.Ordered.ShiftLoopLevels
import MinCostFlow.Chain.Ordered.InitPreserves
import MinCostFlow.Chain.Ordered.ShiftPreserves
import MinCostFlow.Chain.Ordered.RenameFacts
import MinCostFlow.IPM.ConnectedInitialConstruction
import Mathlib.Tactic

/-!
# Connectedness and `G.n ≤ G.m + 1` for every graph the solver passes to the sparse core

Supplies the solver-input fact required by `drySCRepAt_implements_level`
(`Final/AssemblyDryRunSC.lean`) and `SparseCoreOrdProgramUniformBridged`
(`SparseCore/Program/AssemblyBridge.lean`): every level graph `G` passed by Algorithm 2 to the
sparse-core tool (at `Init`, on every reached state `OrdSolverReached`, after `Update`'s chain
refresh `alg2PreLoopState`, and after any `algorithm1_shift` step) is connected and satisfies
`G.n ≤ G.m + 1`.

The argument uses `Chain.Ordered.ChainInv.levels_connected` (`Chain/Ordered/ShiftLoopLevels.lean`),
which lifts `connected_n_le_m_add_one` and `isSparsifiedCoreGraph_connected` to the ordered chain
invariant, and combines it with `FreshInv.connected` and
`IPM.connectedInitialInstance_connected`, and specializes `drySCRepAt_implements_level` to
discharge `hGn_le` automatically (`drySCRepAt_implements_init_level`,
`drySCRepAt_implements_reached_level`, `drySCRepAt_implements_preLoop_level`).
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow.Bundle Chain IPM IPM.Machine SparseCore SparseCore.Program Scaling
  Scaling.Machine MinRatio

/-! ## Level connectedness and `n ≤ m + 1` for the ordered chain -/

/-- At `Chain.Ordered.algorithm2_init`, if `G` is valid, connected, and has lengths in range
of `cfg.Ψ`, then every level graph `(chain.G i)` (`i ≤ cfg.P.d`) is connected and satisfies
`(chain.G i).n ≤ (chain.G i).m + 1`. -/
theorem ordAlgorithm2_init_level_connected {cfg : Alg2Config} {G : MGraph} {g l : ℕ → ℝ}
    (hV : cfg.ValidOrdNoHidden) (hGV : G.IsValid) (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    (hlPos : ∀ e ∈ G.E, 0 < l e) (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ) :
    let chain := (Chain.Ordered.algorithm2_init cfg G g l).chain
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (chain.G i).V, ∀ v ∈ (chain.G i).V, (chain.G i).Connected u v) ∧
      (chain.G i).n ≤ (chain.G i).m + 1 := by
  have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) G l := by
    intro e he
    have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk G l g hGV hmG hnG hℓ
  dsimp only at hInit
  rcases hInit with ⟨hInv, _, hG0, _, _, _, _, _, _, _⟩
  exact Chain.Ordered.ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hInv (by
    dsimp only [Chain.Ordered.algorithm2_init]; rw [hG0]; exact hConn)

/-- On every reached state `OrdSolverReached cfg κ G model` with connected `G`, every level graph
`model.chain.G i` (`i ≤ cfg.P.d`) is connected and satisfies
`(model.chain.G i).n ≤ (model.chain.G i).m + 1`. -/
theorem ordSolverReached_level_connected {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) :
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (model.chain.G i).V, ∀ v ∈ (model.chain.G i).V, (model.chain.G i).Connected u v) ∧
      (model.chain.G i).n ≤ (model.chain.G i).m + 1 := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have hUI := (Chain.Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl
  rw [← hm] at hUI
  rcases hUI with ⟨hInv, _, _, _, hFresh, hExtG, _, _, _, _, _, _, _, _, _⟩
  have hConnExt : ∀ u ∈ model.extG.V, ∀ v ∈ model.extG.V, model.extG.Connected u v := by
    rw [hExtG, hG T le_rfl]; exact hConn
  exact Chain.Ordered.ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hInv (hFresh.connected hConnExt)

/-- Before the shift loop of an `Update` (`alg2PreLoopState`), every level graph of the refreshed
chain (`i ≤ cfg.P.d`) is connected and satisfies `.n ≤ .m + 1`. -/
theorem ordSolverReached_preLoop_level_connected {cfg : Alg2Config} {κ : ℝ} {G : MGraph}
    {model : Alg2State cfg} (h : OrdSolverReached cfg κ G model) (hV : cfg.ValidOrdNoHidden)
    (hmG : G.m ≤ cfg.P.M₀) (hnG : G.n ≤ cfg.N₀)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v)
    {U : List Update} {g l : ℕ → ℝ} (hU : RefreshBatch G U)
    (hl : ∀ e ∈ G.E, 0 < l e) (hlR : ∀ e ∈ G.E, |Real.log (l e)| ≤ cfg.Ψ)
    (hagree : ∀ e ∈ G.E, (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    let chain := (alg2PreLoopState cfg model U g l).chain
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (chain.G i).V, ∀ v ∈ (chain.G i).V, (chain.G i).Connected u v) ∧
      (chain.G i).n ≤ (chain.G i).m + 1 := by
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  obtain ⟨hgx, hlx⟩ := OrdSolverReached.ext hHist hm
  have hEdgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := by
    intro u hu
    have := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd this id
  have hV' := histSnoc_valid (b := true) hHist (hG T le_rfl) hU.1 hU.2.1 hl
    (fun h => absurd h (by decide)) (fun e he hnot => by rw [← hgx, ← hlx]; exact hagree e he hnot)
  have hG' : ∀ t ≤ T + 1, (histSnoc D T G U g l).G t = G := by
    intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT; simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]; exact hG t hle
  have hInv := Chain.Ordered.alg2_preLoop_chainInv_with (η := seqSnoc η T 0) κ hV hV'
    (histSnoc_edgeOnly hE hEdgeU) (histSnoc_lengths hL hlR)
    (fun t ht => by rw [hG' t ht]; exact hmG) (fun t ht => by rw [hG' t ht]; exact hnG) T le_rfl
  dsimp only at hInv
  rw [minRatioFailState_snoc_of_le _ D η op T G U g l 0 true T le_rfl, ← hm] at hInv
  simp only [histSnoc, seqSnoc_succ] at hInv
  have hUI := (Chain.Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl
  rw [← hm] at hUI
  rcases hUI with ⟨_, _, _, _, hFresh, hExtG, _, _, _, _, _, _, _, _, _⟩
  have hExtEq : model.extG = G := hExtG.trans (hG T le_rfl)
  have hTB := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh (hExtEq.symm ▸ hU.1)
  have hRen := Chain.Ordered.update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain g l
    hTB.2.1
  have hConnExt' : ∀ u ∈ (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).1.V,
      ∀ v ∈ (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).1.V,
        (translateBatch model.extG model.extToInt model.intToExt model.nextFresh U).1.Connected u v := by
    rw [hTB.1, hExtEq, hU.2.1]; exact hConn
  exact Chain.Ordered.ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hInv (hRen.1.connected hConnExt')

/-- Across any `Chain.Ordered.algorithm1_shift` step from a chain satisfying `ChainInv` with
connected level-`0` graph, every level graph of the shifted chain (`i ≤ cfg.P.d`) is connected
and satisfies `.n ≤ .m + 1`. -/
theorem ordAlgorithm1_shift_level_connected {cfg : Alg2Config} {st : ChainState cfg.T cfg.P}
    {overflow : ℝ} (hV : cfg.ValidOrdNoHidden)
    (hInv : Chain.Ordered.ChainInv cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀ st)
    (hℓR : Chain.Ordered.LenInRange (max 0 cfg.Ψ) (st.G 0) st.ℓ)
    (hBudget : Chain.Ordered.ChainBudgetInvWith cfg.TP cfg.LP cfg.N₀ st overflow)
    (hConn0 : ∀ u ∈ (st.G 0).V, ∀ v ∈ (st.G 0).V, (st.G 0).Connected u v)
    (i₀ : ℕ) (hi₀ : i₀ ≤ cfg.P.d) :
    let st' := (Chain.Ordered.algorithm1_shift cfg.T cfg.L cfg.P st i₀).1
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (st'.G i).V, ∀ v ∈ (st'.G i).V, (st'.G i).Connected u v) ∧
      (st'.G i).n ≤ (st'.G i).m + 1 := by
  have hSh := Chain.Ordered.shift_preserves_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk hInv hℓR hBudget i₀ hi₀
  dsimp only at hSh
  rcases hSh with ⟨hInv', _, hG0', _, _, _, _, _, _⟩
  exact Chain.Ordered.ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hInv' (by rw [hG0']; exact hConn0)

/-! ## Concrete dry-run corollaries matching `drySCRepAt_implements_level` -/

/-- The augmented solver graph `namedInstance (solverConnectedAugmented J)` is connected on its
vertex set. -/
theorem drySolverGraph_connected (J : Circulation) :
    let G := namedInstance (solverConnectedAugmented J)
    ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v :=
  connectedInitialInstance_connected J.toInstance (solverPenalty J.m : ℤ)

/-- At `Init` in the dry run (`concreteCirculationCfgWithLast dryWitnessUsed J`), every level graph
`chain.G i` (`i ≤ cfg.P.d`, including the terminal graph `chain.G cfg.P.d`) is connected and
satisfies `(chain.G i).n ≤ (chain.G i).m + 1`. -/
theorem drySolver_init_level_n_le_m_add_one (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (g l : ℕ → ℝ)
    (hlPos : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let chain := (Chain.Ordered.algorithm2_init cfg (namedInstance (solverConnectedAugmented J)) g l).chain
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (chain.G i).V, ∀ v ∈ (chain.G i).V, (chain.G i).Connected u v) ∧
      (chain.G i).n ≤ (chain.G i).m + 1 := by
  intro cfg chain
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV := namedInstance_valid (solverConnectedAugmented J)
    (connectedInitialInstance_valid J.toInstance (solverPenalty J.m : ℤ) J.toInstance_valid)
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤ cfg.N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  exact ordAlgorithm2_init_level_connected hV hGV hmG hnG (drySolverGraph_connected J) hlPos hlR

/-- On every reached solver state in the dry run, every level graph `model.chain.G i`
(`i ≤ cfg.P.d`) is connected and satisfies `(model.chain.G i).n ≤ (model.chain.G i).m + 1`. -/
theorem drySolver_reached_level_n_le_m_add_one (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model) :
    ∀ i ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (∀ u ∈ (model.chain.G i).V, ∀ v ∈ (model.chain.G i).V, (model.chain.G i).Connected u v) ∧
      (model.chain.G i).n ≤ (model.chain.G i).m + 1 := by
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  exact ordSolverReached_level_connected h hV hmG hnG (drySolverGraph_connected J)

/-- Before the shift loop of an `Update` in the dry run, every level graph of
`(alg2PreLoopState cfg model U g l).chain` (`i ≤ cfg.P.d`) is connected and satisfies
`.n ≤ .m + 1`. -/
theorem drySolver_preLoop_level_n_le_m_add_one (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model)
    {U : List Update} {g l : ℕ → ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U)
    (hl : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let chain := (alg2PreLoopState cfg model U g l).chain
    ∀ i ≤ cfg.P.d,
      (∀ u ∈ (chain.G i).V, ∀ v ∈ (chain.G i).V, (chain.G i).Connected u v) ∧
      (chain.G i).n ≤ (chain.G i).m + 1 := by
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  exact ordSolverReached_preLoop_level_connected h hV hmG hnG (drySolverGraph_connected J)
    hU hl hlR hagree

/-- At `Init` in the dry run, every level graph `chain.G i` (`i ≤ cfg.P.d`) has at most
`(solverConnectedAugmented J).m` edges. -/
theorem drySolver_init_level_m_le (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    (g l : ℕ → ℝ)
    (hlPos : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let chain := (Chain.Ordered.algorithm2_init cfg (namedInstance (solverConnectedAugmented J)) g l).chain
    ∀ i ≤ cfg.P.d, (chain.G i).m ≤ (solverConnectedAugmented J).m := by
  intro cfg chain i hi
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  have hGV := namedInstance_valid (solverConnectedAugmented J)
    (connectedInitialInstance_valid J.toInstance (solverPenalty J.m : ℤ) J.toInstance_valid)
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤ cfg.N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  have hℓ : Chain.Ordered.LenInRange (max 0 cfg.Ψ) (namedInstance (solverConnectedAugmented J)) l := by
    intro e he
    have hlog := (hlR e he).trans (le_max_right 0 cfg.Ψ)
    rw [abs_le] at hlog
    exact ⟨by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.1,
      by simpa [Real.exp_log (hlPos e he)] using Real.exp_le_exp.mpr hlog.2⟩
  have hInit := Chain.Ordered.initialize_preserves_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hLP hV.hT hV.hL hV.hγM₀ hV.hγk (namedInstance (solverConnectedAugmented J)) l g
    hGV hmG hnG hℓ
  dsimp only at hInit
  rcases hInit with ⟨hInv, _, hG0, _, _, _, _, _, _, _⟩
  have hle := chainInv_levels_m_le hV.hTP hV.hγM₀ hV.hγk hInv i hi
  dsimp only [chain, Chain.Ordered.algorithm2_init]
  rw [hG0, namedInstance_m] at hle
  exact hle

/-- On every reached solver state in the dry run, every level graph `model.chain.G i`
(`i ≤ cfg.P.d`) has at most `(solverConnectedAugmented J).m` edges. -/
theorem drySolver_reached_level_m_le (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model) :
    ∀ i ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).P.d,
      (model.chain.G i).m ≤ (solverConnectedAugmented J).m := by
  intro i hi
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤
      (concreteCirculationCfgWithLast dryWitnessUsed J).N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  have hUI := (Chain.Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl
  rw [← hm] at hUI
  rcases hUI with ⟨hInv, _, _, _, hFresh, hExtG, _, _, _, _, _, _, _, _, _⟩
  have hle := chainInv_levels_m_le hV.hTP hV.hγM₀ hV.hγk hInv i hi
  rw [hFresh.m_eq, hExtG, hG T le_rfl, namedInstance_m] at hle
  exact hle

/-- Before the shift loop of an `Update` in the dry run, every level graph of
`(alg2PreLoopState cfg model U g l).chain` (`i ≤ cfg.P.d`) has at most
`(solverConnectedAugmented J).m` edges. -/
theorem drySolver_preLoop_level_m_le (J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model)
    {U : List Update} {g l : ℕ → ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U)
    (hl : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e) :
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let chain := (alg2PreLoopState cfg model U g l).chain
    ∀ i ≤ cfg.P.d, (chain.G i).m ≤ (solverConnectedAugmented J).m := by
  intro cfg chain i hi
  have hV := concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
    (le_max_right dryWitnessUsed.M_thresh _) (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed)
    J hJn hJm hCap
  have hmG : (namedInstance (solverConnectedAugmented J)).m ≤ cfg.P.M₀ := by
    rw [namedInstance_m]; exact le_max_left _ _
  have hnG : (namedInstance (solverConnectedAugmented J)).n ≤ cfg.N₀ := by
    have hInEq : (namedInstance (solverConnectedAugmented J)).n = (solverConnectedAugmented J).n := by
      simp [namedInstance, MGraph.n]
    rw [hInEq]; exact hIn
  obtain ⟨D, η, op, T, hHist, hE, hL, hG, hm⟩ := h
  obtain ⟨hgx, hlx⟩ := OrdSolverReached.ext hHist hm
  have hEdgeU : ∀ u ∈ U, Bundle.IsEdgeUpdate u := by
    intro u hu
    have := hU.2.2 u hu
    cases u with
    | insert _ _ _ => trivial
    | delete _ => trivial
    | split _ _ _ _ => exact absurd this id
  have hV' := histSnoc_valid (b := true) hHist (hG T le_rfl) hU.1 hU.2.1 hl
    (fun h => absurd h (by decide)) (fun e he hnot => by rw [← hgx, ← hlx]; exact hagree e he hnot)
  have hG' : ∀ t ≤ T + 1, (histSnoc D T (namedInstance (solverConnectedAugmented J)) U g l).G t =
      namedInstance (solverConnectedAugmented J) := by
    intro t ht
    rcases Nat.lt_or_ge T t with hlt | hle
    · have htT : t = T + 1 := by omega
      subst htT; simp only [histSnoc, seqSnoc_succ]
    · simp only [histSnoc, seqSnoc_of_le _ _ hle]; exact hG t hle
  have hInv := Chain.Ordered.alg2_preLoop_chainInv_with (η := seqSnoc η T 0) κ hV hV'
    (histSnoc_edgeOnly hE hEdgeU) (histSnoc_lengths hL hlR)
    (fun t ht => by rw [hG' t ht]; exact hmG) (fun t ht => by rw [hG' t ht]; exact hnG) T le_rfl
  dsimp only at hInv
  rw [minRatioFailState_snoc_of_le _ D η op T (namedInstance (solverConnectedAugmented J)) U g l 0 true T le_rfl, ← hm] at hInv
  simp only [histSnoc, seqSnoc_succ] at hInv
  have hUI := (Chain.Ordered.algorithm2_uncond_preserves_with (η := η) κ hV hHist hE hL
    (fun t ht => by rw [hG t ht]; exact hmG) (fun t ht => by rw [hG t ht]; exact hnG)).1 T le_rfl
  rw [← hm] at hUI
  rcases hUI with ⟨_, _, _, _, hFresh, hExtG, _, _, _, _, _, _, _, _, _⟩
  have hExtEq : model.extG = namedInstance (solverConnectedAugmented J) := hExtG.trans (hG T le_rfl)
  have hTB := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh (hExtEq.symm ▸ hU.1)
  have hRen := Chain.Ordered.update_freshInv_renamed cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain g l
    hTB.2.1
  have hle := chainInv_levels_m_le hV.hTP hV.hγM₀ hV.hγk hInv i hi
  exact hle.trans_eq (by rw [hRen.1.m_eq, hTB.1, hExtEq, hU.2.1, namedInstance_m])

/-- Specialization of `drySCRepAt_implements_level` at `Init`, discharging `G.n ≤ G.m + 1`
automatically for every level `i < cfg.P.d` of `algorithm2_init`. -/
theorem drySCRepAt_implements_init_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    (g l : ℕ → ℝ)
    (hlPos : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let chain := (Chain.Ordered.algorithm2_init cfg (namedInstance I) g l).chain
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw).Implements
      (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFBL F.fmt F.limbs
        (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) cfg.T (chain.G i) cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) :=
  drySCRepAt_implements_level Psc inner allocationCoefficient allocationDegree source J
    hJn hJm hCapPos hw i hi vCap eCap hlim _
    (drySolver_init_level_n_le_m_add_one J hJn hJm hCapPos g l hlPos hlR i hi.le).2
    (drySolver_init_level_m_le J hJn hJm hCapPos g l hlPos hlR i hi.le)

/-- Specialization of `drySCRepAt_implements_level` on any reached state `OrdSolverReached`,
discharging `G.n ≤ G.m + 1` automatically for every level `i < cfg.P.d`. -/
theorem drySCRepAt_implements_reached_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw).Implements
      (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFBL F.fmt F.limbs
        (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) cfg.T (model.chain.G i) cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) :=
  drySCRepAt_implements_level Psc inner allocationCoefficient allocationDegree source J
    hJn hJm hCapPos hw i hi vCap eCap hlim (model.chain.G i)
    (drySolver_reached_level_n_le_m_add_one J hJn hJm hCapPos h i hi.le).2
    (drySolver_reached_level_m_le J hJn hJm hCapPos h i hi.le)

/-- Specialization of `drySCRepAt_implements_level` on `alg2PreLoopState`, discharging
`G.n ≤ G.m + 1` automatically for every level `i < cfg.P.d`. -/
theorem drySCRepAt_implements_preLoop_level (Psc : DrySparseCorePieces) (inner : SolverInnerCode)
    (allocationCoefficient allocationDegree : ℕ) (source J : Circulation)
    (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCapPos : ∀ e, 1 ≤ J.capacity e)
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤
      dryWordSize dryWitnessUsed allocationCoefficient allocationDegree source)
    {κ : ℝ} {model : Alg2State (concreteCirculationCfgWithLast dryWitnessUsed J)}
    (h : OrdSolverReached (concreteCirculationCfgWithLast dryWitnessUsed J) κ
      (namedInstance (solverConnectedAugmented J)) model)
    {U : List Update} {g l : ℕ → ℝ}
    (hU : RefreshBatch (namedInstance (solverConnectedAugmented J)) U)
    (hl : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E, 0 < l e)
    (hlR : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      |Real.log (l e)| ≤ (concreteCirculationCfgWithLast dryWitnessUsed J).Ψ)
    (hagree : ∀ e ∈ (namedInstance (solverConnectedAugmented J)).E,
      (∀ u ∈ U, ¬ u.Inserts e) → g e = model.extg e ∧ l e = model.extℓ e)
    (i : ℕ) (hi : i < (concreteCirculationCfgWithLast dryWitnessUsed J).P.d)
    (vCap eCap : ℕ) (hlim : vCap + eCap + 2 ≤ dryCapLimit dryWitnessUsed J) :
    let W := dryWitnessUsed
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast W) (concreteQualityBudgetWithLast W) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast W J
    let chain := (alg2PreLoopState cfg model U g l).chain
    let lay := dryTailLay Psc.sc inner
    let limbMul := concreteReadout2LimbMul W
    (drySCRepAt Psc allocationCoefficient allocationDegree dryCapExp limbMul vCap eCap source J hw).Implements
      (dryWordSize W allocationCoefficient allocationDegree source)
      (dryLinkedProgram W Psc.sc inner) lay.scInit lay.scOp
      (sparseCoreOrdMachineContractKFBL F.fmt F.limbs
        (Expander.chosenL (max I.m (concreteEdgeThresholdWithLast W) ^ 2)) cfg.T (chain.G i) cfg.P.k
        (levelM cfg.TP cfg.P i) cfg.N₀ vCap eCap dryCapExp
        (drySCParams Psc dryCapExp limbMul) (drySCAlloc Psc dryCapExp limbMul J)) :=
  drySCRepAt_implements_level Psc inner allocationCoefficient allocationDegree source J
    hJn hJm hCapPos hw i hi vCap eCap hlim _
    (drySolver_preLoop_level_n_le_m_add_one J hJn hJm hCapPos h hU hl hlR hagree i hi.le).2
    (drySolver_preLoop_level_m_le J hJn hJm hCapPos h hU hl hlR hagree i hi.le)

end MinCostFlow.Final.DryRun

end
