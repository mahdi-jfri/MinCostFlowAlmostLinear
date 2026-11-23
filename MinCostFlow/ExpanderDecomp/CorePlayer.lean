module

public import MinCostFlow.ExpanderDecomp.CoreCost
import Mathlib.Tactic.NormNum

/-!
# Instantiating `IsCorePlayer` from the recursive core cut player

This file bridges the recursive core cut player `core` (`core_spec`, `Core.lean`) and its operation
count `coreCost` (its recurrence and closed-form bound, `CoreCost.lean`) to the `IsCorePlayer` interface
(`OuterCorePlayer.lean`).

Main definitions and results:
* `coreForParam` and `coreCostForParam`: `core` and `coreCost` instantiated at
  `coreParamsOf cfg M r`.
* `coreOutcomeSpec_of_coreSpec`: equivalence between `CoreSpec (coreParamsOf cfg M r) q G G.verts`
  and `CoreOutcomeSpec cfg M q G`.
* `core_isCorePlayer`: for any `cfg : ParamConfig` with `4 ≤ cfg.a`, `r ≤ ell M`, a matching
  player with `C_route ≤ 39 * cfg.u`, trimming cost with `C_trim ≤ 2 ^ 20 * cfg.u ^ 3`, and a
  `1 / cfg.a₀`-cloud expander, `(coreForParam, coreCostForParam)` satisfies `IsCorePlayer cfg M r`.
* `core_isCorePlayer_default` and `core_isCorePlayer_default_rOf`: specialization to
  `cfg = ParamConfig.default` and `cloud = ExplicitExpander.explicitGraph` (with `r = rOf M`
  discharging `r ≤ ell M` automatically).
* `core_isCorePlayer_exists_u` and `core_isCorePlayer_exists_u_rOf`: for any `IsMatchingPlayer`
  and any `RemoveFakeCostBounded` (with arbitrary existential constants `C_route`, `C_trim`),
  setting `cfg := { ParamConfig.default with u := max C_route (max C_trim 1) }` yields
  `IsCorePlayer cfg M r`.
* `counterexample_r_gt_ell`: small instance (`M = 0, r = 3`) showing `r ≤ ell M` is needed for
  `N^r < 2^L` (precondition of the router `IsMatchingPlayer` and of the round bound `round_bound_nat`).
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- The recursive core cut player `core` instantiated at `coreParamsOf cfg M r`. -/
noncomputable def coreForParam (cfg : ParamConfig) (M r : ℕ)
    (route : RouterFn) (cloud : ℕ → Graph) : ℕ → Graph → CoreResult :=
  core (coreParamsOf cfg M r) route cloud

/-- Operation count of `coreForParam`. -/
noncomputable def coreCostForParam (cfg : ParamConfig) (M r : ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : RemoveFakeCostFn) (cloud : ℕ → Graph) : ℕ → Graph → ℕ :=
  coreCost (coreParamsOf cfg M r) route routeCost removeFakeCost cloud

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- `CoreSpec (coreParamsOf cfg M r) q G G.verts res` implies `CoreOutcomeSpec cfg M q G res`. -/
theorem coreOutcomeSpec_of_coreSpec {cfg : ParamConfig} {M r q : ℕ} {G : Graph}
    {res : CoreResult} (h : CoreSpec (coreParamsOf cfg M r) q G G.verts res) :
    CoreOutcomeSpec cfg M q G res := by
  have hV : G.verts.card = G.n := Finset.card_range G.n
  cases res with
  | cut U =>
    obtain ⟨hsub, hU, hVdiff, hcut⟩ := h
    rw [hV] at hU hVdiff hcut
    exact ⟨hsub, hU, hVdiff, hcut⟩
  | expander S =>
    obtain ⟨hsub, hS, hexp⟩ := h
    rw [hV] at hS
    exact ⟨hsub, hS, hexp⟩

/-- **Core theorem and size-sensitive cost bound** (`IsCorePlayer` for general `cfg : ParamConfig`):
whenever `4 ≤ cfg.a`, `r ≤ ell M`, `C_route ≤ 39 * cfg.u`, and `C_trim ≤ 2 ^ 20 * cfg.u ^ 3`,
`(coreForParam, coreCostForParam)` satisfies `IsCorePlayer cfg M r`. -/
theorem core_isCorePlayer {cfg : ParamConfig} {M r C_route C_trim : ℕ}
    (ha : 4 ≤ cfg.a) (hrl : r ≤ ell M)
    (hCroute : C_route ≤ 39 * cfg.u) (hCtrim : C_trim ≤ 2 ^ 20 * cfg.u ^ 3)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim)
    {cloud : ℕ → Graph} (hcloud : IsCloudExpander cloud (1 / (cfg.a₀ : ℝ))) :
    IsCorePlayer cfg M r
      (coreForParam cfg M r route cloud)
      (coreCostForParam cfg M r route routeCost removeFakeCost cloud) := by
  have hcfg := coreParamsValid_of_paramConfig cfg M r ha hrl
  refine IsCorePlayer.of_coreTimeBound ?_ ?_
  · intro q G hqr hGvalid hGloop hGn hdegG
    exact coreOutcomeSpec_of_coreSpec
      (core_spec hcfg hroute hcloud hqr hGvalid hGloop hGn hdegG)
  · intro q G hqr hGvalid hGloop hGn hdegG
    exact coreCost_le_coreTimeBound ha hrl hqr hCroute hCtrim hroute hrc hrfc hcloud
      hGvalid hGloop hGn hdegG

/-- `ExplicitExpander.explicitGraph` satisfies `IsCloudExpander` at
`1 / ParamConfig.default.a₀ = 1 / 12`. -/
theorem isCloudExpander_explicitGraph_default :
    IsCloudExpander ExplicitExpander.explicitGraph (1 / (ParamConfig.default.a₀ : ℝ)) := by
  have hα : (1 : ℝ) / (ParamConfig.default.a₀ : ℝ) = ExplicitExpander.alpha0 := by
    norm_num [ParamConfig.default, ExplicitExpander.alpha0]
  rw [hα]
  exact isCloudExpander_explicitGraph

/-- Specialization of `core_isCorePlayer` to `cfg = ParamConfig.default` and
`cloud = ExplicitExpander.explicitGraph`, for any `r ≤ ell M`, `C_route ≤ 39`, and
`C_trim ≤ 2 ^ 20`. -/
theorem core_isCorePlayer_default {M r C_route C_trim : ℕ}
    (hrl : r ≤ ell M) (hCroute : C_route ≤ 39) (hCtrim : C_trim ≤ 2 ^ 20)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim) :
    IsCorePlayer ParamConfig.default M r
      (coreForParam ParamConfig.default M r route ExplicitExpander.explicitGraph)
      (coreCostForParam ParamConfig.default M r route routeCost removeFakeCost
        ExplicitExpander.explicitGraph) :=
  core_isCorePlayer (cfg := ParamConfig.default) (by decide) hrl
    (by simpa [ParamConfig.default] using hCroute)
    (by simpa [ParamConfig.default] using hCtrim)
    hroute hrc hrfc isCloudExpander_explicitGraph_default

/-- Specialization of `core_isCorePlayer_default` to the target recursion depth `r = rOf M`
(discharging `r ≤ ell M` via `rOf_le_ell`). -/
theorem core_isCorePlayer_default_rOf {M C_route C_trim : ℕ}
    (hCroute : C_route ≤ 39) (hCtrim : C_trim ≤ 2 ^ 20)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (hrc : RouteCostBounded routeCost C_route)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim) :
    IsCorePlayer ParamConfig.default M (rOf M)
      (coreForParam ParamConfig.default M (rOf M) route ExplicitExpander.explicitGraph)
      (coreCostForParam ParamConfig.default M (rOf M) route routeCost removeFakeCost
        ExplicitExpander.explicitGraph) :=
  core_isCorePlayer_default (rOf_le_ell M) hCroute hCtrim hroute hrc hrfc

/-- For any matching player `IsMatchingPlayer route routeCost` (with arbitrary existential cost
constant `C_route`) and any `RemoveFakeCostBounded` (with arbitrary `C_trim`), adjusting only the
machine constant `u` of `ParamConfig.default` yields `IsCorePlayer` for every `r ≤ ell M`. -/
theorem core_isCorePlayer_exists_u {M r C_trim : ℕ} (hrl : r ≤ ell M)
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim) :
    ∃ (u : ℕ) (hu : 1 ≤ u),
      let cfg : ParamConfig := { ParamConfig.default with u := u, hu := hu }
      IsCorePlayer cfg M r
        (coreForParam cfg M r route ExplicitExpander.explicitGraph)
        (coreCostForParam cfg M r route routeCost removeFakeCost
          ExplicitExpander.explicitGraph) := by
  obtain ⟨C_route, hrc⟩ := hroute.cost_bound
  let u : ℕ := max C_route (max C_trim 1)
  have hu1 : 1 ≤ u := le_trans (le_max_right C_trim 1) (le_max_right C_route _)
  refine ⟨u, hu1, ?_⟩
  let cfg : ParamConfig := { ParamConfig.default with u := u, hu := hu1 }
  have hCr : C_route ≤ 39 * cfg.u := by
    have h1 : C_route ≤ u := le_max_left _ _
    change C_route ≤ 39 * u
    omega
  have hCt : C_trim ≤ 2 ^ 20 * cfg.u ^ 3 := by
    have h1 : C_trim ≤ u := le_trans (le_max_left C_trim 1) (le_max_right C_route _)
    have hu_le_cube : u ≤ u ^ 3 := by
      calc u = u * 1 * 1 := by ring
        _ ≤ u * u * u := Nat.mul_le_mul (Nat.mul_le_mul_left u hu1) hu1
        _ = u ^ 3 := by ring
    change C_trim ≤ 2 ^ 20 * u ^ 3
    calc C_trim ≤ u := h1
      _ ≤ u ^ 3 := hu_le_cube
      _ = 1 * u ^ 3 := (Nat.one_mul _).symm
      _ ≤ 2 ^ 20 * u ^ 3 := Nat.mul_le_mul_right _ (by decide)
  exact core_isCorePlayer (cfg := cfg) (by change 4 ≤ 15; omega) hrl hCr hCt hroute hrc hrfc
    isCloudExpander_explicitGraph_default

/-- Specialization of `core_isCorePlayer_exists_u` to `r = rOf M`. -/
theorem core_isCorePlayer_exists_u_rOf {M C_trim : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    {removeFakeCost : RemoveFakeCostFn}
    (hrfc : RemoveFakeCostBounded removeFakeCost (LParam M) C_trim) :
    ∃ (u : ℕ) (hu : 1 ≤ u),
      let cfg : ParamConfig := { ParamConfig.default with u := u, hu := hu }
      IsCorePlayer cfg M (rOf M)
        (coreForParam cfg M (rOf M) route ExplicitExpander.explicitGraph)
        (coreCostForParam cfg M (rOf M) route routeCost removeFakeCost
          ExplicitExpander.explicitGraph) :=
  core_isCorePlayer_exists_u (rOf_le_ell M) hroute hrfc

/-- Small witness showing `r ≤ ell M` is needed for `IsCorePlayer`: at `M = 0, r = 3`, we have
`ell 0 = 1`, `LParam 0 = 4`, `2 ^ LParam 0 = 16`, and `(NOf 0 3) ^ 3 = 64 > 16`, so graphs of
size `G.n ≤ N^r` violate the `|X| < 2^L` precondition of the router (`IsMatchingPlayer`) and of
the round bound (`round_bound_nat`). -/
theorem counterexample_r_gt_ell :
    ell 0 = 1 ∧ LParam 0 = 4 ∧ 2 ^ LParam 0 = 16 ∧ (NOf 0 3) ^ 3 = 64 ∧
      2 ^ LParam 0 < (NOf 0 3) ^ 3 := by
  have hell0 : ell 0 = 1 := by
    have h1 : 1 ≤ ell 0 := one_le_ell 0
    have h2 : ell 0 ≤ 1 := by
      unfold ell
      exact (Nat.clog_le_iff_le_pow (by decide)).mpr (by decide)
    omega
  have hL0 : LParam 0 = 4 := by unfold LParam; rw [hell0]
  have hN03 : NOf 0 3 = 4 := by
    unfold NOf ceilDiv
    rw [hell0]
    norm_num
  rw [hell0, hL0, hN03]
  omega

/-- Small witness showing `ParamConfig.default` (`u = 1`) cannot satisfy `IsCorePlayer` for an
arbitrary `IsMatchingPlayer` whose existential cost constant `C` is unconstrained: inflating
`routeCost` to a constant `B + 1` still satisfies `IsMatchingPlayer`, yet violates
`IsCorePlayer.cost_le` at `M = 0, r = 1, q = 1` on the 2-vertex edgeless graph `⟨2, []⟩`. -/
theorem counterexample_unbounded_routeCost
    {route : RouterFn} {routeCost : RouterCostFn} (hroute : IsMatchingPlayer route routeCost)
    (removeFakeCost : RemoveFakeCostFn) :
    ∃ routeCost' : RouterCostFn,
      IsMatchingPlayer route routeCost' ∧
      ¬ IsCorePlayer ParamConfig.default 0 1
          (coreForParam ParamConfig.default 0 1 route ExplicitExpander.explicitGraph)
          (coreCostForParam ParamConfig.default 0 1 route routeCost' removeFakeCost
            ExplicitExpander.explicitGraph) := by
  set B : ℕ := 2 * (NOf 0 1) ^ 2 * (WParam ParamConfig.default 0) ^ (10 * 1 ^ 2 + 10)
  let routeCost' : RouterCostFn := fun _ _ _ _ _ _ _ => B + 1
  refine ⟨routeCost', ?_, ?_⟩
  · refine ⟨hroute.spec, B + 1, ?_⟩
    intro G X pairs Δ L b z _ _ _ _ _ _ _ _
    dsimp only [routeCost']
    exact Nat.le_mul_of_pos_right (B + 1) (Nat.succ_pos _)
  · intro hcore
    let G : Graph := ⟨2, []⟩
    have hGvalid : G.IsValid := by intro e he; cases he
    have hGloop : G.IsLoopless := by intro e he; cases he
    have hN01 : NOf 0 1 = 4 := by
      have hell0 : ell 0 = 1 := by
        have h1 : 1 ≤ ell 0 := one_le_ell 0
        have h2 : ell 0 ≤ 1 := by
          unfold ell; exact (Nat.clog_le_iff_le_pow (by decide)).mpr (by decide)
        omega
      unfold NOf ceilDiv; rw [hell0]; norm_num
    have hdegG : ∀ v < G.n, G.deg v ≤ deltaParam 0 := by
      intro v _; simp [Graph.deg, Graph.degIn, Graph.inside, G]
    have hle := hcore.cost_le 1 G (le_refl 1) (le_refl 1) hGvalid hGloop
      (by simp [G]) (by simp [G, hN01]) hdegG
    -- Show `coreCostForParam ... 1 G ≥ B + 1` because Step C routes at least one colour class of
    -- `explicitGraph 2` (which has at least one non-loop edge by its `1/12`-expansion).
    have hH : ∃ c < 17, ¬ (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) c).isEmpty := by
      have hcloud := isCloudExpander_explicitGraph
      have hcn : (ExplicitExpander.explicitGraph 2).n = 2 := hcloud.n_eq 2 (le_refl 2)
      have hcvalid : (ExplicitExpander.explicitGraph 2).IsValid := hcloud.isValid 2 (le_refl 2)
      have hcdeg : ∀ v < (ExplicitExpander.explicitGraph 2).n,
          (ExplicitExpander.explicitGraph 2).deg v ≤ 9 :=
        fun v hv => hcloud.deg_le 2 (le_refl 2) v (hcn ▸ hv)
      have hcol := edgeColor17_spec hcvalid hcdeg
      have hexp := hcloud.expansion 2 (le_refl 2) {0}
        (by simp [Graph.verts, hcn]) (by simp)
        (by
          intro heq
          have h2 : ({0} : Finset ℕ).card = (ExplicitExpander.explicitGraph 2).verts.card :=
            congrArg Finset.card heq
          simp [Graph.verts, hcn] at h2)
      have hcut_pos : 0 < (ExplicitExpander.explicitGraph 2).cutIn
          (ExplicitExpander.explicitGraph 2).verts {0} := by
        have hmin : min (({0} : Finset ℕ).card : ℝ)
            (((ExplicitExpander.explicitGraph 2).verts \ {0}).card : ℝ) = 1 := by
          have hsub : ({0} : Finset ℕ) ⊆ (ExplicitExpander.explicitGraph 2).verts := by
            simp [Graph.verts, hcn]
          have hcard := Finset.card_sdiff_add_card_eq_card hsub
          have hV : (ExplicitExpander.explicitGraph 2).verts.card = 2 := by
            simp [Graph.verts, hcn]
          have hdiff : ((ExplicitExpander.explicitGraph 2).verts \ {0}).card = 1 := by
            simp only [Finset.card_singleton] at hcard; omega
          simp [hdiff]
        rw [hmin, ExplicitExpander.alpha0] at hexp
        by_contra h0
        have hcz : (ExplicitExpander.explicitGraph 2).cutIn
            (ExplicitExpander.explicitGraph 2).verts {0} = 0 := by omega
        rw [hcz] at hexp
        norm_num at hexp
      unfold Graph.cutIn at hcut_pos
      obtain ⟨e, he⟩ := List.length_pos_iff_exists_mem.mp hcut_pos
      have he_f := List.mem_filter.mp he
      have he_in := mem_inside_iff.mp he_f.1
      have hne : e.1 ≠ e.2 := by
        intro h
        have hb := he_f.2
        rw [h] at hb
        simp at hb
      have he_rl : e ∈ (removeLoops (ExplicitExpander.explicitGraph 2)).edges := by
        unfold removeLoops
        exact List.mem_filter.mpr ⟨he_in.1, by simp [hne]⟩
      have he_fm : e ∈ (List.range 17).flatMap
          (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2))) :=
        hcol.2.2.2.2.mem_iff.mpr he_rl
      obtain ⟨c, hc, hec⟩ := List.mem_flatMap.mp he_fm
      exact ⟨c, List.mem_range.mp hc, by cases h : colorClass _ c <;> simp_all⟩
    -- Take the least colour `c₀ < 17` with a nonempty colour class.
    classical
    let c₀ := Nat.find hH
    have hc₀_spec : c₀ < 17 ∧
        ¬ (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) c₀).isEmpty :=
      Nat.find_spec hH
    have hc₀_min : ∀ m < c₀,
        (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) m).isEmpty := by
      intro m hm
      by_contra hne
      exact Nat.find_min hH hm ⟨by omega, hne⟩
    set cp := coreParamsOf ParamConfig.default 0 1
    set vs := G.verts.sort (· ≤ ·)
    set z := G.verts.card / cp.D 1
    have hloop_inr : ∀ m ≤ c₀,
        ∃ p, stepCMacroLoop cp route G G.verts vs 1 z
          (edgeColor17 (ExplicitExpander.explicitGraph 2)) m = Sum.inr p := by
      intro m hm
      induction m with
      | zero => exact ⟨([], []), rfl⟩
      | succ m ih =>
        obtain ⟨p, hp⟩ := ih (Nat.le_of_succ_le hm)
        unfold stepCMacroLoop
        rw [hp]
        have hempty : (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) m).isEmpty = true :=
          hc₀_min m (Nat.lt_of_succ_le hm)
        simp [stepCMacroColor, hempty]
    have hloop_mono : ∀ m₁ m₂, m₁ ≤ m₂ →
        stepCMacroLoopCost cp route routeCost' G G.verts vs 1 z
          (edgeColor17 (ExplicitExpander.explicitGraph 2)) m₁ ≤
        stepCMacroLoopCost cp route routeCost' G G.verts vs 1 z
          (edgeColor17 (ExplicitExpander.explicitGraph 2)) m₂ := by
      intro m₁ m₂ hm
      induction hm with
      | refl => exact le_refl _
      | step _ ih => exact le_trans ih (Nat.le_add_right _ _)
    have hloop_ge : B + 1 ≤ stepCMacroLoopCost cp route routeCost' G G.verts vs 1 z
        (edgeColor17 (ExplicitExpander.explicitGraph 2)) 17 := by
      have hstep : B + 1 ≤ stepCMacroLoopCost cp route routeCost' G G.verts vs 1 z
          (edgeColor17 (ExplicitExpander.explicitGraph 2)) (c₀ + 1) := by
        unfold stepCMacroLoopCost
        obtain ⟨p, hp⟩ := hloop_inr c₀ (le_refl c₀)
        rw [hp]
        have hne : (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) c₀).isEmpty = false := by
          cases h : (colorClass (edgeColor17 (ExplicitExpander.explicitGraph 2)) c₀).isEmpty <;>
            simp_all
        simp only [stepCMacroColorCost, hne, Bool.false_eq_true, ↓reduceIte, routeCost']
        omega
      exact le_trans hstep (hloop_mono (c₀ + 1) 17 (by omega))
    have hD1pos : 1 ≤ 2 * cp.D 1 := by
      show 1 ≤ 2 * DCore ParamConfig.default 0 1
      unfold DCore ParamConfig.A deltaParam tParam PParam
      have hL := four_le_LParam 0
      have hF := one_le_FParam ParamConfig.default 0
      have : 1 ≤ 16 * ParamConfig.default.a * (1024 * LParam 0) * (FParam ParamConfig.default 0) ^ 1 := by
        have h1 : 1 ≤ 16 * ParamConfig.default.a := by decide
        have h2 : 1 ≤ 1024 * LParam 0 := by omega
        exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) (by simpa using hF)
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' hD1pos
    have hVcard : G.verts.card = 2 := by simp [G, Graph.verts]
    have hks : numFullBlocks vs 1 = 2 := by
      simp [numFullBlocks, vs, Finset.length_sort, hVcard]
    have hcost_ge : B + 1 ≤ coreCostForParam ParamConfig.default 0 1 route routeCost'
        removeFakeCost ExplicitExpander.explicitGraph 1 G := by
      unfold coreCostForParam coreCost coreOnCost
      change B + 1 ≤ if G.verts.card ≤ 1 then 1
        else if G.verts.card ≤ cp.N ^ 0 then _
        else corePeelCost cp route routeCost' removeFakeCost ExplicitExpander.explicitGraph 1
          (coreOn cp route ExplicitExpander.explicitGraph 0)
          (coreOnCost cp route routeCost' removeFakeCost ExplicitExpander.explicitGraph 0)
          G G.verts (2 * cp.D 1) ∅
      rw [hVcard, pow_zero]
      simp only [show ¬ (2 ≤ 1) by decide, ↓reduceIte]
      rw [hd]
      unfold corePeelCost
      simp only [hVcard, Finset.card_empty, Nat.mul_zero, show ¬ (2 ≤ 0) by decide, ↓reduceIte,
        Finset.sdiff_empty]
      unfold oneShotCost
      dsimp only
      simp only [↓reduceIte]
      unfold stepCMacroCost
      have hk2 : numFullBlocks (G.verts.sort (· ≤ ·)) 1 = 2 := hks
      rw [hk2]
      simp only [le_refl, ↓reduceIte]
      have hge' : B + 1 ≤ stepCMacroLoopCost cp route routeCost' G G.verts
          (G.verts.sort (· ≤ ·)) 1 (G.verts.card / cp.D 1)
          (edgeColor17 (ExplicitExpander.explicitGraph 2)) 17 := hloop_ge
      omega
    have hB : G.n * (NOf 0 1) ^ 2 * (WParam ParamConfig.default 0) ^ (10 * 1 ^ 2 + 10) = B := rfl
    rw [hB] at hle
    omega

end MinCostFlow.ExpanderDecomp
