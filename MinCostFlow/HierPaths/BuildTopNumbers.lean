module

public import MinCostFlow.HierPaths.BuildTopBounds
public import MinCostFlow.HierPaths.BuildTopDriverCost
public import MinCostFlow.HierPaths.BuildProgCost
public import MinCostFlow.HierPaths.BuildProgData
public import MinCostFlow.HierPaths.BuildTopRootModel

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Numerical guarantees, `StaticData.Good`, and driver cost bounds

Connects the runtime parameters of `BuildTop*` (`x = Nat.clog 2 (2 * G.m)`,
`b = min x (branchBits G.m)`, `D = leafDepth x b`) to the certified bounds in
`BuildNumHier.lean` and `BuildProgCost.lean`:

* `hostGraph_cloud_eq_explicit`: `hostGraph cloud G = hostGraph explicitGraph G`.
* `buildTopBranch` (`min x (branchBits m)`) gives identical `groupSize`, `branching`,
  and `numGroups` to `branchBits m`, while also satisfying `0 < b ≤ x`.
* `buildTopStaticData_good` and `buildTopStaticData_specRest`: certified parent replies
  at every nontrivial depth assemble into a `Good` `StaticData` meeting `SpecRest`.
* `buildTopDriverTotalCost_le_gamma`: summing `buildLevelCost` and driver overhead over
  all `j < leafDepth x b` is at most `2 ^ 14 * (K + 1) * G.m * gammaHP a d M` whenever
  `buildTopMinA ≤ a`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner
open scoped BigOperators

/-- Minimum value of the hierarchy exponent parameter `a` for `ParamConfig.default`. -/
def buildTopMinA : ℕ :=
  10 * (90 + ParamConfig.default.a₀ + 3 * ParamConfig.default.c0 * ParamConfig.default.A) +
    2 * (87 + ParamConfig.default.a₀) + 120

theorem one_le_buildTopMinA : 1 ≤ buildTopMinA := by
  unfold buildTopMinA; omega

theorem two_two_three_le_buildTopMinA : 223 + 2 * ParamConfig.default.a₀ ≤ buildTopMinA := by
  unfold buildTopMinA; omega

/-- Since `cloud s = explicitGraph s` for `s ≥ 2`, the cloud-based root host equals
the explicit-expander root host. -/
theorem hostGraph_cloud_eq_explicit (G : Graph) :
    hostGraph cloud G = hostGraph ExplicitExpander.explicitGraph G := by
  have hpg : portGraph cloud G G.verts = portGraph ExplicitExpander.explicitGraph G G.verts := by
    unfold portGraph allCloudEdges
    congr 1
    congr 1
    apply List.flatMap_congr
    intro v _
    unfold cloudEdgesFor
    dsimp only
    split_ifs with h
    · rw [cloud_eq_explicitGraph h]
    · rfl
  unfold hostGraph
  rw [hpg]

/-- Branching exponent capped at the root exponent `x`. -/
def buildTopBranch (x m : ℕ) : ℕ := min x (branchBits m)

theorem buildTopBranch_pos {x m : ℕ} (hx : 0 < x) : 0 < buildTopBranch x m := by
  have hb := (depth_bound m).2
  unfold buildTopBranch
  exact lt_min hx hb

theorem buildTopBranch_le_x (x m : ℕ) : buildTopBranch x m ≤ x :=
  min_le_left _ _

theorem buildTopBranch_pow_le (x m : ℕ) : 2 ^ buildTopBranch x m ≤ branchOf m :=
  Nat.pow_le_pow_right (by decide) (min_le_right _ _)

theorem min_buildTopBranch (x m j : ℕ) :
    min x (j * buildTopBranch x m) = min x (j * branchBits m) := by
  unfold buildTopBranch
  cases j with
  | zero => simp
  | succ j =>
    by_cases h : x ≤ branchBits m
    · rw [min_eq_left h]
      have h1 : x ≤ (j + 1) * x := Nat.le_mul_of_pos_left x (Nat.succ_pos j)
      have h2 : x ≤ (j + 1) * branchBits m := h.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos j))
      rw [min_eq_left h1, min_eq_left h2]
    · rw [min_eq_right (Nat.le_of_not_ge h)]

theorem groupSize_buildTopBranch (x m j : ℕ) :
    groupSize x (buildTopBranch x m) j = groupSize x (branchBits m) j := by
  unfold groupSize
  rw [min_buildTopBranch]

theorem branching_buildTopBranch (x m j : ℕ) :
    branching x (buildTopBranch x m) j = branching x (branchBits m) j := by
  unfold branching
  rw [groupSize_buildTopBranch, groupSize_buildTopBranch]

theorem numGroups_buildTopBranch (x m j : ℕ) :
    numGroups x (buildTopBranch x m) j = numGroups x (branchBits m) j := by
  unfold numGroups
  rw [min_buildTopBranch]

theorem leafDepth_buildTopBranch_le {x m : ℕ} (hx : 0 < x) (hxX : x ≤ xOf m) :
    leafDepth x (buildTopBranch x m) ≤ depthOf m := by
  unfold buildTopBranch
  by_cases h : x ≤ branchBits m
  · rw [min_eq_left h]
    have h1 : leafDepth x x = 1 := by
      unfold leafDepth
      have : x + x - 1 = x + (x - 1) := by omega
      rw [this, Nat.add_div_left _ hx, Nat.div_eq_of_lt (by omega)]
    rw [h1]
    exact le_trans (by decide) (two_le_depthOf m)
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    have hdep := (depth_bound m).1
    exact le_trans (Nat.div_le_div_right (by omega)) hdep

/-- Basic facts about `x = Nat.clog 2 (2 * G.m)` for a valid graph with `1 ≤ G.m`. -/
theorem buildTop_x_facts {G : Graph} (hG : G.IsValid) (hm : 1 ≤ G.m) :
    let x := Nat.clog 2 (2 * G.m)
    portCount G = 2 * G.m ∧ 2 ^ x = hostSize G ∧ 0 < x ∧ 2 ^ x < 4 * G.m ∧ x ≤ xOf G.m := by
  have hpc : portCount G = 2 * G.m := by simp [portCount, inside_verts_length hG]
  have hhs : 2 ^ Nat.clog 2 (2 * G.m) = hostSize G := by simp [hostSize, hpc]
  have hxpos : 0 < Nat.clog 2 (2 * G.m) := by
    rw [Nat.lt_clog_iff_pow_lt (by decide)]
    omega
  have hlt : 2 ^ Nat.clog 2 (2 * G.m) < 4 * G.m := by
    rw [hhs]
    have h := hostSize_lt (by rw [inside_verts_length hG]; exact hm)
    omega
  have hxX : Nat.clog 2 (2 * G.m) ≤ xOf G.m := by
    unfold xOf
    exact Nat.clog_mono_right 2 (by omega)
  exact ⟨hpc, hhs, hxpos, hlt, hxX⟩

/-- Every valid loopless graph supported on `X` with degree cap `Δ` meets `HostPre` and has
at most `Δ * X.card` edges. -/
theorem buildTop_hostPre_and_m {H : Graph} {X : Finset ℕ} {x Δ : ℕ}
    (hn : H.n = 2 ^ x) (hsub : X ⊆ Finset.range (2 ^ x))
    (hloop : H.IsLoopless) (hΔ : 1 ≤ Δ) (hdeg : ∀ v ∈ X, H.deg v ≤ Δ)
    (hsupp : ∀ e ∈ H.edges, e.1 ∈ X ∧ e.2 ∈ X) :
    HostPre H X Δ (x + 1) ∧ H.m ≤ Δ * X.card := by
  have hXsub : X ⊆ Finset.range H.n := hn.symm ▸ hsub
  have hXverts : X ⊆ H.verts := hXsub
  have hcard : X.card ≤ 2 ^ x := (Finset.card_le_card hsub).trans (by simp)
  have hpow_pos : 1 ≤ 2 ^ x := Nat.one_le_two_pow
  have hltL : X.card < 2 ^ (x + 1) := by rw [pow_succ]; omega
  have hpre : HostPre H X Δ (x + 1) := by
    refine ⟨hXsub, fun e he => hloop e (List.mem_of_mem_filter he), hΔ, fun v hv => ?_,
      Nat.succ_pos x, hltL⟩
    exact (MinCostFlow.Expander.degIn_mono hXverts v).trans (hdeg v hv)
  have hm : H.m ≤ Δ * X.card := by
    have hval : H.IsValid := fun e he => by
      have hs := hsupp e he
      exact ⟨Finset.mem_range.mp (hXsub hs.1), Finset.mem_range.mp (hXsub hs.2)⟩
    have hsum := MinCostFlow.Expander.sum_deg_eq_two_mul_m hval
    have hzero : ∀ v ∈ H.verts \ X, H.deg v = 0 := by
      intro v hv
      have hv_not : v ∉ X := (Finset.mem_sdiff.mp hv).2
      rw [Graph.deg, MinCostFlow.Expander.degIn_eq_sum_map,
        MinCostFlow.Expander.inside_verts_of_isValid hval]
      apply List.sum_eq_zero
      intro k hk
      rw [List.mem_map] at hk
      obtain ⟨e, he, rfl⟩ := hk
      have hs := hsupp e he
      have h1 : e.1 ≠ v := fun h => hv_not (h ▸ hs.1)
      have h2 : e.2 ≠ v := fun h => hv_not (h ▸ hs.2)
      simp [h1, h2]
    have hsplit : ∑ v ∈ H.verts, H.deg v = ∑ v ∈ X, H.deg v := by
      rw [← Finset.sum_sdiff hXverts, Finset.sum_eq_zero hzero, zero_add]
    have hbd : ∑ v ∈ X, H.deg v ≤ Δ * X.card := by
      calc ∑ v ∈ X, H.deg v
          ≤ ∑ _v ∈ X, Δ := Finset.sum_le_sum fun v hv => hdeg v hv
        _ = Δ * X.card := by simp [Finset.sum_const, smul_eq_mul, mul_comm]
    omega
  exact ⟨hpre, hm⟩

/-- The `bh` schedule function used by the runtime player table. -/
def buildTopBh (x m d : ℕ) : ℕ → ℕ
  | 0 => 100 * d
  | _ + 1 => 4 * PParam ParamConfig.default (2 ^ x) (depthOf m)

def buildTopDummyRoute : RouterFn := fun _ _ _ _ _ _ _ => .cut ∅
def buildTopDummyCore : ℕ → Graph → CoreResult := fun _ _ => .expander ∅

theorem buildTopBh_eq_numBh {G : Graph} (hG : G.IsValid) (d j : ℕ) :
    buildTopBh (Nat.clog 2 (2 * G.m)) G.m d j =
      (numParams buildTopDummyRoute buildTopDummyCore G).numBh ParamConfig.default d j := by
  have hpc : portCount G = 2 * G.m := by simp [portCount, inside_verts_length hG]
  cases j <;> simp [buildTopBh, BuildParams.numBh, numParams, hpc]

/-- Certified parent replies at all nontrivial depths produce a `Good` `StaticData`
meeting `SpecRest`. -/
theorem buildTopStaticData_good_and_specRest
    {G : Graph} {phiNum phiDen M a : ℕ} {reply : ℕ → ℕ → BuildLevelData}
    (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hmM : G.m ≤ M) (hdeg : ∀ v < G.n, 1 ≤ G.deg v)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)))
    (ha : buildTopMinA ≤ a)
    (hgood : let x := Nat.clog 2 (2 * G.m)
      let b := buildTopBranch x G.m
      buildTopRepliesGood x b (hostGraph cloud G) reply (2 ^ x) (depthOf G.m)
        (49 * (x + 1) + 2) (x + 1) (x + 1) (buildTopBh x G.m (dOf phiNum phiDen))) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let S : StaticData := ⟨x, b, hostOwner G, hostLabel G,
      buildTopHierarchy x b (hostGraph cloud G) reply⟩
    S.Good a (dOf phiNum phiDen) M G ∧ S.SpecRest a (dOf phiNum phiDen) G := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set d := dOf phiNum phiDen
  set root := hostGraph cloud G
  set H := buildTopHierarchy x b root reply
  set S : StaticData := ⟨x, b, hostOwner G, hostLabel G, H⟩
  obtain ⟨hpc, hhs, hxpos, hlt4m, hxX⟩ := buildTop_x_facts hG hm
  obtain ⟨hφ, hd1, hφd⟩ := dOf_spec h1 h2
  have hbpos : 0 < b := buildTopBranch_pos hxpos
  have hroot_eq : root = hostGraph ExplicitExpander.explicitGraph G :=
    hostGraph_cloud_eq_explicit G
  obtain ⟨⟨hn_root, _, _, _⟩, hval_root, _, _, _, _, _, hown_lt, _, hproj, hinj⟩ :=
    lemma_2 hG hm hφ hcond
  have hroot_supp : ∀ e ∈ root.edges, e.1 ∈ members x b 0 0 ∧ e.2 ∈ members x b 0 0 := by
    intro e he
    rw [hroot_eq] at he
    have hv := hval_root e he
    rw [hn_root, ← hhs] at hv
    simp [members, groupSize, x, hv.1, hv.2]
  have hValidH : H.IsValid x b := buildTopHierarchy_isValid hroot_supp hgood
  have hRawBounds := buildTopHierarchy_bounds hgood
  have ha223 : 223 + 2 * ParamConfig.default.a₀ ≤ a :=
    two_two_three_le_buildTopMinA.trans ha
  have hρ_le : ∀ j, buildLevelDegree (x + 1) *
      routeCong (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
      lvlBound (hOf d) (uOf a G.m) j := by
    intro j
    have h := BuildParams.num_rho_le (route := buildTopDummyRoute) (core := buildTopDummyCore)
      hG hm hφ hcond (cfg := ParamConfig.default) (a := a) (dd := d) ha223 hd1 j
    rw [← buildTopBh_eq_numBh hG d j] at h
    simpa [buildLevelDegree, numParams, hpc] using h
  have hκ_le : ∀ j, routeCong (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
      lvlBound (hOf d) (uOf a G.m) j :=
    fun j => (Nat.le_mul_of_pos_left _ (by unfold buildLevelDegree; omega)).trans (hρ_le j)
  have hd_le : ∀ j, routePathLen (49 * (x + 1) + 2) (buildTopBh x G.m d j) (x + 1) ≤
      lvlBound (hOf d) (uOf a G.m) j := fun j => by
    have hbh1 : 1 ≤ buildTopBh x G.m d j := by
      cases j with
      | zero => simp [buildTopBh]; omega
      | succ _ =>
        simp [buildTopBh]
        have := one_le_PParam ParamConfig.default (2 ^ x) (depthOf G.m)
        omega
    exact (pathLen_le_cong (by omega) hbh1 (by omega)).trans (hκ_le j)
  have hBoundsH : H.Bounds x b (lvlBound (hOf d) (uOf a G.m))
      (lvlBound (hOf d) (uOf a G.m)) (lvlBound (hOf d) (uOf a G.m)) :=
    hRawBounds.mono hd_le hρ_le hκ_le
  have hGood : S.Good a d M G := by
    refine ⟨hbpos, hValidH, hBoundsH, leafDepth_buildTopBranch_le hxpos hxX,
      buildTopBranch_pow_le x G.m, hlt4m.le, n_le_two_m hG hdeg, hmM, ?_, hinj, ?_⟩
    · simpa [S, H, buildTopHierarchy, hroot_eq] using hproj
    · intro p hp
      exact hown_lt p (hhs ▸ hp)
  have hSpecRest : S.SpecRest a d G := by
    refine ⟨?_, StaticData.deg_of_host hhs rfl⟩
    have hpi := staticArrays_pairSpecIn hbpos hValidH (owner := hostOwner G) (label := hostLabel G)
    exact ⟨fun j Y Z hpar hne hY hZ => hpi.lt j Y Z hY hZ hpar hne,
      fun j Y Z hpar hne hY hZ => hpi.sides j Y Z hY hZ hpar hne,
      fun j Y Z hpar hne hY hZ => hpi.matching j Y Z hY hZ hpar hne⟩
  exact ⟨hGood, hSpecRest⟩

/-- Common per-terminal work factor at depth `j` from `buildTopLevelCost_le`,
specialized to the runtime parameters. -/
def buildTopDepthFactor (K x m d j : ℕ) : ℕ :=
  let M := 2 ^ x
  let r := depthOf m
  let L := x + 1
  let Δ := 49 * L + 2
  let bh := buildTopBh x m d j
  let k := branching x (buildTopBranch x m) j
  K * (buildLevelDegree L *
    ((NOf M r) ^ 2 * (WParam ParamConfig.default M) ^ (10 * r ^ 2 + 10) +
      buildLevelDegree L + 1) +
    (buildLevelDegree L * k + k * k + 1) * (Δ + 2) *
      (routePathLen Δ bh L + 1) * (routeCong Δ bh L + 1) + k + 1) + 24

private lemma buildTopDepthFactor_bound
    (K x m d j : ℕ) (cfg : ParamConfig)
    {v h c₁ Kc Dd E e S : ℕ}
    (hxX : x ≤ xOf m) (hV : xOf m + 2 ≤ 2 ^ v) (hv1 : 1 ≤ v) (_hh : 1 ≤ h)
    (hd : 1 ≤ d) (hDd : 1 ≤ Dd) (hDd_def : Dd = (1 + (2 + d) ^ 4) ^ 2)
    (hE_def : E = 63 + 7 * v + 3 * (h * (Kc + 6 * v)))
    (hS_ge1 : 2 * h ^ 2 + 4 + (c₁ + 6 * v) * e ≤ S)
    (hS_ge2 : 2 * h ^ 2 + 2 + E ≤ S)
    (hS_ge3 : 7 + v ≤ S)
    (hN : NOf (2 ^ x) h ^ 2 ≤ 2 ^ (2 * h ^ 2 + 4))
    (hW : WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) ≤ 2 ^ ((c₁ + 6 * v) * e))
    (hP_le : PParam cfg (2 ^ x) h ≤ 2 ^ (h * (Kc + 6 * v)))
    (hP1 : 1 ≤ PParam cfg (2 ^ x) h)
    (hkk : branching x (buildTopBranch x m) j * branching x (buildTopBranch x m) j ≤
      2 ^ (2 * h ^ 2 + 2))
    (hr_eq : depthOf m = h)
    (hcfg_eq : ParamConfig.default = cfg) :
    buildTopDepthFactor K x m d j + 311 ≤ 3000 * (K + 1) * Dd * 2 ^ (v + S) := by
  set L := x + 1
  set Δ := 49 * L + 2
  set bh := buildTopBh x m d j
  set k := branching x (buildTopBranch x m) j
  set dp := routePathLen Δ bh L + 1
  set rc := routeCong Δ bh L
  have h2v : 2 ≤ 2 ^ v := by
    have : 2 ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hv1
    simpa using this
  have hT_le : buildLevelDegree L ≤ 2 ^ 6 * 2 ^ v := by
    unfold buildLevelDegree; omega
  have hΔ_le : Δ ≤ 64 * 2 ^ v := by omega
  have hL_le : L ≤ 2 ^ v := by omega
  have hk1 : 1 ≤ k := branching_pos
  have hbh1 : 1 ≤ bh := by
    cases j with
    | zero => simp [bh, buildTopBh]; omega
    | succ _ => simp [bh, buildTopBh, hr_eq, hcfg_eq]; omega
  have hrc1 : 1 ≤ rc := by
    unfold rc routeCong routeBatchH
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)) (by omega)
  have hdp_le : dp ≤ 2 ^ 12 * bh * (2 ^ v) ^ 2 := by
    have h1 : routePathLen Δ bh L ≤ 32 * (64 * 2 ^ v) * bh * 2 ^ v := by
      unfold routePathLen
      exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hΔ_le)) hL_le
    have h2 : 32 * (64 * 2 ^ v) * bh * 2 ^ v = 2 ^ 11 * (bh * (2 ^ v) ^ 2) := by ring
    have h3 : 1 ≤ bh * (2 ^ v) ^ 2 := Nat.mul_pos hbh1 (Nat.pow_pos (by omega))
    have h4 : 2 ^ 12 * bh * (2 ^ v) ^ 2 = 2 ^ 12 * (bh * (2 ^ v) ^ 2) := by ring
    rw [h2] at h1; rw [h4]; dsimp only [dp]; omega
  have hrc_le : rc ≤ 2 ^ 22 * bh ^ 2 * (2 ^ v) ^ 4 := by
    calc rc ≤ 16 * bh * (64 * 2 ^ v) * (2 ^ 12 * bh * (2 ^ v) ^ 2) * 2 ^ v := by
          unfold rc routeCong routeBatchH
          exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hΔ_le) hdp_le) hL_le
      _ = 2 ^ 22 * bh ^ 2 * (2 ^ v) ^ 4 := by ring
  have hΔ2 : Δ + 2 ≤ 2 ^ 7 * 2 ^ v := by omega
  have hZ_bound : dp * rc * (Δ + 2) + 1 ≤ 2 ^ 42 * bh ^ 3 * (2 ^ v) ^ 7 := by
    have hmain : dp * rc * (Δ + 2) ≤ 2 ^ 41 * (bh ^ 3 * (2 ^ v) ^ 7) := by
      calc dp * rc * (Δ + 2)
          ≤ (2 ^ 12 * bh * (2 ^ v) ^ 2) * (2 ^ 22 * bh ^ 2 * (2 ^ v) ^ 4) * (2 ^ 7 * 2 ^ v) :=
            Nat.mul_le_mul (Nat.mul_le_mul hdp_le hrc_le) hΔ2
        _ = 2 ^ 41 * (bh ^ 3 * (2 ^ v) ^ 7) := by ring
    have hpos : 1 ≤ bh ^ 3 * (2 ^ v) ^ 7 := Nat.mul_pos (Nat.pow_pos hbh1) (Nat.pow_pos (by omega))
    have e42 : 2 ^ 42 * bh ^ 3 * (2 ^ v) ^ 7 = 2 ^ 42 * (bh ^ 3 * (2 ^ v) ^ 7) := by ring
    rw [e42]; omega
  have hZ0 : dp * rc * (Δ + 2) + 1 ≤ Dd * 2 ^ E := by
    have hpow7 : (2 ^ v) ^ 7 = 2 ^ (7 * v) := by rw [← pow_mul, Nat.mul_comm]
    cases j with
    | zero =>
      have hbh0 : bh = 100 * d := rfl
      have hd3 : d ^ 3 ≤ Dd := by
        rw [hDd_def]
        calc d ^ 3 ≤ (2 + d) ^ 8 :=
              (Nat.pow_le_pow_left (by omega) 3).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
          _ = ((2 + d) ^ 4) ^ 2 := by ring
          _ ≤ (1 + (2 + d) ^ 4) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      calc dp * rc * (Δ + 2) + 1 ≤ 2 ^ 42 * (100 * d) ^ 3 * (2 ^ v) ^ 7 := hbh0 ▸ hZ_bound
        _ = 2 ^ 42 * 1000000 * d ^ 3 * 2 ^ (7 * v) := by rw [hpow7]; ring
        _ ≤ 2 ^ 62 * d ^ 3 * 2 ^ (7 * v) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
        _ = d ^ 3 * 2 ^ (62 + 7 * v) := by rw [pow_add]; ring
        _ ≤ Dd * 2 ^ E := Nat.mul_le_mul hd3 (Nat.pow_le_pow_right (by norm_num) (by omega))
    | succ _ =>
      have hbhS : bh = 4 * PParam cfg (2 ^ x) h := by simp [bh, buildTopBh, hr_eq, hcfg_eq]
      calc dp * rc * (Δ + 2) + 1 ≤ 2 ^ 42 * (4 * PParam cfg (2 ^ x) h) ^ 3 * (2 ^ v) ^ 7 :=
            hbhS ▸ hZ_bound
        _ = 2 ^ 48 * PParam cfg (2 ^ x) h ^ 3 * 2 ^ (7 * v) := by rw [hpow7]; ring
        _ ≤ 2 ^ 48 * (2 ^ (h * (Kc + 6 * v))) ^ 3 * 2 ^ (7 * v) :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP_le 3))
        _ = 2 ^ (48 + 3 * (h * (Kc + 6 * v)) + 7 * v) := by
            rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
        _ ≤ 1 * 2 ^ E := by rw [one_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ Dd * 2 ^ E := Nat.mul_le_mul_right _ hDd
  have hRprod : (Δ + 2) * dp * (rc + 1) ≤ 2 * (Dd * 2 ^ E) := by
    have h1 : (Δ + 2) * dp * (rc + 1) ≤ 2 * (dp * rc * (Δ + 2) + 1) := by
      have hrc2 : rc + 1 ≤ 2 * rc := by omega
      calc (Δ + 2) * dp * (rc + 1)
          ≤ (Δ + 2) * dp * (2 * rc) := Nat.mul_le_mul_left _ hrc2
        _ = 2 * (dp * rc * (Δ + 2)) := by ring
        _ ≤ 2 * (dp * rc * (Δ + 2) + 1) := by omega
    exact h1.trans (Nat.mul_le_mul_left 2 hZ0)
  have hA : NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) ≤ 2 ^ S := by
    calc _ ≤ 2 ^ (2 * h ^ 2 + 4) * 2 ^ ((c₁ + 6 * v) * e) := Nat.mul_le_mul hN hW
      _ = 2 ^ (2 * h ^ 2 + 4 + (c₁ + 6 * v) * e) := (pow_add ..).symm
      _ ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hS_ge1
  have hS2 : 2 ^ (2 * h ^ 2 + 2) * 2 ^ E ≤ 2 ^ S := by
    rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hS_ge2
  have hT_le_2S : buildLevelDegree L + 1 ≤ 2 ^ S := by
    have hT1 : buildLevelDegree L + 1 ≤ 2 ^ (7 + v) := by rw [pow_add]; omega
    exact hT1.trans (Nat.pow_le_pow_right (by norm_num) hS_ge3)
  have hpart1 : buildLevelDegree L *
      (NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) +
        buildLevelDegree L + 1) ≤ 128 * 2 ^ (v + S) := by
    have hinner : NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) +
        buildLevelDegree L + 1 ≤ 2 * 2 ^ S := by omega
    calc _ ≤ (2 ^ 6 * 2 ^ v) * (2 * 2 ^ S) := Nat.mul_le_mul hT_le hinner
      _ = 128 * (2 ^ v * 2 ^ S) := by ring
      _ = 128 * 2 ^ (v + S) := by rw [pow_add]
  have hpart2 : (buildLevelDegree L * k + k * k + 1) * (Δ + 2) * dp * (rc + 1) ≤
      260 * Dd * 2 ^ (v + S) := by
    have hcoef : buildLevelDegree L * k + k * k + 1 ≤ 130 * 2 ^ v * 2 ^ (2 * h ^ 2 + 2) := by
      have h1 : buildLevelDegree L * k ≤ 64 * 2 ^ v * (k * k) := by
        have hT64 : buildLevelDegree L ≤ 64 * 2 ^ v := by simpa using hT_le
        exact Nat.mul_le_mul hT64 (Nat.le_mul_of_pos_left k hk1)
      have h2 : k * k ≤ 2 ^ v * (k * k) := Nat.le_mul_of_pos_left _ (by omega)
      have h3 : 1 ≤ 2 ^ v * (k * k) := Nat.mul_pos (by omega) (Nat.mul_pos hk1 hk1)
      have h4 : buildLevelDegree L * k + k * k + 1 ≤ 130 * 2 ^ v * (k * k) := by
        have : 130 * 2 ^ v * (k * k) = 64 * 2 ^ v * (k * k) + 66 * (2 ^ v * (k * k)) := by ring
        omega
      exact h4.trans (Nat.mul_le_mul_left _ hkk)
    calc (buildLevelDegree L * k + k * k + 1) * (Δ + 2) * dp * (rc + 1)
        = (buildLevelDegree L * k + k * k + 1) * ((Δ + 2) * dp * (rc + 1)) := by ring
      _ ≤ (130 * 2 ^ v * 2 ^ (2 * h ^ 2 + 2)) * (2 * (Dd * 2 ^ E)) :=
          Nat.mul_le_mul hcoef hRprod
      _ = 260 * Dd * (2 ^ v * (2 ^ (2 * h ^ 2 + 2) * 2 ^ E)) := by ring
      _ ≤ 260 * Dd * (2 ^ v * 2 ^ S) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hS2)
      _ = 260 * Dd * 2 ^ (v + S) := by rw [pow_add]
  have hpart3 : k + 1 ≤ 2 * 2 ^ (v + S) := by
    have h1 : k ≤ 2 ^ (2 * h ^ 2 + 2) := (Nat.le_mul_of_pos_left k hk1).trans hkk
    have h2 : 2 ^ (2 * h ^ 2 + 2) ≤ 2 ^ (v + S) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ 2 ^ (v + S) := Nat.one_le_two_pow
    omega
  have h1vS : 1 ≤ Dd * 2 ^ (v + S) := Nat.mul_pos hDd Nat.one_le_two_pow
  have h128 : 128 * 2 ^ (v + S) ≤ 128 * Dd * 2 ^ (v + S) := by
    calc 128 * 2 ^ (v + S) = 128 * 1 * 2 ^ (v + S) := by ring
      _ ≤ 128 * Dd * 2 ^ (v + S) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDd)
  have h2' : 2 * 2 ^ (v + S) ≤ 2 * Dd * 2 ^ (v + S) := by
    calc 2 * 2 ^ (v + S) = 2 * 1 * 2 ^ (v + S) := by ring
      _ ≤ 2 * Dd * 2 ^ (v + S) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDd)
  have hbody : buildLevelDegree L *
      (NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) +
        buildLevelDegree L + 1) +
      (buildLevelDegree L * k + k * k + 1) * (Δ + 2) * dp * (rc + 1) + k + 1 ≤
      390 * Dd * 2 ^ (v + S) := by
    have e390 : 390 * Dd * 2 ^ (v + S) =
        128 * Dd * 2 ^ (v + S) + 260 * Dd * 2 ^ (v + S) + 2 * Dd * 2 ^ (v + S) := by ring
    rw [e390]
    have := Nat.add_le_add (Nat.add_le_add (hpart1.trans h128) hpart2) (hpart3.trans h2')
    omega
  unfold buildTopDepthFactor
  dsimp only
  rw [hr_eq, hcfg_eq]
  have hKmul : K * (buildLevelDegree L *
      (NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) +
        buildLevelDegree L + 1) +
      (buildLevelDegree L * k + k * k + 1) * (Δ + 2) * dp * (rc + 1) + k + 1) ≤
      390 * K * Dd * 2 ^ (v + S) := by
    calc _ ≤ K * (390 * Dd * 2 ^ (v + S)) := Nat.mul_le_mul_left K hbody
      _ = 390 * K * Dd * 2 ^ (v + S) := by ring
  have h335 : 24 + 311 ≤ 335 * (Dd * 2 ^ (v + S)) := Nat.le_mul_of_pos_right 335 h1vS
  have hfin : 390 * K * (Dd * 2 ^ (v + S)) + 335 * (Dd * 2 ^ (v + S)) ≤
      3000 * (K + 1) * (Dd * 2 ^ (v + S)) := by
    have : 390 * K + 335 ≤ 3000 * (K + 1) := by omega
    calc _ = (390 * K + 335) * (Dd * 2 ^ (v + S)) := by ring
      _ ≤ 3000 * (K + 1) * (Dd * 2 ^ (v + S)) := Nat.mul_le_mul_right _ this
  have e1 : 390 * K * Dd * 2 ^ (v + S) = 390 * K * (Dd * 2 ^ (v + S)) := by ring
  have e2 : 3000 * (K + 1) * Dd * 2 ^ (v + S) = 3000 * (K + 1) * (Dd * 2 ^ (v + S)) := by ring
  change K * (buildLevelDegree L *
      (NOf (2 ^ x) h ^ 2 * WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) +
        buildLevelDegree L + 1) +
      (buildLevelDegree L * k + k * k + 1) * (Δ + 2) * dp * (rc + 1) + k + 1) + 24 + 311 ≤ _
  omega

/-- Total driver cost (all parent calls + child-directory advances + loop overhead)
is at most `2 ^ 14 * (K + 1) * G.m * gammaHP a d M` when `buildTopMinA ≤ a`. -/
theorem buildTopDriverTotalCost_le_gamma {G : Graph} {K a d M : ℕ}
    (hG : G.IsValid) (hm : 1 ≤ G.m) (hmM : G.m ≤ M) (hd : 1 ≤ d) (ha : buildTopMinA ≤ a) :
    let x := Nat.clog 2 (2 * G.m)
    let b := buildTopBranch x G.m
    let D := leafDepth x b
    2 ^ x * (∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311)) + 9 * D + 12 ≤
      2 ^ 14 * (K + 1) * G.m * gammaHP a d M := by
  dsimp only
  set x := Nat.clog 2 (2 * G.m)
  set b := buildTopBranch x G.m
  set D := leafDepth x b
  generalize hcfg_eq : ParamConfig.default = cfg
  obtain ⟨hpc, _, hxpos, hlt4m, hxX⟩ := buildTop_x_facts hG hm
  obtain ⟨hV, hv1⟩ := BuildParams.num_v G.m
  set v := vxOf G.m
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  have hD_le : D ≤ h := leafDepth_buildTopBranch_le hxpos hxX
  set c₁ := 90 + cfg.a₀ + 3 * cfg.c0 * cfg.A
  set Kc := 87 + cfg.a₀
  set Dd := (1 + (2 + d) ^ 4) ^ 2
  set E := 63 + 7 * v + 3 * (h * (Kc + 6 * v))
  set e := 10 * h ^ 2 + 10
  set S := 2 * h ^ 2 + 4 + (c₁ + 6 * v) * e + E
  have hDd : 1 ≤ Dd := Nat.one_le_pow _ _ (by omega)
  set B := numParams buildTopDummyRoute buildTopDummyCore G
  have hBx : B.x = x := by simp [B, numParams, hpc, x]
  have hBM : B.M = 2 ^ x := by simp [B, numParams, hpc, x]
  have hBr : B.r = h := rfl
  have hN := BuildParams.num_N_sq (route := buildTopDummyRoute) (core := buildTopDummyCore) (G := G) (hBx ▸ hxX)
  rw [hBM, hBr] at hN
  have hk_sq := BuildParams.num_k_sq (route := buildTopDummyRoute) (core := buildTopDummyCore) (G := G)
  have hell : ell (2 ^ x) ≤ 2 ^ v := by
    have := (ell_two_pow x).2; omega
  have hW : WParam cfg (2 ^ x) ^ (10 * h ^ 2 + 10) ≤ 2 ^ ((c₁ + 6 * v) * e) := by
    rw [pow_mul 2 (c₁ + 6 * v) e]
    exact Nat.pow_le_pow_left (BuildParams.num_W_le hell) _
  have hP_le : PParam cfg (2 ^ x) h ≤ 2 ^ (h * (Kc + 6 * v)) := PParam_le hell h
  have hP1 : 1 ≤ PParam cfg (2 ^ x) h := one_le_PParam cfg (2 ^ x) h
  have hterm : ∀ j, buildTopDepthFactor K x G.m d j + 311 ≤
      3000 * (K + 1) * Dd * 2 ^ (v + S) := by
    intro j
    have hk_le : branching x b j ≤ 2 ^ B.b := by
      calc branching x b j ≤ 2 ^ b := branching_le_pow j
        _ ≤ branchOf G.m := buildTopBranch_pow_le x G.m
        _ = 2 ^ B.b := rfl
    have hkk : branching x b j * branching x b j ≤ 2 ^ (2 * h ^ 2 + 2) := by
      calc branching x b j * branching x b j ≤ 2 ^ B.b * 2 ^ B.b := Nat.mul_le_mul hk_le hk_le
        _ = (2 ^ B.b) ^ 2 := by ring
        _ ≤ 2 ^ (2 * h ^ 2 + 2) := hk_sq
    exact buildTopDepthFactor_bound K x G.m d j cfg hxX hV hv1 hh hd hDd rfl rfl
      (by omega) (by omega) (by omega) hN hW hP_le hP1 hkk rfl hcfg_eq
  have hD2 : D ≤ 2 ^ h := le_trans hD_le (Nat.le_of_lt Nat.lt_two_pow_self)
  have ha_cfg : 10 * c₁ + 2 * Kc + 120 ≤ a := by
    have : buildTopMinA = 10 * c₁ + 2 * Kc + 120 := by
      simp only [buildTopMinA, c₁, Kc, hcfg_eq]
    omega
  have hexp := exp_gamma (c₁ := c₁) (K := Kc) ha_cfg hh hv1
  have hU : 2 ^ (h + (v + S)) ≤ uOf a G.m ^ (2 * h + 2) := by
    unfold uOf
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have : h + (v + S) = h + v + (2 * h ^ 2 + 4 + (c₁ + 6 * v) * (10 * h ^ 2 + 10) +
        (63 + 7 * v + 3 * (h * (Kc + 6 * v)))) := by simp only [S, E, e]; ring
    rw [this]
    exact hexp
  have hΓ := BuildParams.gammaHP_ge a d hmM
  have hsum : ∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311) ≤
      2 ^ h * (3000 * (K + 1) * Dd * 2 ^ (v + S)) := by
    calc _ ≤ ∑ _j ∈ Finset.range D, 3000 * (K + 1) * Dd * 2 ^ (v + S) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = D * (3000 * (K + 1) * Dd * 2 ^ (v + S)) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ hD2
  have hmain : 2 ^ x * (∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311)) ≤
      12000 * (K + 1) * G.m * gammaHP a d M := by
    calc 2 ^ x * (∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311))
        ≤ (4 * G.m) * (2 ^ h * (3000 * (K + 1) * Dd * 2 ^ (v + S))) :=
          Nat.mul_le_mul hlt4m.le hsum
      _ = 12000 * (K + 1) * G.m * (Dd * 2 ^ (h + (v + S))) := by
          rw [pow_add 2 h (v + S)]; generalize 2 ^ h = Y1; generalize 2 ^ (v + S) = Y2; ring
      _ ≤ 12000 * (K + 1) * G.m * (Dd * uOf a G.m ^ (2 * h + 2)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hU)
      _ ≤ 12000 * (K + 1) * G.m * gammaHP a d M :=
          Nat.mul_le_mul_left _ hΓ
  have hD_le_gamma : 9 * D + 12 ≤ 21 * G.m * gammaHP a d M := by
    have hD_le_g : D ≤ gammaHP a d M := by
      have h1 : D ≤ 2 ^ (h + (v + S)) := hD2.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h2 : 2 ^ (h + (v + S)) ≤ Dd * uOf a G.m ^ (2 * h + 2) :=
        hU.trans (Nat.le_mul_of_pos_left _ hDd)
      exact h1.trans (h2.trans hΓ)
    have h1g : 1 ≤ gammaHP a d M := one_le_gammaHP a d M
    have h1mg : gammaHP a d M ≤ G.m * gammaHP a d M := Nat.le_mul_of_pos_left _ hm
    have h9 : 9 * D + 12 ≤ 21 * (G.m * gammaHP a d M) := by omega
    linarith
  have h12021 : 12000 * (K + 1) * G.m * gammaHP a d M + 21 * G.m * gammaHP a d M ≤
      2 ^ 14 * (K + 1) * G.m * gammaHP a d M := by
    have h1 : 21 * G.m * gammaHP a d M ≤ 21 * (K + 1) * G.m * gammaHP a d M := by
      have : 21 ≤ 21 * (K + 1) := Nat.le_mul_of_pos_right 21 (Nat.succ_pos K)
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)
    have h2 : 12000 + 21 ≤ 2 ^ 14 := by decide
    calc 12000 * (K + 1) * G.m * gammaHP a d M + 21 * G.m * gammaHP a d M
        ≤ 12000 * (K + 1) * G.m * gammaHP a d M + 21 * (K + 1) * G.m * gammaHP a d M :=
          Nat.add_le_add_left h1 _
      _ = (12000 + 21) * ((K + 1) * G.m * gammaHP a d M) := by ring
      _ ≤ 2 ^ 14 * ((K + 1) * G.m * gammaHP a d M) := Nat.mul_le_mul_right _ h2
      _ = 2 ^ 14 * (K + 1) * G.m * gammaHP a d M := by ring
  calc 2 ^ x * (∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311)) + 9 * D + 12
      = 2 ^ x * (∑ j ∈ Finset.range D, (buildTopDepthFactor K x G.m d j + 311)) + (9 * D + 12) := by omega
    _ ≤ 12000 * (K + 1) * G.m * gammaHP a d M + 21 * G.m * gammaHP a d M :=
        Nat.add_le_add hmain hD_le_gamma
    _ ≤ 2 ^ 14 * (K + 1) * G.m * gammaHP a d M := h12021

end MinCostFlow.HierPaths

end
