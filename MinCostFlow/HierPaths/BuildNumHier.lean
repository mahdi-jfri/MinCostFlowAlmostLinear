module

public import MinCostFlow.HierPaths.BuildNum
public import MinCostFlow.HierPaths.InitModelCost

/-!
# The construction with the numbers of `HierPaths/Params.lean`

For an input graph `G` with `m` edges, we fix the numbers of the construction (`numParams`).
The root host of `lemma_2` has `2^x` vertices, with `x = ⌈log₂(2m)⌉`. We take
`M = 2^x`, `r = h = depthOf m`, `L = L' = x + 1`, `Δ = 49 (x + 1) + 2` and `b = branchBits m`.
The router scale is `100 d` at the root and `4 P_r` below (`numBh`).

`static_construction_hier` says that the output meets what the consumers need: it is a
hierarchy, its bounds are at most `lvlBound (hOf d) (uOf a m)` at each depth when
`a ≥ 223 + 2 a₀` and `1/d ≤ φ`, its depth is at most `depthOf m`, its branching is at most
`branchOf m`, and its root projects onto `G`. These are the hypotheses of
`initRestSteps_le_gamma`, which `static_initRestSteps_le` applies. With `d = ⌈1/φ⌉`, as the
model uses, the conditions on `d` hold (`ceil_inv`).

The idea of the bounds is this. Every number of the construction is a polynomial in `x` and in
the router scale `b̂`. Since `x + 2 ≤ V = 2^v` with `v = vxOf m`, each is a power of two times a
power of `V` times a power of `b̂` (`rho_le`). Below the root `b̂ = 4 P_r` and `P_r = F^h` with
`F` a power of `V` (`PParam_le`), so all is a power of `2^{h v}`, which `uOf a m = 2^{a h v}`
absorbs. At the root `b̂ = 100 d`, and the factor `d^2` is absorbed by `hOf d = (2 + d)^4`.
-/

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Bounds are monotone in the three numbers. -/
theorem HierData.Bounds.mono {H : HierData} {x b : ℕ} {d ρ κ d' ρ' κ' : ℕ → ℕ}
    (hB : H.Bounds x b d ρ κ) (hd : ∀ j, d j ≤ d' j) (hρ : ∀ j, ρ j ≤ ρ' j)
    (hκ : ∀ j, κ j ≤ κ' j) : H.Bounds x b d' ρ' κ' :=
  ⟨fun j c h1 h2 e he => (hB.emb_length j c h1 h2 e he).trans (hd j),
    fun j g h1 h2 c hc c' hc' hlt q hq => (hB.conn_length j g h1 h2 c hc c' hc' hlt q hq).trans (hd j),
    fun j g h1 h2 i hi => (hB.emb_load j g h1 h2 i hi).trans (hρ j),
    fun j g h1 h2 c hc c' hc' hlt i hi => (hB.conn_load j g h1 h2 c hc c' hc' hlt i hi).trans (hκ j)⟩

/-- The value of `lvlBound` at the root, from `prod_lvlBound`. -/
theorem lvlBound_zero (Hc U : ℕ) : lvlBound Hc U 0 = Hc * U := by
  simpa using prod_lvlBound Hc U 0

/-- The value of `lvlBound` below the root, from `prod_lvlBound`. -/
theorem lvlBound_succ {Hc U : ℕ} (hHc : 1 ≤ Hc) (hU : 1 ≤ U) (k : ℕ) :
    lvlBound Hc U (k + 1) = U := by
  have h := prod_lvlBound Hc U (k + 1)
  rw [Finset.prod_range_succ, prod_lvlBound] at h
  have hpos : 0 < Hc * U ^ (k + 1) := Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)

/-- The numbers of the construction for the input graph `G`. -/
@[expose] def numParams (route : RouterFn) (core : ℕ → Graph → CoreResult) (G : Graph) :
    BuildParams where
  route := route
  core := core
  M := 2 ^ Nat.clog 2 (portCount G)
  r := depthOf G.m
  Δ := 49 * (Nat.clog 2 (portCount G) + 1) + 2
  L := Nat.clog 2 (portCount G) + 1
  L' := Nat.clog 2 (portCount G) + 1
  x := Nat.clog 2 (portCount G)
  b := branchBits G.m

/-- The router scale at each depth: `100 d` at the root and `4 P_r` below. -/
@[expose] def BuildParams.numBh (B : BuildParams) (cfg : ParamConfig) (dd : ℕ) : ℕ → ℕ
  | 0 => 100 * dd
  | _ + 1 => 4 * PParam cfg B.M B.r

/-- With `d = ⌈1/φ⌉`: `1 ≤ d` and `1/d ≤ φ`. -/
theorem ceil_inv {φ : ℝ} (hφ : 0 < φ) : 1 ≤ ⌈1 / φ⌉₊ ∧ 1 / (⌈1 / φ⌉₊ : ℝ) ≤ φ := by
  have h1 : 1 ≤ ⌈1 / φ⌉₊ := Nat.one_le_ceil_iff.mpr (by positivity)
  refine ⟨h1, ?_⟩
  have hc : (0 : ℝ) < ⌈1 / φ⌉₊ := by exact_mod_cast h1
  exact (one_div_le hc hφ).mpr (Nat.le_ceil _)

/-- `x ≤ ⌈x/r⌉ · r` for `1 ≤ r`. -/
private theorem le_ceilDiv_mul {n r : ℕ} (hr : 1 ≤ r) : n ≤ ceilDiv n r * r := by
  unfold ceilDiv
  have := Nat.div_add_mod (n + r - 1) r
  have := Nat.mod_lt (n + r - 1) (show 0 < r by omega)
  rw [Nat.mul_comm]
  generalize r * ((n + r - 1) / r) = P at *
  omega

namespace BuildParams

section num

variable {route : RouterFn} {core : ℕ → Graph → CoreResult} {G : Graph}

/-- The facts about the size `2^x` that `lemma_2` gives: `2^x < 4 m` and `x ≤ xOf m`. -/
theorem num_x (hG : G.IsValid) (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ)
    (hcond : G.IsConductanceExpanderOn G.verts φ) :
    2 ^ (numParams route core G).x < 4 * G.m ∧ (numParams route core G).x ≤ xOf G.m := by
  obtain ⟨⟨_, _, _, hlt⟩, _⟩ := lemma_2 hG hm hφ hcond
  have hlt' : 2 ^ (numParams route core G).x < 4 * G.m := hlt
  refine ⟨hlt', ?_⟩
  unfold xOf
  calc (numParams route core G).x = Nat.clog 2 (2 ^ (numParams route core G).x) :=
        (Nat.clog_pow 2 _ (by norm_num)).symm
    _ ≤ Nat.clog 2 (8 * G.m + 8) := Nat.clog_mono_right 2 (by omega)

/-- `x + 2 ≤ 2^v` and `1 ≤ v`, with `v = vxOf m`. -/
theorem num_v (m : ℕ) : xOf m + 2 ≤ 2 ^ vxOf m ∧ 1 ≤ vxOf m := by
  refine ⟨Nat.le_pow_clog (by norm_num) _, ?_⟩
  show 0 < Nat.clog 2 (xOf m + 2)
  rw [Nat.lt_clog_iff_pow_lt (by norm_num)]
  omega

/-- **The conditions `BuildHyp` on the numbers**, for the host of Lemma 2. -/
theorem num_buildHyp (hG : G.IsValid) (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ)
    (hcond : G.IsConductanceExpanderOn G.verts φ) {cfg : ParamConfig} {dd : ℕ} (hd : 1 ≤ dd)
    (hφd : 1 / (dd : ℝ) ≤ φ) :
    (numParams route core G).BuildHyp cfg (hostGraph ExplicitExpander.explicitGraph G)
      ((numParams route core G).rootβ cfg φ) ((numParams route core G).numBh cfg dd) := by
  set B := numParams route core G with hB
  have hell := ell_two_pow B.x
  have hr : 1 ≤ B.r := by have := two_le_depthOf G.m; exact le_trans (by norm_num) this
  refine buildHyp_root hG hm hφ hcond rfl ?_ le_rfl (by simp [hB, numParams])
    (by simp [hB, numParams]) (by simp [hB, numParams]) ?_ ?_
  · intro j
    cases j with
    | zero => exact bh_ge_root hd hφd
    | succ j => exact bh_ge_inner (one_le_PParam cfg B.M B.r)
  · -- `2^x ≤ N^r`, since `N^r = 2^{max(2, ⌈ℓ/r⌉) r}` and `x < ℓ ≤ ⌈ℓ/r⌉ r`
    unfold NOf
    rw [← pow_mul]
    apply Nat.pow_le_pow_right (by norm_num)
    have h1 := le_ceilDiv_mul (n := ell B.M) hr
    have h2 : ceilDiv (ell B.M) B.r * B.r ≤ max 2 (ceilDiv (ell B.M) B.r) * B.r :=
      Nat.mul_le_mul_right _ (le_max_right _ _)
    have : B.M = 2 ^ B.x := rfl
    rw [this] at h1 h2 ⊢
    omega
  · -- `49 L' ≤ 4096 ℓ(M)`, since `L' = x + 1 ≤ ℓ(M)`
    have : B.M = 2 ^ B.x := rfl
    unfold deltaParam tParam LParam
    rw [this]
    show 49 * (B.x + 1) ≤ _
    omega

/-- **The bounds fit**: at each depth `j`, the load bound `(49 L' + 2) R_j` of the construction is
at most `lvlBound (hOf d) (uOf a m) j`. -/
theorem num_rho_le (hG : G.IsValid) (hm : 1 ≤ G.m) {φ : ℝ} (hφ : 0 < φ)
    (hcond : G.IsConductanceExpanderOn G.verts φ) {cfg : ParamConfig} {a dd : ℕ}
    (ha : 223 + 2 * cfg.a₀ ≤ a) (hd : 1 ≤ dd) (j : ℕ) :
    (49 * (numParams route core G).L' + 2) *
        routeCong (numParams route core G).Δ ((numParams route core G).numBh cfg dd j)
          (numParams route core G).L ≤
      lvlBound (hOf dd) (uOf a G.m) j := by
  set B := numParams route core G with hB
  obtain ⟨_, hxX⟩ := num_x (route := route) (core := core) hG hm hφ hcond
  obtain ⟨hV, hv1⟩ := num_v G.m
  set v := vxOf G.m
  set h := depthOf G.m
  have hh : 1 ≤ h := le_trans (by norm_num) (two_le_depthOf G.m)
  have hxc : Nat.clog 2 (portCount G) ≤ xOf G.m := hxX
  have hΔ : B.Δ ≤ 64 * 2 ^ v := by
    show 49 * (Nat.clog 2 (portCount G) + 1) + 2 ≤ _; omega
  have hL : B.L ≤ 2 ^ v := by show Nat.clog 2 (portCount G) + 1 ≤ _; omega
  have hΔeq : 49 * B.L' + 2 = B.Δ := rfl
  rw [hΔeq]
  have hpow : (2 ^ v) ^ 5 = 2 ^ (5 * v) := by rw [← pow_mul, Nat.mul_comm]
  cases j with
  | zero =>
    have hρ := rho_le (bh := 100 * dd) hΔ hL (by omega) Nat.one_le_two_pow
    have hexp := exp_root (show 47 ≤ a by omega) hh hv1
    have hdd : dd ^ 2 ≤ (2 + dd) ^ 4 :=
      calc dd ^ 2 ≤ (2 + dd) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ (2 + dd) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
    show B.Δ * routeCong B.Δ (100 * dd) B.L ≤ _
    rw [lvlBound_zero]
    calc B.Δ * routeCong B.Δ (100 * dd) B.L ≤ 2 ^ 28 * (100 * dd) ^ 2 * (2 ^ v) ^ 5 := hρ
      _ = 2 ^ 28 * 10000 * dd ^ 2 * 2 ^ (5 * v) := by rw [hpow]; ring
      _ ≤ 2 ^ 42 * dd ^ 2 * 2 ^ (5 * v) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
      _ = dd ^ 2 * 2 ^ (42 + 5 * v) := by rw [pow_add]; ring
      _ ≤ (2 + dd) ^ 4 * 2 ^ (a * h * v) :=
          Nat.mul_le_mul hdd (Nat.pow_le_pow_right (by norm_num) hexp)
  | succ j =>
    have hP1 := one_le_PParam cfg B.M B.r
    have hρ := rho_le (bh := 4 * PParam cfg B.M B.r) hΔ hL (by omega) Nat.one_le_two_pow
    have hell : ell B.M ≤ 2 ^ v := by
      have := (ell_two_pow (Nat.clog 2 (portCount G))).2
      show ell (2 ^ Nat.clog 2 (portCount G)) ≤ _
      omega
    have hP := PParam_le (cfg := cfg) hell B.r
    have hr : B.r = h := rfl
    rw [hr] at hP
    have hexp := exp_inner ha hh hv1
    show B.Δ * routeCong B.Δ (4 * PParam cfg B.M B.r) B.L ≤ _
    rw [lvlBound_succ (one_le_hOf' dd) (one_le_uOf a G.m)]
    show _ ≤ 2 ^ (a * h * v)
    calc B.Δ * routeCong B.Δ (4 * PParam cfg B.M B.r) B.L
        ≤ 2 ^ 28 * (4 * PParam cfg B.M B.r) ^ 2 * (2 ^ v) ^ 5 := hρ
      _ = 2 ^ 32 * PParam cfg B.M B.r ^ 2 * 2 ^ (5 * v) := by rw [hpow]; ring
      _ ≤ 2 ^ 32 * (2 ^ (h * (87 + cfg.a₀ + 6 * v))) ^ 2 * 2 ^ (5 * v) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hP 2))
      _ = 2 ^ (32 + 2 * (h * (87 + cfg.a₀ + 6 * v)) + 5 * v) := by
          rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
      _ ≤ 2 ^ (a * h * v) := Nat.pow_le_pow_right (by norm_num) hexp


/-- **The static construction with the numbers of `Params.lean`.** For the router `route` with
cost constant `C`, the output on the root host of `lemma_2` is a hierarchy that meets the hypotheses of
`initRestSteps_le_gamma`: bounds `lvlBound (hOf d) (uOf a m)` at all depths, depth at most
`depthOf m`, branching at most `branchOf m`, at most `4m` terminals, and a root that projects
onto `G`. Its work over the depths `j < D` is at most `∑_{j < D} 2^x F_j(2^b)` (`buildCost_le`).
The hypotheses are on `a` (`a ≥ 223 + 2 a₀`) and on `d` (`1 ≤ d` and `1/d ≤ φ`); with
`d = ⌈1/φ⌉` the latter hold by `ceil_inv`. -/
theorem static_construction_hier {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) :
    ∃ C, ∀ {core : ℕ → Graph → CoreResult} {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ}
      {G : Graph}, G.IsValid → 1 ≤ G.m →
      IsCorePlayer cfg (numParams route core G).M (numParams route core G).r core coreCost →
      ∀ {φ : ℝ}, 0 < φ → G.IsConductanceExpanderOn G.verts φ →
      ∀ {a dd : ℕ}, 223 + 2 * cfg.a₀ ≤ a → 1 ≤ dd → 1 / (dd : ℝ) ≤ φ →
      ((numParams route core G).hier (hostGraph ExplicitExpander.explicitGraph G)).IsValid
        (numParams route core G).x (numParams route core G).b ∧
      ((numParams route core G).hier (hostGraph ExplicitExpander.explicitGraph G)).Bounds
        (numParams route core G).x (numParams route core G).b
        (lvlBound (hOf dd) (uOf a G.m)) (lvlBound (hOf dd) (uOf a G.m))
        (lvlBound (hOf dd) (uOf a G.m)) ∧
      leafDepth (numParams route core G).x (numParams route core G).b ≤ depthOf G.m ∧
      2 ^ (numParams route core G).b ≤ branchOf G.m ∧
      2 ^ (numParams route core G).x ≤ 4 * G.m ∧
      IsProjection G (((numParams route core G).hier
        (hostGraph ExplicitExpander.explicitGraph G)).host 0 0).edges (hostOwner G) (hostLabel G) ∧
      (∀ p < 2 ^ (numParams route core G).x, hostOwner G p < G.n) ∧
      ∀ D, (numParams route core G).buildCost routeCost coreCost
          (hostGraph ExplicitExpander.explicitGraph G) D ≤
        ∑ j ∈ Finset.range D, 2 ^ (numParams route core G).x *
          (numParams route core G).unitCost cfg C ((numParams route core G).numBh cfg dd j)
            (2 ^ (numParams route core G).b) := by
  obtain ⟨C, hC⟩ := hrouter.cost_bound
  refine ⟨C + 2, fun {core cfg coreCost G} hG hm hcore {φ} hφ hcond {a dd} ha hd hφd => ?_⟩
  have hyp := num_buildHyp (route := route) (core := core) (cfg := cfg) hG hm hφ hcond hd hφd
  obtain ⟨hlt, hxX⟩ := num_x (route := route) (core := core) hG hm hφ hcond
  obtain ⟨_, _, _, _, _, _, _, hown, _, hproj, _⟩ := lemma_2 hG hm hφ hcond
  set B := numParams route core G with hB
  have hrouter' : IsMatchingPlayer B.route routeCost := hrouter
  have hcore' : IsCorePlayer cfg B.M B.r B.core coreCost := hcore
  have hΔ : 1 ≤ B.Δ := by show 1 ≤ 49 * _ + 2; omega
  have hL : 1 ≤ B.L := by show 1 ≤ _ + 1; omega
  have hΔL : 1 ≤ 49 * B.L' + 2 := by omega
  have hbh : ∀ j, 1 ≤ B.numBh cfg dd j := by
    intro j
    cases j with
    | zero => show 1 ≤ 100 * dd; omega
    | succ j => show 1 ≤ 4 * PParam cfg B.M B.r; have := one_le_PParam cfg B.M B.r; omega
  have hρ := fun j => num_rho_le (route := route) (core := core) hG hm hφ hcond (cfg := cfg)
    (a := a) (dd := dd) ha hd j
  have hκ : ∀ j, routeCong B.Δ (B.numBh cfg dd j) B.L ≤ lvlBound (hOf dd) (uOf a G.m) j :=
    fun j => (Nat.le_mul_of_pos_left _ hΔL).trans (hρ j)
  have hd' : ∀ j, routePathLen B.Δ (B.numBh cfg dd j) B.L ≤ lvlBound (hOf dd) (uOf a G.m) j :=
    fun j => (pathLen_le_cong hΔ (hbh j) hL).trans (hκ j)
  obtain ⟨hdep, hb1⟩ := depth_bound G.m
  refine ⟨hier_isValid hrouter' hcore' hyp,
    (hier_bounds hrouter' hcore' hyp).mono hd' hρ hκ, ?_, le_rfl, hlt.le, hproj, hown,
    fun D => buildCost_le hrouter' hC hcore' hyp D⟩
  -- the depth: `⌈x/b⌉ ≤ ⌈xOf m / b⌉ ≤ depthOf m`
  have hxc : Nat.clog 2 (portCount G) ≤ xOf G.m := hxX
  exact le_trans (Nat.div_le_div_right (by show Nat.clog 2 (portCount G) + branchBits G.m - 1 ≤ _; omega)) hdep

/-- **The static construction feeds `Init`**: `initRestSteps_le_gamma` applies to the output of
`static_construction_hier` with `d = ⌈1/φ⌉`, when `n ≤ 2m` and `m ≤ M`. -/
theorem static_initRestSteps_le {route : RouterFn} {routeCost : RouterCostFn}
    (hrouter : IsMatchingPlayer route routeCost) {core : ℕ → Graph → CoreResult}
    {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} {G : Graph} (hG : G.IsValid) (hm : 1 ≤ G.m)
    (hcore : IsCorePlayer cfg (numParams route core G).M (numParams route core G).r core coreCost)
    {φ : ℝ} (hφ : 0 < φ) (hcond : G.IsConductanceExpanderOn G.verts φ) {a M : ℕ}
    (ha : 223 + 2 * cfg.a₀ ≤ a) (hn : G.n ≤ 2 * G.m) (hmM : G.m ≤ M) :
    initRestSteps ((numParams route core G).hier (hostGraph ExplicitExpander.explicitGraph G))
        (numParams route core G).x (numParams route core G).b (hostOwner G) (hostLabel G) G.n G.m ≤
      63 * G.m * gammaHP a ⌈1 / φ⌉₊ M := by
  obtain ⟨C, hC⟩ := static_construction_hier hrouter
  obtain ⟨hd, hφd⟩ := ceil_inv hφ
  obtain ⟨hH, hB, hh, hBb, hP, hproj, hown, _⟩ := hC hG hm hcore hφ hcond ha hd hφd
  have hb : 0 < (numParams route core G).b := (depth_bound G.m).2
  exact initRestSteps_le_gamma hb hH (by omega) hB hh hBb hP hn hmM hproj hown

end num

end BuildParams

end MinCostFlow.HierPaths
