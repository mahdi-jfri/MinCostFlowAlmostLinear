module

public import MinCostFlow.HierPaths.BuildNumHier
public import MinCostFlow.HierPaths.InitProg
public import MinCostFlow.HierPaths.InitPairs
public import MinCostFlow.Expander.WordRAMHelpers

/-!
# The output of the static construction, as `StaticData`

The program of the static construction must leave a `StaticData` in memory (`StaticOut`) that
is `Good` and meets `SpecRest` (`StaticContract`). This file fixes that data
and proves its properties; the program that writes it is the subject of the other
`BuildProg*.lean` files.

* `staticDataOf route core G`: the numbers `x, b` of `numParams`, the owners and labels of the
  root host of `lemma_2`, and the hierarchy built on that host.
* `staticDataOf_good`: it is `Good` for `a ≥ 223 + 2 a₀`, `d` with `1 ≤ d` and `1/d ≤ φ`, and
  `m ≤ M`, when no vertex is isolated. All parts come from `static_construction_hier` and
  `lemma_2`; the bound `n ≤ 2m` is the handshake count (`n_le_two_m`).
* `staticDataOf_good_initPre`: the same with the numbers of `Init`'s precondition, with
  `d = dOf phiNum phiDen`.
* `staticDataOf_deg` and `staticDataOf_pairSpecIn`: the degree part of `SpecRest`, and the pair
  arrays for the children that exist (`PairSpecIn`).

The per-depth router scales of the construction do not show in `StaticData`: `Good` asks only
for the bounds `lvlBound (hOf d) (uOf a m)`, which `static_construction_hier` gives at every
depth.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The output of the static construction on the input graph `G`. -/
def staticDataOf (route : RouterFn) (core : ℕ → Graph → CoreResult) (G : Graph) : StaticData :=
  ⟨(numParams route core G).x, (numParams route core G).b, hostOwner G, hostLabel G,
    (numParams route core G).hier (hostGraph ExplicitExpander.explicitGraph G)⟩

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- **No isolated vertex gives `n ≤ 2m`**: the degrees add up to `2m`, and each is at least `1`. -/
theorem n_le_two_m {G : Graph} (hG : G.IsValid) (hdeg : ∀ v < G.n, 1 ≤ G.deg v) :
    G.n ≤ 2 * G.m := by
  rw [← MinCostFlow.Expander.sum_deg_eq_two_mul_m hG]
  calc G.n = ∑ _v ∈ G.verts, 1 := by simp [Graph.verts]
    _ ≤ ∑ v ∈ G.verts, G.deg v := Finset.sum_le_sum fun v hv => hdeg v (by
        simpa [Graph.verts] using hv)

variable {route : RouterFn} {routeCost : RouterCostFn} {core : ℕ → Graph → CoreResult}
  {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ} {G : Graph}

/-- **The output of the construction is `Good`.** -/
theorem staticDataOf_good (hrouter : IsMatchingPlayer route routeCost) (hG : G.IsValid)
    (hm : 1 ≤ G.m)
    (hcore : IsCorePlayer cfg (numParams route core G).M (numParams route core G).r core coreCost)
    {φ : ℝ} (hφ : 0 < φ) (hcond : G.IsConductanceExpanderOn G.verts φ) {a d M : ℕ}
    (ha : 223 + 2 * cfg.a₀ ≤ a) (hd : 1 ≤ d) (hφd : 1 / (d : ℝ) ≤ φ)
    (hdeg : ∀ v < G.n, 1 ≤ G.deg v) (hmM : G.m ≤ M) :
    (staticDataOf route core G).Good a d M G := by
  obtain ⟨C, hC⟩ := BuildParams.static_construction_hier hrouter
  obtain ⟨hH, hB, hh, hBb, hP, hproj, hown, _⟩ := hC hG hm hcore hφ hcond ha hd hφd
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hinj⟩ := lemma_2 hG hm hφ hcond
  exact ⟨(depth_bound G.m).2, hH, hB, hh, hBb, hP, n_le_two_m hG hdeg, hmM, hproj, hinj, hown⟩

/-- `φ = phiNum / phiDen` is positive, and `d = dOf phiNum phiDen` meets `1 ≤ d` and `1/d ≤ φ`. -/
theorem dOf_spec {phiNum phiDen : ℕ} (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) :
    0 < (phiNum : ℝ) / (phiDen : ℝ) ∧ 1 ≤ dOf phiNum phiDen ∧
      1 / (dOf phiNum phiDen : ℝ) ≤ (phiNum : ℝ) / (phiDen : ℝ) := by
  have hn : (0 : ℝ) < phiNum := by exact_mod_cast h1
  have hd : (0 : ℝ) < phiDen := by exact_mod_cast (show 0 < phiDen by omega)
  have hφ : 0 < (phiNum : ℝ) / (phiDen : ℝ) := div_pos hn hd
  exact ⟨hφ, ceil_inv hφ⟩

/-- **`Good` from the precondition of `Init`**, with `d = dOf phiNum phiDen`. -/
theorem staticDataOf_good_initPre (hrouter : IsMatchingPlayer route routeCost)
    {phiNum phiDen M : ℕ} (h1 : 1 ≤ phiNum) (h2 : phiNum ≤ phiDen) (hG : G.IsValid)
    (hm : 1 ≤ G.m) (hmM : G.m ≤ M) (hdeg : ∀ v < G.n, 1 ≤ G.deg v)
    (hcond : G.IsConductanceExpanderOn G.verts ((phiNum : ℝ) / (phiDen : ℝ)))
    (hcore : IsCorePlayer cfg (numParams route core G).M (numParams route core G).r core coreCost)
    {a : ℕ} (ha : 223 + 2 * cfg.a₀ ≤ a) :
    (staticDataOf route core G).Good a (dOf phiNum phiDen) M G := by
  obtain ⟨hφ, hd, hφd⟩ := dOf_spec h1 h2
  exact staticDataOf_good hrouter hG hm hcore hφ hcond ha hd hφd hdeg hmM

/-- **The degree part of `SpecRest`**: the terminals are those of `hostSize G`, with the owners
`hostOwner G`. -/
theorem staticDataOf_deg (a d : ℕ) :
    ∀ w < G.n, G.deg w ≤
      (((staticDataOf route core G).model a d G.m).A.C.ownedBy w).card :=
  StaticData.deg_of_host rfl rfl

/-- **The pair arrays** meet `PairSpecIn` (for the children that exist), from the validity of
the hierarchy. -/
theorem staticDataOf_pairSpecIn {a d M : ℕ} (hS : (staticDataOf route core G).Good a d M G) :
    PairSpecIn ((staticDataOf route core G).model a d G.m).A
      ((staticDataOf route core G).model a d G.m).pairIdx :=
  staticArrays_pairSpecIn hS.b_pos hS.valid

end MinCostFlow.HierPaths

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

variable {route : RouterFn} {routeCost : RouterCostFn} {core : ℕ → Graph → CoreResult}
  {cfg : ParamConfig} {coreCost : ℕ → Graph → ℕ}

/-- **What a program of the static construction must show at its end.** If it is called under
the precondition of `Init` and leaves `staticDataOf route core G` at the heap pointer `h`, with
the returned pointer `v` between `h + |encode|` and `h + Ks · m · Γ`, then the extra part of the
postcondition of `StaticContract` holds. The pair arrays are a hypothesis (the last
conjunct of `hout`, `StaticArrays.PairSpec`). For the children that exist,
`staticDataOf_pairSpecIn` gives them. -/
theorem staticContract_post (hrouter : IsMatchingPlayer route routeCost) {P : PathDSParams}
    {w a Ks : ℕ} (ha : 223 + 2 * cfg.a₀ ≤ a) {args : List ℕ} {mem mem' : ℕ → ℕ} {v : ℕ}
    (hpre : (pathDSDataStructure P w).initPre args mem)
    (hcore : ∀ G : Graph, IsCorePlayer cfg (numParams route core G).M (numParams route core G).r
      core coreCost)
    (hout : ∀ (gAddr phiNum phiDen M h : ℕ) (G : Graph), args = [gAddr, phiNum, phiDen, M, h] →
      GraphAt mem gAddr G →
      StaticOut mem' h (staticDataOf route core G) ∧
        h + (staticDataOf route core G).encode.length ≤ v ∧
        v ≤ h + Ks * G.m * gammaHP a (dOf phiNum phiDen) M ∧
        ((staticDataOf route core G).model a (dOf phiNum phiDen) G.m).A.PairSpec
          ((staticDataOf route core G).model a (dOf phiNum phiDen) G.m).pairIdx) :
    ∃ (gAddr phiNum phiDen M h : ℕ) (G : Graph) (S : StaticData),
      args = [gAddr, phiNum, phiDen, M, h] ∧ GraphAt mem gAddr G ∧ StaticOut mem' h S ∧
      h + S.encode.length ≤ v ∧ v ≤ h + Ks * G.m * gammaHP a (dOf phiNum phiDen) M ∧
      S.Good a (dOf phiNum phiDen) M G ∧ S.SpecRest a (dOf phiNum phiDen) G := by
  obtain ⟨gAddr, phiNum, phiDen, M, h, G, hargs, _, hGat, h1, h2, hG, hm, hmM, hdeg, hcond, _⟩ :=
    hpre
  obtain ⟨hSO, hlo, hhi, hpairs⟩ := hout gAddr phiNum phiDen M h G hargs hGat
  exact ⟨gAddr, phiNum, phiDen, M, h, G, staticDataOf route core G, hargs, hGat, hSO, hlo, hhi,
    staticDataOf_good_initPre hrouter h1 h2 hG hm hmM hdeg hcond (hcore G) ha,
    ⟨hpairs, staticDataOf_deg _ _⟩⟩

end MinCostFlow.HierPaths
