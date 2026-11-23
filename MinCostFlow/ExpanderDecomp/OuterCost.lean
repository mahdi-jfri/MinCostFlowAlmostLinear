module

public import MinCostFlow.ExpanderDecomp.OuterDecomp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Step count of the outer expander decomposition model

This file defines the operation count `outerDecompCost` of the outer decomposition model,
parameterized by the router cost `routeCost`, the core cost `coreCost`, and the fake-edge removal
cost `removeFakeCost`, and proves that it is bounded by `totalTimeRaw cfg G.n G.m r`:

* `IsRemoveFakeCost`: cost specification for `RemoveFake`.
* `outerDecompRecCost`, `outerDecompCost`: exact model operation count mirroring `outerDecompRec`
  and `outerDecompLabels`.
* `outerDecompRecCost_le`: strong induction on `H.edges.length` separating the total cost into
  per-edge game/scan work (multiplied by `outerDecompEdgeSum`) plus trimming work (multiplied by
  `outerDecompWitnessEdgeSum`).
* `outerDecompCost_le_totalTimeRaw`: proves `outerDecompCost ≤ totalTimeRaw cfg G.n G.m r`
  whenever the router and trimming cost constants fit within `cfg.u` (`routeC ≤ 2^11 * cfg.u^3`,
  `trimC ≤ 2^36 * cfg.u^3`).
* `outerDecompCost_le_used`: combines `outerDecompCost_le_totalTimeRaw` with `totalTimeRaw_le_used`
  to obtain the exact target envelope bound at `r = rOf G.m` for `G.m ≥ thresholdB1 envelopeCr`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Cost specification of `RemoveFake` (see `removeFake_spec`): on a compact subgraph `H` with
contracted fake edge list `F'` satisfying `|E(H)| + |F'| ≤ 2 M` and inverse conductance `Λ ≥ 1`,
the work is at most `trimC · (|V(H)| + |F'| + (|E(H)| + |F'|) · Λ² · L²)`. -/
def IsRemoveFakeCost (M trimC : ℕ)
    (removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ) : Prop :=
  ∀ (H : CompactSubgraph) (F' : List (ℕ × ℕ)) (Λ : ℕ),
    H.edges.length + F'.length ≤ 2 * M →
    1 ≤ Λ →
    removeFakeCost H F' Λ ≤
      trimC * (H.verts.length + F'.length +
        (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2)

/-- Recursive operation count of `outerDecompRec`, parameterized by `coreCost`, `routeCost`, and
`removeFakeCost`. Base-case component search on a stripped compact subgraph with `e` edges costs
`4 * e`; each nonterminal node pays `outerGameCost`, `20 * e` for local rounding/splitting/isolation
scans, and (on a witness) `removeFakeCost`. -/
noncomputable def outerDecompRecCost (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ)
    (G : Graph) (H : CompactSubgraph) : ℕ :=
  if _hQ : H.edges.length ≤ QOut cfg M r then
    4 * H.edges.length
  else
    let gCost := outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet
    match outerGame cfg M r cloud core route G H.vertSet with
    | .cut U =>
      let S := roundPortCut G H.vertSet U
      let (_, act₁) := (H.restrict S).stripIsolated
      let (_, act₂) := (H.restrict (H.vertSet \ S)).stripIsolated
      let c₁ := if _h1 : act₁.edges.length < H.edges.length then
          outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₁
        else 0
      let c₂ := if _h2 : act₂.edges.length < H.edges.length then
          outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₂
        else 0
      gCost + 20 * H.edges.length + c₁ + c₂
    | .witness _ F_out =>
      let F' := contractEdges G H.vertSet F_out
      let R := removeFake G.n G.edges F' H.vertSet (1 / (Lambda cfg M r : ℝ))
      let (_, actRest) := (H.restrict (H.vertSet \ R)).stripIsolated
      let tCost := removeFakeCost H F' (Lambda cfg M r)
      let cRest := if _hr : actRest.edges.length < H.edges.length then
          outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G actRest
        else 0
      gCost + 20 * H.edges.length + tCost + cRest
termination_by H.edges.length

/-- Total operation count of the outer algorithm on `G`: root isolation scan, label array
initialization and painting (`4 * G.n + 4 * G.m`), plus `outerDecompRecCost` on the root active
subgraph. -/
noncomputable def outerDecompCost (cfg : ParamConfig) (M r : ℕ)
    (cloud : ℕ → Graph)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ)
    (route : RouterFn) (routeCost : RouterCostFn)
    (removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ)
    (G : Graph) : ℕ :=
  let act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
  4 * G.n + 4 * G.m +
    outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₀

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Per-edge arithmetic helpers for the step count -/

/-- Bounds `(12 * e + 1) * (dOut + 1) * ROut + 1` by `2^29 * e * bOut^3 * L^3` for `1 ≤ e`. -/
private theorem route_term_le (cfg : ParamConfig) (M e : ℕ) (he : 1 ≤ e) :
    (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1 ≤
      2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 := by
  have hb : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hbL : 1 ≤ bOut cfg M * LParam M := Nat.mul_pos hb (by omega)
  have he13 : 12 * e + 1 ≤ 13 * e := by omega
  have hd : dOut cfg M + 1 ≤ 321 * (bOut cfg M * LParam M) := by
    unfold dOut
    have hrew : 320 * bOut cfg M * LParam M = 320 * (bOut cfg M * LParam M) := by ring
    omega
  have hR : ROut cfg M ≤ 160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by
    unfold ROut
    calc 160 * bOut cfg M * (dOut cfg M + 1) * LParam M
        ≤ 160 * bOut cfg M * (321 * (bOut cfg M * LParam M)) * LParam M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hd)
      _ = 160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2 := by ring
  have hprod : (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M ≤
      13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by
    calc (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M
        ≤ (13 * e) * (321 * (bOut cfg M * LParam M)) *
            (160 * 321 * (bOut cfg M) ^ 2 * (LParam M) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul he13 hd) hR
      _ = 13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
  have hpos : 1 ≤ e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 :=
    Nat.mul_pos (Nat.mul_pos he (Nat.pow_pos hb)) (Nat.pow_pos (by omega))
  have hconst : 13 * 321 * 160 * 321 + 1 ≤ 2 ^ 29 := by decide
  calc (12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1
      ≤ 13 * 321 * 160 * 321 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) +
          1 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by omega
    _ = (13 * 321 * 160 * 321 + 1) * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
    _ ≤ 2 ^ 29 * (e * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := Nat.mul_le_mul_right _ hconst
    _ = 2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3 := by ring

/-- Per-node game + scan cost bound: for `1 ≤ e`,
`12 * e + (49 * L + 1) * (2 * e * N^2 * W^{10r^2+10} + routeC * ((12 * e + 1) * (dOut + 1) * ROut + 1) + 4 * e) + 20 * e`
is bounded by `e * perEdgeFactor`. -/
private theorem node_game_scan_le (cfg : ParamConfig) (M r routeC e : ℕ) (he : 1 ≤ e) :
    12 * e + (49 * LParam M + 1) *
      (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
        routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) + 20 * e ≤
    e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
      routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
      232 * LParam M) := by
  have hL4 : 4 ≤ LParam M := four_le_LParam M
  have h49_le_t : 49 * LParam M + 1 ≤ tParam M := by unfold tParam; omega
  have h49_le_50 : 49 * LParam M + 1 ≤ 50 * LParam M := by omega
  have hcore : (49 * LParam M + 1) *
      (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) ≤
      e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) := by
    calc (49 * LParam M + 1) *
          (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10))
        ≤ (tParam M + 1) *
          (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) := by ring
  have hrt : (49 * LParam M + 1) *
      (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1)) ≤
      e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by
    have h1 := route_term_le cfg M e he
    calc (49 * LParam M + 1) *
          (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1))
        ≤ tParam M * (routeC * (2 ^ 29 * e * (bOut cfg M) ^ 3 * (LParam M) ^ 3)) :=
          Nat.mul_le_mul h49_le_t (Nat.mul_le_mul_left routeC h1)
      _ = e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) := by ring
  have hscan : 12 * e + (49 * LParam M + 1) * (4 * e) + 20 * e ≤ e * (232 * LParam M) := by
    have h1 : (49 * LParam M + 1) * (4 * e) ≤ (50 * LParam M) * (4 * e) :=
      Nat.mul_le_mul_right _ h49_le_50
    have h2 : 32 * e ≤ 32 * LParam M * e := by
      have : 32 * 1 ≤ 32 * LParam M := Nat.mul_le_mul_left 32 (by omega)
      calc 32 * e = (32 * 1) * e := by ring
        _ ≤ (32 * LParam M) * e := Nat.mul_le_mul_right e this
    have hring1 : (50 * LParam M) * (4 * e) + 32 * LParam M * e = e * (232 * LParam M) := by ring
    omega
  have hlhs : 12 * e + (49 * LParam M + 1) *
        (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
          routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1) + 4 * e) + 20 * e =
      (49 * LParam M + 1) * (2 * e * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
      (49 * LParam M + 1) * (routeC * ((12 * e + 1) * (dOut cfg M + 1) * ROut cfg M + 1)) +
      (12 * e + (49 * LParam M + 1) * (4 * e) + 20 * e) := by ring
  have hrhs : e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
        routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
        232 * LParam M) =
      e * (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10)) +
      e * (routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3) +
      e * (232 * LParam M) := by ring
  rw [hlhs, hrhs]
  omega

/-- Per-witness trimming cost bound: when `|H.verts| ≤ 2 * e`, `|F'| ≤ e`, `e ≤ M`, and `1 ≤ Λ`,
`removeFakeCost H F' Λ ≤ e * (5 * trimC * Λ^2 * L^2)`. -/
private theorem witness_trim_le {M trimC : ℕ}
    {removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ}
    (htrim : IsRemoveFakeCost M trimC removeFakeCost)
    {H : CompactSubgraph} {F' : List (ℕ × ℕ)} {Λ : ℕ}
    (hV : H.verts.length ≤ 2 * H.edges.length) (hF : F'.length ≤ H.edges.length)
    (heM : H.edges.length ≤ M) (hΛ : 1 ≤ Λ) :
    removeFakeCost H F' Λ ≤ H.edges.length * (5 * trimC * Λ ^ 2 * (LParam M) ^ 2) := by
  have h1 := htrim H F' Λ (by omega) hΛ
  have hL : 4 ≤ LParam M := four_le_LParam M
  have hLL : 1 ≤ Λ ^ 2 * (LParam M) ^ 2 :=
    Nat.mul_pos (Nat.pow_pos hΛ) (Nat.pow_pos (by omega))
  have h3 : H.verts.length + F'.length ≤ 3 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) := by
    calc H.verts.length + F'.length ≤ 3 * H.edges.length := by omega
      _ = 3 * H.edges.length * 1 := (mul_one _).symm
      _ ≤ 3 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) := Nat.mul_le_mul_left _ hLL
  have h2 : (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2 ≤
      2 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) := by
    calc (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2
        = (H.edges.length + F'.length) * (Λ ^ 2 * (LParam M) ^ 2) := by ring
      _ ≤ (2 * H.edges.length) * (Λ ^ 2 * (LParam M) ^ 2) := Nat.mul_le_mul_right _ (by omega)
  have hsum : H.verts.length + F'.length + (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2 ≤
      5 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) := by
    have hring : 3 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) +
        2 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) =
        5 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2) := by ring
    omega
  calc removeFakeCost H F' Λ
      ≤ trimC * (H.verts.length + F'.length +
          (H.edges.length + F'.length) * Λ ^ 2 * (LParam M) ^ 2) := h1
    _ ≤ trimC * (5 * H.edges.length * (Λ ^ 2 * (LParam M) ^ 2)) := Nat.mul_le_mul_left trimC hsum
    _ = H.edges.length * (5 * trimC * Λ ^ 2 * (LParam M) ^ 2) := by ring

/-! ### Strong induction on `outerDecompRecCost` -/

/-- Bounds `outerDecompRecCost` in terms of `outerDecompEdgeSum` and `outerDecompWitnessEdgeSum`. -/
theorem outerDecompRecCost_le {cfg : ParamConfig} {M r routeC trimC : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α) (hA60 : 60 ≤ cfg.A)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ}
    (hcore : IsCorePlayer cfg M r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    (hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
      X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
      1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
      ValidTerminalPairs X' pairs →
      routeCost G' X' pairs Δ L b z' ≤
        routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
    (htrim : IsRemoveFakeCost M trimC removeFakeCost)
    {G : Graph} (hv : G.IsValid)
    (h2M_pow : 2 * M ≤ (NOf M r) ^ r) (h2M_L : 2 * M < 2 ^ LParam M) :
    ∀ (eBound : ℕ) (H : CompactSubgraph),
      H.edges.length ≤ eBound →
      H.Represents G H.vertSet →
      H.vertSet ⊆ G.verts →
      H.edges.length ≤ M →
      (∀ v ∈ H.vertSet, 1 ≤ G.degIn H.vertSet v) →
      H.verts.length ≤ 2 * H.edges.length →
      outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G H ≤
        outerDecompEdgeSum cfg M r cloud core route G H *
          (2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
            routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
            232 * LParam M) +
        outerDecompWitnessEdgeSum cfg M r cloud core route G H *
          (5 * trimC * (Lambda cfg M r) ^ 2 * (LParam M) ^ 2) := by
  let perEdge :=
    2 * (tParam M + 1) * (NOf M r) ^ 2 * (WParam cfg M) ^ (10 * r ^ 2 + 10) +
      routeC * 2 ^ 29 * tParam M * (bOut cfg M) ^ 3 * (LParam M) ^ 3 +
      232 * LParam M
  let perWit := 5 * trimC * (Lambda cfg M r) ^ 2 * (LParam M) ^ 2
  have hD1 : 1 ≤ DOut cfg M r := one_le_DOut cfg M r
  have hb1 : 1 ≤ bOut cfg M := one_le_bOut cfg M
  have hb_a0 : 2 * cfg.a₀ ≤ bOut cfg M := two_mul_a0_le_bOut cfg M
  have h4_le_perEdge : 4 ≤ perEdge := by
    dsimp only [perEdge]
    have := four_le_LParam M
    omega
  intro eBound
  induction eBound with
  | zero =>
    intro H heB _ _ _ _ _
    have he0 : H.edges.length = 0 := by omega
    unfold outerDecompEdgeSum outerDecompWitnessEdgeSum
    rw [outerDecompRecCost.eq_def, outerDecompAux.eq_def]
    have hQ : H.edges.length ≤ QOut cfg M r := by omega
    simp only [hQ, ↓reduceDIte]
    simp only [he0, mul_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    intro H heB hRep hXV heM hXdeg hVlen
    unfold outerDecompEdgeSum outerDecompWitnessEdgeSum
    rw [outerDecompRecCost.eq_def, outerDecompAux.eq_def]
    by_cases hQ : H.edges.length ≤ QOut cfg M r
    · simp only [hQ, ↓reduceDIte, zero_mul, add_zero]
      calc 4 * H.edges.length = H.edges.length * 4 := by ring
        _ ≤ H.edges.length * perEdge := Nat.mul_le_mul_left _ h4_le_perEdge
    · simp only [hQ, ↓reduceDIte]
      have hQlt : QOut cfg M r < H.edges.length := by omega
      have he_eq : (G.inside H.vertSet).length = H.edges.length :=
        congrArg List.length hRep.2.2.symm
      have he_pos : 1 ≤ (G.inside H.vertSet).length := by unfold QOut at hQlt; omega
      have h2D_lt : 2 * DOut cfg M r < (G.inside H.vertSet).length := by unfold QOut at hQlt; omega
      have h2e_pow : 2 * (G.inside H.vertSet).length ≤ (NOf M r) ^ r := by omega
      have h2e_L : 2 * (G.inside H.vertSet).length < 2 ^ LParam M := by omega
      have hgame := outerGame_spec hcloud hcore hroute he_pos h2e_pow h2e_L
      have hgcost := outerGame_cost_le hcloud hcore hroute hrouteC he_pos h2e_pow h2e_L
      have hnode_le :
          outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet +
            20 * H.edges.length ≤ H.edges.length * perEdge := by
        have hstep := node_game_scan_le cfg M r routeC H.edges.length (by omega)
        rw [he_eq] at hgcost
        dsimp only [perEdge]
        omega
      cases hres : outerGame cfg M r cloud core route G H.vertSet with
      | cut U =>
        dsimp only
        rw [hres] at hgame
        obtain ⟨hUV, hUsparse, hUz1, hUz2⟩ := hgame
        let S := roundPortCut G H.vertSet U
        obtain ⟨hSX, _, _, hUret1, hUret2, _, _⟩ := lemma_8 hcloud cfg.ha₀ hα hb_a0 hUV hUsparse
        change S ⊆ H.vertSet at hSX
        change U.card ≤ 2 * G.volIn H.vertSet S at hUret1
        change ((portGraph cloud G H.vertSet).verts \ U).card ≤
          2 * G.volIn H.vertSet (H.vertSet \ S) at hUret2
        obtain ⟨_, _, hlt1_in, hlt2_in⟩ := edge_shrink_cut G hSX hD1 h2D_lt
          (by omega) (by omega) hUret1 hUret2
        have hrep1 := CompactSubgraph.restrict_represents hRep hSX
        have hrep2 := CompactSubgraph.restrict_represents hRep
          (Finset.sdiff_subset (s := H.vertSet) (t := S))
        have hst1 := CompactSubgraph.stripIsolated_spec hrep1
        have hst2 := CompactSubgraph.stripIsolated_spec hrep2
        let act₁ := (H.restrict S).stripIsolated.2
        let act₂ := (H.restrict (H.vertSet \ S)).stripIsolated.2
        have he1_eq : act₁.edges.length = (G.inside S).length := by
          have h1 : act₁.edges = (H.restrict S).edges := hst1.2.2.2.2.2.1
          rw [h1, hrep1.2.2]
        have he2_eq : act₂.edges.length = (G.inside (H.vertSet \ S)).length := by
          have h1 : act₂.edges = (H.restrict (H.vertSet \ S)).edges := hst2.2.2.2.2.2.1
          rw [h1, hrep2.2.2]
        have hlt1 : act₁.edges.length < H.edges.length := by omega
        have hlt2 : act₂.edges.length < H.edges.length := by omega
        have hc1 : (if _h1 : act₁.edges.length < H.edges.length then
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₁
            else 0) =
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₁ :=
          dite_eq_left_of_eq_true (eq_true hlt1)
        have hc2 : (if _h2 : act₂.edges.length < H.edges.length then
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₂
            else 0) =
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₂ :=
          dite_eq_left_of_eq_true (eq_true hlt2)
        have ho1 : (if _h1 : act₁.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G act₁ :=
          dite_eq_left_of_eq_true (eq_true hlt1)
        have ho2 : (if _h2 : act₂.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G act₂ :=
          dite_eq_left_of_eq_true (eq_true hlt2)
        have hact1_sub : act₁.vertSet ⊆ S := by
          rw [← hst1.2.2.1]; exact Finset.subset_union_right
        have hact2_sub : act₂.vertSet ⊆ H.vertSet \ S := by
          rw [← hst2.2.2.1]; exact Finset.subset_union_right
        have ih1 := ih act₁ (by omega) hst1.2.2.2.2.1 ((hact1_sub.trans hSX).trans hXV) (by omega)
          hst1.2.2.2.2.2.2.1 hst1.2.2.2.2.2.2.2
        have ih2 := ih act₂ (by omega) hst2.2.2.2.2.1
          ((hact2_sub.trans Finset.sdiff_subset).trans hXV) (by omega)
          hst2.2.2.2.2.2.2.1 hst2.2.2.2.2.2.2.2
        have hdist1 : (H.edges.length + outerDecompEdgeSum cfg M r cloud core route G act₁ +
            outerDecompEdgeSum cfg M r cloud core route G act₂) * perEdge =
            H.edges.length * perEdge +
            outerDecompEdgeSum cfg M r cloud core route G act₁ * perEdge +
            outerDecompEdgeSum cfg M r cloud core route G act₂ * perEdge := by ring
        have hdist2 : (outerDecompWitnessEdgeSum cfg M r cloud core route G act₁ +
            outerDecompWitnessEdgeSum cfg M r cloud core route G act₂) * perWit =
            outerDecompWitnessEdgeSum cfg M r cloud core route G act₁ * perWit +
            outerDecompWitnessEdgeSum cfg M r cloud core route G act₂ * perWit := by ring
        change outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet +
            20 * H.edges.length +
            (if _h1 : act₁.edges.length < H.edges.length then
              outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₁
              else 0) +
            (if _h2 : act₂.edges.length < H.edges.length then
              outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₂
              else 0) ≤
          (H.edges.length +
            (if _h1 : act₁.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).edgeSum +
            (if _h2 : act₂.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).edgeSum) * perEdge +
          ((if _h1 : act₁.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G act₁ else ⟨[], 0, 0, 0⟩).witnessEdgeSum +
            (if _h2 : act₂.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G act₂ else ⟨[], 0, 0, 0⟩).witnessEdgeSum) * perWit
        rw [hc1, hc2, ho1, ho2]
        change outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet +
            20 * H.edges.length +
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₁ +
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₂ ≤
          (H.edges.length + outerDecompEdgeSum cfg M r cloud core route G act₁ +
            outerDecompEdgeSum cfg M r cloud core route G act₂) * perEdge +
          (outerDecompWitnessEdgeSum cfg M r cloud core route G act₁ +
            outerDecompWitnessEdgeSum cfg M r cloud core route G act₂) * perWit
        rw [hdist1, hdist2]
        dsimp only [perEdge, perWit] at hnode_le ⊢
        omega
      | witness W_out F_out =>
        rw [hres] at hgame
        obtain ⟨hW_exp, hF_valid, hF_len, hF_deg, emb, hemb, hcong⟩ := hgame
        let F' := contractEdges G H.vertSet F_out
        let R := removeFake G.n G.edges F' H.vertSet (1 / (Lambda cfg M r : ℝ))
        obtain ⟨hRX, _, _, _, h35⟩ := outerWitness_removeFake hcloud hA60 hv hXV hXdeg
          he_pos hW_exp hF_valid hF_len hF_deg hemb hcong
        change R ⊆ H.vertSet at hRX
        change 16 * bOut cfg M * G.volIn H.vertSet (H.vertSet \ R) ≤
          (G.inside H.vertSet).length at h35
        obtain ⟨_, _, hltR_in, _, _⟩ := edge_shrink_witness G hRX hb1 hD1 he_pos h35
        have hrepR := CompactSubgraph.restrict_represents hRep
          (Finset.sdiff_subset (s := H.vertSet) (t := R))
        have hstR := CompactSubgraph.stripIsolated_spec hrepR
        let actRest := (H.restrict (H.vertSet \ R)).stripIsolated.2
        have heR_eq : actRest.edges.length = (G.inside (H.vertSet \ R)).length := by
          have h1 : actRest.edges = (H.restrict (H.vertSet \ R)).edges := hstR.2.2.2.2.2.1
          rw [h1, hrepR.2.2]
        have hltR : actRest.edges.length < H.edges.length := by omega
        have hcR : (if _hr : actRest.edges.length < H.edges.length then
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G actRest
            else 0) =
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G actRest :=
          dite_eq_left_of_eq_true (eq_true hltR)
        have hoR : (if _hr : actRest.edges.length < H.edges.length then
            outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩) =
            outerDecompAux cfg M r cloud core route G actRest :=
          dite_eq_left_of_eq_true (eq_true hltR)
        have hactR_sub : actRest.vertSet ⊆ H.vertSet \ R := by
          rw [← hstR.2.2.1]; exact Finset.subset_union_right
        have ihR := ih actRest (by omega) hstR.2.2.2.2.1
          ((hactR_sub.trans Finset.sdiff_subset).trans hXV) (by omega)
          hstR.2.2.2.2.2.2.1 hstR.2.2.2.2.2.2.2
        have hF'_le_e : F'.length ≤ H.edges.length := by
          have h1 : F'.length ≤ tParam M * (H.edges.length / DOut cfg M r) := by
            have := le_trans (contractEdges_length_le G H.vertSet F_out) hF_len
            rwa [he_eq] at this
          have htD : tParam M ≤ DOut cfg M r := by
            unfold DOut
            have hA := cfg.A_pos
            have hLam := one_le_Lambda cfg M r
            have hb := one_le_bOut cfg M
            have hfac : 1 ≤ 16 * cfg.A * Lambda cfg M r * bOut cfg M := by
              calc 1 ≤ 16 * 16 * 1 * 1 := by decide
                _ ≤ 16 * cfg.A * Lambda cfg M r * bOut cfg M :=
                  Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hA) hLam) hb
            calc tParam M = tParam M * 1 := (mul_one _).symm
              _ ≤ tParam M * (16 * cfg.A * Lambda cfg M r * bOut cfg M) :=
                  Nat.mul_le_mul_left _ hfac
              _ = 16 * cfg.A * tParam M * Lambda cfg M r * bOut cfg M := by ring
          calc F'.length ≤ tParam M * (H.edges.length / DOut cfg M r) := h1
            _ ≤ DOut cfg M r * (H.edges.length / DOut cfg M r) := Nat.mul_le_mul_right _ htD
            _ ≤ H.edges.length := Nat.mul_div_le _ _
        have htrim_le : removeFakeCost H F' (Lambda cfg M r) ≤ H.edges.length * perWit :=
          witness_trim_le htrim hVlen hF'_le_e heM (one_le_Lambda cfg M r)
        have hdist1 : (H.edges.length + outerDecompEdgeSum cfg M r cloud core route G actRest) * perEdge =
            H.edges.length * perEdge +
            outerDecompEdgeSum cfg M r cloud core route G actRest * perEdge := by ring
        have hdist2 : (H.edges.length + outerDecompWitnessEdgeSum cfg M r cloud core route G actRest) * perWit =
            H.edges.length * perWit +
            outerDecompWitnessEdgeSum cfg M r cloud core route G actRest * perWit := by ring
        change outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet +
            20 * H.edges.length + removeFakeCost H F' (Lambda cfg M r) +
            (if _hr : actRest.edges.length < H.edges.length then
              outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G actRest
              else 0) ≤
          (H.edges.length +
            (if _hr : actRest.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).edgeSum) * perEdge +
          (H.edges.length +
            (if _hr : actRest.edges.length < H.edges.length then
              outerDecompAux cfg M r cloud core route G actRest else ⟨[], 0, 0, 0⟩).witnessEdgeSum) * perWit
        rw [hcR, hoR]
        change outerGameCost cfg M r cloud core coreCost route routeCost G H.vertSet +
            20 * H.edges.length + removeFakeCost H F' (Lambda cfg M r) +
            outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G actRest ≤
          (H.edges.length + outerDecompEdgeSum cfg M r cloud core route G actRest) * perEdge +
          (H.edges.length + outerDecompWitnessEdgeSum cfg M r cloud core route G actRest) * perWit
        rw [hdist1, hdist2]
        dsimp only [perEdge, perWit] at hnode_le htrim_le ⊢
        omega

/-! ### Main step-count theorems -/

/-- **Outer step count**: for any valid graph `G` with `1 ≤ r ≤ ell G.m`, cloud expanders
of expansion `≥ 1 / cfg.a₀`, `60 ≤ cfg.A`, a core player, a matching player with cost constant
`routeC ≤ 2^11 * cfg.u^3`, and a `RemoveFake` cost bound with `trimC ≤ 2^36 * cfg.u^3`, the total
operation count `outerDecompCost` is at most `totalTimeRaw cfg G.n G.m r`. -/
theorem outerDecompCost_le_totalTimeRaw {cfg : ParamConfig} {r routeC trimC : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α) (hA60 : 60 ≤ cfg.A)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ}
    {G : Graph} (hv : G.IsValid) (hr1 : 1 ≤ r) (hrl : r ≤ ell G.m)
    (hcore : IsCorePlayer cfg G.m r core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    (hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
      X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
      1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
      ValidTerminalPairs X' pairs →
      routeCost G' X' pairs Δ L b z' ≤
        routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
    (htrim : IsRemoveFakeCost G.m trimC removeFakeCost)
    (hrouteU : routeC ≤ 2 ^ 11 * cfg.u ^ 3)
    (htrimU : trimC ≤ 2 ^ 36 * cfg.u ^ 3) :
    outerDecompCost cfg G.m r cloud core coreCost route routeCost removeFakeCost G ≤
      totalTimeRaw cfg G.n G.m r := by
  have h2M_pow : 2 * G.m ≤ (NOf G.m r) ^ r := by
    have := two_mul_add_two_le_NOf_pow G.m hr1; omega
  have h2M_L : 2 * G.m < 2 ^ LParam G.m := by
    have h1 := two_mul_add_two_le_NOf_pow G.m hr1
    have h2 := NOf_pow_add_two_le_two_pow_L G.m hr1 hrl
    omega
  have hrep0 := CompactSubgraph.ofGraph_represents hv
  have hst0 := CompactSubgraph.stripIsolated_spec hrep0
  let act₀ := (CompactSubgraph.ofGraph G).stripIsolated.2
  have he0_eq : act₀.edges.length = G.m := by
    have h1 : act₀.edges = (CompactSubgraph.ofGraph G).edges := hst0.2.2.2.2.2.1
    rw [h1]; rfl
  have hact0_sub : act₀.vertSet ⊆ G.verts := by
    rw [← hst0.2.2.1]; exact Finset.subset_union_right
  have hspec := outerDecompLabels_spec hcloud hα hA60 hv hr1 hrl hcore hroute
  have hesum_le : outerDecompEdgeSum cfg G.m r cloud core route G act₀ ≤ HDepth cfg G.m r * G.m :=
    hspec.2.2.1
  have hwsum_le : outerDecompWitnessEdgeSum cfg G.m r cloud core route G act₀ ≤ 2 * G.m := by
    have h15 : 15 * outerDecompWitnessEdgeSum cfg G.m r cloud core route G act₀ ≤ 16 * G.m :=
      hspec.2.2.2
    omega
  have hrec := outerDecompRecCost_le hcloud hα hA60 hcore hroute hrouteC htrim hv h2M_pow h2M_L
    G.m act₀ (by omega) hst0.2.2.2.2.1 hact0_sub (by omega)
    hst0.2.2.2.2.2.2.1 hst0.2.2.2.2.2.2.2
  have hu3 : 1 ≤ cfg.u ^ 3 := Nat.pow_pos cfg.hu
  have hC_ge_4 : 4 ≤ cfg.CTotal := by unfold ParamConfig.CTotal; nlinarith
  have hC_ge_2 : 2 ≤ cfg.CTotal := by omega
  have hC_ge_236 : 236 ≤ cfg.CTotal := by unfold ParamConfig.CTotal; nlinarith
  have hC_ge_rt : routeC * 2 ^ 29 ≤ cfg.CTotal := by
    unfold ParamConfig.CTotal
    calc routeC * 2 ^ 29 ≤ (2 ^ 11 * cfg.u ^ 3) * 2 ^ 29 := Nat.mul_le_mul_right _ hrouteU
      _ = 2 ^ 40 * cfg.u ^ 3 := by ring
  have hC_ge_trim : 10 * trimC ≤ cfg.CTotal := by
    unfold ParamConfig.CTotal
    calc 10 * trimC ≤ 10 * (2 ^ 36 * cfg.u ^ 3) := Nat.mul_le_mul_left 10 htrimU
      _ ≤ 16 * (2 ^ 36 * cfg.u ^ 3) := Nat.mul_le_mul_right _ (by decide)
      _ = 2 ^ 40 * cfg.u ^ 3 := by ring
  set M := G.m
  set H := HDepth cfg M r
  set L := LParam M
  set t := tParam M
  set N := NOf M r
  set W := WParam cfg M
  set b := bOut cfg M
  set Λ := Lambda cfg M r
  have hH1 : 1 ≤ H := by unfold H HDepth; omega
  have hL1 : 1 ≤ L := le_trans (by decide) (four_le_LParam M)
  have h4M : 4 * M ≤ 4 * (M * H * L) := by
    have : 1 ≤ H * L := Nat.mul_pos hH1 hL1
    calc 4 * M = 4 * (M * 1) := by ring
      _ ≤ 4 * (M * (H * L)) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left M this)
      _ = 4 * (M * H * L) := by ring
  have ht1 : 4 * G.n ≤ cfg.CTotal * G.n := Nat.mul_le_mul_right G.n hC_ge_4
  have ht2 : (H * M) * (2 * (t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10)) ≤
      cfg.CTotal * (M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))) := by
    calc (H * M) * (2 * (t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))
        = 2 * (M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))) := by ring
      _ ≤ cfg.CTotal * (M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))) :=
          Nat.mul_le_mul_right _ hC_ge_2
  have ht3 : (H * M) * (routeC * 2 ^ 29 * t * b ^ 3 * L ^ 3) ≤
      cfg.CTotal * (M * H * (t * b ^ 3 * L ^ 3)) := by
    calc (H * M) * (routeC * 2 ^ 29 * t * b ^ 3 * L ^ 3)
        = (routeC * 2 ^ 29) * (M * H * (t * b ^ 3 * L ^ 3)) := by ring
      _ ≤ cfg.CTotal * (M * H * (t * b ^ 3 * L ^ 3)) := Nat.mul_le_mul_right _ hC_ge_rt
  have ht4 : 4 * M + (H * M) * (232 * L) ≤ cfg.CTotal * (M * H * L) := by
    have hsum : 4 * M + (H * M) * (232 * L) ≤ 236 * (M * H * L) := by
      have hring : (H * M) * (232 * L) = 232 * (M * H * L) := by ring
      omega
    exact le_trans hsum (Nat.mul_le_mul_right _ hC_ge_236)
  have ht5 : (2 * M) * (5 * trimC * Λ ^ 2 * L ^ 2) ≤ cfg.CTotal * (M * Λ ^ 2 * L ^ 2) := by
    calc (2 * M) * (5 * trimC * Λ ^ 2 * L ^ 2)
        = (10 * trimC) * (M * Λ ^ 2 * L ^ 2) := by ring
      _ ≤ cfg.CTotal * (M * Λ ^ 2 * L ^ 2) := Nat.mul_le_mul_right _ hC_ge_trim
  have hrec_M : outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₀ ≤
      (H * M) * (2 * (t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) +
        routeC * 2 ^ 29 * t * b ^ 3 * L ^ 3 + 232 * L) +
      (2 * M) * (5 * trimC * Λ ^ 2 * L ^ 2) :=
    le_trans hrec (Nat.add_le_add (Nat.mul_le_mul_right _ hesum_le)
      (Nat.mul_le_mul_right _ hwsum_le))
  unfold outerDecompCost totalTimeRaw
  dsimp only
  have hlhs_exp :
      (H * M) * (2 * (t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) +
        routeC * 2 ^ 29 * t * b ^ 3 * L ^ 3 + 232 * L) =
      (H * M) * (2 * (t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10)) +
      (H * M) * (routeC * 2 ^ 29 * t * b ^ 3 * L ^ 3) +
      (H * M) * (232 * L) := by ring
  have hrhs_exp :
      cfg.CTotal *
        (G.n + M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
          M * Λ ^ 2 * L ^ 2) =
      cfg.CTotal * G.n +
      cfg.CTotal * (M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10))) +
      cfg.CTotal * (M * H * (t * b ^ 3 * L ^ 3)) +
      cfg.CTotal * (M * H * L) +
      cfg.CTotal * (M * Λ ^ 2 * L ^ 2) := by ring
  change 4 * G.n + 4 * M +
      outerDecompRecCost cfg M r cloud core coreCost route routeCost removeFakeCost G act₀ ≤
    cfg.CTotal *
      (G.n + M * H * ((t + 1) * N ^ 2 * W ^ (10 * r ^ 2 + 10) + t * b ^ 3 * L ^ 3 + L) +
        M * Λ ^ 2 * L ^ 2)
  rw [hrhs_exp]
  rw [hlhs_exp] at hrec_M
  omega

/-- **Target envelope step-count corollary**: for `G.m ≥ thresholdB1 envelopeCr` and `r = rOf G.m`,
`outerDecompCost` satisfies the exact target envelope bound of `ExpanderDecompositionUsed`. -/
theorem outerDecompCost_le_used {cfg : ParamConfig} {routeC trimC : ℕ}
    {cloud : ℕ → Graph} {α : ℝ} (hcloud : IsCloudExpander cloud α)
    (hα : (1 : ℝ) / (cfg.a₀ : ℝ) ≤ α) (hA60 : 60 ≤ cfg.A)
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ}
    {route : RouterFn} {routeCost : RouterCostFn}
    {removeFakeCost : CompactSubgraph → List (ℕ × ℕ) → ℕ → ℕ}
    {G : Graph} (hv : G.IsValid) (hm : thresholdB1 envelopeCr ≤ G.m)
    (hcore : IsCorePlayer cfg G.m (rOf G.m) core coreCost)
    (hroute : IsMatchingPlayer route routeCost)
    (hrouteC : ∀ (G' : Graph) (X' : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z' : ℕ),
      X' ⊆ Finset.range G'.n → (∀ ed ∈ G'.inside X', ed.1 ≠ ed.2) →
      1 ≤ Δ → (∀ v ∈ X', G'.degIn X' v ≤ Δ) → 1 ≤ L → X'.card < 2 ^ L → 2 ≤ b →
      ValidTerminalPairs X' pairs →
      routeCost G' X' pairs Δ L b z' ≤
        routeC * (pairs.length * (X'.card + (G'.inside X').length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L + 1))
    (htrim : IsRemoveFakeCost G.m trimC removeFakeCost)
    (hrouteU : routeC ≤ 2 ^ 11 * cfg.u ^ 3)
    (htrimU : trimC ≤ 2 ^ 36 * cfg.u ^ 3) :
    (outerDecompCost cfg G.m (rOf G.m) cloud core coreCost route routeCost removeFakeCost G : ℝ) ≤
      envelopeK cfg * (G.n + ((G.m : ℝ) + 2) ^ (1 + envelopeK cfg / rOf G.m) *
        Real.log ((G.m : ℝ) + 2) ^ (envelopeK cfg * (rOf G.m : ℝ) ^ 2) /
          (((1 : ℕ) : ℝ) / ((200 : ℕ) : ℝ)) ^ 2) := by
  have hm4 : 4 ≤ G.m := le_trans (four_le_thresholdB1 envelopeCr) hm
  have h1 := outerDecompCost_le_totalTimeRaw hcloud hα hA60 hv
    (one_le_rOf (by omega)) (rOf_le_ell G.m) hcore hroute hrouteC htrim hrouteU htrimU
  exact le_trans (by exact_mod_cast h1) (totalTimeRaw_le_used cfg G.n hm)

/-- `IsRemoveFakeCost` is non-vacuous for any `M` and `trimC`. -/
theorem exists_isRemoveFakeCost (M trimC : ℕ) :
    ∃ removeFakeCost, IsRemoveFakeCost M trimC removeFakeCost :=
  ⟨fun _ _ _ => 0, fun _ _ _ _ _ => Nat.zero_le _⟩

end MinCostFlow.ExpanderDecomp
