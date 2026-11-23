module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Per-call cost bounds for the expander tools of Algorithm 4

This file defines the per-call cost bound parameters for the three tools used by Algorithm 4
(`Sparsify`, page 42; *A Deterministic Almost-Linear Time Algorithm for Minimum-Cost Flow*,
arXiv:2309.16629v1):

1. `ConstructExpanderCost` (**Theorem 8.4**, page 40): each call `ConstructExpander(n, w)` costs
   `O(n + ‖w‖₁)` (`⌈K_ce · (n + ‖w‖₁)⌉`).
2. `DecomposeCost` (**Theorem 8.5**, page 41): each call `Decompose(G)` on a graph with `m` edges
   costs `⌈K_dec · m · decFactor(m)⌉`, where `decFactor(m)` captures the subpolynomial factor
   `exp(O(log(m)^{2/3} log log m))` (monotone in `m`, `≥ 1`).
3. `PathDSCost` (**Theorem 8.6**, page 41): initialization plus all deletions on an instance with
   `|E|` initial edges costs `O(|E| · γ_ExpPath)` (`⌈K_dsUpdate · |E| · γ_ExpPath⌉`), and each
   `GetPath` query costs `O(γ_query)` (`⌈K_dsQuery · γ_query⌉`), where the query time `γ_query ≥ γ_ExpPath`.
4. `SpannerToolCosts`: bundles all three cost specifications.
-/

@[expose] public section

namespace MinCostFlow.Spanner

/-- Per-call cost bound for `ConstructExpander(n, w)` (**Theorem 8.4**, page 40):
runtime `O(n + ‖w‖₁)`. -/
structure ConstructExpanderCost where
  /-- Leading constant `K_ce ≥ 0` in the `O(n + ‖w‖₁)` bound. -/
  K_ce : ℝ
  hK_ce : 0 ≤ K_ce

namespace ConstructExpanderCost

/-- Integer operation charge `⌈K_ce · (n + ‖w‖₁)⌉` for one call `ConstructExpander(n, w)`. -/
noncomputable def callCost (c : ConstructExpanderCost) (n : ℕ) (wSum : ℝ) : ℕ :=
  Nat.ceil (c.K_ce * ((n : ℝ) + wSum))

theorem callCost_zero (c : ConstructExpanderCost) : c.callCost 0 0 = 0 := by
  simp [callCost]

theorem callCost_le (c : ConstructExpanderCost) (n : ℕ) {wSum : ℝ}
    (hw : 0 ≤ wSum) :
    (c.callCost n wSum : ℝ) ≤ c.K_ce * ((n : ℝ) + wSum) + 1 := by
  unfold callCost
  have hnn : 0 ≤ c.K_ce * ((n : ℝ) + wSum) := mul_nonneg c.hK_ce (by positivity)
  exact (Nat.ceil_lt_add_one hnn).le

theorem callCost_le_of_one_le (c : ConstructExpanderCost) {n : ℕ} (hn : 1 ≤ n)
    {wSum : ℝ} (hw : 0 ≤ wSum) :
    (c.callCost n wSum : ℝ) ≤ (c.K_ce + 1) * ((n : ℝ) + wSum) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + wSum := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have h2 := c.callCost_le n hw
  nlinarith

end ConstructExpanderCost

/-- Per-call cost bound for `Decompose(G)` (**Theorem 8.5**, page 41):
a function of `m = |E(G)|` of the form `⌈K_dec · m · decFactor(m)⌉`, where `decFactor(m) ≥ 1`
is monotone in `m` (in Theorem 8.5, `exp(O(log(m + 2)^{2/3} log(log(m + 2) + 2)))`). -/
structure DecomposeCost where
  /-- Leading constant `K_dec ≥ 0`. -/
  K_dec : ℝ
  /-- Per-edge subpolynomial factor `decFactor(m) ≥ 1`, monotone nondecreasing in `m`. -/
  decFactor : ℕ → ℝ
  hK_dec : 0 ≤ K_dec
  hdec_ge : ∀ m, 1 ≤ decFactor m
  hdec_mono : ∀ ⦃m₁ m₂ : ℕ⦄, m₁ ≤ m₂ → decFactor m₁ ≤ decFactor m₂

namespace DecomposeCost

/-- Integer operation charge `⌈K_dec · m · decFactor(m)⌉` for calling `Decompose` on `m` edges. -/
noncomputable def callCost (c : DecomposeCost) (m : ℕ) : ℕ :=
  Nat.ceil (c.K_dec * (m : ℝ) * c.decFactor m)

theorem callCost_zero (c : DecomposeCost) : c.callCost 0 = 0 := by
  simp [callCost]

theorem callCost_le (c : DecomposeCost) (m : ℕ) :
    (c.callCost m : ℝ) ≤ (c.K_dec + 1) * (m : ℝ) * c.decFactor m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [callCost]
  · unfold callCost
    have hf : 1 ≤ c.decFactor m := c.hdec_ge m
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hnn : 0 ≤ c.K_dec * (m : ℝ) * c.decFactor m :=
      mul_nonneg (mul_nonneg c.hK_dec (Nat.cast_nonneg m)) (by linarith)
    have hceil : (Nat.ceil (c.K_dec * (m : ℝ) * c.decFactor m) : ℝ) ≤
        c.K_dec * (m : ℝ) * c.decFactor m + 1 :=
      (Nat.ceil_lt_add_one hnn).le
    have h1 : (1 : ℝ) ≤ (m : ℝ) * c.decFactor m := by nlinarith
    linarith

theorem callCost_le_of_le (c : DecomposeCost) {m M : ℕ} (hm : m ≤ M) :
    (c.callCost m : ℝ) ≤ (c.K_dec + 1) * (m : ℝ) * c.decFactor M := by
  have h1 := c.callCost_le m
  have h2 := c.hdec_mono hm
  have hnn : 0 ≤ (c.K_dec + 1) * (m : ℝ) := mul_nonneg (by linarith [c.hK_dec]) (Nat.cast_nonneg m)
  exact le_trans h1 (mul_le_mul_of_nonneg_left h2 hnn)

end DecomposeCost

/-- Per-instance and per-query cost bounds for `PathDSTool` (**Theorem 8.6**, page 41):
initialization plus all deletions on an instance with `|E|` edges takes `O(|E| · γ_ExpPath)`,
and each `GetPath` query takes `O(γ_query)`. -/
structure PathDSCost where
  /-- Constant `K_dsUpdate ≥ 0` in the `O(|E| · γ_query)` total bound for initialization plus
  all deletions on one `PathDS` instance (`Init` uses `O(|E| · γ_ExpPath) ≤ O(|E| · γ_query)` and
  fallback `Delete` pruning costs `≤ fbCostBound d ≤ γ_query` per deletion, at most `|E|` times). -/
  K_dsUpdate : ℝ
  /-- Constant `K_dsQuery ≥ 0` in the `O(γ_query)` bound per `GetPath` call. -/
  K_dsQuery : ℝ
  hK_dsUpdate : 0 ≤ K_dsUpdate
  hK_dsQuery : 0 ≤ K_dsQuery

namespace PathDSCost

/-- Total operation charge `⌈K_dsUpdate · m · γ_query⌉` for initializing one `PathDS` instance
on `m` edges and performing all deletions on it (honest for both `[CS21]` and fallback). -/
noncomputable def updateCost (c : PathDSCost) (m : ℕ) (γ_query : ℝ) : ℕ :=
  Nat.ceil (c.K_dsUpdate * (m : ℝ) * γ_query)

/-- Per-query operation charge `⌈K_dsQuery · γ_query⌉` for one `GetPath` call. -/
noncomputable def queryCost (c : PathDSCost) (γ_query : ℝ) : ℕ :=
  Nat.ceil (c.K_dsQuery * γ_query)

theorem updateCost_zero (c : PathDSCost) (γ_query : ℝ) : c.updateCost 0 γ_query = 0 := by
  simp [updateCost]

theorem updateCost_le (c : PathDSCost) (m : ℕ) {γ_query : ℝ} (hγ : 1 ≤ γ_query) :
    (c.updateCost m γ_query : ℝ) ≤ (c.K_dsUpdate + 1) * (m : ℝ) * γ_query := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [updateCost]
  · unfold updateCost
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hnn : 0 ≤ c.K_dsUpdate * (m : ℝ) * γ_query :=
      mul_nonneg (mul_nonneg c.hK_dsUpdate (Nat.cast_nonneg m)) (by linarith)
    have hceil : (Nat.ceil (c.K_dsUpdate * (m : ℝ) * γ_query) : ℝ) ≤
        c.K_dsUpdate * (m : ℝ) * γ_query + 1 :=
      (Nat.ceil_lt_add_one hnn).le
    have h1 : (1 : ℝ) ≤ (m : ℝ) * γ_query := by nlinarith
    linarith

theorem queryCost_le (c : PathDSCost) {γ_query : ℝ} (hγ : 1 ≤ γ_query) :
    (c.queryCost γ_query : ℝ) ≤ (c.K_dsQuery + 1) * γ_query := by
  unfold queryCost
  have hnn : 0 ≤ c.K_dsQuery * γ_query := mul_nonneg c.hK_dsQuery (by linarith)
  have hceil : (Nat.ceil (c.K_dsQuery * γ_query) : ℝ) ≤ c.K_dsQuery * γ_query + 1 :=
    (Nat.ceil_lt_add_one hnn).le
  linarith

end PathDSCost

/-- Bundle of per-call cost bounds for all three tools used by Algorithm 4 (`Sparsify`). -/
structure SpannerToolCosts where
  constructExpander : ConstructExpanderCost
  decompose : DecomposeCost
  pathDS : PathDSCost

end MinCostFlow.Spanner
