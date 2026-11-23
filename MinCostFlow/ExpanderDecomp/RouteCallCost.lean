module

public import MinCostFlow.ExpanderDecomp.RouteMeets
public import MinCostFlow.ExpanderDecomp.CoreCost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cost of one call of the router program

A program that runs `RouteOrCut` must read its input before it routes: the edge list of `G`, the
set `X`, and the terminal pairs. It also sorts `X` and the cut, and it works with numbers as large
as the congestion bound `R` of the router, which must fit in a word. The model count
`routeOrCutCost` does not count this work, and it is `0` when the demand is already met.

This file defines the cost of one call, `routerCallCost`: the model count plus an overhead
`routeCallOverhead` that depends only on `|X|`, the number of pairs `k` and the parameters
`Δ, L, b`. Callers give the router a graph with at most `2 Δ |X|` edges, so the overhead pays for
reading the graph without a term in `G.m`. The overhead is `0` when there are no pairs.

For `k ≥ 1` each term of the overhead is at most a constant times `k (|X| + 1) (d + 1) R`, the
shape of the router step-count bound. So the call cost keeps that bound with a larger constant:

* `routerCallCost_bounded : RouteCostBounded routerCallCost 80`;
* `routeOrCut_isMatchingPlayer_callCost : IsMatchingPlayer routeOrCut routerCallCost`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- Work of one router call beyond the model count `routeOrCutCost`, for `nX = |X|` and
`k` terminal pairs: reading the graph (at most `2 Δ |X|` edges), sorting `X` and the cut
(`log |X| ≤ L`), reading the pairs, and the size of the numbers the router stores. It is `0`
when there are no pairs. -/
@[expose] def routeCallOverhead (nX k Δ L b : ℕ) : ℕ :=
  if k = 0 then 0 else
    routeCong Δ b L * (k * (routePathLen Δ b L + 3) + 1) +
      (nX + 1) * (routeBatchH Δ b L + Δ + L + 2) + routePathLen Δ b L +
      16 * b * (4 * Δ * nX + Δ + 1) + k + 32

/-- Cost of one call of the router program: the model count of `routeOrCut` plus
`routeCallOverhead`. It has no term in `G.m`. -/
@[expose] def routerCallCost (G : Graph) (X : Finset ℕ) (pairs : List (Finset ℕ × Finset ℕ))
    (Δ L b z : ℕ) : ℕ :=
  routeOrCutCost G X pairs Δ L b z + routeCallOverhead X.card pairs.length Δ L b

/-- With no pairs the call cost is `0`: the demand is met and there is nothing to read. -/
lemma routerCallCost_nil (G : Graph) (X : Finset ℕ) (Δ L b z : ℕ) :
    routerCallCost G X [] Δ L b z = 0 := by
  simp [routerCallCost, routeCallOverhead, routeOrCutCost, routeOrCutRaw, totalDemand]

lemma routeOrCutCost_le_routerCallCost (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L b z : ℕ) :
    routeOrCutCost G X pairs Δ L b z ≤ routerCallCost G X pairs Δ L b z :=
  Nat.le_add_right _ _

/-- For `k ≥ 1` the overhead is at most `47 k (|X| + 1) (d + 1) R`. -/
lemma routeCallOverhead_le {nX k Δ L b : ℕ} (hk : 1 ≤ k) (hΔ : 1 ≤ Δ) (hL : 1 ≤ L)
    (hb : 1 ≤ b) :
    routeCallOverhead nX k Δ L b ≤
      47 * (k * (nX + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L) := by
  have hk0 : k ≠ 0 := by omega
  unfold routeCallOverhead
  simp only [hk0, ↓reduceIte]
  have hHb : routeBatchH Δ b L = (16 * b * Δ) * (routePathLen Δ b L + 1) := rfl
  have hR : routeCong Δ b L = routeBatchH Δ b L * L := rfl
  have hdL : routePathLen Δ b L = (32 * Δ * b) * L := rfl
  set d := routePathLen Δ b L with hd_def
  set Hb := routeBatchH Δ b L with hHb_def
  set R := routeCong Δ b L with hR_def
  have h16 : 1 ≤ 16 * b * Δ := Nat.mul_pos (Nat.mul_pos (by omega) hb) hΔ
  have hΔ16 : Δ ≤ 16 * b * Δ := Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hb)
  have hHb_ge : 16 * b * Δ ≤ Hb := by
    rw [hHb]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hHb_R : Hb ≤ R := by rw [hR]; exact Nat.le_mul_of_pos_right _ hL
  have hΔ_Hb : Δ ≤ Hb := le_trans hΔ16 hHb_ge
  have hL_d : L ≤ d := by
    rw [hdL]; exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (Nat.mul_pos (by omega) hΔ) hb)
  have hR1 : 1 ≤ R := le_trans (le_trans h16 hHb_ge) hHb_R
  set Q := (d + 1) * R with hQ_def
  have hR_Q : R ≤ Q := by rw [hQ_def]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hd_Q : d + 1 ≤ Q := by rw [hQ_def]; exact Nat.le_mul_of_pos_right _ hR1
  have hP : k * (nX + 1) * (d + 1) * R = (k * (nX + 1)) * Q := by rw [hQ_def]; ring
  rw [hP]
  set K := k * (nX + 1) with hK_def
  have hK1 : 1 ≤ K := by
    rw [hK_def]; have : 1 * 1 ≤ k * (nX + 1) := Nat.mul_le_mul hk (by omega)
    omega
  have hk_K : k ≤ K := by rw [hK_def]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hn_K : nX + 1 ≤ K := by rw [hK_def]; exact Nat.le_mul_of_pos_left _ (by omega)
  -- term 1
  have t1 : R * (k * (d + 3) + 1) ≤ 4 * (K * Q) := by
    have h1 : k * (d + 3) + 1 ≤ 4 * (k * (d + 1)) := by
      have : 1 ≤ k * (d + 1) := by
        have : 1 * 1 ≤ k * (d + 1) := Nat.mul_le_mul hk (by omega)
        omega
      have : k * (d + 3) = k * (d + 1) + 2 * k := by ring
      have : k ≤ k * (d + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have h2 : R * (k * (d + 3) + 1) ≤ R * (4 * (k * (d + 1))) := Nat.mul_le_mul_left _ h1
    have h3 : R * (4 * (k * (d + 1))) = 4 * (k * Q) := by rw [hQ_def]; ring
    have h4 : k * Q ≤ K * Q := Nat.mul_le_mul_right _ hk_K
    omega
  -- term 2
  have t2 : (nX + 1) * (Hb + Δ + L + 2) ≤ 5 * (K * Q) := by
    have h1 : Hb + Δ + L + 2 ≤ 5 * Q := by omega
    have h2 : (nX + 1) * (Hb + Δ + L + 2) ≤ (nX + 1) * (5 * Q) := Nat.mul_le_mul_left _ h1
    have h3 : (nX + 1) * (5 * Q) ≤ K * (5 * Q) := Nat.mul_le_mul_right _ hn_K
    have h4 : K * (5 * Q) = 5 * (K * Q) := by ring
    omega
  -- term 3
  have hQ_KQ : Q ≤ K * Q := Nat.le_mul_of_pos_left _ hK1
  have t3 : d ≤ K * Q := by omega
  -- term 4
  have t4 : 16 * b * (4 * Δ * nX + Δ + 1) ≤ 4 * (K * Q) := by
    have h1 : 4 * Δ * nX + Δ + 1 ≤ Δ * (4 * (nX + 1)) := by
      have : Δ * (4 * (nX + 1)) = 4 * Δ * nX + 4 * Δ := by ring
      omega
    have h2 : 16 * b * (4 * Δ * nX + Δ + 1) ≤ 16 * b * (Δ * (4 * (nX + 1))) :=
      Nat.mul_le_mul_left _ h1
    have h3 : 16 * b * (Δ * (4 * (nX + 1))) = (16 * b * Δ) * (4 * (nX + 1)) := by ring
    have h4 : (16 * b * Δ) * (4 * (nX + 1)) ≤ Q * (4 * K) :=
      Nat.mul_le_mul (le_trans (le_trans hHb_ge hHb_R) hR_Q) (by omega)
    have h5 : Q * (4 * K) = 4 * (K * Q) := by ring
    omega
  -- term 5
  have t5 : k + 32 ≤ 33 * (K * Q) := by
    have : K ≤ K * Q := Nat.le_mul_of_pos_right _ (le_trans hR1 hR_Q)
    omega
  omega

/-- **The router call cost keeps the shape of the router step-count bound.** `routerCallCost` satisfies
`RouteCostBounded` with constant `80`. -/
theorem routerCallCost_bounded : RouteCostBounded routerCallCost 80 := by
  intro G X pairs Δ L b z hX hloop hΔ hdeg hL hcard hb hvalid
  have hle := routeOrCutCost_le G pairs (routeTerminalPairs_of_validTerminalPairs hvalid)
    (z := z) hΔ hb hL hdeg hcard
  have hmul :
      routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
        (routeD Δ b L + 1) * routeR Δ b L =
      20 * (pairs.length * (X.card + (G.inside X).length + 1) *
        (routePathLen Δ b L + 1) * routeCong Δ b L) := by
    unfold routeCostConst routeD routeR
    ring
  rw [hmul] at hle
  unfold routerCallCost
  set P := pairs.length * (X.card + (G.inside X).length + 1) * (routePathLen Δ b L + 1) *
    routeCong Δ b L with hP_def
  rcases Nat.eq_zero_or_pos pairs.length with hk | hk
  · have : routeCallOverhead X.card pairs.length Δ L b = 0 := by
      unfold routeCallOverhead; simp [hk]
    omega
  · have hov := routeCallOverhead_le (nX := X.card) hk hΔ hL (by omega : 1 ≤ b)
    have hmono : pairs.length * (X.card + 1) * (routePathLen Δ b L + 1) * routeCong Δ b L ≤ P := by
      rw [hP_def]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (by omega)))
    omega

/-- `routeOrCut` with the call cost `routerCallCost` is a static matching player. -/
theorem routeOrCut_isMatchingPlayer_callCost : IsMatchingPlayer routeOrCut routerCallCost where
  spec := routeOrCut_isMatchingPlayer.spec
  cost_bound := ⟨80, fun G X pairs Δ L b z hX hloop hΔ hdeg hL hcard hb hvalid =>
    routerCallCost_bounded G X pairs Δ L b z hX hloop hΔ hdeg hL hcard hb hvalid⟩

end MinCostFlow.ExpanderDecomp
