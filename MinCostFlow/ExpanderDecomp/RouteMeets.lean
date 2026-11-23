module

public import MinCostFlow.ExpanderDecomp.MatchingPlayer
public import MinCostFlow.ExpanderDecomp.RouteOrCut
import Mathlib.Tactic.Ring

/-!
# `RouteOrCut` meets `IsMatchingPlayer`

This file proves that the static multi-pair matching player `routeOrCut` and its explicit
operation count `routeOrCutCost` (`RouteOrCut.lean`) satisfy the shared interface
`IsMatchingPlayer` defined in `MinCostFlow/ExpanderDecomp/MatchingPlayer.lean`.

Main result:
* `routeOrCut_isMatchingPlayer : IsMatchingPlayer routeOrCut routeOrCutCost`.
-/

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- `routeOrCut` together with its explicit operation count `routeOrCutCost` satisfies the
shared static matching-player interface `IsMatchingPlayer` (router correctness and
running-time bound). -/
theorem routeOrCut_isMatchingPlayer : IsMatchingPlayer routeOrCut routeOrCutCost where
  spec := fun G X pairs Δ L b z _hX _hloop hΔ hdeg hL hcard hb hvalid =>
    routeOrCut_spec G pairs (routeTerminalPairs_of_validTerminalPairs hvalid) hΔ hb hL hdeg hcard
  cost_bound := by
    refine ⟨routeCostConst, fun G X pairs Δ L b z _hX _hloop hΔ hdeg hL hcard hb hvalid => ?_⟩
    have hle := routeOrCutCost_le G pairs (routeTerminalPairs_of_validTerminalPairs hvalid)
      (z := z) hΔ hb hL hdeg hcard
    have hmul :
        routeCostConst * pairs.length * (X.card + (G.inside X).length + 1) *
          (routeD Δ b L + 1) * routeR Δ b L =
        routeCostConst * (pairs.length * (X.card + (G.inside X).length + 1) *
          (routePathLen Δ b L + 1) * routeCong Δ b L) := by
      unfold routeD routeR
      ring
    rw [hmul] at hle
    exact le_trans hle (Nat.mul_le_mul_left routeCostConst (Nat.le_succ _))

end MinCostFlow.ExpanderDecomp
