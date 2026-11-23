module

public import MinCostFlow.HierPaths.BuildProgErase
public import MinCostFlow.HierPaths.BuildCall
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.GetD

/-!
# The cost of a router call, with the shortcuts

Each router call of the construction is followed by `erase` on each walk it returns. The work of
one call is the cost of the router (`fullRouteCost`) plus the steps of the linear shortcut of
`BuildProgErase.lean` on each returned walk (`resEraseCost`). Together this is `callCost`.

`callCost_le` (in `BuildCost.lean`): under the router's conditions, a call with `n` terminal pairs costs at most
`2 ρ_n` with the router constant raised from `C` to `C + 2`. The reason: the call returns at most
`n |X|` walks, each of length at most `d`, so the shortcuts take at most `3 n |X| (d + 1)` steps,
which is at most `4 (ρ_n / C)`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The steps of the shortcuts of the walks of a router result, with the position array starting
at `0`. -/
def resEraseCost (E : List (ℕ × ℕ)) : RouteResult → ℕ
  | .matched Ms emb => ((List.range Ms.flatten.length).map fun j =>
      eraseSteps E (edgeAt Ms.flatten j).1 (emb j) (fun _ => 0)).sum
  | .cut _ => 0

/-- The work of one full-routing call: the router and the shortcuts of its walks. -/
def callCost (route : RouterFn) (routeCost : RouterCostFn) (G : Graph) (X : Finset ℕ)
    (pairs : List (Finset ℕ × Finset ℕ)) (Δ L : ℕ) : ℕ :=
  fullRouteCost route routeCost G X pairs Δ L X.card 2 +
    resEraseCost G.edges (lemma1Route route G X pairs Δ L).1

end MinCostFlow.HierPaths

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The shortcuts of a matched result take at most `3 (d + 1)` steps per walk. -/
theorem resEraseCost_le {E : List (ℕ × ℕ)} {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ} {d : ℕ}
    (hd : ∀ j < Ms.flatten.length, (emb j).length ≤ d) :
    resEraseCost E (.matched Ms emb) ≤ Ms.flatten.length * (3 * (d + 1)) := by
  show ((List.range Ms.flatten.length).map fun j =>
      eraseSteps E (edgeAt Ms.flatten j).1 (emb j) (fun _ => 0)).sum ≤ _
  have h : ∀ x ∈ (List.range Ms.flatten.length).map (fun j =>
      eraseSteps E (edgeAt Ms.flatten j).1 (emb j) (fun _ => 0)), x ≤ 3 * (d + 1) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    have := eraseSteps_le (E := E) (edgeAt Ms.flatten j).1 (emb j) (fun _ => 0)
    have := hd j (List.mem_range.mp hj)
    omega
  have := List.sum_le_length_nsmul _ _ h
  simpa using this

/-- A router call returns at most `n |X|` walks. -/
theorem length_flatten_le {X : Finset ℕ} {pairs : List (Finset ℕ × Finset ℕ)}
    {Ms : List (List (ℕ × ℕ))} (hv : ValidTerminalPairs X pairs) (hlen : Ms.length = pairs.length)
    (hcard : ∀ i (hi : i < pairs.length), (Ms.getD i []).length = (pairs[i]'hi).1.card) :
    Ms.flatten.length ≤ pairs.length * X.card := by
  rw [List.length_flatten]
  have h : ∀ x ∈ Ms.map List.length, x ≤ X.card := by
    intro x hx
    obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hM
    have hi' : i < pairs.length := hlen ▸ hi
    have h1 := hcard i hi'
    rw [List.getD_eq_getElem _ _ hi] at h1
    rw [h1]
    exact Finset.card_le_card (hv.1 _ (List.getElem_mem hi')).1
  have := List.sum_le_length_nsmul _ _ h
  simp only [List.length_map, smul_eq_mul, hlen] at this
  exact this

end MinCostFlow.HierPaths
