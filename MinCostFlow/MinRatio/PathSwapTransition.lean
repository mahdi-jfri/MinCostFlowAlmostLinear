module

public import MinCostFlow.Basic.Forest
import MinCostFlow.MinRatio.PathSwapWords
import MinCostFlow.MinRatio.PathCancellationAccounting
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Linarith

/-!
# The route transition after a successful pair comparison

Algorithm 2 (page 29) routes the selected signed circulation.
An improving exchange changes two destinations, retaining the flow
and the number of paths. The weighted comparison supplies the
opposite traversal needed to charge this step to a forest cut.
-/

public section

namespace MinCostFlow.MinRatio

/-- A successful increasing-index comparison preserves the signed
route and provides the witness needed for the forest swap budget. -/
theorem pathSwap_index_transition {F : MGraph} (hF : F.IsForest)
    (length : ℕ → ℝ) (hℓ : ∀ e ∈ F.E, 0 < length e)
    (paths : List (ℕ × ℕ)) {i j : ℕ} (hij : i < j) (hj : j < paths.length)
    (hc : ∀ p ∈ paths, F.Connected p.1 p.2) :
    let hi : i < paths.length := hij.trans hj
    let a := paths[i].1
    let b := paths[i].2
    let c := paths[j].1
    let d := paths[j].2
    let next := (paths.set i (a,d)).set j (c,b)
    F.Connected a c →
    walkLength length (F.forestPath a d) + walkLength length (F.forestPath c b) <
      walkLength length (F.forestPath a b) + walkLength length (F.forestPath c d) →
    next.length = paths.length ∧ (∀ p ∈ next, F.Connected p.1 p.2) ∧
    (∀ e, (next.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum =
      (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum) ∧
    ∃ x rest, x ∈ F.forestPath a b ∧ (x.1, !x.2) ∈ F.forestPath c d ∧
      paths.Perm ((a,b) :: (c,d) :: rest) ∧ next.Perm ((a,d) :: (c,b) :: rest) := by
  dsimp only
  intro hac hlt
  have hi : i < paths.length := hij.trans hj
  have hab := hc paths[i] (List.getElem_mem hi)
  have hcd := hc paths[j] (List.getElem_mem hj)
  obtain ⟨x, hx, hy⟩ := (pathCancel_weighted_swap_iff hF length hℓ hab hac hcd).mp hlt
  obtain ⟨had, hcb, hflow, _⟩ := pathCancel_swap hF hab hcd hx hy
  obtain ⟨hbefore, hafter⟩ := pathSwapWords_pair_permutations paths hij hj
  refine ⟨by simp, ?_, ?_, x, _, hx, hy, ?_, hafter⟩
  · intro p hp
    have hp' := hafter.mem_iff.mp hp
    simp only [List.mem_cons] at hp'
    rcases hp' with rfl | rfl | hr
    · exact had
    · exact hcb
    · exact hc p (hbefore.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
  · intro e
    rw [(hbefore.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum_eq,
      (hafter.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum_eq]
    simp only [List.map_cons, List.sum_cons]
    linarith only [hflow e]
  · simpa only [Prod.eta] using hbefore

end MinCostFlow.MinRatio
