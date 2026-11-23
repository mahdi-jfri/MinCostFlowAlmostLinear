module

public import MinCostFlow.IPM.RecoverySupport
public import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# A simple return route in the residual support

The real-flow recovery argument for Appendix B.1 (page 92) of Chen et al.,
arXiv:2203.00671v2, needs a bounded-length residual return route.
Starting with the return reachability proved by the cut argument, erase
loops by keeping the suffix whenever a new initial vertex is already
in the route. The remaining vertices are distinct, so their count is
bounded by any finite set containing the support endpoints.
-/

public section
namespace MinCostFlow.IPM

private theorem exists_nodup_chain {V : Type*} [DecidableEq V] {R : V → V → Prop}
    {a b : V} (h : Relation.ReflTransGen R a b) :
    ∃ l : List V, List.IsChain R (a::l) ∧ (a::l).getLast? = some b ∧ (a::l).Nodup := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], List.IsChain.singleton _, rfl, by simp⟩
  · intro c d hcd _ ih
    obtain ⟨l, hl, hlast, hnodup⟩ := ih
    by_cases hc : c ∈ d::l
    · obtain ⟨pre, suf, heq⟩ := List.mem_iff_append.mp hc
      rw [heq] at hl hlast hnodup
      have hsuffix : (c::suf) <:+ (pre++c::suf) := ⟨pre, rfl⟩
      refine ⟨suf, hl.suffix hsuffix, ?_, hnodup.sublist hsuffix.sublist⟩
      simpa only [List.getLast?_append_of_ne_nil pre (by simp : (c::suf) ≠ [])] using hlast
    · refine ⟨d::l, List.IsChain.cons_cons hcd hl, ?_, List.nodup_cons.mpr ⟨hc, hnodup⟩⟩
      simpa only [List.getLast?_cons_cons] using hlast

/-- A supported arc of a real circulation has a return chain with distinct
vertices. This bounds the number of arcs used in the recovery improvement. -/
theorem residualSupport_simple_return (I : Instance) (hI : I.IsValid)
    (d : Fin I.m → ℝ) (hd : IsCirculation I d) (u v : Fin I.n)
    (huv : residualSupport I hI d u v) :
    ∃ l : List (Fin I.n), List.IsChain (residualSupport I hI d) (v::l) ∧
      (v::l).getLast? = some u ∧ (v::l).Nodup :=
  exists_nodup_chain (residualSupport_return I hI d hd u v huv)

/-- A simple return route uses at most the number of support vertices.
The containing set is explicit so isolated vertices do not affect the bound. -/
theorem residualSupport_return_length (I : Instance) (hI : I.IsValid)
    (d : Fin I.m → ℝ) (hd : IsCirculation I d) (u v : Fin I.n)
    (huv : residualSupport I hI d u v) (S : Finset (Fin I.n)) (hv : v ∈ S)
    (hS : ∀ x y, residualSupport I hI d x y → x ∈ S ∧ y ∈ S) :
    ∃ l : List (Fin I.n), List.IsChain (residualSupport I hI d) (v::l) ∧
      (v::l).getLast? = some u ∧ (v::l).Nodup ∧ (v::l).length ≤ S.card := by
  obtain ⟨l, hl, hlast, hnodup⟩ := residualSupport_simple_return I hI d hd u v huv
  have hall : ∀ x ∈ v::l, x ∈ S := by
    apply List.IsChain.induction (fun x => x ∈ S) (v::l) hl
    · intro x y hxy _
      exact (hS x y hxy).2
    · intro _
      exact hv
  have hsub : (v::l).toFinset ⊆ S := by
    intro x hx
    exact hall x (List.mem_toFinset.mp hx)
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  exact ⟨l, hl, hlast, hnodup, hcard⟩

end MinCostFlow.IPM
