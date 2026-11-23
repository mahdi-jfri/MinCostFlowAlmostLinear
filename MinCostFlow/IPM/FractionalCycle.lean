module

public import MinCostFlow.IPM.Definitions
public import MinCostFlow.Rounding.Rounding
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Circulations on cycles of fractional edges

The integer optimal-cost search in Section 4 of Chen et al.,
arXiv:2203.00671v2 (page 24), needs an integral optimum. A nonempty closed
walk with distinct fractional edges gives a nonzero circulation supported
only on those edges. Orienting the edges along the walk gives its
coordinates in `{-1, 0, 1}`. This also treats loops and parallel edges.
-/

public section
namespace MinCostFlow.IPM
open Rounding

private theorem rawEdge_injective (I : Instance) {e j : Fin I.m} :
    rawEdge I e = rawEdge I j ↔ e = j := by
  constructor
  · intro h
    exact Fin.ext (congrArg RawEdge.eid h)
  · rintro rfl; rfl

private theorem extend_walk_flow (I : Instance) (es : List RawEdge)
    (a b c : ℕ) (j : Fin I.m) (σ : ℝ) (d : Fin I.m → ℝ)
    (hσ : |σ| = 1) (hj : rawEdge I j ∉ es)
    (hd : ∀ e, |d e| = if rawEdge I e ∈ es then 1 else 0)
    (hroute : ∀ v : ℕ, (∑ e, (I.edge e).b v*d e) =
      (if v = b then (1 : ℝ) else 0)-(if v = c then 1 else 0))
    (hσroute : ∀ v : ℕ, (I.edge j).b v*σ =
      (if v = a then (1 : ℝ) else 0)-(if v = b then 1 else 0)) :
    ∃ d' : Fin I.m → ℝ,
      (∀ e, |d' e| = if rawEdge I e ∈ rawEdge I j::es then 1 else 0) ∧
      ∀ v : ℕ, (∑ e, (I.edge e).b v*d' e) =
        (if v = a then (1 : ℝ) else 0)-(if v = c then 1 else 0) := by
  classical
  have hdj : d j = 0 := abs_eq_zero.mp (by simpa only [hj, ↓reduceIte] using hd j)
  refine ⟨fun e => d e + if e = j then σ else 0, ?_, ?_⟩
  · intro e
    by_cases he : e = j
    · subst e
      simp only [hdj, ↓reduceIte, zero_add, List.mem_cons_self, hσ]
    · have hraw : rawEdge I e ≠ rawEdge I j := fun h => he ((rawEdge_injective I).mp h)
      simp only [he, ↓reduceIte, add_zero, List.mem_cons, hraw, false_or]
      exact hd e
  · intro v
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ j), hroute, hσroute]
    ring

/-- Orient a walk with distinct fractional edges. Its nonzero coordinates
are exactly the edges of the walk, and its divergence is the difference
of the two endpoint indicators. -/
theorem fractional_walk_flow (I : Instance) (f : Fin I.m → ℝ)
    (a b : ℕ) (es : List RawEdge) (hw : Rounding.IsWalk (fracEdges I f) a b es)
    (hnd : es.Nodup) :
    ∃ d : Fin I.m → ℝ,
      (∀ e, |d e| = if rawEdge I e ∈ es then 1 else 0) ∧
      ∀ v : ℕ, (∑ e, (I.edge e).b v*d e) =
        (if v = a then (1 : ℝ) else 0)-(if v = b then 1 else 0) := by
  classical
  induction hw with
  | nil a =>
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro e; simp
    · intro v; simp
  | @cons a b c x es hx hconn hrest ih =>
    obtain ⟨j, rfl, _⟩ := mem_fracEdges_iff.mp hx
    obtain ⟨d, hd, hroute⟩ := ih hnd.of_cons
    have hj := (List.nodup_cons.mp hnd).1
    rcases hconn with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · apply extend_walk_flow I es a b c j 1 d (by norm_num) hj hd hroute
      intro v
      dsimp only [rawEdge] at ha hb
      simp only [Edge.b, ha, hb, mul_one]
    · apply extend_walk_flow I es a b c j (-1) d (by norm_num) hj hd hroute
      intro v
      dsimp only [rawEdge] at ha hb
      simp only [Edge.b, ha, hb]
      ring

/-- A nonempty cycle of fractional edges gives a nonzero circulation
whose support consists only of fractional coordinates. This is the
perturbation direction used to prove an integral optimum exists. -/
theorem fractional_cycle_direction (I : Instance) (f : Fin I.m → ℝ)
    (hcycle : ¬ Rounding.IsAcyclic (fracEdges I f)) :
    ∃ d : Fin I.m → ℝ, IsCirculation I d ∧ (∃ e, d e ≠ 0) ∧
      ∀ e, d e ≠ 0 → ¬ ∃ z : ℤ, f e = z := by
  classical
  obtain ⟨a, es, hw, hnd, hne⟩ : ∃ a es,
      Rounding.IsWalk (fracEdges I f) a a es ∧ es.Nodup ∧ es ≠ [] := by
    have hn : ∃ a es, ∃ (_ : Rounding.IsWalk (fracEdges I f) a a es)
        (_ : es.Nodup), es ≠ [] := by
      simpa only [Rounding.IsAcyclic, not_forall, not_imp] using hcycle
    obtain ⟨a, es, hw, hnd, hne⟩ := hn
    exact ⟨a, es, hw, hnd, hne⟩
  obtain ⟨d, hd, hroute⟩ := fractional_walk_flow I f a a es hw hnd
  refine ⟨d, fun v => by simpa only [sub_self] using hroute v, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil es hne
    obtain ⟨e, he, _⟩ := mem_fracEdges_iff.mp (hw.subset x hx)
    refine ⟨e, ?_⟩
    have hh : |d e| = 1 := by simpa only [← he, hx, ↓reduceIte] using hd e
    intro hz
    rw [hz, abs_zero] at hh
    exact zero_ne_one hh
  · intro e he
    have hm : rawEdge I e ∈ es := by
      by_contra hn
      have hh : |d e| = 0 := by simpa only [hn, ↓reduceIte] using hd e
      exact he (abs_eq_zero.mp hh)
    obtain ⟨j, hj, hfrac⟩ := mem_fracEdges_iff.mp (hw.subset _ hm)
    have heq := (rawEdge_injective I).mp hj
    simpa only [heq] using hfrac

end MinCostFlow.IPM
