module

public import MinCostFlow.Scaling.PositiveSupport
public import MinCostFlow.Scaling.StrongDuality
public import MinCostFlow.Scaling.WalkShortening
import Mathlib.Tactic.Linarith

/-!
# An optimum avoids sufficiently expensive arcs

The remark following Definition C.6 in Appendix C of Chen et al.,
arXiv:2203.00671v2, removes high positive costs. Every positive-flow arc of
a circulation has a return path in its support. Shorten that path to fewer
than `n` arcs. If all costs are at least `-C`, an arc costing at least `n*C`
would give a positive cycle. Optimal residual-potential inequalities force
any cycle in the positive support to have nonpositive cost, a contradiction.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation
namespace DirectedWalk
variable {I : Circulation} {a b : Fin I.n}

/-- Removing repeated vertices gives a path, independently of its costs. -/
theorem exists_nodup (p : I.DirectedWalk a b) :
    ∃ q : I.DirectedWalk a b, q.vertices.Nodup := by
  induction p with
  | nil v => exact ⟨.nil v, by simp [vertices]⟩
  | cons e he p ih =>
    obtain ⟨q, hq⟩ := ih
    by_cases hv : I.tail e ∈ q.vertices
    · obtain ⟨_, r, _, hr⟩ := q.split_at_vertex (I.tail e) hv
      exact ⟨r, hr.nodup hq⟩
    · exact ⟨.cons e he q, List.nodup_cons.mpr ⟨hv, hq⟩⟩

/-- Arc upper bounds by potential differences telescope along a walk. -/
theorem cost_le_potential (p : I.DirectedWalk a b) (y : Fin I.n → ℤ)
    (h : ∀ e, 0 < I.capacity e → I.cost e ≤ y (I.tail e) - y (I.head e)) :
    p.cost ≤ y a - y b := by
  induction p with
  | nil => simp only [cost, sub_self, le_refl]
  | cons e he p ih =>
    have hh := h e he
    simp only [cost]
    omega

end DirectedWalk

/-- The high-cost arc removal step used by the cost-scaling proof.
The returned integral optimum cannot use an arc costing at least `n*C`
when all costs are at least `-C` and `C` is positive. -/
theorem optimal_zero_on_expensive_arc (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ))) (C : ℤ) (hC : 0 < C)
    (hc : ∀ e, -C ≤ I.cost e) (e : Fin I.m) (he : (I.n : ℤ) * C ≤ I.cost e) :
    f e = 0 := by
  classical
  have hnon : 0 ≤ f e := (Int.cast_nonneg_iff (R := ℝ)).mp (hf.1.2 e).1
  by_contra hn
  have hpos : 0 < f e := by omega
  have hpos' : 0 < (f e : ℝ) := Int.cast_pos.mpr hpos
  obtain ⟨y, _, hreverse⟩ := I.exists_optimal_residual_potential f hf
  have hsign (a : Fin I.m) (ha : 0 < (f a : ℝ)) :
      I.cost a ≤ y (I.tail a) - y (I.head a) := by
    have hh := hreverse a ha
    dsimp only [reducedCost, potentialDifference] at hh
    have hi : (I.cost a : ℝ) ≤ (y (I.tail a) : ℝ) - (y (I.head a) : ℝ) := by linarith only [hh]
    exact_mod_cast hi
  obtain ⟨p⟩ := I.exists_support_return_walk (fun a => (f a : ℝ)) hf.1 e hpos'
  obtain ⟨q, hq⟩ := p.exists_nodup
  have hl : q.length < I.n := q.length_lt_vertices_of_nodup hq
  have hupper := q.cost_le_potential y (by
    intro a ha
    apply hsign a
    change 0 < if 0 < (f a : ℝ) then 1 else 0 at ha
    split at ha
    · assumption
    · contradiction)
  have hlower := q.cost_ge_neg_length_mul C hc
  have hedge := hsign e hpos'
  have hli : (q.length : ℤ) + 1 ≤ I.n := by exact_mod_cast hl
  have hprod := mul_le_mul_of_nonneg_right hli hC.le
  change q.cost ≤ y (I.head e) - y (I.tail e) at hupper
  simp only [add_mul, one_mul] at hprod
  simp only [neg_mul] at hlower
  omega

end MinCostFlow.Scaling.Circulation
