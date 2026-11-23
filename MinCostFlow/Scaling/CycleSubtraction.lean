module

public import MinCostFlow.Scaling.SupportWalkConversion
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Subtracting a support cycle removes a positive edge

The decomposition in the proof of Lemma C.9 through Lemmas C.10 and C.12
of Chen et al., arXiv:2203.00671v2, Appendix C, repeatedly subtracts the
minimum flow on a simple support cycle. The remaining flow is feasible,
nonnegative, and no larger on any edge. At least one positive edge disappears,
so at most `m` cycles are needed. Cycles may share edges, repairing the
source's edge-disjoint decomposition claim.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The set of positive coordinates of a real flow. -/
noncomputable def flowSupport (I : Circulation) (f : Fin I.m → ℝ) : Finset (Fin I.m) :=
  Finset.univ.filter (fun e => 0 < f e)

/-- Subtracting the minimum on one simple support cycle preserves feasibility
and strictly reduces the number of positive-flow edges. -/
theorem exists_cycle_subtraction (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) (hpos : ∃ e, 0 < f e) :
    ∃ v : Fin I.n, ∃ p : I.DirectedWalk v v, ∃ amount : ℝ,
      0 < p.length ∧ (∀ e, p.count e ≤ 1) ∧ 0 < amount ∧
      (∀ e, amount * (p.count e : ℝ) ≤ f e) ∧
      I.Feasible (fun e => f e - amount * (p.count e : ℝ)) ∧
      (I.flowSupport (fun e => f e - amount * (p.count e : ℝ))).card < (I.flowSupport f).card := by
  classical
  obtain ⟨v, q, hlen, hcount, _⟩ := I.exists_simple_support_cycle f hf hpos
  let p := q.ofPositiveSupport hf
  let S : Finset (Fin I.m) := Finset.univ.filter (fun e => 0 < p.count e)
  have hS : S.Nonempty := by
    have hh : 0 < ∑ e, p.count e := by
      rw [p.sum_count]
      simpa only [p, DirectedWalk.length_ofPositiveSupport] using hlen
    by_contra hn
    have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hz (e : Fin I.m) : p.count e = 0 := by
      have he : e ∉ S := by rw [hempty]; simp
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at he
      omega
    simp only [hz, Finset.sum_const_zero] at hh
    omega
  obtain ⟨k, hk, hmin⟩ := S.exists_min_image f hS
  have hkpos : 0 < p.count k := (Finset.mem_filter.mp hk).2
  have hflowpos (e : Fin I.m) (he : 0 < p.count e) : 0 < f e := by
    apply q.flow_pos_of_support_count hf e
    simpa only [p, DirectedWalk.count_ofPositiveSupport] using he
  have ha : 0 < f k := hflowpos k hkpos
  have hbound (e : Fin I.m) : f k * (p.count e : ℝ) ≤ f e := by
    by_cases he : p.count e = 0
    · rw [he, Nat.cast_zero, mul_zero]
      exact (hf.2 e).1
    · have hone : p.count e = 1 := by
        have hh := hcount e
        change q.count e ≤ 1 at hh
        have hle : p.count e ≤ 1 := by simpa only [p, DirectedWalk.count_ofPositiveSupport] using hh
        omega
      rw [hone, Nat.cast_one, mul_one]
      exact hmin e (Finset.mem_filter.mpr ⟨Finset.mem_univ e, Nat.pos_of_ne_zero he⟩)
  have hpcount : ∀ e, p.count e ≤ 1 := fun e => by
    simpa only [p, DirectedWalk.count_ofPositiveSupport] using hcount e
  have hfeasible : I.Feasible (fun e => f e - f k * (p.count e : ℝ)) := by
    constructor
    · intro w
      simp only [balance, mul_sub, Finset.sum_sub_distrib]
      change I.balance f w - ∑ e, I.incidence e w * (f k * (p.count e : ℝ)) = 0
      have heq : (∑ e, I.incidence e w * (f k * (p.count e : ℝ))) =
          f k * I.balance (fun e => (p.count e : ℝ)) w := by
        simp only [balance, Finset.mul_sum, mul_left_comm]
      rw [heq, hf.1 w, p.balance_count]
      simp
    · intro e
      have hnon : 0 ≤ f k * (p.count e : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg _)
      exact ⟨sub_nonneg.mpr (hbound e), le_trans (sub_le_self _ hnon) (hf.2 e).2⟩
  refine ⟨v, p, f k, ?_, hpcount, ha, hbound, hfeasible, ?_⟩
  · simpa only [p, DirectedWalk.length_ofPositiveSupport] using hlen
  · apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro e he
      have hepos := (Finset.mem_filter.mp he).2
      have hnon : 0 ≤ f k * (p.count e : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg _)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ e, by linarith only [hepos, hnon]⟩
    · intro heq
      have hkold : k ∈ I.flowSupport f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
      rw [← heq] at hkold
      have hknew := (Finset.mem_filter.mp hkold).2
      have hcountk : p.count k = 1 := by have hh := hpcount k; omega
      dsimp only at hknew
      rw [hcountk, Nat.cast_one, mul_one, sub_self] at hknew
      exact lt_irrefl _ hknew

end MinCostFlow.Scaling.Circulation
