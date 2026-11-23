module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Removing prescribed demands

The reduction in the proof of Lemma C.1 of Chen et al., arXiv:2203.00671v2,
needs to decide feasibility before optimizing costs. Add a new vertex and arcs
that cancel the prescribed demand at every old vertex. Give these arcs cost
minus one and give the old arcs cost zero. A circulation saturating all new
arcs corresponds exactly to a flow routing the prescribed demands. Zero
capacity slots keep the construction independent of signs of demands.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Every flow has total net flow zero, including flows that are not circulations. -/
theorem sum_balance (I : Circulation) (f : Fin I.m → ℝ) :
    ∑ v, I.balance f v = 0 := by
  have h := I.potential_pairing f (fun _ => 1)
  simpa [potentialDifference] using h.symm

private theorem all_zero_of_castSucc (n : ℕ) (a : Fin (n + 1) → ℝ)
    (hs : ∑ v, a v = 0) (h : ∀ v : Fin n, a v.castSucc = 0) : ∀ v, a v = 0 := by
  rw [Fin.sum_univ_castSucc] at hs
  have ht : (∑ v : Fin n, a v.castSucc) = 0 := by
    apply Finset.sum_eq_zero
    intro v _
    exact h v
  rw [ht, zero_add] at hs
  intro v
  exact Fin.lastCases hs h v

/-- The circulation instance for testing whether `d` can be routed. -/
abbrev demandInstance (I : Circulation) (d : Fin I.n → ℤ) : Circulation where
  n := I.n + 1
  m := I.m + (I.n + I.n)
  tail := Fin.addCases (fun e => (I.tail e).castSucc)
    (Fin.addCases (fun _ => Fin.last I.n) (fun v => v.castSucc))
  head := Fin.addCases (fun e => (I.head e).castSucc)
    (Fin.addCases (fun v => v.castSucc) (fun _ => Fin.last I.n))
  capacity := Fin.addCases I.capacity
    (Fin.addCases (fun v => (d v).toNat) (fun v => (-d v).toNat))
  cost := Fin.addCases (fun _ => 0) (fun _ => -1)

/-- Extend a candidate flow by saturating every artificial demand arc. -/
def demandLift (I : Circulation) (d : Fin I.n → ℤ) (f : Fin I.m → ℝ) :
    Fin (I.m + (I.n + I.n)) → ℝ :=
  Fin.addCases f (Fin.addCases (fun v => ((d v).toNat : ℝ))
    (fun v => ((-d v).toNat : ℝ)))

/-- The old part of the lifted flow has unchanged incidence at old vertices. -/
private theorem demand_old_incidence (I : Circulation) (d : Fin I.n → ℤ)
    (e : Fin I.m) (v : Fin I.n) :
    (I.demandInstance d).incidence (Fin.castAdd (I.n + I.n) e) v.castSucc =
      I.incidence e v := by
  classical
  simp [incidence, demandInstance, Fin.ext_iff]

/-- Saturated artificial arcs contribute minus the prescribed demand. -/
theorem demandLift_balance (I : Circulation) (d : Fin I.n → ℤ)
    (f : Fin I.m → ℝ) (v : Fin I.n) :
    (I.demandInstance d).balance (I.demandLift d f) v.castSucc =
      I.balance f v - (d v : ℝ) := by
  classical
  unfold balance
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [demandLift, Fin.addCases_left, Fin.addCases_right]
  simp only [demand_old_incidence]
  have hi : ((d v).toNat : ℝ) - ((-d v).toNat : ℝ) = (d v : ℝ) := by
    rcases le_total 0 (d v) with h | h
    · rw [Int.toNat_eq_zero.mpr (neg_nonpos.mpr h)]
      simp only [Nat.cast_zero, sub_zero]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    · rw [Int.toNat_eq_zero.mpr h]
      simp only [Nat.cast_zero, zero_sub]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (neg_nonneg.mpr h), Int.cast_neg,
        neg_neg]
  simp only [incidence, demandInstance, Fin.addCases_left, Fin.addCases_right]
  simp [Finset.sum_sub_distrib, sub_mul, ite_mul] 
  linarith only [hi]

/-- A bounded flow routing `d` extends to a feasible circulation by saturating
the new arcs. This proves the forward direction of the feasibility reduction. -/
theorem demandLift_feasible (I : Circulation) (d : Fin I.n → ℤ)
    (f : Fin I.m → ℝ) (hr : ∀ v, I.balance f v = (d v : ℝ))
    (hb : ∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e) :
    (I.demandInstance d).Feasible (I.demandLift d f) := by
  constructor
  · apply all_zero_of_castSucc I.n _ ((I.demandInstance d).sum_balance _)
    intro v
    rw [demandLift_balance, hr, sub_self]
  · intro e
    refine Fin.addCases (fun e => ?_) (fun a => ?_) e
    · simpa [demandLift, demandInstance] using hb e
    · refine Fin.addCases (fun v => ?_) (fun v => ?_) a
      · simp only [demandLift, Fin.addCases_left, Fin.addCases_right]
        exact ⟨Nat.cast_nonneg _, le_rfl⟩
      · simp only [demandLift, Fin.addCases_right]
        exact ⟨Nat.cast_nonneg _, le_rfl⟩

/-- The amount of artificial capacity that must all be saturated. -/
def demandMass (I : Circulation) (d : Fin I.n → ℤ) : ℕ :=
  ∑ v, ((d v).toNat + (-d v).toNat)

/-- Discard the artificial arcs after the feasibility phase. -/
def demandRestrict (I : Circulation) (g : Fin (I.m + (I.n + I.n)) → ℝ) :
    Fin I.m → ℝ := fun e => g (Fin.castAdd (I.n + I.n) e)

/-- The objective is minus the total flow on artificial arcs. -/
theorem demand_objective (I : Circulation) (d : Fin I.n → ℤ)
    (g : Fin (I.m + (I.n + I.n)) → ℝ) :
    (I.demandInstance d).objective g =
      -(∑ a : Fin (I.n + I.n), g (Fin.natAdd I.m a)) := by
  unfold objective
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Int.cast_zero,
    Int.cast_neg, Int.cast_one, zero_mul, neg_one_mul, Finset.sum_const_zero,
    zero_add, Finset.sum_neg_distrib]

private theorem auxiliary_capacity_sum (I : Circulation) (d : Fin I.n → ℤ) :
    (∑ a : Fin (I.n + I.n),
      ((I.demandInstance d).capacity (Fin.natAdd I.m a) : ℝ)) = I.demandMass d := by
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_right, Fin.addCases_left, demandMass,
    Nat.cast_sum, Nat.cast_add, Finset.sum_add_distrib]

/-- The objective lower bound is minus the total artificial capacity. -/
theorem demand_objective_lower_bound (I : Circulation) (d : Fin I.n → ℤ)
    (g : Fin (I.m + (I.n + I.n)) → ℝ) (hg : (I.demandInstance d).Feasible g) :
    -(I.demandMass d : ℝ) ≤ (I.demandInstance d).objective g := by
  rw [demand_objective, neg_le_neg_iff, ← auxiliary_capacity_sum]
  apply Finset.sum_le_sum
  intro a _
  exact (hg.2 (Fin.natAdd I.m a)).2

/-- Equality with the objective lower bound forces every artificial arc to
be saturated. Its restriction then routes precisely the prescribed demands. -/
theorem demandRestrict_routes (I : Circulation) (d : Fin I.n → ℤ)
    (g : Fin (I.m + (I.n + I.n)) → ℝ) (hg : (I.demandInstance d).Feasible g)
    (heq : (I.demandInstance d).objective g = -(I.demandMass d : ℝ)) :
    (∀ v, I.balance (I.demandRestrict g) v = (d v : ℝ)) ∧
      ∀ e, 0 ≤ I.demandRestrict g e ∧ I.demandRestrict g e ≤ I.capacity e := by
  have hsat : ∀ a : Fin (I.n + I.n), g (Fin.natAdd I.m a) =
      ((I.demandInstance d).capacity (Fin.natAdd I.m a) : ℝ) := by
    have hs : (∑ a : Fin (I.n + I.n),
        (((I.demandInstance d).capacity (Fin.natAdd I.m a) : ℝ) -
          g (Fin.natAdd I.m a))) = 0 := by
      rw [Finset.sum_sub_distrib, auxiliary_capacity_sum]
      rw [demand_objective] at heq
      linarith only [heq]
    have hnon : ∀ a (_ : a ∈ (Finset.univ : Finset (Fin (I.n + I.n)))),
        0 ≤ ((I.demandInstance d).capacity (Fin.natAdd I.m a) : ℝ) -
          g (Fin.natAdd I.m a) := by
      intro a _
      exact sub_nonneg.mpr (hg.2 (Fin.natAdd I.m a)).2
    intro a
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnon).mp hs a (Finset.mem_univ a)
    exact (sub_eq_zero.mp hz).symm
  have hext : I.demandLift d (I.demandRestrict g) = g := by
    funext e
    refine Fin.addCases (fun a => ?_) (fun a => ?_) e
    · simp only [demandLift, Fin.addCases_left, demandRestrict]
    · rw [hsat]
      refine Fin.addCases (fun v => ?_) (fun v => ?_) a
      · simp only [demandLift, Fin.addCases_left, Fin.addCases_right]
      · simp only [demandLift, Fin.addCases_right]
  constructor
  · intro v
    have hb := I.demandLift_balance d (I.demandRestrict g) v
    rw [hext, hg.1 v.castSucc] at hb
    linarith only [hb]
  · intro e
    simpa only [demandRestrict, Fin.addCases_left] using
      hg.2 (Fin.castAdd (I.n + I.n) e)

/-- Every bounded flow routing the demands attains the objective lower bound
in the feasibility circulation. -/
theorem demandLift_objective (I : Circulation) (d : Fin I.n → ℤ)
    (f : Fin I.m → ℝ) :
    (I.demandInstance d).objective (I.demandLift d f) = -(I.demandMass d : ℝ) := by
  rw [demand_objective, ← auxiliary_capacity_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  refine Fin.addCases (fun v => ?_) (fun v => ?_) a
  · simp only [demandLift, Fin.addCases_left, Fin.addCases_right]
  · simp only [demandLift, Fin.addCases_right]

/-- An optimal feasibility-phase circulation decides whether the prescribed
demands have a bounded routing. This includes the infeasible-answer direction. -/
theorem demand_feasible_iff_optimal_value (I : Circulation) (d : Fin I.n → ℤ)
    (g : Fin (I.m + (I.n + I.n)) → ℝ) (hg : (I.demandInstance d).Optimal g) :
    (∃ f : Fin I.m → ℝ, (∀ v, I.balance f v = (d v : ℝ)) ∧
      ∀ e, 0 ≤ f e ∧ f e ≤ I.capacity e) ↔
      (I.demandInstance d).objective g = -(I.demandMass d : ℝ) := by
  constructor
  · rintro ⟨f, hr, hb⟩
    have hu := hg.2 _ (I.demandLift_feasible d f hr hb)
    rw [demandLift_objective] at hu
    exact le_antisymm hu (I.demand_objective_lower_bound d g hg.1)
  · intro h
    exact ⟨I.demandRestrict g, I.demandRestrict_routes d g hg.1 h⟩

end MinCostFlow.Scaling.Circulation
