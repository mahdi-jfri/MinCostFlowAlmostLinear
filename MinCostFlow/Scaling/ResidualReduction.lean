module

public import MinCostFlow.Scaling.Residual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Optimizing after finding a feasible flow

The reduction used in the proof of Lemma C.1 of Chen et al.,
arXiv:2203.00671v2, first finds a feasible integral flow and then optimizes a
circulation in its residual graph. This file proves both directions of that
reduction, including comparison with every feasible real flow. Prescribed
demands cancel when subtracting two flows, so the residual problem always has
zero demand.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Taking a difference of flows takes the difference of their net flows. -/
theorem balance_sub (I : Circulation) (f g : Fin I.m → ℝ) (v : Fin I.n) :
    I.balance (fun e => f e - g e) v = I.balance f v - I.balance g v := by
  simp only [balance, mul_sub, Finset.sum_sub_distrib]

/-- Adding a residual flow adds its net flow to the original one. -/
theorem augment_balance (I : Circulation) (f : Fin I.m → ℤ)
    (g : Fin (I.m + I.m) → ℝ) (v : Fin I.n) :
    I.balance (I.augment f g) v = I.balance (fun e => (f e : ℝ)) v +
      (I.residual f).balance g v := by
  rw [residual_balance]
  simp only [balance, augment, mul_add, Finset.sum_add_distrib]

/-- Lift the difference of two flows into forward and reverse residual slots. -/
def differenceLift (I : Circulation) (f : Fin I.m → ℤ) (h : Fin I.m → ℝ) :
    Fin (I.m + I.m) → ℝ :=
  Fin.addCases (fun e => max (h e - (f e : ℝ)) 0)
    (fun e => max ((f e : ℝ) - h e) 0)

/-- Projection recovers the signed difference exactly. -/
theorem project_differenceLift (I : Circulation) (f : Fin I.m → ℤ)
    (h : Fin I.m → ℝ) :
    I.project (I.differenceLift f h) = fun e => h e - (f e : ℝ) := by
  funext e
  simp only [project, differenceLift, Fin.addCases_left, Fin.addCases_right]
  rcases le_total (h e) (f e : ℝ) with hs | hs
  · rw [max_eq_right (sub_nonpos.mpr hs), max_eq_left (sub_nonneg.mpr hs)]
    ring
  · rw [max_eq_left (sub_nonneg.mpr hs), max_eq_right (sub_nonpos.mpr hs)]
    ring

/-- Exact real values of the two integer residual capacities for a bounded flow. -/
theorem residual_capacity_cast (I : Circulation) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ (f e : ℝ) ∧ (f e : ℝ) ≤ I.capacity e) (e : Fin I.m) :
    (((I.residual f).capacity (Fin.castAdd I.m e) : ℕ) : ℝ) =
        (I.capacity e : ℝ) - (f e : ℝ) ∧
    (((I.residual f).capacity (Fin.natAdd I.m e) : ℕ) : ℝ) = (f e : ℝ) := by
  have hnon : 0 ≤ f e := (Int.cast_nonneg_iff (R := ℝ)).mp (hf e).1
  have hbound : f e ≤ (I.capacity e : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_natCast] using (hf e).2
  constructor
  · simp only [Fin.addCases_left]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hbound),
      Int.cast_sub, Int.cast_natCast]
  · simp only [Fin.addCases_right]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hnon]

/-- Two bounded flows routing the same demands differ by a feasible residual
circulation. The second flow may be fractional. -/
theorem differenceLift_feasible (I : Circulation) (f : Fin I.m → ℤ)
    (h : Fin I.m → ℝ)
    (hf : ∀ e, 0 ≤ (f e : ℝ) ∧ (f e : ℝ) ≤ I.capacity e)
    (hh : ∀ e, 0 ≤ h e ∧ h e ≤ I.capacity e)
    (hr : ∀ v, I.balance h v = I.balance (fun e => (f e : ℝ)) v) :
    (I.residual f).Feasible (I.differenceLift f h) := by
  constructor
  · intro v
    rw [residual_balance, project_differenceLift, balance_sub, hr, sub_self]
  · intro a
    refine Fin.addCases (fun e => ?_) (fun e => ?_) a
    · rw [(I.residual_capacity_cast f hf e).1]
      simp only [differenceLift, Fin.addCases_left]
      exact ⟨le_max_right _ _, max_le (by linarith only [(hh e).2])
        (sub_nonneg.mpr (hf e).2)⟩
    · rw [(I.residual_capacity_cast f hf e).2]
      simp only [differenceLift, Fin.addCases_right]
      exact ⟨le_max_right _ _, max_le (by linarith only [(hh e).1]) (hf e).1⟩

/-- Augmentation preserves the capacity constraints even when the original
flow has nonzero demands. -/
theorem augment_bounds (I : Circulation) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ (f e : ℝ) ∧ (f e : ℝ) ≤ I.capacity e)
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Feasible g) :
    ∀ e, 0 ≤ I.augment f g e ∧ I.augment f g e ≤ I.capacity e := by
  intro e
  have ha := hg.2 (Fin.castAdd I.m e)
  have hb := hg.2 (Fin.natAdd I.m e)
  rw [(I.residual_capacity_cast f hf e).1] at ha
  rw [(I.residual_capacity_cast f hf e).2] at hb
  dsimp only [augment, project]
  constructor <;> linarith only [ha.1, ha.2, hb.1, hb.2]

/-- Exact optimization of the residual circulation minimizes cost among all
bounded flows with the original demands. This is the optimization half of the
reduction used in Lemma C.1. -/
theorem augment_optimal_with_demands (I : Circulation) (f : Fin I.m → ℤ)
    (hf : ∀ e, 0 ≤ (f e : ℝ) ∧ (f e : ℝ) ≤ I.capacity e)
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Optimal g) :
    (∀ v, I.balance (I.augment f g) v = I.balance (fun e => (f e : ℝ)) v) ∧
    (∀ e, 0 ≤ I.augment f g e ∧ I.augment f g e ≤ I.capacity e) ∧
    ∀ h : Fin I.m → ℝ,
      (∀ v, I.balance h v = I.balance (fun e => (f e : ℝ)) v) →
      (∀ e, 0 ≤ h e ∧ h e ≤ I.capacity e) →
      I.objective (I.augment f g) ≤ I.objective h := by
  refine ⟨?_, I.augment_bounds f hf g hg.1, ?_⟩
  · intro v
    rw [augment_balance, hg.1.1 v, add_zero]
  · intro h hr hh
    have hcomp := hg.2 _ (I.differenceLift_feasible f h hf hh hr)
    simp only [residual_objective, project_differenceLift] at hcomp
    have hc : I.objective (fun e => h e - (f e : ℝ)) =
        I.objective h - I.objective (fun e => (f e : ℝ)) := by
      simp only [objective, mul_sub, Finset.sum_sub_distrib]
    rw [hc] at hcomp
    rw [augment_objective, residual_objective]
    linarith only [hcomp]

/-- At an optimal integral flow, zero is an optimal circulation in the residual
graph. Otherwise a residual improvement would improve the original flow. -/
theorem zero_residual_optimal (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Optimal (fun e => (f e : ℝ))) :
    (I.residual f).Optimal (fun _ => 0) := by
  refine ⟨(I.residual f).zero_feasible, ?_⟩
  intro g hg
  have h := hf.2 (I.augment f g) (I.augment_feasible f hf.1 g hg)
  rw [augment_objective] at h
  have hz : (I.residual f).objective (fun _ => 0) = 0 := by simp [objective]
  rw [hz]
  linarith only [h]

end MinCostFlow.Scaling.Circulation
