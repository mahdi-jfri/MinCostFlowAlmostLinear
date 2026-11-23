module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Residual circulations

Appendix C of Chen et al., arXiv:2203.00671v2, defines the residual graph just
after the primal and dual equations. A forward arc has capacity `u - f` and
cost `c`. A reverse arc has capacity `f` and cost `-c`. Here each original edge
has two slots. Slots with capacity zero can only carry zero flow, so retaining
them does not change the problem. This representation gives an explicit edge
bound and avoids renumbering edges after each augmentation.
-/

@[expose] public section

namespace MinCostFlow.Scaling.Circulation

/-- The residual instance of an integral flow. The first half contains forward
arcs and the second half reverse arcs. For feasible flows `toNat` is exact. -/
abbrev residual (I : Circulation) (f : Fin I.m → ℤ) : Circulation where
  n := I.n
  m := I.m + I.m
  tail := Fin.addCases I.tail I.head
  head := Fin.addCases I.head I.tail
  capacity := Fin.addCases (fun e => ((I.capacity e : ℤ) - f e).toNat)
    (fun e => (f e).toNat)
  cost := Fin.addCases I.cost (fun e => -I.cost e)

/-- Project a residual flow back onto the original edge directions. -/
def project (I : Circulation) (g : Fin (I.m + I.m) → ℝ) (e : Fin I.m) : ℝ :=
  g (Fin.castAdd I.m e) - g (Fin.natAdd I.m e)

/-- Augment an original flow by a residual flow. -/
def augment (I : Circulation) (f : Fin I.m → ℤ)
    (g : Fin (I.m + I.m) → ℝ) (e : Fin I.m) : ℝ :=
  (f e : ℝ) + I.project g e

/-- Residual instances have exactly two slots for each original edge. -/
theorem residual_edges (I : Circulation) (f : Fin I.m → ℤ) :
    (I.residual f).m = 2 * I.m := by
  dsimp [residual]
  omega

/-- Reversing an edge negates its incidence coefficient. -/
theorem residual_incidence_reverse (I : Circulation) (f : Fin I.m → ℤ)
    (e : Fin I.m) (v : Fin I.n) :
    (I.residual f).incidence (Fin.natAdd I.m e) v = -I.incidence e v := by
  simp only [incidence, residual, Fin.addCases_right]
  ring

/-- Projection preserves net flow at every vertex. -/
theorem residual_balance (I : Circulation) (f : Fin I.m → ℤ)
    (g : Fin (I.m + I.m) → ℝ) (v : Fin I.n) :
    (I.residual f).balance g v = I.balance (I.project g) v := by
  classical
  unfold balance
  change (∑ e : Fin (I.m + I.m), (I.residual f).incidence e v * g e) = _
  rw [Fin.sum_univ_add]
  dsimp only [residual, incidence]
  simp only [Fin.addCases_left, Fin.addCases_right, project]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Projection preserves residual objective values. -/
theorem residual_objective (I : Circulation) (f : Fin I.m → ℤ)
    (g : Fin (I.m + I.m) → ℝ) :
    (I.residual f).objective g = I.objective (I.project g) := by
  unfold objective
  change (∑ e : Fin (I.m + I.m), ((I.residual f).cost e : ℝ) * g e) = _
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, Int.cast_neg, project]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- The objective change is exactly the cost paid in the residual instance. -/
theorem augment_objective (I : Circulation) (f : Fin I.m → ℤ)
    (g : Fin (I.m + I.m) → ℝ) :
    I.objective (I.augment f g) =
      I.objective (fun e => (f e : ℝ)) + (I.residual f).objective g := by
  rw [residual_objective]
  simp only [objective, augment, mul_add, Finset.sum_add_distrib]

/-- Augmentation by a feasible residual circulation preserves primal feasibility.
This justifies the flow update in both scaling algorithms of Appendix C. -/
theorem augment_feasible (I : Circulation) (f : Fin I.m → ℤ)
    (hf : I.Feasible (fun e => (f e : ℝ)))
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Feasible g) :
    I.Feasible (I.augment f g) := by
  constructor
  · intro v
    have hr := (I.residual_balance f g v).symm.trans (hg.1 v)
    change I.balance (I.augment f g) v = 0
    simp only [balance, augment, mul_add, Finset.sum_add_distrib]
    change I.balance (fun e => (f e : ℝ)) v + I.balance (I.project g) v = 0
    rw [hf.1 v, hr, zero_add]
  · intro e
    have hforward := hg.2 (Fin.castAdd I.m e)
    have hreverse := hg.2 (Fin.natAdd I.m e)
    have hnonneg : 0 ≤ f e := by
      apply (Int.cast_nonneg_iff (R := ℝ)).mp
      exact (hf.2 e).1
    have hbound : f e ≤ (I.capacity e : ℤ) := by
      apply (Int.cast_le (R := ℝ)).mp
      simpa only [Int.cast_natCast] using (hf.2 e).2
    have hfwd : (((I.residual f).capacity (Fin.castAdd I.m e) : ℕ) : ℝ) =
        (I.capacity e : ℝ) - (f e : ℝ) := by
      simp only [Fin.addCases_left]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (sub_nonneg.mpr hbound),
        Int.cast_sub, Int.cast_natCast]
    have hrev : (((I.residual f).capacity (Fin.natAdd I.m e) : ℕ) : ℝ) =
        (f e : ℝ) := by
      simp only [Fin.addCases_right]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hnonneg]
    rw [hfwd] at hforward
    rw [hrev] at hreverse
    dsimp only [augment, project]
    constructor <;> linarith only [hforward.1, hforward.2, hreverse.1, hreverse.2]

end MinCostFlow.Scaling.Circulation
