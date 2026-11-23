module

public import MinCostFlow.Scaling.Circulation
import Mathlib.Tactic.Linarith

/-!
# Positive-capacity solver calls

The circulation solver assumed in Appendix C of Chen et al.,
arXiv:2203.00671v2, accepts positive capacities. Residual and rounded instances
in this formalization retain inactive edge slots of capacity zero. Replace
each such slot by a zero-cost capacity-one loop at a new isolated vertex.
This preserves the number of edge slots and does not change the optimization
problem after the unused slots are set back to zero.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- Replace capacity-zero slots by harmless positive-capacity loops. -/
abbrev positiveInstance (I : Circulation) : Circulation where
  n := I.n + 1
  m := I.m
  tail := fun e => if I.capacity e = 0 then Fin.last I.n else (I.tail e).castSucc
  head := fun e => if I.capacity e = 0 then Fin.last I.n else (I.head e).castSucc
  capacity := fun e => if I.capacity e = 0 then 1 else I.capacity e
  cost := fun e => if I.capacity e = 0 then 0 else I.cost e

/-- Discard flows on dummy loops after a solver call. -/
def eraseZeroFlow (I : Circulation) (f : Fin I.m → ℝ) (e : Fin I.m) : ℝ :=
  if I.capacity e = 0 then 0 else f e

/-- Every capacity presented to the solver is positive. -/
theorem positiveInstance_capacity_pos (I : Circulation) (e : Fin I.m) :
    0 < I.positiveInstance.capacity e := by
  dsimp only [positiveInstance]
  split
  · exact Nat.zero_lt_one
  · exact Nat.pos_of_ne_zero ‹_›

/-- The new isolated vertex has zero net flow for every flow vector. -/
theorem positiveInstance_balance_last (I : Circulation) (f : Fin I.m → ℝ) :
    I.positiveInstance.balance f (Fin.last I.n) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro e _
  by_cases h : I.capacity e = 0
  · simp [incidence, positiveInstance, h]
  · have ht := (Fin.castSucc_ne_last (I.tail e)).symm
    have hh := (Fin.castSucc_ne_last (I.head e)).symm
    simp [incidence, positiveInstance, h, ht, hh]

/-- At old vertices, the net flow equals that of the vector with unused slots
set to zero. -/
theorem positiveInstance_balance_old (I : Circulation) (f : Fin I.m → ℝ)
    (v : Fin I.n) :
    I.positiveInstance.balance f v.castSucc = I.balance (I.eraseZeroFlow f) v := by
  classical
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : I.capacity e = 0
  · simp [incidence, positiveInstance, eraseZeroFlow, h]
  · simp [incidence, positiveInstance, eraseZeroFlow, h]

/-- The solver's objective is exactly the original objective after zero slots
are erased. -/
theorem positiveInstance_objective (I : Circulation) (f : Fin I.m → ℝ) :
    I.positiveInstance.objective f = I.objective (I.eraseZeroFlow f) := by
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : I.capacity e = 0 <;>
    simp [eraseZeroFlow, h]

/-- Feasible original flows already vanish on every zero-capacity slot. -/
theorem eraseZeroFlow_of_feasible (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) : I.eraseZeroFlow f = f := by
  funext e
  by_cases h : I.capacity e = 0
  · have hz : f e = 0 := le_antisymm (by simpa only [h, Nat.cast_zero] using (hf.2 e).2)
      (hf.2 e).1
    simp [eraseZeroFlow, h, hz]
  · simp [eraseZeroFlow, h]

/-- Any feasible result from a positive-capacity call restricts to a feasible
flow on the original instance. -/
theorem eraseZeroFlow_feasible (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.positiveInstance.Feasible f) : I.Feasible (I.eraseZeroFlow f) := by
  constructor
  · intro v
    rw [← positiveInstance_balance_old]
    exact hf.1 v.castSucc
  · intro e
    by_cases h : I.capacity e = 0
    · simp [eraseZeroFlow, h]
    · simpa only [positiveInstance, eraseZeroFlow, h, ↓reduceIte] using hf.2 e

/-- A feasible original flow can be passed to the positive-capacity instance
without changing any coordinate. -/
theorem positiveInstance_feasible (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.Feasible f) : I.positiveInstance.Feasible f := by
  constructor
  · intro v
    refine Fin.lastCases (I.positiveInstance_balance_last f) (fun w => ?_) v
    rw [positiveInstance_balance_old, I.eraseZeroFlow_of_feasible f hf]
    exact hf.1 w
  · intro e
    by_cases h : I.capacity e = 0
    · have he : f e = 0 := by
        have hh := congrFun (I.eraseZeroFlow_of_feasible f hf) e
        simpa only [eraseZeroFlow, h, ↓reduceIte] using hh.symm
      simp [h, he]
    · simpa only [positiveInstance, h, ↓reduceIte] using hf.2 e

/-- An exact positive-capacity solver result gives an exact original optimum.
Thus no stronger solver hypothesis is needed for zero-capacity instances. -/
theorem eraseZeroFlow_optimal (I : Circulation) (f : Fin I.m → ℝ)
    (hf : I.positiveInstance.Optimal f) : I.Optimal (I.eraseZeroFlow f) := by
  refine ⟨I.eraseZeroFlow_feasible f hf.1, ?_⟩
  intro g hg
  have h := hf.2 g (I.positiveInstance_feasible g hg)
  rw [positiveInstance_objective, positiveInstance_objective,
    I.eraseZeroFlow_of_feasible g hg] at h
  exact h

end MinCostFlow.Scaling.Circulation
