module

public import MinCostFlow.Scaling.CostStepCorrectness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Correctness of the finite cost-scaling loop

The proof of Lemma C.3 of Chen et al., arXiv:2203.00671v2, Appendix C,
starts from zero flow, halves epsilon each round by Lemma C.7, and applies
Lemma C.5 once epsilon is below `1/(n+1)`. This file follows that induction
for the actual integer-state loop. Initialization uses `C+1` to satisfy the
source's strict epsilon definition, and the loop budget includes that repair.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Increasing positive epsilon preserves the same witness potential. -/
theorem Circulation.epsilonOptimalWith_mono (I : Circulation)
    (f : Fin I.m → ℝ) (y : Fin I.n → ℝ) (epsilon larger : ℝ)
    (h : I.EpsilonOptimalWith f epsilon y) (he : epsilon ≤ larger) :
    I.EpsilonOptimalWith f larger y := by
  refine ⟨lt_of_lt_of_le h.1 he, h.2.1, ?_⟩
  intro e
  constructor
  · intro ha
    exact lt_of_le_of_lt (neg_le_neg he) ((h.2.2 e).1 ha)
  · intro ha
    exact lt_of_le_of_lt (neg_le_neg he) ((h.2.2 e).2 ha)

/-- Epsilon optimality is preserved through every state of the finite loop. -/
theorem costLoop_epsilonOptimalWith
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ)
    (hU : 1 ≤ U) (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hc : I.CostsBounded C) (hu : ∀ e, I.capacity e ≤ U) :
    I.EpsilonOptimalWith (fun e => ((costLoop solve I C).value.flow e : ℝ))
      ((costLoop solve I C).value.epsilon C)
      (CostState.realPotential (I := I) C (costLoop solve I C).value) := by
  let P (s : CostState I) := 0 < s.power ∧
    I.EpsilonOptimalWith (fun e => (s.flow e : ℝ)) (s.epsilon C)
      (CostState.realPotential (I := I) C s)
  have hstep : ∀ s, P s → P (s.step solve C).value := by
    intro s hs
    refine ⟨?_, s.step_epsilonOptimalWith solve C U hU hm hn hsolve hu hs.1 hs.2⟩
    change 0 < 2 * s.power
    exact Nat.mul_pos (by decide) hs.1
  have hinit : P (CostState.initial I) := by
    refine ⟨?_, ?_⟩
    · simp only [CostState.initial]
      decide
    · rw [CostState.initial_epsilon, CostState.initial_realPotential]
      simp only [CostState.initial, Int.cast_zero]
      apply I.zero_epsilonOptimal C
      intro e
      have hh := hc e
      omega
  exact (CallResult.forRounds_invariant (CostState.step solve C) P hstep
    (costRounds I.n C) (CostState.initial I) hinit).2

/-- The final represented epsilon lies below the source's exactness threshold. -/
theorem costLoop_epsilon_lt (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (C : ℕ) :
    (costLoop solve I C).value.epsilon C < 1 / ((I.n : ℝ) + 1) := by
  unfold CostState.epsilon
  rw [costLoop_power]
  have hp : (0 : ℝ) < ((2 ^ costRounds I.n C : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.pow_pos (by decide))
  have hn : (0 : ℝ) < (I.n : ℝ) + 1 := by positivity
  apply (div_lt_div_iff₀ hp hn).mpr
  have hh := costRounds_stopping I.n C
  simp only [one_mul]
  exact_mod_cast hh

/-- The actual finite loop returns an exact integral circulation optimum.
This is the loop conclusion in the proof of Lemma C.3. -/
theorem costLoop_optimal
    (solve : (J : Circulation) → Fin J.m → ℤ) (I : Circulation) (C U : ℕ)
    (hU : 1 ≤ U) (hm : 0 < I.m) (hn : I.n ≤ I.m + I.m)
    (hsolve : ∀ J : Circulation, J.CostsBounded (J.m ^ 10) →
      (∀ e, 1 ≤ J.capacity e ∧ J.capacity e ≤ max U (I.n + 1)) →
      J.Optimal (fun e => (solve J e : ℝ)))
    (hc : I.CostsBounded C) (hu : ∀ e, I.capacity e ≤ U) :
    I.Optimal (fun e => ((costLoop solve I C).value.flow e : ℝ)) := by
  have heps := costLoop_epsilonOptimalWith solve I C U hU hm hn hsolve hc hu
  have hl := costLoop_epsilon_lt solve I C
  apply I.lemma_C_5 (costLoop solve I C).value.flow
  exact ⟨_, I.epsilonOptimalWith_mono _ _ _ _ heps hl.le⟩

end MinCostFlow.Scaling
