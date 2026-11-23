module

public import MinCostFlow.IPM.Iteration
public import MinCostFlow.IPM.IntegralOptimum
import MinCostFlow.IPM.OptimalDirection
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Testing an integer target by a bounded IPM run

Section 4 of Chen et al., arXiv:2203.00671v2 (page 24), proposes binary
search for the target cost. For a supplied guess, run the IPM for at
most its explicit iteration limit. Accept if some feasible iterate has
cost at most the guess plus `(mU)^(-10)`. A permitted min-ratio step is
a parameter. It may report failure only if no permitted step exists.
Such a selector exists by choosing a permitted step when one exists.
This is a mathematical model, with no claim about the selector's cost.

For an upper guess, the comparison direction from Lemma 4.7 provides a
permitted step until acceptance. Thus Theorem 4.3 forces acceptance.
For a lower integer guess, an integral optimum and a tolerance less than
one rule out acceptance. No comparison test is assumed as a hypothesis.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The min-ratio step parameter for the guess test. At an input flow it
returns a permitted step, or reports that none exists. -/
abbrev StepSelector (I : Instance) (U κ : ℝ) :=
  (F : ℝ) → (f : Fin I.m → ℝ) → Option (Update I U F κ f)

/-- Completeness of the permitted-step selection. Correctness of every
returned step is part of its type `Update`, not an extra conclusion. -/
@[expose] def SelectsPermittedSteps {I : Instance} {U κ : ℝ}
    (step : StepSelector I U κ) : Prop :=
  ∀ F f, Nonempty (Update I U F κ f) → (step F f).isSome = true

/-- Permitted-step selectors exist. This proves the mathematical model's
parameter conditions can hold simultaneously. -/
theorem exists_stepSelector (I : Instance) (U κ : ℝ) :
    ∃ step : StepSelector I U κ, SelectsPermittedSteps step := by
  classical
  refine ⟨fun F f => if h : Nonempty (Update I U F κ f) then some (Classical.choice h) else none, ?_⟩
  intro F f h
  simp only [h, ↓reduceDIte, Option.isSome_some]

/-- A bounded test step freezes once the cost threshold is reached, or
when the supplied min-ratio step reports failure. -/
@[expose] def guessNext (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f : Fin I.m → ℝ) : Fin I.m → ℝ :=
  if Real.rpow (I.m*U) (-10) < residual I F f then
    match step F f with
    | some s => s.next
    | none => f
  else f

/-- The flow sequence of one bounded IPM target test. -/
@[expose] def guessFlow (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f₀ : Fin I.m → ℝ) : ℕ → Fin I.m → ℝ
  | 0 => f₀
  | t+1 => guessNext I U F κ step (guessFlow I U F κ step f₀ t)

/-- Domain and potential invariants hold even if step selection fails.
Freezing the flow on failure preserves all four invariants. -/
theorem guessFlow_invariants (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f₀ : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (hf : StrictlyInside I f₀) (hroute : I.Routes f₀) (hr : 0 < residual I F f₀)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) (t : ℕ) :
    I.Routes (guessFlow I U F κ step f₀ t) ∧
      StrictlyInside I (guessFlow I U F κ step f₀ t) ∧
      0 < residual I F (guessFlow I U F κ step f₀ t) ∧
      potential I (alpha I U) F (guessFlow I U F κ step f₀ t) ≤
        200*I.m*Real.log (I.m*U) := by
  have hκ' : κ ≤ 1 := by linarith only [hκa, alpha_le I U hsize]
  induction t with
  | zero => exact ⟨hroute, hf, hr, hinit⟩
  | succ t ih =>
    simp only [guessFlow, guessNext]
    split_ifs with hstop
    · cases heq : step F (guessFlow I U F κ step f₀ t) with
      | none => exact ih
      | some s =>
        have hs := s.spec hm hU hsize hnums ih.2.1 ih.1 ih.2.2.1 hκ hκ'
        refine ⟨hs.1, hs.2.1, hs.2.2.1, ?_⟩
        linarith only [hs.2.2.2, ih.2.2.2, sq_nonneg κ]
    · exact ih

/-- For a feasible comparison flow below the target, the guess run is
admissible. The upper-target extension of Lemma 4.7 supplies the step
whose existence invokes the selector's completeness. -/
theorem guessFlow_admissible (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (hstep : SelectsPermittedSteps step) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hr : 0 < residual I F f₀) (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) :
    AdmissibleRun I U F κ (guessFlow I U F κ step f₀) := by
  intro t hstop
  have hi := guessFlow_invariants I U F κ step f₀ hm hU hsize hnums hf hroute hr hκ hκa hinit t
  have hex := exact_approximations I (alpha I U) F (κ/8) _ hi.2.1
    (div_nonneg hκ.le (by norm_num : (0 : ℝ) ≤ 8))
  obtain ⟨s, _, _, _⟩ := exists_update_with_approximations_of_cost_le I U F κ _ fstar
    (gradient I (alpha I U) F _) (lengths I (alpha I U) _) hm hsize hi.2.1 hi.1 hs
    hi.2.2.1 hF hκ hκa hex.1 hex.2 hi.2.2.2
    (log_residual_before_stop I U F _ hsize hstop)
  obtain ⟨s', heq⟩ := Option.isSome_iff_exists.mp (hstep F _ ⟨s⟩)
  refine ⟨s', ?_⟩
  simp only [guessFlow, guessNext, hstop, ↓reduceIte, heq]

/-- Search the bounded run for its first iterate meeting the target cost.
The search examines at most `iterationLimit + 1` iterates. -/
@[expose] def guessAcceptedStage (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f₀ : Fin I.m → ℝ) : Option ℕ :=
  (List.range (iterationLimit I U κ+1)).find? fun t =>
    decide (I.cost (guessFlow I U F κ step f₀ t) ≤ F+Real.rpow (I.m*U) (-10))

/-- One target test uses at most one IPM run. If the initial flow already
meets the threshold, it is returned directly. -/
@[expose] def guessTest (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f₀ : Fin I.m → ℝ) : Option (Fin I.m → ℝ) :=
  if I.cost f₀ ≤ F+Real.rpow (I.m*U) (-10) then some f₀ else
    (guessAcceptedStage I U F κ step f₀).map (guessFlow I U F κ step f₀)

/-- Every accepted test supplies a feasible flow below the cost threshold,
regardless of which side of the optimal value the guess lies on. -/
theorem guessTest_sound (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (f₀ g : Fin I.m → ℝ) (hm : 0 < I.m) (hU : 0 ≤ U)
    (hsize : 2 ≤ (I.m : ℝ)*U) (hnums : NumbersBounded I U)
    (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : 0 < residual I F f₀ →
      potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U))
    (hout : guessTest I U F κ step f₀ = some g) :
    I.IsFeasible g ∧ I.cost g ≤ F+Real.rpow (I.m*U) (-10) := by
  classical
  unfold guessTest at hout
  split_ifs at hout with hstart
  · have heq := Option.some.inj hout
    subst g
    exact ⟨feasible_of_inside I _ hroute hf, hstart⟩
  · have hr : 0 < residual I F f₀ := by
      have hpos : 0 < Real.rpow (I.m*U) (-10) :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hsize) _
      dsimp only [residual]
      linarith only [not_le.mp hstart, hpos]
    obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp hout
    have hi := guessFlow_invariants I U F κ step f₀ hm hU hsize hnums hf hroute hr hκ hκa (hinit hr) t
    refine ⟨feasible_of_inside I _ hi.1 hi.2.1, ?_⟩
    unfold guessAcceptedStage at ht
    have hh := List.find?_some ht
    exact of_decide_eq_true hh

/-- Every upper guess is accepted within the iteration bound. This is
proved from the universal Theorem 4.3, rather than assumed of the test. -/
theorem guessTest_complete (I : Instance) (U F κ : ℝ) (step : StepSelector I U κ)
    (hstep : SelectsPermittedSteps step) (f₀ fstar : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 < U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : 0 < residual I F f₀ →
      potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U)) :
    (guessTest I U F κ step f₀).isSome = true := by
  classical
  unfold guessTest
  split_ifs with hstart
  · rfl
  · have hr : 0 < residual I F f₀ := by
      have hpos : 0 < Real.rpow (I.m*U) (-10) :=
        Real.rpow_pos_of_pos (lt_of_lt_of_le (by norm_num) hsize) _
      dsimp only [residual]
      linarith only [not_le.mp hstart, hpos]
    have hadm := guessFlow_admissible I U F κ step hstep f₀ fstar hm hU.le hsize hnums
      hf hroute hr hs hF hκ hκa (hinit hr)
    obtain ⟨t, ht, _, hcost⟩ := theorem_4_3_prefix I U F κ (guessFlow I U F κ step f₀)
      hm hU hsize hnums hf hroute hr hκ hκa (hinit hr) hadm
    have hsome : (guessAcceptedStage I U F κ step f₀).isSome = true := by
      apply List.find?_isSome.mpr
      exact ⟨t, List.mem_range.mpr (Nat.lt_succ_of_le ht), decide_eq_true hcost⟩
    simpa only [Option.isSome_map] using hsome

/-- The residual tolerance is less than one, so an accepted integer guess
cannot lie below an integral optimum. -/
theorem guess_tolerance_lt_one (I : Instance) (U : ℝ) (hsize : 2 ≤ (I.m : ℝ)*U) :
    Real.rpow (I.m*U) (-10) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (lt_of_lt_of_le (by norm_num) hsize) (by norm_num)

/-- For an integer optimal value `z`, a successful integer guess `F`
certifies `z ≤ F`. The certificate is the feasible returned flow. -/
theorem guessTest_integer_sound (I : Instance) (U κ : ℝ) (F z : ℤ)
    (step : StepSelector I U κ) (f₀ fstar g : Fin I.m → ℝ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hf : StrictlyInside I f₀) (hroute : I.Routes f₀)
    (hs : I.IsMinCostFlow fstar) (hz : I.cost fstar = z)
    (hκ : 0 < κ) (hκa : κ ≤ alpha I U/4)
    (hinit : 0 < residual I F f₀ →
      potential I (alpha I U) F f₀ ≤ 200*I.m*Real.log (I.m*U))
    (hout : guessTest I U F κ step f₀ = some g) : z ≤ F := by
  have h := guessTest_sound I U F κ step f₀ g hm hU hsize hnums hf hroute hκ hκa hinit hout
  have hopt := hs.2 g h.1
  rw [hz] at hopt
  have hgap : (z : ℝ) < F+1 := lt_of_le_of_lt (hopt.trans h.2)
    (add_lt_add_right (guess_tolerance_lt_one I U hsize) (F : ℝ))
  have hi : z < F+1 := by exact_mod_cast hgap
  exact Int.lt_add_one_iff.mp hi

end MinCostFlow.IPM
