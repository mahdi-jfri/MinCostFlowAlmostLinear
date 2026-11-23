module

public import MinCostFlow.Scaling.AugmentationResidual
public import MinCostFlow.Scaling.EpsilonOptimal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The cost-perturbation step in a scaling round

Lemma C.7 of Chen et al., arXiv:2203.00671v2, Appendix C, uses the rounding
error and complementary slackness to bound every new residual reduced cost.
The result below isolates that argument for any rounded arc costs. Both
residual directions are considered, so simultaneous forward and reverse
augmentation does not create a missing case. The integer rounding model
must supply its error bound and its computed dual's slackness inequalities.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Circulation

/-- The perturbation argument in Lemma C.7: bounded rounding error and the
rounded optimum's residual signs give epsilon optimality after augmentation.
The hypotheses are explicit numerical inequalities, not a solver contract. -/
theorem epsilonOptimalWith_augment_of_rounded_signs
    (I : Circulation) (f : Fin I.m → ℤ) (hf : I.Feasible (fun e => (f e : ℝ)))
    (g : Fin (I.m + I.m) → ℝ) (hg : (I.residual f).Feasible g)
    (y dy : Fin I.n → ℝ) (rounded : Fin (I.m + I.m) → ℝ)
    (err epsilon : ℝ) (heps : 0 < epsilon) (herr : err < epsilon)
    (herror : ∀ a, 0 < (I.residual f).capacity a →
      -err ≤ (I.residual f).reducedCost y a - rounded a ∧
        (0 < g a → (I.residual f).reducedCost y a - rounded a ≤ err))
    (hsigns : ∀ a,
      (g a < (I.residual f).capacity a →
        0 ≤ rounded a - (I.residual f).potentialDifference dy a) ∧
      (0 < g a → rounded a - (I.residual f).potentialDifference dy a ≤ 0)) :
    I.EpsilonOptimalWith (I.augment f g) epsilon (fun v => y v + dy v) := by
  refine ⟨heps, I.augment_feasible f hf g hg, ?_⟩
  intro e
  have hforward : (I.residual f).reducedCost y (Fin.castAdd I.m e) -
      (I.residual f).potentialDifference dy (Fin.castAdd I.m e) =
      I.reducedCost (fun v => y v + dy v) e := by
    simp only [reducedCost, potentialDifference, Fin.addCases_left]
    ring
  have hreverse : (I.residual f).reducedCost y (Fin.natAdd I.m e) -
      (I.residual f).potentialDifference dy (Fin.natAdd I.m e) =
      -I.reducedCost (fun v => y v + dy v) e := by
    simp only [reducedCost, potentialDifference, Fin.addCases_right, Int.cast_neg]
    ring
  constructor
  · intro ha
    rcases I.augment_forward_alternatives f hf g hg e ha with h | h
    · have he := (herror _ h.2).1
      have hs := (hsigns _).1 h.1
      linarith only [he, hs, herr, hforward]
    · have he := (herror _ h.2).2 h.1
      have hs := (hsigns _).2 h.1
      linarith only [he, hs, herr, hreverse]
  · intro ha
    rcases I.augment_reverse_alternatives f hf g hg e ha with h | h
    · have he := (herror _ h.2).1
      have hs := (hsigns _).1 h.1
      linarith only [he, hs, herr, hreverse]
    · have he := (herror _ h.2).2 h.1
      have hs := (hsigns _).2 h.1
      linarith only [he, hs, herr, hforward]

end MinCostFlow.Scaling.Circulation
