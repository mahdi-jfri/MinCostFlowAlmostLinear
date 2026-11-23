module

public import MinCostFlow.IPM.EpochHiddenInputs
public import MinCostFlow.IPM.HiddenStability
public import MinCostFlow.IPM.EpochTolerances
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith

/-!
# Hidden stability of actual epoch inputs from numerical invariants

The adapted Lemma 9.2 of Chen et al., arXiv:2203.00671v2
(pages 70--71), now applies to the actual input sequence. Detect and the
movement bound prove the unchanged-edge condition. Lemma 9.1 proves
the gradient and length tolerances. The potential and residual bounds
prove the logarithmic width bounds. Finally the fixed gradient scaling
gives the `1/(8000 log(m+2))` hidden parameter of Theorem 4.6.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- All five hidden-stability conditions hold for the actual epoch input
prefix when its numerical invariants hold. None of the hidden witness,
its width stability, or its magnitude bounds is an input hypothesis.
This is the invariant-to-interface part of the epoch induction. -/
theorem epoch_hiddenStable_of_numerical (I : Instance) (U F κ r : ℝ) (A : MinRatioDataStructure)
    (base fstar : Fin I.m → ℝ) (T : ℕ)
    (hm : 0 < I.m) (hU : 1 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hs : I.IsFeasible fstar) (hF : I.cost fstar ≤ F)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (hstored : ∀ j ≤ T/2, StrictlyInside I (epochState I U κ r A base j).stored)
    (hcurrent : ∀ j ≤ T/2, StrictlyInside I (epochFlow I U κ r A base j))
    (hroute : ∀ j ≤ T/2, I.Routes (epochFlow I U κ r A base j))
    (hbefore : ∀ j ≤ T/2, Real.rpow (I.m*U) (-10) < residual I F (epochFlow I U κ r A base j))
    (hpot : ∀ j ≤ T/2, potential I (alpha I U) F (epochFlow I U κ r A base j) ≤
      200*I.m*Real.log (I.m*U))
    (hres : ∀ j ≤ T/2, ScalarApprox (1+8*ipmDetectThreshold I U κ) r
      (residual I F (epochFlow I U κ r A base j)))
    (hmove : ∀ j, 2*(j+1) ≤ T → weightedLength
      (lengths I (alpha I U) (epochState I U κ r A base j).stored)
      (fun e => epochIncrement I U κ r A base j e) ≤ ipmDetectThreshold I U κ) :
    (epochInstance I U κ r A base).HiddenStable T (normalizedIpmAlpha I) (ipmPsi I U) := by
  let D := epochInstance I U κ r A base
  let D₀ : DynamicInstance := {D with g := fun t => namedVector (gradientWithResidual I (alpha I U) r (epochRemembered I U κ r A base t))}
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have hd0 : 0 ≤ 8*ipmDetectThreshold I U κ := mul_nonneg (by norm_num) he.1.le
  have hbound : (κ*alpha I U/32)/16 ≤ alpha I U/2 := by
    have ha := alpha_pos I U hsize
    have hmul := mul_le_mul_of_nonneg_right hk' ha.le
    linarith only [hmul, ha]
  have hstage : ∀ t ≤ T,
      VectorApprox 2 (lengths I (alpha I U) (epochRemembered I U κ r A base t))
        (lengths I (alpha I U) (epochStageFlow I U κ r A base t)) ∧
      GradientTolerance (lengths I (alpha I U) (epochStageFlow I U κ r A base t))
        (fun e => (r/residual I F (epochStageFlow I U κ r A base t))*
          gradientWithResidual I (alpha I U) r (epochRemembered I U κ r A base t) e)
        (gradient I (alpha I U) F (epochStageFlow I U κ r A base t)) (alpha I U/2) := by
    intro t ht
    have herror := epoch_stage_error I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
      (ipmDetectThreshold I U κ) A base T hA hvalid he.1.le hmove t ht
    have hst : (t-1)/2 ≤ T/2 := by omega
    have hcur : t/2 ≤ T/2 := by omega
    have htol := epoch_stability_tolerances I U F κ r
      (epochRemembered I U κ r A base t) (epochStageFlow I U κ r A base t) hm
      (le_trans (by norm_num) hU) hsize hnums (hstored _ hst) hk hk'
      (by intro e; exact (herror e).trans (by linarith only [he.1])) (hres _ hcur)
    exact ⟨htol.1, fun e => (htol.2 e).trans hbound⟩
  have hh : D₀.HiddenStable T (alpha I U/8) (ipmPsi I U) := by
    apply lemma_9_2 I U F (8*ipmDetectThreshold I U κ) D₀ T fstar
      (epochStageFlow I U κ r A base)
      (fun t => gradientWithResidual I (alpha I U) r (epochRemembered I U κ r A base t))
      (fun t => lengths I (alpha I U) (epochRemembered I U κ r A base t)) (fun _ => r)
      hm hU hsize hnums hs hF hd0 (he.2.1.trans (by norm_num))
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    · intro t ht
      exact hcurrent _ (by omega)
    · intro t ht
      exact hroute _ (by omega)
    · intro t ht
      exact hbefore _ (by omega)
    · intro t ht
      exact hpot _ (by omega)
    · intro t ht
      exact hres _ (by omega)
    · intro t ht
      exact (hstage t ht).2
    · intro t ht
      exact (hstage t ht).1
    · intro t ht e s hst hnot
      have hc := epoch_notInserted_displacement I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
        (ipmDetectThreshold I U κ) A base T hA hvalid he.1.le hmove s t hst ht e hnot
      exact ⟨hc.1, hc.2.trans (by linarith only [he.2.1])⟩
  have hnormalized := hiddenStable_normalized I U D₀ T hsize hh
  have heq : scaleInstanceGradient D₀ (ipmGradientScale I U) = D := by
    dsimp only [scaleInstanceGradient, D₀, D, epochInstance]
    congr 1
    funext t e
    change ipmGradientScale I U*namedVector
        (gradientWithResidual I (alpha I U) r (epochRemembered I U κ r A base t)) e =
      namedVector (epochGradient I U r (epochRemembered I U κ r A base t)) e
    unfold namedVector epochGradient
    split_ifs
    · rfl
    · exact mul_zero _
  rw [heq] at hnormalized
  exact hnormalized

end MinCostFlow.IPM
