module

public import MinCostFlow.IPM.Machine.InitialNumericBounds
public import MinCostFlow.IPM.Machine.InitialPositiveInput
public import MinCostFlow.IPM.Machine.PrecisionPolynomialBounds
import MinCostFlow.IPM.InitialSize
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds after the bounded solver's initialization

Positive capacities keep all original edges in Lemma 4.12. The common
penalty bound for original capacities at most `m^40` is `4m^81`, which
is also at most the same polynomial in the augmented edge count.
This connects the machine precision and hidden-parameter bounds to
the actual augmented instance used by the solver.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open Scaling

/-- Positive-capacity solver edges all survive augmentation. -/
theorem circulation_augmented_m_ge (J : Circulation) (K : ℤ)
    (hp : ∀ e,1 ≤ J.capacity e) : J.m ≤ (initialInstance J.toInstance K).m := by
  rw [initialInstance_m,freeEdges_circulation J hp,Finset.card_univ,Fintype.card_fin,
    Circulation.toInstance_m]
  omega

/-- The prescribed common bound simplifies to `4m^81` on the bounded
solver's `m^40` capacity scale. -/
theorem bounded_solver_penalty_eq (J : Circulation) :
    initialPenaltyWord J (J.m^40)=4*J.m^81 := by
  unfold initialPenaltyWord
  rw [← pow_mul]
  norm_num only [show 40*2=80 by decide]
  rw [show 81=80+1 by decide,pow_succ]
  ring

/-- The actual augmented edge count and common integer bound meet the
polynomial precision hypotheses simultaneously. -/
theorem bounded_solver_augmented_parameters (J : Circulation) (hm : 0 < J.m)
    (hp : ∀ e,1 ≤ J.capacity e) :
    let M := (initialInstance J.toInstance (initialPenaltyWord J (J.m^40):ℤ)).m
    let V := initialPenaltyWord J (J.m^40)
    0 < M ∧ 4 ≤ V ∧ V ≤ 4*M^81 := by
  dsimp only
  have hM := circulation_augmented_m_ge J (initialPenaltyWord J (J.m^40):ℤ) hp
  have hpow : 1 ≤ J.m^81 := Nat.one_le_pow _ _ hm
  have hmono := Nat.pow_le_pow_left hM 81
  refine ⟨hm.trans_le hM,?_,?_⟩
  · rw [bounded_solver_penalty_eq]
    omega
  · calc
      initialPenaltyWord J (J.m^40)=4*J.m^81 := bounded_solver_penalty_eq J
      _ ≤ _ := Nat.mul_le_mul_left 4 hmono

/-- The actual bounded-solver augmentation has the promised squared-log
hidden range, with an explicit constant. -/
theorem bounded_solver_hidden_parameter_bounds (J : Circulation) (hm : 0 < J.m)
    (hp : ∀ e,1 ≤ J.capacity e) :
    let I := initialInstance J.toInstance (initialPenaltyWord J (J.m^40):ℤ)
    let V := initialPenaltyWord J (J.m^40)
    precisionHiddenPsi I.m V ≤ 200000000000*(Real.log ((I.m:ℝ)+2))^2 ∧
      1/(6720000*Real.log ((I.m:ℝ)+2)) ≤ Num.IPM.alphaPrime I.m V/8 ∧
      Num.IPM.alphaPrime I.m V/8 ≤ 1/(8000*Real.log ((I.m:ℝ)+2)) := by
  dsimp only
  have hh := bounded_solver_augmented_parameters J hm hp
  dsimp only at hh
  have hprod := Nat.mul_le_mul hh.1 hh.2.1
  have hsize : 2 ≤ (initialInstance J.toInstance (initialPenaltyWord J (J.m^40):ℤ)).m*
      initialPenaltyWord J (J.m^40) := by omega
  exact ⟨precisionHiddenPsi_polynomial_input _ _ hh.1 (by omega) hsize hh.2.2,
    dyadic_hidden_parameter_bounds _ _ hh.1 hh.2.1 hh.2.2⟩

end MinCostFlow.IPM.Machine
