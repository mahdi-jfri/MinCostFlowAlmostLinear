module

public import MinCostFlow.Scaling.CostMeasuredPrefixBounds
public import MinCostFlow.Scaling.CostStepSpace
import Mathlib.Tactic.Ring

/-!
# Polynomial bounds on reached cost-state numbers

The explicit round count is logarithmic in the cost bound and vertex
count. Its denominator power is therefore at most eight times their
padded product. The common cost-round numerical base absorbs this into
power three. Combining that bound with the geometric potential invariant
gives power six for every reached potential numerator.
-/

public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

private theorem two_pow_clog_le (x : ℕ) (hx : 1≤x) : 2^Nat.clog 2 x≤2*x := by
  by_cases he : x=1
  · subst x
    simp only [Nat.clog_one_right,Nat.pow_zero,Nat.mul_one]
    decide
  · have hx2 : 1<x := by omega
    have hcpos := Nat.clog_pos (by decide : 1<2) hx2
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1<2) hx2
    have heq : Nat.clog 2 x=(Nat.clog 2 x).pred+1 := (Nat.succ_pred_eq_of_pos hcpos).symm
    rw [heq,pow_succ]
    exact (Nat.mul_le_mul_right 2 hp.le).trans_eq (Nat.mul_comm x 2)

/-- The cost loop's full denominator power is polynomial in the two
numbers whose logarithms determine its explicit round count. -/
theorem costRounds_two_pow_le (n C : ℕ) : 2^costRounds n C≤8*(C+1)*(n+1) := by
  have hC := two_pow_clog_le (C+1) (by omega)
  have hn := two_pow_clog_le (n+1) (by omega)
  calc
    _ = 2*(2^Nat.clog 2 (C+1)*2^Nat.clog 2 (n+1)) := by
      simp only [costRounds,pow_add,pow_one]
      ring
    _ ≤ 2*((2*(C+1))*(2*(n+1))) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul hC hn)
    _ = _ := by ring

/-- The common cost-round base bounds the full denominator power by its
cube, also when the cost or vertex count is zero. -/
theorem costRounds_power_le_base (J : Circulation) (C U : ℕ) :
    2^costRounds J.n C≤(costStepNumberBase J C U)^3 := by
  let D := costStepNumberBase J C U
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hC : C+1≤D := by omega
  have hn : J.n+1≤D := by omega
  have hD8 : 8≤D := by omega
  calc
    _ ≤ 8*(C+1)*(J.n+1) := costRounds_two_pow_le J.n C
    _ ≤ 8*D^2 := by
      have h := Nat.mul_le_mul_left 8 (Nat.mul_le_mul hC hn)
      simpa only [pow_two,Nat.mul_assoc] using h
    _ ≤ D^3 := (Nat.mul_le_mul_right (D^2) hD8).trans_eq (pow_succ' D 2).symm

/-- Every power in an executed measured prefix fits the common cubic
bound when its index does not exceed the prescribed cost-round count. -/
theorem costMeasuredPrefix_power_le
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C U t : ℕ)
    (ht : t≤costRounds J.n C) :
    (CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.power≤
      (costStepNumberBase J C U)^3 := by
  rw [costMeasuredPrefix_power]
  exact (Nat.pow_le_pow_right (by decide : 0<2) ht).trans (costRounds_power_le_base J C U)

/-- Every reached potential numerator is bounded by power six of the same
numerical base, independently of which exact inner optimum is chosen. -/
theorem costMeasuredPrefix_potential_le
    (inner : (K : Circulation) → CallResult (Fin K.m → ℤ)) (J : Circulation) (C U t : ℕ)
    (ht : t≤costRounds J.n C) :
    ∀ v,((CallResult.forRounds (CostState.stepMeasured inner C) t (CostState.initial J)).value.potential v).natAbs≤
      (costStepNumberBase J C U)^6 := by
  let D := costStepNumberBase J C U
  let Q := (4*J.m+J.n)*(J.m+J.m)^10
  have hD : J.n+4*J.m+(J.m+J.m)^10+C+U+8=D := rfl
  have hD8 : 8≤D := by omega
  have hQ : Q≤D^2 := by
    have h := Nat.mul_le_mul (show 4*J.m+J.n≤D by omega) (show (J.m+J.m)^10≤D by omega)
    simpa only [pow_two] using h
  have hpow : 2^(t+1)≤2*D^3 := by
    calc
      _ = 2*2^t := pow_succ' 2 t
      _ ≤ 2*(2^costRounds J.n C) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) ht)
      _ ≤ _ := Nat.mul_le_mul_left 2 (costRounds_power_le_base J C U)
  have hprod : 2^(t+1)*Q≤2*D^5 := by
    have h := Nat.mul_le_mul hpow hQ
    simpa only [Nat.mul_assoc,←pow_add] using h
  have hlast : 2*D^5≤D^6 :=
    (Nat.mul_le_mul_right (D^5) (show 2≤D by omega)).trans_eq (pow_succ' D 5).symm
  have hprefix := costMeasuredPrefix_potential inner J C t
  intro v
  exact (Nat.le_add_right _ (2*Q)).trans ((hprefix v).trans (hprod.trans hlast))

end MinCostFlow.Scaling.Machine
