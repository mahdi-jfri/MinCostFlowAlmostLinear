module

public import MinCostFlow.Scaling.CostLoopModel

/-!
# Integer rounding error

Definition C.6 of Chen et al., arXiv:2203.00671v2, Appendix C, rounds reduced
costs to a known integral unit. The implementation uses integer division and
ties away from zero. Its error is strictly less than one unit, the bound
used in the proof of Lemma C.7. Negating the numerator negates the result.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Rounding preserves odd symmetry, including the tie convention. -/
theorem nearestQuotient_neg (z : ℤ) (d : ℕ) :
    nearestQuotient (-z) d = -nearestQuotient z d := by
  unfold nearestQuotient
  simp only [Int.natAbs_neg]
  by_cases hz : z = 0
  · subst z
    have hzero : (d / 2) / d = 0 := by
      by_cases hd : d = 0
      · subst d; rfl
      · exact Nat.div_eq_of_lt (Nat.div_lt_self (Nat.pos_of_ne_zero hd) (by decide))
    simp only [Int.natAbs_zero, Nat.zero_add, hzero, Nat.cast_zero, neg_zero]
    simp
  · split <;> split <;> omega

private theorem rounded_natural_error (n d : ℕ) (hd : 0 < d) :
    -((d : ℕ) : ℤ) < (n : ℤ) - (d : ℤ) * (((n + d / 2) / d : ℕ) : ℤ) ∧
    (n : ℤ) - (d : ℤ) * (((n + d / 2) / d : ℕ) : ℤ) < d := by
  have hr := Nat.mod_lt (n + d / 2) hd
  have he := Nat.mod_add_div (n + d / 2) d
  have hh : d / 2 < d := Nat.div_lt_self hd (by decide)
  have he' : ((n + d / 2) % d : ℤ) + (d : ℤ) * (((n + d / 2) / d : ℕ) : ℤ) =
      (n : ℤ) + (d / 2 : ℕ) := by exact_mod_cast he
  omega

/-- The integer rounding error is strictly smaller than the positive denominator. -/
theorem nearestQuotient_error (z : ℤ) (d : ℕ) (hd : 0 < d) :
    -(d : ℤ) < z - (d : ℤ) * nearestQuotient z d ∧
      z - (d : ℤ) * nearestQuotient z d < d := by
  have hh := rounded_natural_error z.natAbs d hd
  by_cases hz : z < 0
  · rw [nearestQuotient, ite_eq_left hz]
    have he : (z.natAbs : ℤ) = -z := by rw [Int.natCast_natAbs, abs_of_neg hz]
    rw [he] at hh
    rw [mul_neg]
    omega
  · rw [nearestQuotient, ite_eq_right hz]
    have he : (z.natAbs : ℤ) = z := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ z)]
    rw [he] at hh
    exact hh

end MinCostFlow.Scaling
