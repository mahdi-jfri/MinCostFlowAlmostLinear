module

public import MinCostFlow.Num.SignedPair
public import MinCostFlow.Statement.Problem
import Mathlib.Tactic.NormNum

/-!
# Signed addition in the statement's two-word representation

Subtracting lower-capacity contributions in Appendix C uses integral addition.
When two input signs agree, their magnitudes add. Otherwise the larger
magnitude determines the sign, and equal magnitudes give canonical zero.
These identities justify the branches of the one-word-magnitude addition
procedure, including exact cancellation and negative inputs.
-/

public section
namespace MinCostFlow.Scaling.Machine

/-- Equal input signs add magnitudes without changing the sign. -/
theorem encodeInt_add_same_sign (x y : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) = if y < 0 then 1 else 0) :
    encodeSignedPair (x + y) = [if x < 0 then 1 else 0, x.natAbs + y.natAbs] := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · have hs : x + y < 0 := by omega
    have ha : (x + y).natAbs = x.natAbs + y.natAbs := by omega
    simp only [encodeSignedPair, hx, hs, ↓reduceIte, ha]
  · simp only [hx, hy, ↓reduceIte] at h
    cases h
  · simp only [hx, hy, ↓reduceIte] at h
    cases h
  · have hs : ¬x + y < 0 := by omega
    have ha : (x + y).natAbs = x.natAbs + y.natAbs := by omega
    simp only [encodeSignedPair, hx, hs, ↓reduceIte, ha]

/-- With opposite signs and a larger second magnitude, the second sign wins. -/
theorem encodeInt_add_second_larger (x y : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) ≠ if y < 0 then 1 else 0)
    (hl : x.natAbs < y.natAbs) :
    encodeSignedPair (x + y) = [if y < 0 then 1 else 0, y.natAbs - x.natAbs] := by
  by_cases hx : x < 0 <;> by_cases hy : y < 0
  · exact False.elim (h (by simp only [hx, hy, ↓reduceIte]))
  · have hs : ¬x + y < 0 := by omega
    have ha : (x + y).natAbs = y.natAbs - x.natAbs := by omega
    simp only [encodeSignedPair, hy, hs, ↓reduceIte, ha]
  · have hs : x + y < 0 := by omega
    have ha : (x + y).natAbs = y.natAbs - x.natAbs := by omega
    simp only [encodeSignedPair, hy, hs, ↓reduceIte, ha]
  · exact False.elim (h (by simp only [hx, hy, ↓reduceIte]))

/-- Opposite signs with equal magnitudes cancel to the canonical zero pair. -/
theorem encodeInt_add_cancel (x y : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) ≠ if y < 0 then 1 else 0)
    (he : x.natAbs = y.natAbs) : encodeSignedPair (x + y) = [0, 0] := by
  have hs : x + y = 0 := by
    by_cases hx : x < 0 <;> by_cases hy : y < 0
    · exact False.elim (h (by simp only [hx, hy, ↓reduceIte]))
    · omega
    · omega
    · exact False.elim (h (by simp only [hx, hy, ↓reduceIte]))
  rw [hs]
  rfl

/-- With opposite signs and a larger first magnitude, the first sign wins. -/
theorem encodeInt_add_first_larger (x y : ℤ)
    (h : (if x < 0 then 1 else 0 : ℕ) ≠ if y < 0 then 1 else 0)
    (hl : y.natAbs < x.natAbs) :
    encodeSignedPair (x + y) = [if x < 0 then 1 else 0, x.natAbs - y.natAbs] := by
  rw [add_comm]
  exact encodeInt_add_second_larger y x (Ne.symm h) hl

end MinCostFlow.Scaling.Machine
