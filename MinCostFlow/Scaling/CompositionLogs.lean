module

public import MinCostFlow.Scaling.IterationBounds
import Mathlib.Tactic.Ring

/-!
# Logarithms for composing the two scaling loops

Appendix C of Chen et al., arXiv:2203.00671v2, composes reductions whose
intermediate graphs grow by a constant factor. These elementary bounds keep
that growth explicit, including graphs with one edge and zero input bounds.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Multiplying an argument by `2^k` adds at most `k` to its binary ceiling logarithm. -/
theorem clog_two_le_of_le_pow_mul (x y k : ℕ) (h : x ≤ 2 ^ k * y) :
    Nat.clog 2 x ≤ k + Nat.clog 2 y := by
  apply Nat.clog_le_of_le_pow
  calc
    x ≤ 2 ^ k * y := h
    _ ≤ 2 ^ k * 2 ^ Nat.clog 2 y :=
      Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) y)
    _ = 2 ^ (k + Nat.clog 2 y) := (Nat.pow_add _ _ _).symm

/-- The edge growth by twelve adds at most four binary logarithms. -/
theorem composition_edge_log (m j : ℕ) (h : j ≤ 12 * m) :
    Nat.clog 2 (j + 1) ≤ Nat.clog 2 (m + 1) + 4 := by
  have hb : j + 1 ≤ 2 ^ 4 * (m + 1) := by omega
  have hh := clog_two_le_of_le_pow_mul (j + 1) (m + 1) 4 hb
  omega

/-- The capacity increase for shortest-path extraction contributes only the
input edge and capacity logarithms. -/
theorem composition_capacity_log (m U : ℕ) :
    Nat.clog 2 (max U (2 * m + 1) + 1) ≤
      1 + Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1) := by
  apply Nat.clog_le_of_le_pow
  have hm := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
  have hU := Nat.le_pow_clog (by decide : 1 < 2) (U + 1)
  have hprod := Nat.mul_le_mul hm hU
  have ha : U + 1 ≤ 2 * ((m + 1) * (U + 1)) := by
    have h := Nat.mul_le_mul_right (U + 1) (show 1 ≤ m + 1 by omega)
    omega
  have hb : 2 * m + 1 + 1 ≤ 2 * ((m + 1) * (U + 1)) := by
    have h := Nat.mul_le_mul_left (m + 1) (show 1 ≤ U + 1 by omega)
    omega
  have hh : max U (2 * m + 1) + 1 ≤ 2 * ((m + 1) * (U + 1)) := by omega
  calc
    max U (2 * m + 1) + 1 ≤ 2 * ((m + 1) * (U + 1)) := hh
    _ ≤ 2 * (2 ^ Nat.clog 2 (m + 1) * 2 ^ Nat.clog 2 (U + 1)) :=
      Nat.mul_le_mul_left 2 hprod
    _ = 2 ^ (1 + Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1)) := by
      rw [Nat.pow_add, Nat.pow_add]
      ring

end MinCostFlow.Scaling
