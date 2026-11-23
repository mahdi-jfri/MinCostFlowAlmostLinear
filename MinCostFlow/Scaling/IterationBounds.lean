module

public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Ring

/-!
# Explicit iteration budgets for Appendix C

Chen et al., arXiv:2203.00671v2, Appendix C, uses halving in cost scaling and
in closing the integral capacity-scaling gap. The natural-number budgets here
make the strict stopping inequalities explicit. Ceiling binary logarithms
include an added one in their arguments, so the budgets also cover small inputs.
These are budgets for the loops, not running-time claims about a machine.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Cost scaling needs to make `(C+1)/2^T` smaller than `1/(n+1)`.
The extra one repairs the strict initialization in Definition C.4. -/
def costRounds (n C : ℕ) : ℕ := 1 + Nat.clog 2 (C + 1) + Nat.clog 2 (n + 1)

/-- Capacity scaling starts with an integral gap of at most `m^11*U`.
This budget makes the remaining halved gap strictly smaller than one half. -/
def capacityRounds (m U : ℕ) : ℕ :=
  1 + 11 * Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1)

/-- The cost-scaling denominator exceeds the product in its stopping test. -/
theorem costRounds_stopping (n C : ℕ) : (C + 1) * (n + 1) < 2 ^ costRounds n C := by
  have hC := Nat.le_pow_clog (by decide : 1 < 2) (C + 1)
  have hn := Nat.le_pow_clog (by decide : 1 < 2) (n + 1)
  have hm := Nat.mul_le_mul hC hn
  have hp : 0 < 2 ^ (Nat.clog 2 (C + 1) + Nat.clog 2 (n + 1)) := Nat.pow_pos (by decide)
  rw [← Nat.pow_add] at hm
  have he : 2 ^ costRounds n C =
      2 * 2 ^ (Nat.clog 2 (C + 1) + Nat.clog 2 (n + 1)) := by
    simp only [costRounds, Nat.add_assoc, Nat.pow_add, Nat.pow_one]
  rw [he]
  omega

/-- The capacity-scaling denominator exceeds twice the initial objective gap. -/
theorem capacityRounds_stopping (m U : ℕ) :
    2 * m ^ 11 * U < 2 ^ capacityRounds m U := by
  have hm := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
  have hU := Nat.le_pow_clog (by decide : 1 < 2) (U + 1)
  have hm' : m ^ 11 ≤ (2 ^ Nat.clog 2 (m + 1)) ^ 11 :=
    Nat.pow_le_pow_left (le_trans (Nat.le_succ m) hm) 11
  have hp : 0 < (2 ^ Nat.clog 2 (m + 1)) ^ 11 := Nat.pow_pos (Nat.pow_pos (by decide))
  have hlt : m ^ 11 * U < (2 ^ Nat.clog 2 (m + 1)) ^ 11 *
      2 ^ Nat.clog 2 (U + 1) := by
    calc
      m ^ 11 * U ≤ (2 ^ Nat.clog 2 (m + 1)) ^ 11 * U := Nat.mul_le_mul_right U hm'
      _ < (2 ^ Nat.clog 2 (m + 1)) ^ 11 * 2 ^ Nat.clog 2 (U + 1) :=
        Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (Nat.lt_succ_self U) hU) hp
  have he : 2 ^ capacityRounds m U =
      2 * ((2 ^ Nat.clog 2 (m + 1)) ^ 11 * 2 ^ Nat.clog 2 (U + 1)) := by
    simp only [capacityRounds, Nat.pow_add, Nat.pow_one]
    rw [Nat.mul_comm 11, Nat.pow_mul]
    ring
  rw [he, Nat.mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left hlt (by decide)

/-- In the nontrivial cost-scaling branch, `n <= 2*C` gives a budget of at most
four ceiling binary logarithms of `C+1`. Small-cost instances can use the
bounded solver directly, so they do not need a cost-scaling loop. -/
theorem costRounds_le_four_log (n C : ℕ) (hC : 0 < C) (hn : n ≤ 2 * C) :
    costRounds n C ≤ 4 * Nat.clog 2 (C + 1) := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (C + 1)
  have hnp : n + 1 ≤ 2 ^ (1 + Nat.clog 2 (C + 1)) := by
    rw [Nat.pow_add, Nat.pow_one]
    omega
  have hnl := Nat.clog_le_of_le_pow hnp
  have hl : 1 ≤ Nat.clog 2 (C + 1) := by
    by_contra h
    have he : Nat.clog 2 (C + 1) = 0 := by omega
    rw [he, Nat.pow_zero] at hp
    omega
  unfold costRounds
  omega

/-- A uniform padded-log bound for capacity scaling, including `m=U=1`. -/
theorem capacityRounds_le_twelve_logs (m U : ℕ) :
    capacityRounds m U ≤ 12 * (1 + Nat.clog 2 (m + 1) + Nat.clog 2 (U + 1)) := by
  unfold capacityRounds
  omega

end MinCostFlow.Scaling
