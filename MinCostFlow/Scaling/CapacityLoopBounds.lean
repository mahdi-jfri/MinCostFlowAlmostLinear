module

public import MinCostFlow.Scaling.CapacityLoopModel
import Mathlib.Tactic.Ring

/-!
# Explicit logarithmic bounds for the capacity loop

Appendix C of Chen et al., arXiv:2203.00671v2, uses a logarithmic bottleneck
search inside each halving iteration. This file combines the actual loop
budgets, including inputs of size one, with the proved model counters.
-/

@[expose] public section
namespace MinCostFlow.Scaling

/-- Doubling the graph size adds at most one ceiling binary logarithm. -/
theorem clog_double_add_one_le (m : ℕ) :
    Nat.clog 2 (m + m + 1) ≤ Nat.clog 2 (m + 1) + 1 := by
  have hp := Nat.le_pow_clog (by decide : 1 < 2) (m + 1)
  apply Nat.clog_le_of_le_pow
  rw [Nat.pow_succ]
  omega

/-- The capacity loop makes at most twenty-four times the product of the two
padded logarithmic factors many calls. -/
theorem capacityLoop_calls_le_logs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) :
    (capacityLoop solve I U).calls.length ≤
      24 * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
  have h := capacityLoop_calls solve I U
  have hb := clog_double_add_one_le I.m
  have ht : capacityRounds I.m U ≤
      12 * (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
    have hT := capacityRounds_le_twelve_logs I.m U
    omega
  have hs : Nat.clog 2 (I.m + I.m + 1) + 1 ≤ 2 * (Nat.clog 2 (I.m + 1) + 1) := by
    omega
  calc
    (capacityLoop solve I U).calls.length ≤
        capacityRounds I.m U * (Nat.clog 2 (I.m + I.m + 1) + 1) := h
    _ ≤ (12 * (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1)) *
        (2 * (Nat.clog 2 (I.m + 1) + 1)) := Nat.mul_le_mul ht hs
    _ = _ := by ring

private theorem step_budget_compressed (I : Circulation) (hm : 0 < I.m)
    (hn : I.n ≤ 2 * I.m) :
    CapacityState.workBudget I + 1 ≤ 16001 * I.m * (Nat.clog 2 (I.m + 1) + 1) := by
  have h := CapacityState.workBudget_le I
  have hb := clog_double_add_one_le I.m
  have hs : Nat.clog 2 (I.m + I.m + 1) + 1 ≤ 2 * (Nat.clog 2 (I.m + 1) + 1) := by omega
  have hn' : I.m + I.n + 1 ≤ 4 * I.m := by omega
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 2000 hs) hn'
  have hw : CapacityState.workBudget I ≤ 16000 * I.m * (Nat.clog 2 (I.m + 1) + 1) := by
    calc
      CapacityState.workBudget I ≤
          2000 * (Nat.clog 2 (I.m + I.m + 1) + 1) * (I.m + I.n + 1) := h
      _ ≤ (2000 * (2 * (Nat.clog 2 (I.m + 1) + 1))) * (4 * I.m) := hprod
      _ = _ := by ring
  have hp : 1 ≤ I.m * (Nat.clog 2 (I.m + 1) + 1) :=
    Nat.mul_pos hm (Nat.zero_lt_succ _)
  simp only [Nat.mul_assoc] at hw ⊢
  omega

/-- After vertex compression, the capacity loop's counter has the source's
`m log m log(mU)` form, with an explicit uniform coefficient. -/
theorem capacityLoop_work_le_logs (solve : (J : Circulation) → Fin J.m → ℤ)
    (I : Circulation) (U : ℕ) (hm : 0 < I.m) (hn : I.n ≤ 2 * I.m) :
    (capacityLoop solve I U).work ≤
      200000 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
  have h := capacityLoop_work solve I U
  have hs := step_budget_compressed I hm hn
  have ht : capacityRounds I.m U ≤
      12 * (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by
    have hT := capacityRounds_le_twelve_logs I.m U
    omega
  calc
    (capacityLoop solve I U).work ≤
        capacityRounds I.m U * (CapacityState.workBudget I + 1) := h
    _ ≤ (12 * (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1)) *
        (16001 * I.m * (Nat.clog 2 (I.m + 1) + 1)) := Nat.mul_le_mul ht hs
    _ = 192012 * I.m * (Nat.clog 2 (I.m + 1) + 1) *
        (Nat.clog 2 (I.m + 1) + Nat.clog 2 (U + 1) + 1) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (by decide : 192012 ≤ 200000)))

end MinCostFlow.Scaling
