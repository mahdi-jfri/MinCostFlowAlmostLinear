module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry
import Mathlib.Tactic.Ring

/-!
# The shared capacity rounding power

Definition C.11 of Appendix C of Chen et al., arXiv:2203.00671v2,
uses `m^20` both in the rounding unit and in the clipping threshold.
Repeated squaring computes this power once, before scanning capacities.
All intermediate powers fit whenever `m^20` fits. The procedure changes
no memory and costs at most 40 steps.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Argument `[m]`, returning `m^20` by repeated squaring. -/
def capacityPowerBody : Stmt :=
  .assign 1 (.bin .mul (.reg 0) (.reg 0)) ;;
  .assign 2 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 3 (.bin .mul (.reg 2) (.reg 2)) ;;
  .assign 4 (.bin .mul (.reg 3) (.reg 3)) ;;
  .ret (.bin .mul (.reg 4) (.reg 2))

/-- The shared power occupies one procedure slot. -/
def capacityPowerModule : List Stmt := [capacityPowerBody]

/-- Only the final power must fit. The result leaves memory unchanged. -/
def capacityPowerContract (w m : ℕ) : Contract where
  pre args _ := args = [m] ∧ m ^ 20 < 2 ^ w
  post _ mem out mem' := mem' = mem ∧ out = m ^ 20
  cost _ _ := 40

/-- Computing the power uses no random instructions. -/
theorem capacityPowerBody_noRand : capacityPowerBody.NoRand := by
  simp only [capacityPowerBody, Stmt.NoRand, and_self]

private theorem small_power_le (m k : ℕ) (hk : k ≤ 20) (hpos : 0 < k) :
    m ^ k ≤ m ^ 20 := by
  by_cases hm : m = 0
  · subst m
    simp only [Nat.zero_pow hpos, Nat.zero_pow (by decide : 0 < 20)]
    exact le_rfl
  · exact Nat.pow_le_pow_right (by omega) hk

/-- The shared power is computed exactly in constant time, with every
intermediate product bounded by the final result. -/
theorem capacityPower_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b capacityPowerModule) (m : ℕ) :
    MeetsContract w p b (capacityPowerContract w m) := by
  have h2 : m * m = m ^ 2 := by ring
  have h4 : m ^ 2 * m ^ 2 = m ^ 4 := by ring
  have h8 : m ^ 4 * m ^ 4 = m ^ 8 := by ring
  have h16 : m ^ 8 * m ^ 8 = m ^ 16 := by ring
  have h20 : m ^ 16 * m ^ 4 = m ^ 20 := by ring
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨rfl, hbound⟩ := hpre
  have hm : m < 2 ^ w := hwords _ (List.mem_cons_self)
  have hm2 : m * m < 2 ^ w := by
    rw [h2]
    exact lt_of_le_of_lt (small_power_le m 2 (by decide) (by decide)) hbound
  have hm4 : (m * m) * (m * m) < 2 ^ w := by
    rw [h2, h4]
    exact lt_of_le_of_lt (small_power_le m 4 (by decide) (by decide)) hbound
  have hm8 : ((m * m) * (m * m)) * ((m * m) * (m * m)) < 2 ^ w := by
    rw [h2, h4, h8]
    exact lt_of_le_of_lt (small_power_le m 8 (by decide) (by decide)) hbound
  have hm16 : (((m * m) * (m * m)) * ((m * m) * (m * m))) *
      (((m * m) * (m * m)) * ((m * m) * (m * m))) < 2 ^ w := by
    rw [h2, h4, h8, h16]
    exact lt_of_le_of_lt (small_power_le m 16 (by decide) (by decide)) hbound
  have hm20 : ((((m * m) * (m * m)) * ((m * m) * (m * m))) *
      (((m * m) * (m * m)) * ((m * m) * (m * m)))) *
      ((m * m) * (m * m)) < 2 ^ w := by
    rw [h2, h4, h8, h16, h20]
    exact hbound
  apply runs_start_le
  unfold capacityPowerBody
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (by eval_expr) ?_ ?_
  · exact ⟨rfl, by rw [h2, h4, h8, h16, h20]; rfl⟩
  · simp only [capacityPowerContract, Expr.size_bin, Expr.size_reg]
    omega

/-- The argument and final-power bounds can hold together for every `m`. -/
theorem exists_capacityPower_pre (m : ℕ) :
    ∃ w, (∀ a ∈ [m], a < 2 ^ w) ∧
      (capacityPowerContract w m).pre [m] (fun _ => 0) := by
  let w := wordSize 1 [m + m ^ 20 + 2]
  have hlarge : m + m ^ 20 + 2 < 2 ^ w :=
    lt_two_pow_wordSize_of_mem (by decide) (List.mem_cons_self)
  refine ⟨w, ?_, rfl, by omega⟩
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  subst a
  omega

end MinCostFlow.Scaling.Machine
