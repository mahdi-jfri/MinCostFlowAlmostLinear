module

public import MinCostFlow.HierPaths.InitWriters
public import MinCostFlow.HierPaths.BoundsProgBlocks

/-!
# Computing the hierarchy schedule for the initial header

The schedule is computed from the input edge count. Three small loops find its two ceiling
logarithms and its ceiling cube root. The bounds on the stored walk length also bound the
intermediate numbers in these loops.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited

/-- The exponent of the power of two in the stored walk-length bound. -/
def lengthExponent (a m : ℕ) : ℕ := a * depthOf m * vxOf m * depthOf m

theorem vOf_eq_pow_lengthExponent (a m : ℕ) : vOf a m = 2 ^ lengthExponent a m := by
  rw [vOf, uOf, ← pow_mul, lengthExponent]

theorem schedule_input_cube_le_vOf (a m : ℕ) (ha : 1 ≤ a) :
    (xOf m + 2) ^ 3 ≤ vOf a m := by
  have hv : xOf m + 2 ≤ 2 ^ vxOf m := Nat.le_pow_clog (by decide) _
  have hp : 3 * vxOf m ≤ lengthExponent a m := by
    have hdepth := two_le_depthOf m
    have hprod : 3 ≤ a * depthOf m * depthOf m := by
      calc
        3 ≤ 1 * 2 * 2 := by decide
        _ ≤ a * depthOf m * depthOf m := Nat.mul_le_mul (Nat.mul_le_mul ha hdepth) hdepth
    simpa [lengthExponent, Nat.mul_right_comm] using Nat.mul_le_mul_right (vxOf m) hprod
  calc
    (xOf m + 2) ^ 3 ≤ (2 ^ vxOf m) ^ 3 := Nat.pow_le_pow_left hv _
    _ ≤ vOf a m := by
      rw [← pow_mul, vOf_eq_pow_lengthExponent, Nat.mul_comm (vxOf m) 3]
      exact Nat.pow_le_pow_right (by decide) hp

theorem schedule_cube_le_vOf (a m : ℕ) (ha : 1 ≤ a) : depthOf m ^ 3 ≤ vOf a m :=
  (Nat.pow_le_pow_left ((ceilRoot_le_self 2 (xOf m)).trans (Nat.le_add_right _ _)) 3).trans
    (schedule_input_cube_le_vOf a m ha)

/-- A ceiling division that avoids adding the numerator and denominator in a word. -/
theorem dOf_eq_div_pred (num den : ℕ) (hn : 0 < num) (hd : 0 < den) :
    dOf num den = (den - 1) / num + 1 := by
  have hnR : (0 : ℝ) < num := by exact_mod_cast hn
  have hdR : (0 : ℝ) < den := by exact_mod_cast hd
  rw [dOf, one_div_div, Nat.ceil_eq_iff (Nat.succ_ne_zero _)]
  constructor
  · apply (lt_div_iff₀ hnR).2
    exact_mod_cast (show (den - 1) / num * num < den by
      exact (Nat.div_mul_le_self _ _).trans_lt (by omega))
  · apply (div_le_iff₀ hnR).2
    exact_mod_cast (show den ≤ ((den - 1) / num + 1) * num by
      have h := (Nat.div_lt_iff_lt_mul hn).1 (Nat.lt_succ_self ((den - 1) / num))
      change den - 1 < ((den - 1) / num + 1) * num at h
      omega)

/-- Computing the ceiling logarithm after scaling by eight adds three to the result. -/
theorem xOf_eq_clog_add (m : ℕ) : xOf m = Nat.clog 2 (m + 1) + 3 := by
  have key (j : ℕ) (hj : 3 ≤ j) :
      8 * m + 8 ≤ 2 ^ j ↔ m + 1 ≤ 2 ^ (j - 3) := by
    rw [show 2 ^ j = 2 ^ (j - 3) * 8 by
      rw [← Nat.pow_add 2 (j - 3) 3, Nat.sub_add_cancel hj]]
    omega
  apply le_antisymm
  · rw [xOf, Nat.clog_le_iff_le_pow (by decide)]
    exact (key _ (by omega)).2 (by simp [Nat.le_pow_clog (by decide : 1 < 2)])
  · have hx := three_le_xOf m
    have hm : m + 1 ≤ 2 ^ (xOf m - 3) :=
      (key _ hx).1 (Nat.le_pow_clog (by decide) _)
    have := Nat.clog_le_of_le_pow hm
    omega

/-- Compute `x`, `h` and `v_x` in registers 5, 9 and 21. -/
def initSchedule : Stmt :=
  .assign 20 (.bin .add (.reg 10) (.const 1)) ;;
  clogBlock ;;
  .assign 5 (.bin .add (.reg 21) (.const 3)) ;;
  .assign 20 (.reg 5) ;;
  cbrtBlock ;;
  .assign 9 (.reg 21) ;;
  .assign 20 (.bin .add (.reg 5) (.const 2)) ;;
  clogBlock

theorem initSchedule_noRand : initSchedule.NoRand := by
  simp [initSchedule, clogBlock_noRand, cbrtBlock_noRand, Stmt.NoRand]

/-- The cost of the schedule loops, including the assignments between them. -/
def initScheduleCost (m : ℕ) : ℕ :=
  13 * xOf m + 13 * vxOf m + 19 * depthOf m + 120

theorem initSchedule_triple {w m : ℕ} {p : Program} (s : State) (hm : s.regs 10 = m)
    (hmPos : 1 ≤ m) (hmw : m + 1 < 2 ^ w) (hcube : depthOf m ^ 3 < 2 ^ w)
    (hx2w : xOf m + 2 < 2 ^ w) :
    Triple w p (fun st => st = s) initSchedule
      (normalPost fun t => t.regs 5 = xOf m ∧ t.regs 9 = depthOf m ∧ t.regs 21 = vxOf m ∧
        t.regs 0 = s.regs 0 ∧ t.mem = s.mem)
      (fun _ => initScheduleCost m) := by
  have h4 : 4 ≤ 2 ^ w := by
    have h8 := Nat.pow_le_pow_left (two_le_depthOf m) 3
    omega
  have hx := three_le_xOf m
  have hxle : xOf m ≤ depthOf m ^ 3 := le_ceilRoot_pow 2 _
  have hxw := hxle.trans_lt hcube
  intro st ω heq
  subst st
  refine runs_start_le ?_
  unfold initSchedule
  refine runs_seq_assign_le (v := m + 1) (Expr.eval_add
    (Expr.eval_reg_of_eq hm) (Expr.eval_const (by omega)) hmw) ?_
  refine runs_seq_triple_le (clogBlock_triple (n := m + 1) (by omega) hmw h4 _ (by simp))
    rfl ?_
  intro s₁ ⟨hx₁, hmem₁, _hpos, hframe₁⟩
  refine runs_seq_assign_le (v := xOf m) ?_ ?_
  · rw [xOf_eq_clog_add]
    exact Expr.eval_add (Expr.eval_reg_of_eq hx₁) (Expr.eval_const (by omega))
      (xOf_eq_clog_add m ▸ hxw)
  refine runs_seq_assign_le (v := xOf m) (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_triple_le (cbrtBlock_triple (n := xOf m) (by omega) hxw hcube h4 _ (by simp))
    rfl ?_
  intro s₂ ⟨hh₂, hmem₂, _hpos, hframe₂⟩
  change s₂.regs 21 = depthOf m at hh₂
  have hx₂ : s₂.regs 5 = xOf m := by
    rw [hframe₂ 5 (by decide) (by decide) (by decide) (by decide)]
    simp
  refine runs_seq_assign_le (v := depthOf m) (Expr.eval_reg_of_eq hh₂) ?_
  refine runs_seq_assign_le (v := xOf m + 2)
    (Expr.eval_add (Expr.eval_reg_of_eq (by simp [hx₂])) (Expr.eval_const (by omega)) hx2w) ?_
  refine runs_triple_le (clogBlock_triple (n := xOf m + 2) (by omega) hx2w h4 _ (by simp))
    rfl ?_ ?_
  · intro o s₃ hpost
    cases o with
    | returned => exact False.elim hpost
    | normal =>
      obtain ⟨hv, hmem₃, _hpos, hframe₃⟩ := hpost
      refine ⟨?_, ?_, hv, ?_, ?_⟩
      · rw [hframe₃ 5 (by decide) (by decide) (by decide)]
        simp [hx₂]
      · rw [hframe₃ 9 (by decide) (by decide) (by decide)]
        simp
      · rw [hframe₃ 0 (by decide) (by decide) (by decide)]
        simp only [Function.update_of_ne (by decide : 0 ≠ 20), Function.update_of_ne (by decide : 0 ≠ 9)]
        rw [hframe₂ 0 (by decide) (by decide) (by decide) (by decide)]
        simp only [Function.update_of_ne (by decide : 0 ≠ 20), Function.update_of_ne (by decide : 0 ≠ 5)]
        rw [hframe₁ 0 (by decide) (by decide) (by decide)]
        rfl
      · exact hmem₃.trans (hmem₂.trans hmem₁)
  · simp only [Expr.size, initScheduleCost]
    have ex : Nat.log 2 (m + 1 - 1) + 1 = Nat.clog 2 (m + 1) :=
      (clog_eq_log_pred (by omega)).symm
    have ev : Nat.log 2 (xOf m + 2 - 1) + 1 = vxOf m :=
      (clog_eq_log_pred (by omega)).symm
    change _ + (13 * (Nat.log 2 (xOf m + 2 - 1) + 1) + 20) ≤ _
    rw [ex, ev, show ceilRoot 2 (xOf m) = depthOf m from rfl]
    have hxEq := xOf_eq_clog_add m
    omega

end MinCostFlow.HierPaths

end
