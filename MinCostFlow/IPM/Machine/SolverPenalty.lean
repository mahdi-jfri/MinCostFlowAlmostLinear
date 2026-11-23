module

public import MinCostFlow.IPM.Machine.InitialNumericBounds
import WordRAM.Tactic

/-!
# The penalty word for the bounded circulation solver

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31) uses penalty
`4mU²`. For a positive edge count the bounded solver can use
`U = max 2 (m^40)`. The machine computes this choice with a fixed
sequence of squarings and handles the one-edge case in the same sequence.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- A numerical bound that satisfies the initialization's lower limit. -/
def solverCapacityBound (m : ℕ) : ℕ := max 2 (m^40)

/-- Input `[m]`. The final comparison adds one exactly when `m = 1`. -/
def solverPenaltyBody : Stmt :=
  .assign 1 (.bin .mul (.reg 0) (.reg 0)) ;;
  .assign 1 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 1 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 2 (.bin .mul (.reg 1) (.reg 1)) ;;
  .assign 2 (.bin .mul (.reg 2) (.reg 2)) ;;
  .assign 2 (.bin .mul (.reg 1) (.reg 2)) ;;
  .assign 2 (.bin .add (.reg 2) (.bin .lt (.reg 0) (.const 2))) ;;
  .assign 2 (.bin .mul (.reg 2) (.reg 2)) ;;
  .assign 3 (.bin .mul (.const 4) (.reg 0)) ;;
  .ret (.bin .mul (.reg 3) (.reg 2))

/-- Constant-cost read-only computation of the exact penalty. -/
def solverPenaltyContract (w : ℕ) : Contract where
  pre args _ := ∃ m, args = [m] ∧ 0 < m ∧ 4*m*(solverCapacityBound m)^2 < 2^w
  post args mem v mem' := mem'=mem ∧ v=4*(args.getD 0 0)*(solverCapacityBound (args.getD 0 0))^2
  cost _ _ := 52

theorem solverPenaltyBody_noRand : solverPenaltyBody.NoRand := by
  simp [solverPenaltyBody,Stmt.NoRand]

/-- Repeated squaring computes the source penalty with no wrapped products. -/
theorem solverPenalty_meetsContract {w entry : ℕ} {p : Program}
    (hbody : p.procs[entry]? = some solverPenaltyBody) :
    MeetsContract w p entry (solverPenaltyContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hWords hPre
  obtain ⟨m,rfl,hm,hFit⟩ := hPre
  let U := solverCapacityBound m
  have hU : 2 ≤ U := le_max_left _ _
  have hm1 : 1 ≤ m := hm
  have hU1 : 1 ≤ U := by omega
  have hU2 : U ≤ U^2 := by simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left U hU1
  have hP₁ : U^2 ≤ 4*m*U^2 := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (U^2) (show 1 ≤ 4*m by omega)
  have hP₂ : 4*m ≤ 4*m*U^2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (4*m) (Nat.one_le_pow 2 U hU1)
  have hFitPow (i : ℕ) (hi : i ≤ 40) : m^i < 2^w :=
    ((Nat.pow_le_pow_right hm hi).trans (le_max_right 2 (m^40))).trans_lt
      (hU2.trans_lt (hP₁.trans_lt hFit))
  have hTwo : 2 < 2^w := by have := hP₂.trans_lt hFit; omega
  have hFour : 4 < 2^w := by have := hP₂.trans_lt hFit; omega
  have hUfit := hU2.trans_lt (hP₁.trans_lt hFit)
  have hAdj : m^40 + (if m < 2 then 1 else 0) = U := by
    by_cases h : m < 2
    · have he : m = 1 := by omega
      subst m
      decide
    · have hh : 2 ≤ m^40 := (show 2 ≤ m by omega).trans (by
        simpa only [pow_one] using Nat.pow_le_pow_right hm (show 1 ≤ 40 by decide))
      simp only [U,solverCapacityBound,ite_eq_right h,Nat.add_zero,max_eq_right hh]
  have hCmp (st : State) (hreg : st.regs 0 = m) :
      Expr.eval w st (.bin .lt (.reg 0) (.const 2)) = some (if m < 2 then 1 else 0) := by
    have hRead : Expr.eval w st (.reg 0) = some m := congrArg some hreg
    by_cases h : m < 2
    · simpa only [ite_eq_left h] using Expr.eval_lt_true hRead (Expr.eval_const hTwo) h (by omega)
    · simpa only [ite_eq_right h] using Expr.eval_lt_false hRead (Expr.eval_const hTwo) (Nat.le_of_not_gt h) (by omega)
  apply runs_start_le
  unfold solverPenaltyBody
  refine runs_seq_assign_le (v := m^2) (by
    have hf : m^1 * m^1 < 2^w := by rw [←pow_add]; exact hFitPow 2 (by decide)
    have he : m^1 * m^1 = m^2 := (pow_add m 1 1).symm
    exact (congrArg some he) ▸ Expr.eval_mul (by simp [pow_one,Expr.eval,startState]) (by simp [pow_one,Expr.eval,startState]) hf) ?_
  refine runs_seq_assign_le (v := m^4) (by
    have hf : m^2 * m^2 < 2^w := by rw [←pow_add]; exact hFitPow 4 (by decide)
    have he : m^2 * m^2 = m^4 := (pow_add m 2 2).symm
    exact (congrArg some he) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := m^8) (by
    have hf : m^4 * m^4 < 2^w := by rw [←pow_add]; exact hFitPow 8 (by decide)
    have he : m^4 * m^4 = m^8 := (pow_add m 4 4).symm
    exact (congrArg some he) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := m^16) (by
    have hf : m^8 * m^8 < 2^w := by rw [←pow_add]; exact hFitPow 16 (by decide)
    have he : m^8 * m^8 = m^16 := (pow_add m 8 8).symm
    exact (congrArg some he) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := m^32) (by
    have hf : m^16 * m^16 < 2^w := by rw [←pow_add]; exact hFitPow 32 (by decide)
    have he : m^16 * m^16 = m^32 := (pow_add m 16 16).symm
    exact (congrArg some he) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := m^40) (by
    have hf : m^8 * m^32 < 2^w := by rw [←pow_add]; exact hFitPow 40 (by decide)
    have he : m^8 * m^32 = m^40 := (pow_add m 8 32).symm
    exact (congrArg some he) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := U) (by
    have hf : m^40 + (if m < 2 then 1 else 0) < 2^w := hAdj ▸ hUfit
    exact (congrArg some hAdj) ▸ Expr.eval_add rfl (hCmp _ rfl) hf) ?_
  refine runs_seq_assign_le (v := U^2) (by
    have hf : U * U < 2^w := by simpa only [←pow_two] using hP₁.trans_lt hFit
    exact (congrArg some (pow_two U).symm) ▸ Expr.eval_mul rfl rfl hf) ?_
  refine runs_seq_assign_le (v := 4*m) (Expr.eval_mul (Expr.eval_const hFour) rfl (hP₂.trans_lt hFit)) ?_
  exact runs_ret_le (Expr.eval_mul rfl rfl hFit) ⟨rfl,rfl⟩ (by change 51 ≤ 52; decide)

end MinCostFlow.IPM.Machine
