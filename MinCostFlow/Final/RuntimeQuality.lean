module

public import MinCostFlow.IPM.Machine.SolverDataStructures
public import MinCostFlow.Num.IPM.BitLength
import Mathlib.Tactic

/-!
# Integer selection of the IPM quality exponent

The reciprocal quality in Theorem 5.1 (page 15) is subpolynomial.
The exponent is computed from two binary lengths and one shift on the
augmented edge count. The procedure uses the read-only solver quality
interface and counts both binary-length calls.
-/

@[expose] public section
namespace MinCostFlow.Final
open WordRAM IPM.Machine

/-- The integer exponent approximates the power of the logarithm by
rounding its binary exponent up. -/
def integerQualityExponent (A M : ℕ) : ℕ :=
  let b := (M.size+1).size
  128*(A+1)*b*2^((47*b+47)/48)

/-- Two binary length calls and a fixed number of word operations. -/
def integerQualityCost (M : ℕ) : ℕ :=
  14*(M.size+(M.size+1).size)+80

/-- The program takes a single augmented edge count. -/
def integerQualityBody (bitLength A : ℕ) : Stmt :=
  .call 1 bitLength [.reg 0] ;;
  .call 2 bitLength [.bin .add (.reg 1) (.const 1)] ;;
  .assign 3 (.bin .div (.bin .add (.bin .mul (.const 47) (.reg 2)) (.const 47)) (.const 48)) ;;
  .assign 4 (.bin .shiftLeft (.const 1) (.reg 3)) ;;
  .ret (.bin .mul (.bin .mul (.const (128*(A+1))) (.reg 2)) (.reg 4))

theorem integerQualityBody_noRand (bitLength A : ℕ) :
    (integerQualityBody bitLength A).NoRand := by
  simp [integerQualityBody, Stmt.NoRand]

/-- The read-only quality procedure returns the integer exponent and
has the advertised cost whenever the result fits a word. -/
theorem integerQuality_meetsContract {w entry bitLength A : ℕ} {p : Program}
    (hBody : p.procs[entry]? = some (integerQualityBody bitLength A))
    (hBits : MeetsContract w p bitLength Num.IPM.bitLengthContract) :
    MeetsContract w p entry (solverQualityContract w (integerQualityExponent A) integerQualityCost) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hWords hPre
  obtain ⟨M, rfl, hFit⟩ := hPre
  let b := (M.size+1).size
  let c := 128*(A+1)
  let i := (47*b+47)/48
  have hb : 0 < b := Nat.size_pos.mpr (by omega)
  have hc : 128 ≤ c := by unfold c; omega
  have hPower : 1 ≤ 2^i := Nat.one_le_two_pow
  change c*b*2^i<2^w at hFit
  have hCB : c*b < 2^w := (Nat.le_mul_of_pos_right _ hPower).trans_lt hFit
  have hcW : c < 2^w := (Nat.le_mul_of_pos_right _ hb).trans_lt hCB
  have hBig : 128 < 2^w := hc.trans_lt hcW
  have hw : 7 < w := by
    by_contra! h
    exact (not_le_of_gt hBig) (Nat.pow_le_pow_right (by decide) h)
  have hMW := hWords M (by simp)
  have hsW : M.size+1 < 2^w := by
    apply lt_of_le_of_lt (Nat.succ_le_succ (Nat.size_le.mpr hMW))
    have h₁ : w+1 ≤ 2^(w-1)+1 := by
      have h₂ := Nat.lt_two_pow_self (n := w-1)
      omega
    have h₃ : 2 ≤ 2^(w-1) := by
      exact Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega : 1 ≤ w-1)
    have hEq : w=(w-1)+1 := by omega
    rw [hEq, pow_succ]
    omega
  have h47 : 47 < 2^w := by omega
  have h48 : 48 < 2^w := by omega
  have hOne : 1 < 2^w := by omega
  have hn : 47*b+47 < 2^w := by
    have h₁ : 128*b ≤ c*b := Nat.mul_le_mul_right b hc
    omega
  have hn₀ : 47*b < 2^w := by omega
  have hShift : 1 <<< i < 2^w := by
    rw [Nat.shiftLeft_eq]
    simp only [Nat.one_mul]
    exact (Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) hb)).trans_lt hFit
  apply runs_start_le
  unfold integerQualityBody
  refine runs_seq_call_le hBits (vs := [M]) rfl hWords ⟨M,rfl⟩ ?_
  intro x mem' pos' hPost
  change mem'=mem ∧ x=M.size at hPost
  obtain ⟨rfl,rfl⟩ := hPost
  refine runs_seq_call_le hBits (vs := [M.size+1])
    (evalArgs_cons (Expr.eval_add rfl (Expr.eval_const hOne) hsW) rfl)
    (by intro v hv; simpa using (List.mem_singleton.mp hv ▸ hsW)) ⟨_,rfl⟩ ?_
  intro y mem'' pos'' hPost'
  change mem''=mem' ∧ y=b at hPost'
  obtain ⟨rfl,rfl⟩ := hPost'
  refine runs_seq_assign_le (v := i) (Expr.eval_div
    (Expr.eval_add (Expr.eval_mul (Expr.eval_const h47) rfl hn₀) (Expr.eval_const h47) hn)
    (Expr.eval_const h48) hn) ?_
  refine runs_seq_assign_le (v := 1 <<< i) (Expr.eval_shiftLeft (Expr.eval_const hOne) rfl hShift) ?_
  have hResult : c*b*(1 <<< i) = integerQualityExponent A M := by
    simp only [Nat.shiftLeft_eq, Nat.one_mul]
    rfl
  refine runs_ret_le (v := integerQualityExponent A M) ?_ ⟨rfl,rfl⟩ ?_
  · rw [← hResult]
    exact Expr.eval_mul (Expr.eval_mul (Expr.eval_const hcW) rfl hCB) rfl (hResult ▸ hFit)
  · simp only [solverQualityContract, integerQualityCost, Num.IPM.bitLengthContract,
      List.getD_cons_zero, argsSize_cons, argsSize_nil, Expr.size_bin, Expr.size_const, Expr.size_reg]
    change _ ≤ 14*(M.size+b)+80
    omega

end MinCostFlow.Final
