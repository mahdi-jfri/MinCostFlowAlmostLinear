module

public import MinCostFlow.IPM.Machine.IterationBudget
public import WordRAM.Logic
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Computing the integer target-test iteration budget

Use word arithmetic and one binary shift to compute the conservative
budget. A bound on the final result bounds every intermediate value, so
the procedure performs no truncated arithmetic. It does not allocate or
change memory and uses no real-logarithm operation.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,binaryLengthBound,qualityExponent,alphaExponent]`. -/
def iterationBudgetBody : Stmt :=
  .assign 4 (.bin .add (.reg 2) (.reg 3)) ;;
  .assign 5 (.bin .add (.reg 4) (.const 5)) ;;
  .assign 6 (.bin .mul (.const 2) (.reg 5)) ;;
  .assign 7 (.bin .shiftLeft (.const 1) (.reg 6)) ;;
  .assign 8 (.bin .mul (.reg 0) (.reg 1)) ;;
  .assign 9 (.bin .mul (.const 800000) (.reg 8)) ;;
  .ret (.bin .mul (.reg 9) (.reg 7))

/-- One constant-cost integer budget entry. -/
def iterationBudgetModule : List Stmt := [iterationBudgetBody]

/-- Positive dimensions and a fitting final budget suffice for every
intermediate word. The returned number is exact and memory is unchanged. -/
def iterationBudgetContract (w : ℕ) : Contract where
  pre args _ := ∃ m bits k j,args=[m,bits,k,j] ∧ 0<m ∧ 0<bits ∧
    dyadicIterationBudget m bits k j<2^w
  post args mem v mem' := mem'=mem ∧
    v=dyadicIterationBudget (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) (args.getD 3 0)
  cost _ _ := 100

/-- Budget computation contains no random statement. -/
theorem iterationBudget_noRand : iterationBudgetBody.NoRand := by
  simp [iterationBudgetBody,Stmt.NoRand]

/-- The machine computes the full dyadic budget in at most one hundred
operations, without changing memory or truncating any intermediate. -/
theorem iterationBudget_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b iterationBudgetModule) : MeetsContract w p b (iterationBudgetContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨m,bits,k,j,rfl,hm,hbits,hbound⟩ := hpre
  let C := 800000*m*bits
  let E := 2*(k+j+5)
  have hC : 0<C := Nat.mul_pos (Nat.mul_pos (by decide) hm) hbits
  have hpow : 0<2^E := by positivity
  have hpowN : 2^E≤dyadicIterationBudget m bits k j := by
    change 2^E≤C*2^E
    calc
      2^E=1*2^E := (one_mul _).symm
      _≤C*2^E := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hC)
  have hCN : C≤dyadicIterationBudget m bits k j := by
    change C≤C*2^E
    calc
      C=C*1 := (mul_one _).symm
      _≤C*2^E := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt hpow)
  have hmb : 1≤m*bits := Nat.succ_le_of_lt (Nat.mul_pos hm hbits)
  have hconstant : 800000≤C := by
    calc
      800000=800000*1 := (mul_one _).symm
      _≤800000*(m*bits) := Nat.mul_le_mul_left _ hmb
      _=C := by dsimp [C]; ring
  have hmbC : m*bits≤C := by
    calc
      m*bits=1*(m*bits) := (one_mul _).symm
      _≤800000*(m*bits) := Nat.mul_le_mul_right _ (by decide)
      _=C := by dsimp [C]; ring
  have hCW : C<2^w := hCN.trans_lt hbound
  have hmbW : m*bits<2^w := hmbC.trans_lt hCW
  have hEW : E<2^w := (Nat.lt_two_pow_self (n:=E)).trans_le hpowN |>.trans hbound
  have hkjW : k+j<2^w := by dsimp only [E] at hEW; omega
  have hkj5W : k+j+5<2^w := by dsimp only [E] at hEW; omega
  have hpowW : 2^E<2^w := hpowN.trans_lt hbound
  have hcW : 800000<2^w := hconstant.trans_lt hCW
  have hmW : m<2^w := hwords _ (by simp)
  have hbW : bits<2^w := hwords _ (by simp)
  have hkW : k<2^w := hwords _ (by simp)
  have hjW : j<2^w := hwords _ (by simp)
  have hCW' : 800000*(m*bits)<2^w := by simpa only [C,Nat.mul_assoc] using hCW
  have hfinalW : 800000*(m*bits)*2^E<2^w := by
    simpa only [dyadicIterationBudget,Nat.mul_assoc,E] using hbound
  have hshiftW : 1 <<< (2*(k+j+5))<2^w := by
    simpa only [Nat.shiftLeft_eq,one_mul,E] using hpowW
  apply runs_start_le
  unfold iterationBudgetBody
  wram_step
  wram_step
  wram_step
  wram_step
  simp only [Nat.shiftLeft_eq,one_mul]
  wram_step
  wram_step
  refine runs_ret_le (v:=800000*(m*bits)*2^E) (by eval_expr) ?_ ?_
  · refine ⟨rfl,?_⟩
    change 800000*(m*bits)*2^E=dyadicIterationBudget m bits k j
    unfold dyadicIterationBudget E
    ring
  · simp only [iterationBudgetContract,Expr.size_reg,Expr.size_bin,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
