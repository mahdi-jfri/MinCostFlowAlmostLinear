module

public import MinCostFlow.Scaling.OuterEntryContract
public import MinCostFlow.Scaling.ArbitraryDemandPaperCost
import MinCostFlow.Scaling.SolverTimePositive
import Mathlib.Tactic.Ring

/-!
# The whole program's paper-form budget

The complete arbitrary-demand procedure has the three logarithmic
factors of Appendix C. Computing input bounds, copying the answer, and
the machine's entry call add only linear work. Doubling the explicit
constant absorbs that work and the two entry-call steps, also on empty
instances, because every contracted solver takes positive time.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- The whole program uses twice the procedure's explicit constant. -/
def wholeScalingConstant (solver : Program) : ℕ := 2*outerScalingConstant solver

set_option maxRecDepth 4096 in
private theorem entry_paper_budget (cost K A B L time m n : ℕ)
    (hc : cost≤K*A*B*L*(time+m)+K*n) (hK : 2002≤K)
    (hA : 1≤A) (hB : 1≤B) (hL : 1≤L) (ht : 1≤time) :
    cost+2000*(m+n+1)+2≤(2*K)*A*B*L*(time+m)+(2*K)*n := by
  have hkA : K≤K*A := Nat.le_mul_of_pos_right _ hA
  have hkB : K*A≤K*A*B := Nat.le_mul_of_pos_right _ hB
  have hkL : K*A*B≤K*A*B*L := Nat.le_mul_of_pos_right _ hL
  have hcoef : 2002≤K*A*B*L := hK.trans (hkA.trans (hkB.trans hkL))
  have hq : 2002*(m+1)≤K*A*B*L*(time+m) := Nat.mul_le_mul hcoef (by omega)
  have hn : 2002*n≤K*n := Nat.mul_le_mul_right n hK
  have he : (2*K)*A*B*L*(time+m)+(2*K)*n=2*(K*A*B*L*(time+m)+K*n) := by ring
  rw [he]
  omega

/-- The complete original-input program, including its entry call, has
`K*log(m)*log(mU)*log(C)*(T(K*n,K*m)+m)+K*n` cost with padded binary
logs and the explicit constant `K=2*10^18*(solver.regBound+1)`. -/
theorem outerEntry_cost_paper (w : ℕ) (solver : Program) (entry : ℕ) (T : ℕ → ℕ → ℕ)
    (hproc : ∀ w,MeetsContract w solver entry (solverContract w T solverScratch))
    (hmono : SolverTimeMonotone T) (I : Instance) (hv : I.IsValid)
    (args : List ℕ) (mem : ℕ → ℕ) :
    (outerEntryContract w solver entry T hproc I hv).cost args mem+2≤
      wholeScalingConstant solver*(Nat.clog 2 (I.m+1)+1)*
        (Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2)*
          (T (wholeScalingConstant solver*I.n) (wholeScalingConstant solver*I.m)+I.m)+
        wholeScalingConstant solver*I.n := by
  let K := outerScalingConstant solver
  have hb := arbitraryDemand_cost_paper w solver entry T hproc hmono I hv I.maxCost I.maxCapacity [] (fun _ => 0)
  have hK : 2002≤K := by dsimp only [K,outerScalingConstant]; omega
  have hKK : K≤wholeScalingConstant solver := by change K≤2*K; omega
  have ht := hmono (K*I.n) (wholeScalingConstant solver*I.n)
    (K*I.m) (wholeScalingConstant solver*I.m)
    (Nat.mul_le_mul_right I.n hKK) (Nat.mul_le_mul_right I.m hKK)
  have htime : 1≤T (wholeScalingConstant solver*I.n) (wholeScalingConstant solver*I.m) :=
    (solverTime_zero_pos solver entry T hproc).trans (hmono 0 _ 0 _ (Nat.zero_le _) (Nat.zero_le _))
  have hraise := hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left
    (K*(Nat.clog 2 (I.m+1)+1)*(Nat.clog 2 (I.m+1)+Nat.clog 2 (I.maxCapacity+1)+1)*Nat.clog 2 (I.maxCost+2))
    (Nat.add_le_add_right ht I.m)) (K*I.n))
  exact entry_paper_budget _ K _ _ _ _ I.m I.n hraise hK (by omega) (by omega)
    (Nat.clog_pos (by decide) (by omega)) htime

end MinCostFlow.Scaling.Machine
