module

public import MinCostFlow.IPM.Machine.TargetSearchArithmetic
public import MinCostFlow.IPM.Machine.TargetTestInvariant
public import MinCostFlow.IPM.Machine.IterationBudgetProgram
public import MinCostFlow.Num.IPM.BitLength
import WordRAM.Tactic

/-!
# Word computations of both search limits

The bisection counts the bits in its unsigned span. Its inner
test uses the integer iteration budget for one edge plus one
final residual check. Both procedures preserve memory.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The number of midpoint rounds, computed from the signed radius. -/
def targetSearchRoundsBody (bits : ℕ) : Stmt :=
  .call 1 bits [.bin .mul (.const 2) (.reg 0)] ;;
  .ret (.reg 1)

/-- The span must fit as a word for its bit length to be read. -/
def targetSearchRoundsContract (w : ℕ) : Contract where
  pre args _ := ∃ B,args=[B] ∧ 2*B<2^w
  post args mem v final := final=mem ∧ v=targetSearchRounds (args.getD 0 0)
  cost args _ := 14*targetSearchRounds (args.getD 0 0)+100

/-- The number of stages per target, including the final check. -/
def targetTestLimitBody (budget : ℕ) : Stmt :=
  .call 3 budget [.const 1,.reg 0,.reg 1,.reg 2] ;;
  .ret (.bin .add (.reg 3) (.const 1))

/-- The dyadic iteration budget divided by the edge count, plus one. -/
def targetTestLimitContract (w : ℕ) : Contract where
  pre args _ := ∃ m U k,args=[m.size+U.size,k,Num.IPM.alphaExponent m U] ∧
    2≤m*U ∧ targetTestLimit m U k<2^w
  post args mem v final := final=mem ∧
    v=dyadicEpochLimit (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)+1
  cost _ _ := 130

/-- The two loop-limit computations use no random operation. -/
theorem targetSearchRounds_noRand (bits : ℕ) : (targetSearchRoundsBody bits).NoRand := by
  simp [targetSearchRoundsBody,Stmt.NoRand]

/-- The integer stage-limit computation uses no random operation. -/
theorem targetTestLimit_noRand (budget : ℕ) : (targetTestLimitBody budget).NoRand := by
  simp [targetTestLimitBody,Stmt.NoRand]

/-- Compute the bisection count by the verified word bit-length scanner. -/
theorem targetSearchRounds_meetsContract {w entry bits : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (targetSearchRoundsBody bits))
    (hbits : MeetsContract w p bits Num.IPM.bitLengthContract) (hTwo : 2<2^w) :
    MeetsContract w p entry (targetSearchRoundsContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨B,rfl,hfit⟩ := hpre
  have hb : B<2^w := hwords _ (by simp)
  apply runs_start_le
  unfold targetSearchRoundsBody
  refine runs_seq_call_le hbits (vs:=[2*B]) (by eval_expr) ?_ ⟨_,rfl⟩ ?_
  · intro x hx
    simpa only [List.mem_singleton.mp hx] using hfit
  · intro v final newPos hout
    have hpost : (targetSearchRoundsContract w).post [B] mem v final := hout
    refine runs_ret_le (v:=v) (by eval_expr) hpost ?_
    simp only [targetSearchRoundsContract,Num.IPM.bitLengthContract,targetSearchRounds,List.getD_cons_zero,
      argsSize_cons,argsSize_nil,Expr.size_reg,Expr.size_const,Expr.size_bin]
    omega

/-- Compute the complete target limit with one call of the verified
integer budget routine and one exact increment. -/
theorem targetTestLimit_meetsContract {w entry budget : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (targetTestLimitBody budget))
    (hbudget : MeetsContract w p budget (iterationBudgetContract w)) (hOne : 1<2^w) :
    MeetsContract w p entry (targetTestLimitContract w) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨m,U,k,rfl,hsize,hfit⟩ := hpre
  let b := m.size+U.size
  let j := Num.IPM.alphaExponent m U
  have hm : 0<m := by
    by_contra h
    have he : m=0 := by omega
    simp [he] at hsize
  have hb : 0<b := by have hh := Nat.size_pos.mpr hm; unfold b; omega
  have hbW : b<2^w := hwords _ (by simp [b])
  have hkW : k<2^w := hwords _ (by simp)
  have hjW : j<2^w := hwords _ (by simp [j])
  have hBound : dyadicIterationBudget 1 b k j<2^w := by
    change dyadicIterationBudget 1 b k j+1<2^w at hfit
    omega
  have hArgs : ∀ x∈[1,b,k,j],x<2^w := by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hOne
    · exact hbW
    · exact hkW
    · exact hjW
  let init := startState [b,k,j] mem pos
  have hArgsEval : evalArgs w init [.const 1,.reg 0,.reg 1,.reg 2]=some [1,b,k,j] :=
    evalArgs_cons (Expr.eval_const hOne) rfl
  apply runs_start_le
  unfold targetTestLimitBody
  refine runs_seq_call_le hbudget (vs:=[1,b,k,j]) hArgsEval hArgs
    ⟨1,b,k,j,rfl,by decide,hb,hBound⟩ ?_
  intro v final newPos hout
  obtain ⟨rfl,hEnd⟩ := hout
  have hVal : v=dyadicEpochLimit b k j := hEnd
  have hv : v+1<2^w := by rw [hVal]; exact hfit
  refine runs_ret_le (v:=v+1) (Expr.eval_add (x:=v) (y:=1) (by rfl) (Expr.eval_const hOne) hv) ⟨rfl,?_⟩ ?_
  · exact congrArg (·+1) hVal
  · simp only [targetTestLimitContract,iterationBudgetContract,argsSize_cons,argsSize_nil,
      Expr.size_const,Expr.size_reg,Expr.size_bin]
    decide

end MinCostFlow.IPM.Machine
