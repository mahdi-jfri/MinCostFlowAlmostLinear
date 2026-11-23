module

public import MinCostFlow.IPM.Machine.EpochBudgetRecord
import WordRAM.Tactic

/-!
# Initial budget for the guarded epoch loop

After the epoch's data structure initialization, append the initial
five-edge report budget. The new record has zero reported names and
success status. Its endpoint is the first iteration's incoming heap.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,heap]`. The product is computed by the machine before
calling the existing three-word metadata writer. -/
def epochBudgetInitBody (record : ℕ) : Stmt :=
  .call 2 record [.bin .mul (.const 5) (.reg 0),.const 0,.const 1,.reg 1] ;;
  .ret (.reg 2)

/-- The initial metadata reserves three fresh words and requires its
five-edge count to fit the chosen word size. -/
def epochBudgetInitContract (w : ℕ) : Contract where
  pre args mem := ∃ m heap,args=[m,heap] ∧ 5<2^w ∧ 5*m<2^w ∧
    (epochBudgetRecordContract w).pre [5*m,0,1,heap] mem
  post args mem v final :=
    (epochBudgetRecordContract w).post [5*args.getD 0 0,0,1,args.getD 1 0] mem v final
  cost _ _ := 80

/-- Initializing the report budget has no random instruction. -/
theorem epochBudgetInit_noRand (record : ℕ) : (epochBudgetInitBody record).NoRand := by
  simp [epochBudgetInitBody,Stmt.NoRand]

/-- The actual multiplication, metadata call and return cost at most
eighty operations and produce the loop's initial budget record. -/
theorem epochBudgetInit_meetsContract {w entry record : ℕ} {p : Program}
    (hp : p.procs[entry]?=some (epochBudgetInitBody record))
    (hrecord : MeetsContract w p record (epochBudgetRecordContract w)) :
    MeetsContract w p entry (epochBudgetInitContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨m,heap,rfl,hfive,hproduct,hpre⟩ := hpre
  have hm := hwords m (by simp)
  have hh := hwords heap (by simp)
  have hzero : 0<2^w := Nat.two_pow_pos w
  have hone : 1<2^w := by omega
  apply runs_start_le
  unfold epochBudgetInitBody
  refine runs_seq_call_le hrecord (vs:=[5*m,0,1,heap]) (by eval_expr) (by wram_words) hpre ?_
  intro v final pos' hout
  have hv : v=heap+3 := hout.2
  have hspace : heap+3<2^w := hpre.2.2
  have hvword : v<2^w := by omega
  refine runs_ret_le (v:=v) (by eval_expr) ?_ ?_
  · exact hout
  · simp only [epochBudgetInitContract,epochBudgetRecordContract,heapContract,Expr.size_reg,Expr.size_bin,
      Expr.size_const,argsSize_cons,argsSize_nil]
    omega

end MinCostFlow.IPM.Machine
