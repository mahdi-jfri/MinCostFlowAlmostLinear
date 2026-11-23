module

public import MinCostFlow.IPM.Machine.Layout
import WordRAM.Tactic

/-!
# Reserving zero lower-capacity blocks

The augmented target-test graph has zero lower capacities. Fresh-zero
heap memory already represents those numbers at every precision. The
procedure reserves the whole dense array and advances its heap pointer.
It charges the address calculation and preserves all memory.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,L,heap]`. -/
def zeroTableBody : Stmt := .ret (.bin .add (.reg 2) (.bin .mul (.reg 0) (.reg 1)))

/-- One zero-table reservation entry. -/
def zeroTableModule : List Stmt := [zeroTableBody]

/-- The reserved output contains m zero blocks, at any fixed precision P. -/
def zeroTableContract (w h P : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ m L heap,args=[m,L,heap])
    (fun args _ mem' => ∀ i < args.getD 0 0,ScalarAt mem'
      (heapArg args+i*args.getD 1 0) h (args.getD 1 0) P 0)
    (fun _ _ => 10) (fun args _ => args.getD 0 0*args.getD 1 0)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧
    v=heapArg args+args.getD 0 0*args.getD 1 0}

/-- Reserving fresh-zero words is deterministic. -/
theorem zeroTable_noRand : zeroTableBody.NoRand := by
  simp [zeroTableBody,Stmt.NoRand]

/-- Zero lower-capacity blocks need no stores. Their validity, decoding
and the heap frame follow from the fresh-zero precondition. -/
theorem zeroTable_meetsContract {w h P b : ℕ} {p : Program}
    (hp : p.HasAt b zeroTableModule) : MeetsContract w p b (zeroTableContract w h P) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨m,L,heap,rfl⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+m*L < 2^w at hspace
  have hm : m < 2^w := hwords _ (by simp)
  have hL : L < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  have hprod : m*L < 2^w := by omega
  apply runs_start_le
  unfold zeroTableBody
  refine runs_ret_le (v:=heap+m*L) (by eval_expr) ?_ ?_
  · change (heap ≤ heap+m*L ∧ heap+m*L ≤ heap+m*L ∧
      (∀ x < heap,mem x=mem x) ∧ ZeroFrom mem (heap+m*L) ∧
      (∀ i < m,ScalarAt mem (heap+i*L) h L P 0)) ∧ heap+m*L=heap+m*L
    refine ⟨⟨by omega,le_rfl,fun _ _ => rfl,?_,?_⟩,rfl⟩
    · intro x hx
      exact hzero x (by omega)
    · intro i _
      exact ⟨Num.zeroFrom_valid hzero (by omega),Num.fixVal_zeroFrom hzero (by omega)⟩
  · simp only [zeroTableContract,heapContract,Expr.size_bin,Expr.size_reg]
    omega

/-- The reservation preconditions hold on an actual nonempty zero table. -/
theorem zeroTable_pre_example :
    (zeroTableContract 16 4 8).pre [1,8,0] (fun _ => 0) := by
  exact ⟨⟨1,8,0,rfl⟩,(fun _ _ => rfl),by decide⟩

end MinCostFlow.IPM.Machine
