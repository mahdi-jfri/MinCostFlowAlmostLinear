module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic.IntervalCases

/-!
# Writing a coefficient-refresh update pair

Definition 4.5 (page 14) consumes the batch's deletion and insertion
records. For a changed fixed edge the six words are
`[1,edge,0,edge,tail,head]`. This entry writes exactly that record,
preserving the old heap prefix and the fresh suffix after its result.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[edge,tail,head,heap]`. -/
def refreshRecordBody : Stmt :=
  .store (.reg 3) (.const 1) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 0) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 3) (.const 3)) (.reg 0) ;;
  .store (.bin .add (.reg 3) (.const 4)) (.reg 1) ;;
  .store (.bin .add (.reg 3) (.const 5)) (.reg 2) ;;
  .ret (.bin .add (.reg 3) (.const 6))

/-- One delete/reinsert record entry. -/
def refreshRecordModule : List Stmt := [refreshRecordBody]

/-- Six fresh output words, exact pointer and constant cost. -/
def refreshRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ e u v heap,args=[e,u,v,heap])
    (fun args _ mem' => ListAt mem' (heapArg args) [1,args.getD 0 0,0,args.getD 0 0,args.getD 1 0,args.getD 2 0])
    (fun _ _ => 60) (fun _ _ => 6)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+6}

/-- Writing a delete/reinsert record is deterministic. -/
theorem refreshRecord_noRand : refreshRecordBody.NoRand := by
  simp [refreshRecordBody,Stmt.NoRand]

/-- The record is written exactly in at most sixty operations. -/
theorem refreshRecord_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b refreshRecordModule) : MeetsContract w p b (refreshRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨e,u,v,heap,rfl⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+6 < 2^w at hspace
  have he : e < 2^w := hwords _ (by simp)
  have hu : u < 2^w := hwords _ (by simp)
  have hv : v < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold refreshRecordBody
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v:=heap+6) (by eval_expr) ?_ ?_
  · let outMem := Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update mem heap 1) (heap+1) e) (heap+2) 0)
      (heap+3) e) (heap+4) u) (heap+5) v
    change (heap ≤ heap+6 ∧ heap+6 ≤ heap+6 ∧ (∀ x < heap,outMem x=mem x) ∧
      ZeroFrom outMem (heap+6) ∧ ListAt outMem heap [1,e,0,e,u,v]) ∧ heap+6=heap+6
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      dsimp only [outMem]
      rw [Function.update_of_ne (by omega : x ≠ heap+5),
        Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),
        Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      change heap+6 ≤ x at hx
      dsimp only [outMem]
      rw [Function.update_of_ne (by omega : x ≠ heap+5),
        Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),
        Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro i hi
      change i < 6 at hi
      interval_cases i <;> simp [outMem]
  · simp only [refreshRecordContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
