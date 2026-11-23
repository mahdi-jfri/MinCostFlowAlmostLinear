module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic.IntervalCases

/-!
# Writing one named edge for min-ratio initialization

The min-ratio graph layout stores `[edge,tail,head]` for each fixed
IPM edge. This entry writes exactly one such record, preserving the
entire earlier heap prefix and the fresh-zero suffix after its result.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[edge,tail,head,heap]`. -/
def namedEdgeRecordBody : Stmt :=
  .store (.reg 3) (.reg 0) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 2) ;;
  .ret (.bin .add (.reg 3) (.const 3))

/-- One named-edge record entry. -/
def namedEdgeRecordModule : List Stmt := [namedEdgeRecordBody]

/-- Three fresh output words, exact pointer and constant cost. -/
def namedEdgeRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ e u v heap,args=[e,u,v,heap])
    (fun args _ mem' => ListAt mem' (heapArg args) [args.getD 0 0,args.getD 1 0,args.getD 2 0])
    (fun _ _ => 30) (fun _ _ => 3)
  {C with post := fun args mem v mem' => C.post args mem v mem' ∧ v=heapArg args+3}

/-- Writing a named-edge record is deterministic. -/
theorem namedEdgeRecord_noRand : namedEdgeRecordBody.NoRand := by
  simp [namedEdgeRecordBody,Stmt.NoRand]

/-- The record is written exactly in at most thirty operations. -/
theorem namedEdgeRecord_meetsContract {w b : ℕ} {p : Program}
    (hp : p.HasAt b namedEdgeRecordModule) : MeetsContract w p b (namedEdgeRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨⟨e,u,v,heap,rfl⟩,hzero,hspace⟩ := hpre
  change ZeroFrom mem heap at hzero
  change heap+3 < 2^w at hspace
  have he : e < 2^w := hwords _ (by simp)
  have hu : u < 2^w := hwords _ (by simp)
  have hv : v < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold namedEdgeRecordBody
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v:=heap+3) (by eval_expr) ?_ ?_
  · let outMem := Function.update (Function.update (Function.update mem heap e) (heap+1) u) (heap+2) v
    change (heap ≤ heap+3 ∧ heap+3 ≤ heap+3 ∧ (∀ x < heap,outMem x=mem x) ∧
      ZeroFrom outMem (heap+3) ∧ ListAt outMem heap [e,u,v]) ∧ heap+3=heap+3
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      dsimp only [outMem]
      rw [Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      change heap+3 ≤ x at hx
      dsimp only [outMem]
      rw [Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro i hi
      change i < 3 at hi
      interval_cases i <;> simp [outMem]
  · simp only [namedEdgeRecordContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
