module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Memory
import Mathlib.Tactic.IntervalCases

/-!
# Writing an auxiliary edge of the initialized circulation

Lemma 4.12 (Chen et al., arXiv:2203.00671v2, page 31 and
Appendix B.1 page 92) gives every auxiliary edge a nonnegative capacity,
zero lower capacity and positive penalty cost. This procedure writes
one such edge in the existing solver layout: tail, head, capacity,
cost sign zero and penalty magnitude. Selecting its endpoints and
capacity from the two routing tables is handled by its caller.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[tail,head,capacity,penalty,heap]`. -/
def initialAuxiliaryRecordBody : Stmt :=
  .store (.reg 4) (.reg 0) ;;
  .store (.bin .add (.reg 4) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 4) (.const 2)) (.reg 2) ;;
  .store (.bin .add (.reg 4) (.const 3)) (.const 0) ;;
  .store (.bin .add (.reg 4) (.const 4)) (.reg 3) ;;
  .ret (.bin .add (.reg 4) (.const 5))

/-- One record writer. -/
def initialAuxiliaryRecordModule : List Stmt := [initialAuxiliaryRecordBody]

/-- A five-word record with an exact positive-cost encoding. -/
def initialAuxiliaryRecordContract (w : ℕ) : Contract :=
  let C := heapContract w
    (fun args _ => ∃ u v cap penalty heap, args = [u,v,cap,penalty,heap])
    (fun args _ mem' => ListAt mem' (heapArg args)
      [args.getD 0 0,args.getD 1 0,args.getD 2 0,0,args.getD 3 0])
    (fun _ _ => 50) (fun _ _ => 5)
  { C with post := fun args mem v mem' => C.post args mem v mem' ∧ v = heapArg args+5 }

/-- The auxiliary-edge record writer is deterministic. -/
theorem initialAuxiliaryRecordBody_noRand : initialAuxiliaryRecordBody.NoRand := by
  simp [initialAuxiliaryRecordBody,Stmt.NoRand]

/-- The exact record is written in at most fifty operations, preserving
all old memory and the fresh suffix above its five output words. -/
theorem initialAuxiliaryRecord_meetsContract {w b : ℕ} {p : Program} (hw : 5 < 2^w)
    (hp : p.HasAt b initialAuxiliaryRecordModule) :
    MeetsContract w p b (initialAuxiliaryRecordContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos omegaBits hwords hpre
  obtain ⟨⟨u,v,cap,penalty,heap,rfl⟩,hzero,hspace⟩ := hpre
  change heap+5 < 2^w at hspace
  change ZeroFrom mem heap at hzero
  have hu : u < 2^w := hwords _ (by simp)
  have hv : v < 2^w := hwords _ (by simp)
  have hc : cap < 2^w := hwords _ (by simp)
  have hk : penalty < 2^w := hwords _ (by simp)
  have hh : heap < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold initialAuxiliaryRecordBody
  wram_step
  wram_step
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v := heap+5) (by eval_expr) ?_ ?_
  · let outMem := Function.update
      (Function.update (Function.update (Function.update (Function.update mem heap u)
        (heap+1) v) (heap+2) cap) (heap+3) 0) (heap+4) penalty
    change (heap ≤ heap+5 ∧ heap+5 ≤ heap+5 ∧
      (∀ x < heap, outMem x = mem x) ∧ ZeroFrom outMem (heap+5) ∧
      ListAt outMem heap [u,v,cap,0,penalty]) ∧ heap+5 = heap+5
    dsimp only [outMem]
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      change x < heap at hx
      rw [Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),
        Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),
        Function.update_of_ne (by omega : x ≠ heap)]
    · intro x hx
      change heap+5 ≤ x at hx
      rw [Function.update_of_ne (by omega : x ≠ heap+4),
        Function.update_of_ne (by omega : x ≠ heap+3),
        Function.update_of_ne (by omega : x ≠ heap+2),
        Function.update_of_ne (by omega : x ≠ heap+1),
        Function.update_of_ne (by omega : x ≠ heap)]
      exact hzero x (by omega)
    · intro i hi
      change i < 5 at hi
      interval_cases i <;> simp
  · simp only [initialAuxiliaryRecordContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    omega

end MinCostFlow.IPM.Machine
