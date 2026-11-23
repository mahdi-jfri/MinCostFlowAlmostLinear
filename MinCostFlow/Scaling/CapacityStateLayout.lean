module

public import MinCostFlow.Scaling.CapacityLoopModel
public import MinCostFlow.Scaling.SolverOutputLayout
import WordRAM.Memory

/-!
# Capacity-scaling state in memory

The capacity loop retains an unsigned integral flow and an early-stop
flag. A two-word header stores its flow pointer and the flag's zero/one
encoding. The referenced array lies below the current heap bound. This
layout records data only; feasibility is established by the loop proof.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Exact unsigned integral flow and stored early-stop flag. -/
def CapacityStateAt {J : Circulation} (mem : ℕ → ℕ) (base bound : ℕ) (s : CapacityState J) : Prop :=
  ∃ ptr,ListAt mem base [ptr,s.stopped.toNat] ∧ ptr+J.m≤bound ∧ J.readSolverFlow mem ptr=s.flow

/-- A nonnegative flow array and its two-word header give the exact
capacity-state representation. -/
theorem capacityStateAt_of_array {J : Circulation} {mem : ℕ → ℕ} {base bound ptr : ℕ}
    {s : CapacityState J} (hheader : ListAt mem base [ptr,s.stopped.toNat])
    (hbound : ptr+J.m≤bound) (hflow : ListAt mem ptr (List.ofFn (fun e => (s.flow e).toNat)))
    (hvalues : ∀ e,0≤s.flow e) : CapacityStateAt mem base bound s :=
  ⟨ptr,hheader,hbound,solverOutput_read_eq J hvalues hflow⟩

/-- Enlarging the fresh heap while preserving the old prefix preserves
both the capacity-state header and referenced flow. -/
theorem CapacityStateAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {s : CapacityState J} (hat : CapacityStateAt mem base bound s)
    (hheader : base+2≤bound) (hbound : bound≤bound') (hframe : ∀ x<bound,mem' x=mem x) :
    CapacityStateAt mem' base bound' s := by
  obtain ⟨ptr,hstored,hend,hread⟩ := hat
  refine ⟨ptr,hstored.of_agree_below (h₀ := bound) hheader hframe,hend.trans hbound,?_⟩
  funext e
  have h := congrFun hread e
  change (mem' (ptr+e.val) : ℤ)=s.flow e
  change (mem (ptr+e.val) : ℤ)=s.flow e at h
  rw [hframe _ (by have he := e.isLt; omega)]
  exact h

end MinCostFlow.Scaling.Machine
