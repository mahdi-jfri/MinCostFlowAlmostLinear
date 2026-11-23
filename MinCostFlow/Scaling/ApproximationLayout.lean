module

public import MinCostFlow.Scaling.ApproximationModel
public import MinCostFlow.Scaling.SolverOutputLayout
import WordRAM.Memory

/-!
# The approximation result in memory

A two-word header stores an unsigned flow pointer and the objective-based
magnitude. The referenced array stores exactly the integral flow, using
one unsigned cell per coordinate. Both the header and array lie below
the returned heap.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- A flow pointer, magnitude, and exact referenced unsigned flow array. -/
def ApproximationResultAt {J : Circulation} (mem : ℕ → ℕ) (base bound : ℕ)
    (r : ApproximationResult J) : Prop :=
  ∃ ptr,ListAt mem base [ptr,r.magnitude] ∧ ptr+J.m≤bound ∧ J.readSolverFlow mem ptr=r.flow

/-- An unsigned flow array and its header represent the corresponding
integer-valued approximation result. -/
theorem approximationResultAt_of_unsigned {J : Circulation} {mem : ℕ → ℕ}
    {base bound ptr magnitude : ℕ} {f : Fin J.m → ℕ}
    (hheader : ListAt mem base [ptr,magnitude]) (hbound : ptr+J.m≤bound)
    (hflow : ListAt mem ptr (List.ofFn f)) :
    ApproximationResultAt mem base bound (⟨fun e => (f e : ℤ),magnitude⟩ : ApproximationResult J) := by
  refine ⟨ptr,hheader,hbound,?_⟩
  exact solverOutput_read_eq J (fun _ => Int.natCast_nonneg _) (by simpa only [Int.toNat_natCast] using hflow)

/-- Preserving an existing result's header and flow prefix preserves the
representation when the heap bound increases. -/
theorem ApproximationResultAt.of_agree_below {J : Circulation} {mem mem' : ℕ → ℕ}
    {base bound bound' : ℕ} {r : ApproximationResult J}
    (hat : ApproximationResultAt mem base bound r) (hheader : base+2≤bound)
    (hbound : bound≤bound') (hframe : ∀ x<bound,mem' x=mem x) :
    ApproximationResultAt mem' base bound' r := by
  obtain ⟨ptr,hstored,hend,hread⟩ := hat
  refine ⟨ptr,hstored.of_agree_below (h₀ := bound) hheader hframe,hend.trans hbound,?_⟩
  funext e
  have h := congrFun hread e
  change (mem' (ptr+e.val) : ℤ)=r.flow e
  change (mem (ptr+e.val) : ℤ)=r.flow e at h
  rw [hframe _ (by have he := e.isLt; omega)]
  exact h

end MinCostFlow.Scaling.Machine
