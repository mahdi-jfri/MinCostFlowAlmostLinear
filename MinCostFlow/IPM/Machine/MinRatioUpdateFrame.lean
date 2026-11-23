module

public import MinCostFlow.IPM.Machine.MinRatioContract
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Preserving an Update transition across fresh metadata

The Update postcondition reads only its reserved scalar and answer bit
from the final memory. A caller that preserves this prefix preserves the
transition for the same abstract state. No uniqueness property of the
concrete representation is needed.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Fresh writes above the reserved answer preserve the Update transition,
including the actual normalization and the exact returned abstract state. -/
theorem minRatioMachine_update_post_frozen {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ)
    {s s' : A.State} {b batch g l eta heap end_ : ℕ} {mem core final : ℕ → ℕ}
    (hpost : (minRatioMachineContract F A G m κ α rate allocation).post
      0 s [b,batch,g,l,eta,heap] mem s' core)
    (hframe : ∀ z<end_,final z=core z)
    (hend : heap+1+2*F.limbs≤end_) :
    (minRatioMachineContract F A G m κ α rate allocation).post
      0 s [b,batch,g,l,eta,heap] mem s' final := by
  obtain ⟨actual,hscalar,hnorm,hfit,hstep⟩ := hpost
  change ScalarAt core (heap+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual at hscalar
  refine ⟨actual,?_,hnorm,hfit,?_⟩
  · exact ⟨Num.IPM.valid_frozen hframe hend hscalar.1,
      (Num.IPM.fixVal_frozen hframe hend).trans hscalar.2⟩
  · intro U hU
    obtain ⟨heq,hanswer⟩ := hstep U hU
    refine ⟨heq,?_⟩
    change final heap = _
    change core heap = _ at hanswer
    exact (hframe heap (by omega)).trans hanswer

end MinCostFlow.IPM.Machine
