module

public import MinCostFlow.IPM.Machine.DetectNames

/-!
# Reading the stable Detect report

The last returned word points to the caller-owned snapshot. Recover
its exact model set and packed extent from the two actual call
postconditions. The snapshot starts above the incoming heap, and
Detect's next abstract state fits the fixed-point format. These are the
data used to construct the following reported-list call.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The returned pointer decodes the exact Detect set, its packed extent
and the next model state's format fit, without a stability premise. -/
theorem detectNames_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b heap v : ℕ} {s : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hout : (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem v mem') :
    DetectAt mem' (mem' (v-1)) (A.detect s).1 ∧
      mem' (v-1)+1+(A.detect s).1.card=v-1 ∧ heap<mem' (v-1) ∧
      MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision (A.detect s).2 := by
  obtain ⟨reserved,detectMem,snapshotEnd,snapshotMem,x',hdetect,hsnapshot,hv,hpointer,hframe,_⟩ := hout
  have hsEnd := hsnapshot.2
  change snapshotEnd=reserved+(1+(A.detect s).1.card) at hsEnd
  have hdata := hsnapshot.1.2.2.2.2.1
  change DetectAt snapshotMem reserved (A.detect s).1 at hdata
  obtain ⟨es,hnd,hset,hheader,hnames⟩ := hdata
  have hlen : es.length=(A.detect s).1.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hdata' : DetectAt mem' reserved (A.detect s).1 := by
    refine ⟨es,hnd,hset,?_,?_⟩
    · exact (hframe reserved (by omega)).trans hheader
    · intro i hi
      exact (hframe (reserved+1+i) (by omega)).trans (hnames i hi)
  obtain ⟨detectEnd,sD,xD,hreserved,hbefore,_,_,_,hDout,_⟩ := hdetect
  change reserved=detectEnd+(m+1) at hreserved
  change heap≤detectEnd at hbefore
  change sD=(A.detect s).2 ∧ DetectAt detectMem heap (A.detect s).1 ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision sD at hDout
  refine ⟨by simpa only [hpointer] using hdata',?_,?_,?_⟩
  · rw [hpointer]
    omega
  · rw [hpointer]
    omega
  · simpa only [hDout.1] using hDout.2.2

end MinCostFlow.IPM.Machine
