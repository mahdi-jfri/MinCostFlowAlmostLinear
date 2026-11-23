module

public import MinCostFlow.IPM.Machine.DetectNames

/-!
# Supplying the stable-name continuation after Detect

The combined entry reserves one full Detect answer and one copied
answer, plus its pointer word. The wrapped Detect postcondition gives
the exact model set and its reserved extent. Its cardinality bound then
supplies the snapshot's complete input condition and space for the final
pointer record. No additional DS output condition is assumed.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual reserved Detect output completes the snapshot input and
leaves room for the pointer record, using the combined entry's budget. -/
theorem detectNames_snapshot_pre {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b heap reserved : ℕ} {s : A.State} {x : R.τ} {mem detectMem : ℕ → ℕ}
    (hpre : (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem)
    (hout : (minRatioDetectContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).post
      [b,m+1,heap] mem reserved detectMem) :
    (detectSnapshotContract w (A.detect s).1).pre [heap,reserved] detectMem ∧
      reserved+(1+(A.detect s).1.card)+1<2^w ∧
      MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision (A.detect s).2 := by
  obtain ⟨heap',heq,_,hcard,hspace⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  subst heap'
  obtain ⟨detectEnd,s',x',hv,hlo,hhi,hzero,_,hD,_⟩ := hout
  change reserved=detectEnd+(m+1) at hv
  change heap≤detectEnd at hlo
  change detectEnd≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem at hhi
  change s'=(A.detect s).2 ∧ DetectAt detectMem heap (A.detect s).1 ∧
    MinRatioStateFits A G F.fmt.limbBits F.limbs F.fmt.precision s' at hD
  change heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1<2^w at hspace
  have hs : reserved+(1+(A.detect s).1.card)+1<2^w := by omega
  refine ⟨⟨⟨heap,reserved,rfl,hD.2.1,by omega,by omega⟩,hzero,by change reserved+(1+(A.detect s).1.card)<2^w; omega⟩,hs,?_⟩
  simpa only [hD.1] using hD.2.2

end MinCostFlow.IPM.Machine
