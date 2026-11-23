module

public import MinCostFlow.IPM.Machine.DetectNamesInput
import MinCostFlow.IPM.Machine.DetectSnapshotState

/-!
# Recording the stable Detect snapshot pointer

After copying the answer, write its starting address in one fresh word.
The copied list and pointer both lie beyond the concrete DS footprint.
Locality preserves the same DS state and potential. Compose the two
actual call postconditions and the pointer write to obtain the combined
entry's complete output condition and allocation bound.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A fresh pointer write after the actual snapshot establishes the full
Detect/name-list output condition and preserves the same concrete credit. -/
theorem detectNames_post_pointer {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {b heap reserved snapshotEnd : ℕ} {s : A.State} {x mid : R.τ}
    {mem detectMem snapshotMem : ℕ → ℕ}
    (hpre : (detectNamesContract F A G m κ α rate allocation R b s x).pre [b,m,heap] mem)
    (hdetect : (minRatioDetectContract w R
      (minRatioMachineContract F A G m κ α rate allocation) b s x).post
      [b,m+1,heap] mem reserved detectMem)
    (hsnapshot : (detectSnapshotContract w (A.detect s).1).post
      [heap,reserved] detectMem snapshotEnd snapshotMem)
    (hrep : R.rep b (A.detect s).2 mid detectMem)
    (hmeta : ∀ z,R.foot b mid z → z<reserved ∧ (R.foot b x z ∨ heap≤z)) :
    (detectNamesContract F A G m κ α rate allocation R b s x).post [b,m,heap] mem
      (snapshotEnd+1) (Function.update snapshotMem snapshotEnd reserved) ∧
    R.rep b (A.detect s).2 mid (Function.update snapshotMem snapshotEnd reserved) ∧
    R.phi b mid detectMem=R.phi b mid (Function.update snapshotMem snapshotEnd reserved) := by
  have hdetectCopy := hdetect
  have hstate := detectSnapshot_preserves_state R hlocal hsnapshot hrep (fun z hz => (hmeta z hz).1)
  have hsEnd := hsnapshot.2
  change snapshotEnd=reserved+(1+(A.detect s).1.card) at hsEnd
  have hsFrame := hsnapshot.1.2.2.1
  change ∀ z<reserved,snapshotMem z=detectMem z at hsFrame
  have hsZero := hsnapshot.1.2.2.2.1
  change ZeroFrom snapshotMem snapshotEnd at hsZero
  have hpointerSame : ∀ z,R.foot b mid z → snapshotMem z=
      Function.update snapshotMem snapshotEnd reserved z := by
    intro z hz
    rw [Function.update_of_ne (by have hh := (hmeta z hz).1; omega : z≠snapshotEnd)]
  have hpointerState := hlocal b (A.detect s).2 mid snapshotMem
    (Function.update snapshotMem snapshotEnd reserved) hpointerSame
  have hfinalRep := hpointerState.1 hstate.1
  refine ⟨?_,hfinalRep,hstate.2.1.trans hpointerState.2⟩
  obtain ⟨heap',heq,_,hcard,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  subst heap'
  obtain ⟨detectEnd,s',other,hreserved,hlo,hhi,_,_,_,hframeD,_⟩ := hdetect
  change reserved=detectEnd+(m+1) at hreserved
  change heap≤detectEnd at hlo
  change detectEnd≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem at hhi
  change ∀ z<heap,¬ R.foot b x z → detectMem z=mem z at hframeD
  refine ⟨reserved,detectMem,snapshotEnd,snapshotMem,mid,hdetectCopy,hsnapshot,rfl,?_,?_,?_,hfinalRep,?_,?_,?_,?_,?_,?_⟩
  · simp
  · intro z hz
    exact Function.update_of_ne (by omega : z≠snapshotEnd) _ _
  · intro z hz
    rw [Function.update_of_ne (by omega : z≠snapshotEnd)]
    exact hsZero z (by omega)
  · intro z hz
    exact ⟨by have hh := (hmeta z hz).1; omega,(hmeta z hz).2⟩
  · exact hstate.2.2
  · intro hz
    have hh := (hmeta snapshotEnd hz).1
    omega
  · change heap≤snapshotEnd+1
    omega
  · change snapshotEnd+1≤heap+(minRatioMachineContract F A G m κ α rate allocation).space 2 s [b,heap] mem+2*(m+1)+1
    omega
  · intro z hz hnot
    change z<heap at hz
    rw [Function.update_of_ne (by omega : z≠snapshotEnd),hsFrame z (by omega)]
    exact hframeD z hz hnot

end MinCostFlow.IPM.Machine
