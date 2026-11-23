module

public import MinCostFlow.IPM.Machine.BatchUpdateStatus
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# The uniform result preserves the actual effective step

The final metadata record lies after the complete reserved answer.
Its frame preserves the doubled-width effective normalization, the
actual answer bit and the exact same concrete model state. Thus the
admissibility proof can decode the effective scalar from the final
returned memory, including on a failure answer.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the uniform status, actual effective scalar, model transition
and fixed-point state fit from the final memory, after its record write. -/
theorem batchUpdateStatus_answer {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (hlocal : R.Local)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem)
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    ∃ (es : List ℕ) (actual : ℝ) (final : R.τ),
      es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      let answerHeap := heap+(1+6*S.card)
      let result := A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
      mem' (v-2)=answerHeap ∧ R.rep b result.1 final mem' ∧
      ScalarAt mem' (answerHeap+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision result.1 ∧
      AnswerAt mem' (v-1) result.2 ∧ mem' (v-1)≤1 ∧
      (∀ z,R.foot b final z → z<v ∧ (R.foot b x z ∨ heap≤z)) := by
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  obtain ⟨es,actual,final,hnd,hset,hlen,hrep,hscalar,hnorm,hfit,hanswer,hextent,hmeta⟩ :=
    batchUpdate_answer F A I κ α rate allocation R hpre.1 hCore
  have hs := reportStatus_preserves_state R hlocal hRecord hrep (fun z hz => (hmeta z hz).1)
  have hframe := hRecord.1.2.2.1
  change ∀ z<coreEnd,mem' z=coreMem z at hframe
  have hrecordOut := reportStatus_output hRecord
  have hv := hRecord.2
  change v=coreEnd+2 at hv
  have hbit := batchUpdate_answer_bit F A I κ α rate allocation R hCore
  refine ⟨es,actual,final,hnd,hset,hlen,hrecordOut.1,hs.1,?_,hnorm,hfit,?_,?_,?_⟩
  · refine ⟨Num.IPM.valid_frozen hframe hextent hscalar.1,?_⟩
    exact (Num.IPM.fixVal_frozen hframe hextent).trans hscalar.2
  · change mem' (v-1)=_
    rw [hrecordOut.2]
    exact hanswer
  · rw [hrecordOut.2]
    exact hbit
  · intro z hz
    refine ⟨?_,(hmeta z hz).2⟩
    have hh := (hmeta z hz).1
    omega

/-- The final status record preserves every old caller word outside the
original DS footprint, and provides the fresh zero suffix for the next call. -/
theorem batchUpdateStatus_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    ZeroFrom mem' v ∧ ∀ z<heap,¬ R.foot b x z → mem' z=mem z := by
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  have hcoreFrame := batchUpdate_frame F A I κ α rate allocation R hCore
  have hcoreEnd := (batchUpdate_end_le F A I κ α rate allocation R hCore).1
  have hframe := hRecord.1.2.2.1
  change ∀ z<coreEnd,mem' z=coreMem z at hframe
  refine ⟨hRecord.1.2.2.2.1,?_⟩
  intro z hz hnot
  exact (hframe z (by omega)).trans (hcoreFrame z hz hnot)

/-- The final status bit equals the actual reserved Update header in
that same final memory. This ties a retained state-indexed Update
transition to its caller-visible answer without representation uniqueness. -/
theorem batchUpdateStatus_header {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    mem' (v-1)=mem' (heap+(1+6*S.card)) := by
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  change (reportStatusContract w).post
    [heap+(1+6*S.card),coreMem (heap+(1+6*S.card)),coreEnd] coreMem v mem' at hRecord
  have hEnd := (batchUpdate_end_le F A I κ α rate allocation R hCore).1
  have hframe : ∀ z<coreEnd,mem' z=coreMem z := hRecord.1.2.2.1
  exact (reportStatus_output hRecord).2.trans (hframe _ (by omega)).symm

/-- The uniform last-word Update answer is always a bit. -/
theorem batchUpdateStatus_bit {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') : mem' (v-1)≤1 := by
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  have hd := reportStatus_output hRecord
  rw [hd.2]
  exact batchUpdate_answer_bit F A I κ α rate allocation R hCore

/-- The uniform Update allocation bounds the exact returned endpoint,
leaving an explicit caller margin available for fresh metadata. -/
theorem batchUpdateStatus_end_le {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hspace : heap+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w)
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    v≤heap+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2 := by
  have hh : heap<2^w := by omega
  have hn : heap+(1+6*S.card)<2^w := by omega
  have halloc := update_allocation_le_bound (b:=b) (g:=g) (l:=l) (eta:=eta) allocation hh hn
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  have hbound := (batchUpdate_end_le F A I κ α rate allocation R hCore).2.1
  have hv : v=coreEnd+2 := hRecord.2
  omega

/-- The explicit uniform input budget bounds the complete returned heap,
including the final record, by one machine word. -/
theorem batchUpdateStatus_value_lt_of_budget {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hspace : heap+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w)
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') : v<2^w := by
  have hh : heap<2^w := by omega
  have hn : heap+(1+6*S.card)<2^w := by omega
  have halloc := update_allocation_le_bound (b:=b) (g:=g) (l:=l) (eta:=eta) allocation hh hn
  obtain ⟨coreEnd,coreMem,hCore,hRecord⟩ := hout
  have hbound := (batchUpdate_end_le F A I κ α rate allocation R hCore).2.1
  have hv := hRecord.2
  change v=coreEnd+2 at hv
  omega

/-- The full uniform-result precondition supplies its returned-word bound. -/
theorem batchUpdateStatus_value_lt {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem)
    (hout : (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') : v<2^w :=
  batchUpdateStatus_value_lt_of_budget F A I κ α rate allocation R hpre.2 hout

end MinCostFlow.IPM.Machine
