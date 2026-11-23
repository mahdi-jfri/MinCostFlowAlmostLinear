module

public import MinCostFlow.IPM.Machine.BatchUpdate
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.IPM.Machine.VectorFrame

/-!
# Decoding the actual batch/Update transition

The batch writer preserves all coefficient and normalization blocks.
Its exact extent identifies the Update answer header. The parameter's
postcondition then gives one common effective normalization, the exact
model transition at the original table values, and the success bit.
This decoding also holds on failure, without a hidden witness.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual combined run follows exactly the model Update with the
original checked coefficient tables and its decoded effective scalar.
The answer and doubled-width normalization have explicit addresses. -/
theorem batchUpdate_answer {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hpre : (batchUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap] mem)
    (hout : (batchUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    ∃ (es : List ℕ) (actual : ℝ) (final : R.τ),
      es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      let answerHeap := heap+(1+6*S.card)
      let result := A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
      R.rep b result.1 final mem' ∧
      ScalarAt mem' (answerHeap+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision result.1 ∧
      AnswerAt mem' answerHeap result.2 ∧ answerHeap+1+2*F.limbs≤v ∧
      (∀ z,R.foot b final z → z<v ∧ (R.foot b x z ∨ heap≤z)) := by
  obtain ⟨source',report',g',l',eta',heap',heq,hBpre,_,_,_,_,_,_,hgEnd,hlEnd,heEnd,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  simp only [batchUpdateContract,List.getD_cons_zero,List.getD_cons_succ] at hout
  obtain ⟨batchEnd,batchMem,s',final,hBpost,hUpost,hrep,hDpost,hmeta⟩ := hout
  have hvB := hBpost.2
  change batchEnd=heap+(1+6*S.card) at hvB
  obtain ⟨updateEnd,_,_,hv,hbefore,_⟩ := hUpost
  change v=updateEnd+(1+2*F.limbs) at hv
  change batchEnd≤updateEnd at hbefore
  have hbatch := hBpost.1.2.2.2.2
  change ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧
    BatchAt batchMem heap (refreshEdges (namedInstance I) es) ∧ _ at hbatch
  obtain ⟨es,hnd,hset,hBatch,_⟩ := hbatch
  have hlen : es.length=S.card := by rw [← hset,List.toFinset_card_of_nodup hnd]
  have hframe := hBpost.1.2.2.1
  change ∀ z<heap,batchMem z=mem z at hframe
  have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have heSame := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd
  obtain ⟨actual,hactual,hnorm,hfit,hmodel⟩ := hDpost
  have hresult := hmodel _ hBatch
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hresult hnorm
  change ScalarAt mem' (batchEnd+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual at hactual
  rw [hgSame,hlSame] at hresult
  rw [hresult.1] at hrep hfit
  rw [heSame] at hnorm
  refine ⟨es,actual,final,hnd,hset,hlen,hrep,?_,hnorm,hfit,?_,?_,hmeta⟩
  · simpa only [hvB] using hactual
  · have hh := hresult.2
    change AnswerAt mem' batchEnd _ at hh
    simpa only [hvB] using hh
  · omega

/-- Every old caller word outside the old DS footprint survives both
batch preparation and Update, on either answer. -/
theorem batchUpdate_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    ∀ z<heap,¬ R.foot b x z → mem' z=mem z := by
  obtain ⟨batchEnd,batchMem,_,_,hB,hU,_⟩ := hout
  have hLo := hB.1.1
  change heap≤batchEnd at hLo
  have hFB := hB.1.2.2.1
  change ∀ z<heap,batchMem z=mem z at hFB
  obtain ⟨_,_,_,_,_,_,_,_,_,hFU,_⟩ := hU
  change ∀ z<batchEnd,¬ R.foot b x z → mem' z=batchMem z at hFU
  intro z hz hnot
  exact (hFU z (hz.trans_le hLo) hnot).trans (hFB z hz)

/-- The actual Update answer header is a bit, including failure. It is
at the end of the prepared batch, rather than the reserved heap's last word. -/
theorem batchUpdate_answer_bit {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    mem' (heap+(1+6*S.card))≤1 := by
  obtain ⟨batchEnd,batchMem,_,_,hB,_,_,hD,_⟩ := hout
  have hv := hB.2
  change batchEnd=heap+(1+6*S.card) at hv
  obtain ⟨es,_,_,hbatch,_⟩ := hB.1.2.2.2.2
  obtain ⟨actual,_,_,_,hmodel⟩ := hD
  have hh := (hmodel _ hbatch).2
  change mem' batchEnd=(if (A.update s (refreshEdges (namedInstance I) es)
    (readVector batchMem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector batchMem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual).2.isSome then 1 else 0) at hh
  rw [hv] at hh
  split_ifs at hh <;> omega

/-- The combined endpoint obeys exactly its argument-dependent local
allocation bound, so a caller can reserve a final status record. -/
theorem batchUpdate_end_le {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b source report g l eta heap v : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hout : (batchUpdateContract F A I κ α rate allocation R b s x S).post
      [b,source,report,g,l,eta,F.limbs,heap] mem v mem') :
    heap+(1+6*S.card)+(1+2*F.limbs)≤v ∧
    v≤heap+(1+6*S.card)+allocation 0 [b,heap,g,l,eta,heap+(1+6*S.card)]+(1+2*F.limbs) ∧
    ZeroFrom mem' v := by
  obtain ⟨batchEnd,batchMem,_,_,hB,hU,_⟩ := hout
  have hvB := hB.2
  change batchEnd=heap+(1+6*S.card) at hvB
  obtain ⟨updateEnd,_,_,hv,hlo,hhi,hzero,_⟩ := hU
  change v=updateEnd+(1+2*F.limbs) at hv
  change batchEnd≤updateEnd at hlo
  change updateEnd≤batchEnd+allocation 0 [b,heap,g,l,eta,batchEnd] at hhi
  rw [hvB] at hlo hhi
  exact ⟨by omega,by omega,hzero⟩

end MinCostFlow.IPM.Machine
