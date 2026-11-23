module

public import MinCostFlow.IPM.Machine.CheckedUpdateModel
import MinCostFlow.IPM.Machine.CheckedUpdateRanges
import MinCostFlow.IPM.Machine.VectorFrame
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# A successful state-indexed trace contains the actual Update

The trace records the rejected branch's heap and memory identity, so a
final success bit forces the scan's accepted branch. Its retained header
equality then forces the parameter's actual Update answer to be present.
All decoding uses the same final abstract state as the credit bound.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- A final success bit selects the actual accepted trace, including its
reserved Update header in the same final memory. -/
theorem checkedUpdateTransition_success {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (S : Finset ℕ)
    {b source report g l eta heap neg mx mn v : ℕ} {s s' : A.State}
    {mem final : ℕ → ℕ}
    (htrace : checkedUpdateTransition F A I κ α rate allocation S
      b source report g l eta heap neg mx mn s s' mem final v)
    (haccept : final (v-1)=1) :
    ∃ checkedEnd checkedMem batchEnd batchMem,
      (coefficientRangeReportContract w F.fmt.limbBits S).post
        [report,g,l,neg,mx,mn,F.limbs,heap] mem checkedEnd checkedMem ∧
      checkedMem (checkedEnd-1)=1 ∧
      (detectBatchContract w I S).post [source,report,checkedEnd] checkedMem batchEnd batchMem ∧
      (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
        0 s [b,checkedEnd,g,l,eta,batchEnd] batchMem s' final ∧ final batchEnd=1 := by
  obtain ⟨checkedEnd,checkedMem,hcheck,hbranch⟩ := htrace
  by_cases hscan : checkedMem (checkedEnd-1)=1
  · rw [ite_eq_left hscan] at hbranch
    obtain ⟨batchEnd,batchMem,hbatch,hupdate,hheader⟩ := hbranch
    exact ⟨checkedEnd,checkedMem,batchEnd,batchMem,hcheck,hscan,hbatch,hupdate,hheader ▸ haccept⟩
  · rw [ite_eq_right hscan] at hbranch
    obtain ⟨_,rfl,rfl⟩ := hbranch
    exact False.elim (hscan haccept)

/-- Acceptance of the actual scan supplies the full coefficient range
invariant before the min-ratio Update is run. -/
theorem checkedUpdateCalls_input_ranges {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    {b source report g l eta heap neg mx mn checkedEnd : ℕ} {s : A.State} {x : R.τ}
    {S : Finset ℕ} {mem checkedMem : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (hReport : (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem checkedEnd checkedMem)
    (hscan : checkedMem (checkedEnd-1)=1) :
    ∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,hbatch,hRpt,_,_,_,_,_,_,_,_,_,_,_,_,hvalid,hn,hx,hm,hold,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  exact checkedUpdate_coefficient_ranges F I hbatch hRpt hReport hscan hn hx hm hvalid hold

/-- The actual accepted scan in a successful trace supplies the full
range invariant for the coefficient arrays read by that Update. -/
theorem checkedUpdateTransition_success_input_ranges {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : WordRAM.DSRep A.State)
    {b source report g l eta heap neg mx mn v : ℕ} {s s' : A.State} {x : R.τ}
    {S : Finset ℕ} {mem final : ℕ → ℕ}
    (hpre : (checkedUpdateContract F A I κ α rate allocation R b s x S).pre
      [b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] mem)
    (htrace : checkedUpdateTransition F A I κ α rate allocation S
      b source report g l eta heap neg mx mn s s' mem final v)
    (haccept : final (v-1)=1) :
    ∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  obtain ⟨checkedEnd,checkedMem,_,_,hReport,hscan,_⟩ :=
    checkedUpdateTransition_success F A I κ α rate allocation S htrace haccept
  exact checkedUpdateCalls_input_ranges F A I κ α rate allocation R hpre hReport hscan

/-- An Update reached after an accepted scan has the exact model
state and rounded scalar, even if its direction is absent. -/
theorem checkedUpdateCalls_model {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (S : Finset ℕ)
    {b source report g l eta heap neg mx mn v checkedEnd batchEnd : ℕ} {s s' : A.State}
    {mem final checkedMem batchMem : ℕ → ℕ}
    (hgEnd : g+I.m*F.limbs≤heap) (hlEnd : l+I.m*F.limbs≤heap)
    (heEnd : eta+F.limbs≤heap)
    (hcheck : (coefficientRangeReportContract w F.fmt.limbBits S).post
      [report,g,l,neg,mx,mn,F.limbs,heap] mem checkedEnd checkedMem)
    (hbatch : (detectBatchContract w I S).post [source,report,checkedEnd] checkedMem batchEnd batchMem)
    (hupdate : (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
      0 s [b,checkedEnd,g,l,eta,batchEnd] batchMem s' final)
    (hheader : final (v-1)=final batchEnd) :
    ∃ (es : List ℕ) (actual : ℝ) (answer : ℕ),
      es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s' ∧
      let result := A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
      s'=result.1 ∧ final (v-1)=(if result.2.isSome then 1 else 0) := by
  obtain ⟨_,_,hrecord⟩ := hcheck
  have hscanFrame : ∀ z<heap,checkedMem z=mem z := hrecord.1.2.2.1
  have hchecked : checkedEnd=heap+2 := hrecord.2
  have hbatchFrame : ∀ z<checkedEnd,batchMem z=checkedMem z := hbatch.1.2.2.1
  have hframe : ∀ z<heap,batchMem z=mem z :=
    fun z hz => (hbatchFrame z (by omega)).trans (hscanFrame z hz)
  have hg := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hgEnd
  have hl := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hlEnd
  have he := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd
  have hb := hbatch.1.2.2.2.2
  change ∃ es : List ℕ,es.Nodup ∧ es.toFinset=S ∧
    BatchAt batchMem checkedEnd (refreshEdges (namedInstance I) es) ∧ _ at hb
  obtain ⟨es,hnd,hset,hBatch,_⟩ := hb
  obtain ⟨actual,hscalar,hnorm,hfit,hstep⟩ := hupdate
  have hresult := hstep _ hBatch
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hresult hnorm
  rw [hg,hl] at hresult
  rw [he] at hnorm
  have hanswer := hresult.2
  change final batchEnd=(if _ then 1 else 0) at hanswer
  exact ⟨es,actual,batchEnd,hnd,hset,by rw [← hset,List.toFinset_card_of_nodup hnd],
    hscalar,hnorm,hfit,hresult.1,hheader.trans hanswer⟩

/-- A successful trace identifies its actual state as one exact model
Update at the original coefficients and actual rounded normalization,
with a present direction answer. -/
theorem checkedUpdateTransition_success_model {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (S : Finset ℕ)
    {b source report g l eta heap neg mx mn v : ℕ} {s s' : A.State}
    {mem final : ℕ → ℕ}
    (hgEnd : g+I.m*F.limbs≤heap) (hlEnd : l+I.m*F.limbs≤heap)
    (heEnd : eta+F.limbs≤heap)
    (htrace : checkedUpdateTransition F A I κ α rate allocation S
      b source report g l eta heap neg mx mn s s' mem final v)
    (haccept : final (v-1)=1) :
    ∃ (es : List ℕ) (actual : ℝ) (answer : ℕ),
      es.Nodup ∧ es.toFinset=S ∧ es.length=S.card ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s' ∧
      let result := A.update s (refreshEdges (namedInstance I) es)
        (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
      s'=result.1 ∧ result.2.isSome=true := by
  obtain ⟨checkedEnd,checkedMem,batchEnd,batchMem,hcheck,_,hbatch,hupdate,hheader⟩ :=
    checkedUpdateTransition_success F A I κ α rate allocation S htrace haccept
  have hsame : final (v-1)=final batchEnd := haccept.trans hheader.symm
  obtain ⟨es,actual,answer,hnd,hset,hlen,hscalar,hnorm,hfit,hstate,hbit⟩ :=
    checkedUpdateCalls_model F A I κ α rate allocation S hgEnd hlEnd heEnd hcheck hbatch hupdate hsame
  refine ⟨es,actual,answer,hnd,hset,hlen,hscalar,hnorm,hfit,hstate,?_⟩
  by_contra hn
  rw [haccept,ite_eq_right hn] at hbit
  omega

end MinCostFlow.IPM.Machine
