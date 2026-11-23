module

public import MinCostFlow.IPM.Machine.DetectRefreshProgram
public import MinCostFlow.IPM.Machine.DetectCheckedTail
public import MinCostFlow.IPM.Machine.DetectCheckedResult
public import MinCostFlow.IPM.Machine.DetectRefreshQueryInput
public import MinCostFlow.IPM.Machine.DetectRefreshCheckedInput
import MinCostFlow.IPM.Machine.DetectCheckedCost
import WordRAM.Tactic

/-!
# One complete actual Detect/check/Update iteration

Run the verified combined Detect/refresh procedure. Rejection returns
immediately. On acceptance use the preceding history and preserved
source data to establish the implicit-flow bound, then derive every
checked-driver input and execute its actual continuation. Both paths
retain their final concrete credit and have one linear reported-size
charge. Hidden stability is not needed for these input-safety proofs.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete actual iteration stops on its first rejected guard or
Update answer. Every accepted continuation input follows from the
preceding history and source/cache invariants. The statement covers
every random tape and retains the final concrete amortized credit. -/
theorem detectChecked_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked b q K sourceEnd tableEnd : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop
      (minRatioMachineContractAt F A (namedInstance I) I.m κ α rate allocation initPre))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hI : I.IsValid) (hgraph : ListAt mem source (zeroLowerWords I))
    (hgraphEnd : source+(zeroLowerWords I).length≤f) (hgraphWords : ∀ z∈zeroLowerWords I,z<2^w)
    (heEnd : request+F.limbs≤f) (hnEnd : neg+F.limbs≤f)
    (hxEnd : maximum+F.limbs≤f) (hmEnd : minimum+F.limbs≤f)
    (hrequest : ScalarAt mem request F.fmt.limbBits F.limbs F.fmt.precision normalization)
    (heLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization) (heHi : normalization≤(2:ℝ)^F.rangeExponent)
    (hn : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hx : ScalarAt mem maximum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hm : ScalarAt mem minimum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hvalid : ∀ e<I.m,Num.Valid mem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (ld+e*F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e∈(namedInstance I).E,
      |readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ ptr∈[base,lo,up],ptr+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2<2^w) :
    ∃ o st cost s' final,Runs w p ω (detectCheckedBody combined checked)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      detectCheckedResult F A I κ α rate allocation R b s x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      detectCheckedTransition F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*detectCheckedCharge F I.m E rate+R.phi b x mem := by
  have hCwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],z<2^w := by
    intro z hz
    exact hwords z (List.mem_append_left [source,request,neg,maximum,minimum] hz)
  obtain ⟨oC,stC,cC,mid,hrC,hCpost,hCrep,hCmeta,hCcost⟩ :=
    detectRefresh_runs_with_potential_at F A (namedInstance I) I.m κ α rate allocation R himpl hrawDetect hdetect
      hstore hquery hcoefficient hflag hedge hrefresh hrecord s x hsnapshot
      names base lo up f heap c r a one mn mx E ld gd mem pos ω hCwords hpre
  have hd := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  have hCpostCopy := hCpost
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hCpostCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hCzero,_,hCmax⟩ := hCpostCopy
  have hnextSpace : (oC.value+2)+(1+6*(A.detect s).1.card)+updateAllocationBound w b gd ld request allocation+
      (1+2*F.limbs)+2<2^w := by omega
  have hvWord : oC.value<2^w := by omega
  have hw2 : 2<2^w := by omega
  change cC+R.phi b mid stC.mem≤((A.detect s).1.card+1)*
    (2*rate I.m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
      Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+4200)+R.phi b x mem at hCcost
  let start := startState
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum] mem pos
  let afterC : State := ⟨stC.mem,Function.update start.regs 25 oC.value,stC.pos⟩
  have hcall : Runs w p ω
      (.call 25 combined [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
        .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19]) start .normal afterC (20+cC+1) := by
    apply runs_call_iff.mpr
    refine ⟨[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],
      detectRefreshBody detect refresh record,oC,stC,cC,by dsimp only [start]; eval_expr,hcombined,hrC,rfl,?_,rfl⟩
    cases stC
    rfl
  by_cases haccept : stC.mem (oC.value-1)=1
  · have hq : ∀ e∈(namedInstance I).E,|A.query (A.detect s).2 e|≤(2:ℝ)^F.rangeExponent := by
      subst s
      exact detectRefresh_query_range_of_sources F A I U κ α Ψ eps rate allocation R hA D eta op T t
        hvalidHistory ht hop hG heps hformat capacity hpre hCpost haccept hcapacity hsourceEnd hsource hell hcache
    obtain ⟨hCheckedPre,hCheckedWords⟩ := checkedUpdate_pre_after_detectRefresh F A I κ α rate allocation R
      hpre hCpost haccept hCrep (fun z hz => (hCmeta z hz).1) (hCwords b (by simp)) (hCwords I.m (by simp))
      hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hq hvalid hrange
      ⟨D,eta,op,t,hvalidHistory.mono D op T t (by omega),hG t (by omega),hs,hcoef,
        by rw [namedInstance_m]; exact htBound⟩ hnextSpace
    obtain ⟨o,st,cTail,s',final,hrTail,hTpost,hTrep,hTransition,hTmeta,hTcost⟩ := detectCheckedTail_success_runs_at F A I κ α rate allocation R
      himpl (A.detect s).1 hbatchBody hbatch hupdate hcore hrecord hstatus hreportBody hreport hchecked
      (A.detect s).2 mid source (stC.mem (oC.value-2)) gd ld request oC.value neg maximum minimum afterC ω hw2
      (by simp [afterC,start,startState]) (by simp [afterC]) haccept rfl hCheckedWords hCheckedPre
    have hTstatus := checkedUpdate_status F A I κ α rate allocation R hTpost
    refine ⟨o,st,cC+cTail+22,s',final,?_,?_,hTrep,?_,?_,?_⟩
    · unfold detectCheckedBody
      exact runs_seq_iff.mpr (Or.inr ⟨afterC,20+cC+1,cTail,hcall,hrTail,by omega⟩)
    · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_,hTstatus.1,hTstatus.2⟩
      rw [ite_eq_left haccept]
      exact hTpost
    · refine ⟨oC.value,stC.mem,hCpost,?_⟩
      rw [ite_eq_left haccept]
      exact ⟨mid,hCheckedPre,hTransition⟩
    · intro z hz
      refine ⟨(hTmeta z hz).1,?_⟩
      rcases (hTmeta z hz).2 with hold | hfresh
      · exact (hCmeta z hold).2
      · have hBefore : heap≤oC.value := by
          obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hCpost
          exact hLo
        exact Or.inr (hBefore.trans hfresh)
    · dsimp only [afterC] at hTcost
      exact detectChecked_cost_sum hCcost hTcost
  · have hreject : stC.mem (oC.value-1)=0 := by have hb := hd.2.1; omega
    obtain ⟨o,st,cTail,hrTail,⟨ho,hmemory,_⟩,hTailCost⟩ :=
      detectCheckedTail_failure_runs afterC ω (by omega) hvWord (by simp [afterC]) hreject
    have hv : o.value=oC.value := by rw [ho]; rfl
    have hbit : st.mem (o.value-1)≤1 := by rw [hmemory,hv]; exact hd.2.1
    have hzero : ZeroFrom st.mem o.value := by rw [hmemory,hv]; exact hCzero
    have hcredit : cTail+R.phi b mid st.mem≤(A.detect s).1.card*(164*F.limbs+680)+
        rate I.m*(1+2*(A.detect s).1.card)+R.phi b mid stC.mem+1050 := by
      rw [hmemory]
      dsimp only [afterC]
      omega
    refine ⟨o,st,cC+cTail+22,(A.detect s).2,mid,?_,?_,?_,?_,?_,?_⟩
    · unfold detectCheckedBody
      exact runs_seq_iff.mpr (Or.inr ⟨afterC,20+cC+1,cTail,hcall,hrTail,by omega⟩)
    · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_,hbit,hzero⟩
      rw [ite_eq_right haccept]
      exact ⟨hv,hmemory⟩
    · rw [hmemory]
      exact hCrep
    · refine ⟨oC.value,stC.mem,hCpost,?_⟩
      rw [ite_eq_right haccept]
      exact ⟨rfl,hv,hmemory⟩
    · intro z hz
      rw [hv]
      exact hCmeta z hz
    · exact detectChecked_cost_sum hCcost hcredit

theorem detectChecked_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked b q K sourceEnd tableEnd : ℕ}
    {dsop : ℕ → ℕ}
    (himpl : R.Implements w p init dsop (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrawDetect : p.procs[rawDetect]?=some (minRatioDetectBody (dsop 2)))
    (hdetect : p.procs[detect]?=some (detectNamesBody rawDetect snapshot))
    (hstore : MeetsContract w p store (storeCoordinateContract w F.fmt.limbBits))
    (hquery : p.procs[query]?=some (queryCoordinateBody (dsop 1) store))
    (hcoefficient : MeetsContract w p coefficient (coefficientStatusContract w F.fmt.limbBits q K))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hedge : p.procs[edge]?=some (reportedEdgeBody query coefficient flag))
    (hrefresh : p.procs[refresh]?=some (reportedEdgesBody edge flag))
    (hrecord : MeetsContract w p record (reportStatusContract w))
    (hcombined : p.procs[combined]?=some (detectRefreshBody detect refresh record))
    (hsnapshot : MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hI : I.IsValid) (hgraph : ListAt mem source (zeroLowerWords I))
    (hgraphEnd : source+(zeroLowerWords I).length≤f) (hgraphWords : ∀ z∈zeroLowerWords I,z<2^w)
    (heEnd : request+F.limbs≤f) (hnEnd : neg+F.limbs≤f)
    (hxEnd : maximum+F.limbs≤f) (hmEnd : minimum+F.limbs≤f)
    (hrequest : ScalarAt mem request F.fmt.limbBits F.limbs F.fmt.precision normalization)
    (heLo : (2:ℝ)^(-(F.rangeExponent:ℤ))≤normalization) (heHi : normalization≤(2:ℝ)^F.rangeExponent)
    (hn : ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hx : ScalarAt mem maximum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hm : ScalarAt mem minimum F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hk : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprec : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hvalid : ∀ e<I.m,Num.Valid mem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (ld+e*F.limbs) F.fmt.limbBits F.limbs)
    (hrange : ∀ e∈(namedInstance I).E,
      |readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ ptr∈[base,lo,up],ptr+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2<2^w) :
    ∃ o st cost s' final,Runs w p ω (detectCheckedBody combined checked)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      detectCheckedResult F A I κ α rate allocation R b s x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      detectCheckedTransition F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem st.mem o.value ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*detectCheckedCharge F I.m E rate+R.phi b x mem :=
  detectChecked_runs_with_potential_at F A I U κ α Ψ eps rate allocation R s x hA D eta op T t hs
    hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore hquery hcoefficient hflag
    hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody
    hreport hchecked names base lo up f heap c r a one mn mx E ld gd source request neg maximum
    minimum mem pos ω capacity normalization hwords hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd
    hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hell
    hcache hcoef hspace

end MinCostFlow.IPM.Machine
