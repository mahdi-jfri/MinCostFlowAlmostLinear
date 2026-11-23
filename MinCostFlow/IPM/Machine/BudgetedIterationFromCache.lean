module

public import MinCostFlow.IPM.Machine.BudgetedIterationProgram
public import MinCostFlow.IPM.Machine.BudgetedIterationCacheHistory

/-!
# Running an actual iteration from the maintained cache

The full cache identifies each held Query value and gives strict slacks
and numerical length accuracy. Nonnegative lower capacities and the
source capacity bounds derive both Query-recovery safety inputs. Thus
the complete iteration runs from the maintained cache without separate
hypotheses about its implicit flow or a potential bound on a wrong guess.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual budgeted iteration is executable from its full held-state
cache, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem := by
  have hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e := by
    intro e he _
    have heM : e<I.m := Finset.mem_range.mp he
    have hup : Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤
        (2:ℝ)^(slackRangeExponent I.m U) :=
      (le_abs_self _).trans ((hsource e he).2.2.trans hcapacity)
    have hl := reportedCachePost_query_length_lower F A _ heM (hCache e he) (hLower e he) hup hAlpha.1 hAlpha.2
    simpa only [hnextLength] using hl
  have hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity := by
    intro e he _
    have hin := (hCache e he).2.2.2.2.2.2
    have hf0 := (hLower e he).trans hin.1.le
    have hfUpper : Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤capacity :=
      hin.2.le.trans ((le_abs_self _).trans (hsource e he).2.2)
    have hfb : |Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity := by
      rw [abs_of_nonneg hf0]
      exact hfUpper
    exact (congrArg abs (hCache e he).2.1.symm).le.trans hfb
  exact budgetedIteration_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R s x hA
    D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx E ld gd
    source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord hpre hI
    hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid
    hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

theorem budgetedIteration_runs_from_cache_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_upTo_at F A I U κ α Ψ eps rate allocation R s x hA D eta op T
    t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore hquery hcoefficient
    hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus
    hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx E ld gd
    source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord hpre hI
    hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid
    hrange hcapacity hsourceEnd hsource hnextLength hAlpha hLower hCache hcoef hspace

/-- The actual budgeted iteration is executable from its full held-state
cache, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache_at {w : ℕ} (F : MinRatioFormat w)
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
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_upTo_at F A I U κ α Ψ eps rate allocation R s x (hA.upTo I.m
    I.n) D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch
    hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r
    a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity normalization
    hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest
    heLo heHi hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hnextLength hAlpha
    hLower hCache hcoef hspace

/-- The actual budgeted iteration is executable from its full held-state
cache, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : F.rangeExponent=ipmRangeExponent I.m U)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_upTo F A I U κ α Ψ eps rate allocation R s x (hA.upTo I.m
    I.n) D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch
    hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r
    a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity normalization
    hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest
    heLo heHi hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hnextLength hAlpha
    hLower hCache hcoef hspace

/-- The actual budgeted iteration is executable from its full held-state
cache under `P`, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache_at_range_upTo_on_at {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (heps : eps≤1)
    (hformat : ipmRangeExponent I.m U≤F.rangeExponent)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem := by
  have hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e := by
    intro e he _
    have heM : e<I.m := Finset.mem_range.mp he
    have hup : Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤
        (2:ℝ)^(slackRangeExponent I.m U) :=
      (le_abs_self _).trans ((hsource e he).2.2.trans hcapacity)
    have hl := reportedCachePost_query_length_lower F A _ heM (hCache e he) (hLower e he) hup hAlpha.1 hAlpha.2
    simpa only [hnextLength] using hl
  have hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity := by
    intro e he _
    have hin := (hCache e he).2.2.2.2.2.2
    have hf0 := (hLower e he).trans hin.1.le
    have hfUpper : Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤capacity :=
      hin.2.le.trans ((le_abs_self _).trans (hsource e he).2.2)
    have hfb : |Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity := by
      rw [abs_of_nonneg hf0]
      exact hfUpper
    exact (congrArg abs (hCache e he).2.1.symm).le.trans hfb
  exact budgetedIteration_runs_with_potential_at_range_upTo_on_at F A I U κ α Ψ eps rate allocation R s x hA
    D eta op T t hs hvalidHistory ht hop hG htBound hPD heps hformat himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx E ld gd
    source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord hpre hI
    hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid
    hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

theorem budgetedIteration_runs_from_cache_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (heps : eps≤1)
    (hformat : ipmRangeExponent I.m U≤F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_at_range_upTo_on_at F A I U κ α Ψ eps rate allocation R s x hA
     D eta op T t hs hvalidHistory ht hop hG htBound hPD heps hformat himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx E ld gd
    source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord hpre hI
    hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid
    hrange hcapacity hsourceEnd hsource hnextLength hAlpha hLower hCache hcoef hspace

/-- The actual budgeted iteration is executable from its full held-state
cache, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache_at_range_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : ipmRangeExponent I.m U≤F.rangeExponent)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_at_range_upTo_on_at F A I U κ α Ψ eps rate allocation R s x
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hs hvalidHistory ht hop hG htBound (fun _ _ => trivial) heps hformat
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up
    f heap c r a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity normalization
    hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi
    hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hnextLength hAlpha hLower hCache hcoef hspace

/-- The actual budgeted iteration is executable from its full held-state
cache, deriving the unconditional implicit-flow and length bounds. -/
theorem budgetedIteration_runs_from_cache_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (s : A.State) (x : R.τ) (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hs : s=minRatioState A.eraseFailure D eta op t)
    (hvalidHistory : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (htBound : t ≤ 2 * I.m) (heps : eps≤1)
    (hformat : ipmRangeExponent I.m U≤F.rangeExponent)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord b q K sourceEnd tableEnd : ℕ}
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
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum : ℕ)
    (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool) (capacity normalization : ℝ)
    (hwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum],z<2^w)
    (hBudgetWord : mem (heap-3)<2^w)
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
    (hnextLength : D.ℓ (t+1)=readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hAlpha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1)
    (hLower : ∀ e∈(namedInstance I).E,0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hCache : ∀ e∈(namedInstance I).E,reportedCachePost F A
      (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e))
      I.m q base lo up f c r a ld gd e mem)
    (hcoef : CoefficientTablesAt F I mem gd ld (D.g t) (D.ℓ t))
    (hspace : (heap+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s [b,heap] mem+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4+2)+(1+6*(A.detect s).1.card)+
      updateAllocationBound w b gd ld request allocation+(1+2*F.limbs)+2+3<2^w) :
    ∃ o st cost s' final,Runs w p ω (budgetedIterationBody combined checked budgetRecord)
      (startState [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem pos) o st cost ∧
      budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
          source,request,neg,maximum,minimum] mem o.value st.mem ∧
      R.rep b s' final st.mem ∧
      (∀ z,R.foot b final z → z<o.value ∧ (R.foot b x z ∨ heap≤z)) ∧
      cost+R.phi b final st.mem≤((A.detect s).1.card+1)*budgetedIterationCharge F I.m E rate+R.phi b x mem :=
  budgetedIteration_runs_from_cache_at_range_upTo_on F A I U κ α Ψ eps rate allocation R s x
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hs hvalidHistory ht hop hG htBound (fun _ _ => trivial) heps hformat
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up
    f heap c r a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity normalization
    hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi
    hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hnextLength hAlpha hLower hCache hcoef hspace

end MinCostFlow.IPM.Machine
