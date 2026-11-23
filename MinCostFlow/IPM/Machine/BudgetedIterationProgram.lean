module

public import MinCostFlow.IPM.Machine.DetectCheckedProgram
public import MinCostFlow.IPM.Machine.BudgetedIterationResult
public import MinCostFlow.IPM.Machine.BudgetedIteration
import MinCostFlow.IPM.Machine.BudgetedIterationRead
import MinCostFlow.IPM.Machine.BudgetedIterationReject
import MinCostFlow.IPM.Machine.BudgetedIterationAccepted
import MinCostFlow.IPM.Machine.BudgetedIterationCost
import WordRAM.Tactic

/-!
# A complete actual iteration with the report-size budget guard

Read the previous fresh budget record, execute Detect/refresh and decode
its actual report count. A failed refresh or over-budget report returns
before Update. The fitting branch executes the verified checked driver.
Every path appends fresh budget metadata and retains the same concrete
state and credit, with a single linear reported-size charge.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete budgeted machine iteration stops before an over-budget
Update and retains the exact selected state transition and concrete
credit on every branch, for every tape. -/
theorem budgetedIteration_runs_with_potential_upTo_at {w : ℕ} (F : MinRatioFormat w)
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  let remaining := mem (heap-3)
  let count := (A.detect s).1.card
  have hCwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],z<2^w :=
    fun z hz => hwords z (List.mem_append_left [source,request,neg,maximum,minimum] hz)
  obtain ⟨oC,stC,cC,mid,hrC,hCpost,hCrep,hCmeta,hCcost⟩ :=
    detectRefresh_runs_with_potential_at F A (namedInstance I) I.m κ α rate allocation R himpl hrawDetect hdetect
      hstore hquery hcoefficient hflag hedge hrefresh hrecord s x hsnapshot
      names base lo up f heap c r a one mn mx E ld gd mem pos ω hCwords hpre
  have hd := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  have hCpostCopy := hCpost
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hCpostCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hCzero,hCbefore,hCmax⟩ := hCpostCopy
  have hbefore : heap≤oC.value := hCbefore
  have hnextSpace : (oC.value+2)+(1+6*count)+updateAllocationBound w b gd ld request allocation+
      (1+2*F.limbs)+2+3<2^w := by dsimp only [count]; omega
  have hvWord : oC.value<2^w := by omega
  have hThree : 3<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hOne : 1<2^w := by omega
  have hheapWord : heap<2^w := hwords _ (by simp)
  have hremainingWord : remaining<2^w := hBudgetWord
  have hsubset : (A.detect s).1⊆(namedInstance I).E := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩ := hpre
    exact hh
  have hcountM : count≤I.m := by
    simpa only [count,namedInstance,Finset.card_range] using Finset.card_le_card hsubset
  have hcountWord : count<2^w := hcountM.trans_lt (hwords _ (by simp))
  let report := stC.mem (oC.value-2)
  have hheader : stC.mem report=count := by
    obtain ⟨es,hnd,hset,hh,_⟩ := hd.1
    rw [hh]
    exact (List.toFinset_card_of_nodup hnd).symm.trans (congrArg Finset.card hset)
  change cC+R.phi b mid stC.mem≤(count+1)*
    (2*rate I.m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
      Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+4200)+R.phi b x mem at hCcost
  let original := startState
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum] mem pos
  let afterBudget : State := {original with regs:=Function.update original.regs 25 remaining}
  let afterC : State := ⟨stC.mem,Function.update afterBudget.regs 26 oC.value,stC.pos⟩
  let reported : State := {afterC with regs:=Function.update (Function.update (Function.update afterC.regs 27 report) 28 count) 29 (stC.mem (oC.value-1))}
  have hreadBudget : Runs w p ω budgetedIterationReadBudget original .normal afterBudget 5 :=
    budgetedIterationReadBudget_runs p original ω heap remaining (by simp [original,startState]) rfl hheapWord hThree
  have hcall : Runs w p ω
      (.call 26 combined [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
        .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19]) afterBudget .normal afterC (21+cC) := by
    apply runs_call_iff.mpr
    refine ⟨[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],
      detectRefreshBody detect refresh record,oC,stC,cC,
      by dsimp only [afterBudget,original]; eval_expr,hcombined,hrC,rfl,?_,by simp [argsSize]; omega⟩
    cases stC
    rfl
  have hreadReport : Runs w p ω budgetedIterationReadReport afterC .normal reported 15 :=
    budgetedIterationReadReport_runs p afterC ω oC.value report count (stC.mem (oC.value-1))
      (by simp [afterC]) rfl hheader rfl hvWord hTwo
  let branch := Stmt.cond (.reg 29)
    (.cond (.bin .lt (.reg 25) (.reg 28))
      (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
    (budgetedIterationReject budgetRecord)
  have hfull (o : Outcome) (st : State) (cBranch : ℕ) (hr : Runs w p ω branch reported o st cBranch) :
      Runs w p ω (budgetedIterationBody combined checked budgetRecord) original o st (cC+cBranch+44) := by
    unfold budgetedIterationBody
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterBudget,5,(21+cC)+(15+cBranch+1)+1,hreadBudget,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterC,21+cC,15+cBranch+1,hcall,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨reported,15,cBranch,hreadReport,hr,rfl⟩)
  have hrejectWords : ∀ z∈[remaining,count,0,oC.value],z<2^w := by wram_words
  have hrecordSpace : oC.value+3<2^w := by omega
  by_cases hCaccept : stC.mem (oC.value-1)=1
  · have hq : ∀ e∈(namedInstance I).E,|A.query (A.detect s).2 e|≤(2:ℝ)^F.rangeExponent := by
      subst s
      exact detectRefresh_query_range_of_sources_upTo F A I U κ α Ψ eps rate allocation R hA D eta op T t
        hvalidHistory ht hop hG heps hformat capacity hpre hCpost hCaccept hcapacity hsourceEnd hsource hell hcache
    obtain ⟨hCheckedPre,hCheckedWords⟩ := checkedUpdate_pre_after_detectRefresh F A I κ α rate allocation R
      hpre hCpost hCaccept hCrep (fun z hz => (hCmeta z hz).1) (hCwords b (by simp)) (hCwords I.m (by simp))
      hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hq hvalid hrange
      ⟨D,eta,op,t,hvalidHistory.mono D op T t (by omega),hG t (by omega),hs,hcoef,
        by rw [namedInstance_m]; exact htBound⟩
      (by dsimp only [count] at hnextSpace; omega)
    by_cases hfits : count≤remaining
    · obtain ⟨oQ,stQ,cQ,s',final,hrQ,hQpost,hQrep,hQtrace,hQmeta,hQcost⟩ :=
        checkedUpdate_runs_with_potential_at F A I κ α rate allocation R himpl (A.detect s).1 hbatchBody hbatch hupdate
          hcore hrecord hstatus hreportBody hreport (A.detect s).2 mid
          source report gd ld request oC.value neg maximum minimum stC.mem stC.pos ω hCheckedWords hCheckedPre
      obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost,_⟩ := budgetedIterationAccepted_runs F A I κ α rate allocation R
        himpl.1 hchecked hbudgetRecord (A.detect s).1 b source report gd ld request oC.value neg maximum minimum
        remaining count _ reported ω (A.detect s).2 mid
        (by dsimp only [budgetedIterationCheckedArgs,reported,afterC,afterBudget,original]; eval_expr)
        (by simp [reported,afterC,afterBudget]) hremainingWord hcountWord hfits hrQ hQpost hQrep
        (fun z hz => (hQmeta z hz).1) hQcost hnextSpace
      have hinner : Runs w p ω (.cond (.bin .lt (.reg 25) (.reg 28))
          (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
          reported o st (cTail+4) := by
        apply runs_cond_iff.mpr
        refine ⟨0,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
        exact Expr.eval_lt_false (x:=remaining) (y:=count)
          (by simp [Expr.eval,reported,afterC,afterBudget]) (by simp [Expr.eval,reported]) hfits hOne
      have hbranch : Runs w p ω branch reported o st (cTail+6) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail+4,?_,by simpa using hinner,by simp [Expr.size]; omega⟩
        simp [Expr.eval,reported,hCaccept]
      refine ⟨o,st,cC+cTail+50,s',final,?_,?_,hRep,?_,?_⟩
      · simpa only [Nat.add_assoc] using hfull o st (cTail+6) hbranch
      · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_left (And.intro hCaccept hfits)]
        exact ⟨oQ.value,stQ.mem,hCheckedPre,hQpost,hQtrace,hRecord⟩
      · intro z hz
        refine ⟨hFoot z hz,?_⟩
        rcases (hQmeta z hz).2 with hold | hfresh
        · exact (hCmeta z hold).2
        · exact Or.inr (hbefore.trans hfresh)
      · have ht : cTail+R.phi b final st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := hTailCost
        exact budgetedIteration_cost_sum hCcost ht
    · obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost⟩ := budgetedIterationReject_runs R himpl.1 hbudgetRecord
        reported ω remaining count oC.value b (by simp [reported,afterC,afterBudget]) hrejectWords hCzero hrecordSpace hCrep
        (fun z hz => (hCmeta z hz).1)
      have hlt : remaining<count := Nat.lt_of_not_ge hfits
      have hinner : Runs w p ω (.cond (.bin .lt (.reg 25) (.reg 28))
          (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
          reported o st (cTail+4) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
        exact Expr.eval_lt_true (x:=remaining) (y:=count)
          (by simp [Expr.eval,reported,afterC,afterBudget]) (by simp [Expr.eval,reported]) hlt hOne
      have hbranch : Runs w p ω branch reported o st (cTail+6) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail+4,?_,by simpa using hinner,by simp [Expr.size]; omega⟩
        simp [Expr.eval,reported,hCaccept]
      refine ⟨o,st,cC+cTail+50,(A.detect s).2,mid,?_,?_,hRep,?_,?_⟩
      · simpa only [Nat.add_assoc] using hfull o st (cTail+6) hbranch
      · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right (fun hh => hfits hh.2)]
        exact ⟨trivial,hRecord⟩
      · exact fun z hz => ⟨hFoot z hz,(hCmeta z hz).2⟩
      · have ht : cTail+R.phi b mid st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := by
          dsimp only [reported,afterC] at hTailCost
          omega
        exact budgetedIteration_cost_sum hCcost ht
  · obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost⟩ := budgetedIterationReject_runs R himpl.1 hbudgetRecord
      reported ω remaining count oC.value b (by simp [reported,afterC,afterBudget]) hrejectWords hCzero hrecordSpace hCrep
      (fun z hz => (hCmeta z hz).1)
    have hzero : stC.mem (oC.value-1)=0 := by have hb := hd.2.1; omega
    have hbranch : Runs w p ω branch reported o st (cTail+2) := by
      apply runs_cond_iff.mpr
      refine ⟨0,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
      simp [Expr.eval,reported,hzero]
    refine ⟨o,st,cC+cTail+46,(A.detect s).2,mid,?_,?_,hRep,?_,?_⟩
    · simpa only [Nat.add_assoc] using hfull o st (cTail+2) hbranch
    · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ite_eq_right (fun hh => hCaccept hh.1)]
      exact ⟨trivial,hRecord⟩
    · exact fun z hz => ⟨hFoot z hz,(hCmeta z hz).2⟩
    · have ht : cTail+R.phi b mid st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := by
        dsimp only [reported,afterC] at hTailCost
        omega
      have hh := budgetedIteration_cost_sum hCcost ht
      exact (Nat.add_le_add_right (by omega : cC+cTail+46≤cC+cTail+50) _).trans hh

theorem budgetedIteration_runs_with_potential_upTo {w : ℕ} (F : MinRatioFormat w)
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  budgetedIteration_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R s x hA
    D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx
    E ld gd source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord
    hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk
    hprec hvalid hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

/-- The complete budgeted machine iteration stops before an over-budget
Update and retains the exact selected state transition and concrete
credit on every branch, for every tape. -/
theorem budgetedIteration_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  budgetedIteration_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R s x (hA.upTo
    I.m I.n) D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
    hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx
    E ld gd source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord
    hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk
    hprec hvalid hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

theorem budgetedIteration_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  budgetedIteration_runs_with_potential_upTo F A I U κ α Ψ eps rate allocation R s x (hA.upTo
    I.m I.n) D eta op T t hs hvalidHistory ht hop hG htBound heps hformat himpl hrawDetect hdetect
    hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody
    hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f
    heap c r a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity
    normalization hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd
    hmEnd hrequest heLo heHi hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hell
    hcache hcoef hspace

/-- The complete budgeted machine iteration under `P` stops before an over-budget
Update and retains the exact selected state transition and concrete
credit on every branch, for every tape. -/
theorem budgetedIteration_runs_with_potential_at_range_upTo_on_at {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  let remaining := mem (heap-3)
  let count := (A.detect s).1.card
  have hCwords : ∀ z∈[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],z<2^w :=
    fun z hz => hwords z (List.mem_append_left [source,request,neg,maximum,minimum] hz)
  obtain ⟨oC,stC,cC,mid,hrC,hCpost,hCrep,hCmeta,hCcost⟩ :=
    detectRefresh_runs_with_potential_at F A (namedInstance I) I.m κ α rate allocation R himpl hrawDetect hdetect
      hstore hquery hcoefficient hflag hedge hrefresh hrecord s x hsnapshot
      names base lo up f heap c r a one mn mx E ld gd mem pos ω hCwords hpre
  have hd := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  have hCpostCopy := hCpost
  simp only [detectRefreshContract,List.getD_cons_zero,List.getD_cons_succ] at hCpostCopy
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hCzero,hCbefore,hCmax⟩ := hCpostCopy
  have hbefore : heap≤oC.value := hCbefore
  have hnextSpace : (oC.value+2)+(1+6*count)+updateAllocationBound w b gd ld request allocation+
      (1+2*F.limbs)+2+3<2^w := by dsimp only [count]; omega
  have hvWord : oC.value<2^w := by omega
  have hThree : 3<2^w := by omega
  have hTwo : 2<2^w := by omega
  have hOne : 1<2^w := by omega
  have hheapWord : heap<2^w := hwords _ (by simp)
  have hremainingWord : remaining<2^w := hBudgetWord
  have hsubset : (A.detect s).1⊆(namedInstance I).E := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hh,_⟩ := hpre
    exact hh
  have hcountM : count≤I.m := by
    simpa only [count,namedInstance,Finset.card_range] using Finset.card_le_card hsubset
  have hcountWord : count<2^w := hcountM.trans_lt (hwords _ (by simp))
  let report := stC.mem (oC.value-2)
  have hheader : stC.mem report=count := by
    obtain ⟨es,hnd,hset,hh,_⟩ := hd.1
    rw [hh]
    exact (List.toFinset_card_of_nodup hnd).symm.trans (congrArg Finset.card hset)
  change cC+R.phi b mid stC.mem≤(count+1)*
    (2*rate I.m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
      Num.IPM.gradientCost F.limbs F.fmt.precision E+1534*F.limbs+4200)+R.phi b x mem at hCcost
  let original := startState
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
      source,request,neg,maximum,minimum] mem pos
  let afterBudget : State := {original with regs:=Function.update original.regs 25 remaining}
  let afterC : State := ⟨stC.mem,Function.update afterBudget.regs 26 oC.value,stC.pos⟩
  let reported : State := {afterC with regs:=Function.update (Function.update (Function.update afterC.regs 27 report) 28 count) 29 (stC.mem (oC.value-1))}
  have hreadBudget : Runs w p ω budgetedIterationReadBudget original .normal afterBudget 5 :=
    budgetedIterationReadBudget_runs p original ω heap remaining (by simp [original,startState]) rfl hheapWord hThree
  have hcall : Runs w p ω
      (.call 26 combined [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 7,.reg 8,.reg 9,
        .reg 10,.reg 11,.reg 12,.reg 13,.reg 14,.reg 15,.reg 16,.reg 17,.reg 18,.reg 19]) afterBudget .normal afterC (21+cC) := by
    apply runs_call_iff.mpr
    refine ⟨[b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m],
      detectRefreshBody detect refresh record,oC,stC,cC,
      by dsimp only [afterBudget,original]; eval_expr,hcombined,hrC,rfl,?_,by simp [argsSize]; omega⟩
    cases stC
    rfl
  have hreadReport : Runs w p ω budgetedIterationReadReport afterC .normal reported 15 :=
    budgetedIterationReadReport_runs p afterC ω oC.value report count (stC.mem (oC.value-1))
      (by simp [afterC]) rfl hheader rfl hvWord hTwo
  let branch := Stmt.cond (.reg 29)
    (.cond (.bin .lt (.reg 25) (.reg 28))
      (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
    (budgetedIterationReject budgetRecord)
  have hfull (o : Outcome) (st : State) (cBranch : ℕ) (hr : Runs w p ω branch reported o st cBranch) :
      Runs w p ω (budgetedIterationBody combined checked budgetRecord) original o st (cC+cBranch+44) := by
    unfold budgetedIterationBody
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterBudget,5,(21+cC)+(15+cBranch+1)+1,hreadBudget,?_,by omega⟩
    apply runs_seq_iff.mpr
    refine Or.inr ⟨afterC,21+cC,15+cBranch+1,hcall,?_,rfl⟩
    exact runs_seq_iff.mpr (Or.inr ⟨reported,15,cBranch,hreadReport,hr,rfl⟩)
  have hrejectWords : ∀ z∈[remaining,count,0,oC.value],z<2^w := by wram_words
  have hrecordSpace : oC.value+3<2^w := by omega
  by_cases hCaccept : stC.mem (oC.value-1)=1
  · have hq : ∀ e∈(namedInstance I).E,|A.query (A.detect s).2 e|≤(2:ℝ)^F.rangeExponent := by
      subst s
      exact detectRefresh_query_range_of_sources_at_range_upTo_on F A I U κ α Ψ eps rate allocation R hA D eta op T t
        hvalidHistory ht hop hG hPD heps hformat capacity hpre hCpost hCaccept hcapacity hsourceEnd hsource hell hcache
    obtain ⟨hCheckedPre,hCheckedWords⟩ := checkedUpdate_pre_after_detectRefresh F A I κ α rate allocation R
      hpre hCpost hCaccept hCrep (fun z hz => (hCmeta z hz).1) (hCwords b (by simp)) (hCwords I.m (by simp))
      hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk hprec hq hvalid hrange
      ⟨D,eta,op,t,hvalidHistory.mono D op T t (by omega),hG t (by omega),hs,hcoef,
        by rw [namedInstance_m]; exact htBound⟩
      (by dsimp only [count] at hnextSpace; omega)
    by_cases hfits : count≤remaining
    · obtain ⟨oQ,stQ,cQ,s',final,hrQ,hQpost,hQrep,hQtrace,hQmeta,hQcost⟩ :=
        checkedUpdate_runs_with_potential_at F A I κ α rate allocation R himpl (A.detect s).1 hbatchBody hbatch hupdate
          hcore hrecord hstatus hreportBody hreport (A.detect s).2 mid
          source report gd ld request oC.value neg maximum minimum stC.mem stC.pos ω hCheckedWords hCheckedPre
      obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost,_⟩ := budgetedIterationAccepted_runs F A I κ α rate allocation R
        himpl.1 hchecked hbudgetRecord (A.detect s).1 b source report gd ld request oC.value neg maximum minimum
        remaining count _ reported ω (A.detect s).2 mid
        (by dsimp only [budgetedIterationCheckedArgs,reported,afterC,afterBudget,original]; eval_expr)
        (by simp [reported,afterC,afterBudget]) hremainingWord hcountWord hfits hrQ hQpost hQrep
        (fun z hz => (hQmeta z hz).1) hQcost hnextSpace
      have hinner : Runs w p ω (.cond (.bin .lt (.reg 25) (.reg 28))
          (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
          reported o st (cTail+4) := by
        apply runs_cond_iff.mpr
        refine ⟨0,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
        exact Expr.eval_lt_false (x:=remaining) (y:=count)
          (by simp [Expr.eval,reported,afterC,afterBudget]) (by simp [Expr.eval,reported]) hfits hOne
      have hbranch : Runs w p ω branch reported o st (cTail+6) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail+4,?_,by simpa using hinner,by simp [Expr.size]; omega⟩
        simp [Expr.eval,reported,hCaccept]
      refine ⟨o,st,cC+cTail+50,s',final,?_,?_,hRep,?_,?_⟩
      · simpa only [Nat.add_assoc] using hfull o st (cTail+6) hbranch
      · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_left (And.intro hCaccept hfits)]
        exact ⟨oQ.value,stQ.mem,hCheckedPre,hQpost,hQtrace,hRecord⟩
      · intro z hz
        refine ⟨hFoot z hz,?_⟩
        rcases (hQmeta z hz).2 with hold | hfresh
        · exact (hCmeta z hold).2
        · exact Or.inr (hbefore.trans hfresh)
      · have ht : cTail+R.phi b final st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := hTailCost
        exact budgetedIteration_cost_sum hCcost ht
    · obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost⟩ := budgetedIterationReject_runs R himpl.1 hbudgetRecord
        reported ω remaining count oC.value b (by simp [reported,afterC,afterBudget]) hrejectWords hCzero hrecordSpace hCrep
        (fun z hz => (hCmeta z hz).1)
      have hlt : remaining<count := Nat.lt_of_not_ge hfits
      have hinner : Runs w p ω (.cond (.bin .lt (.reg 25) (.reg 28))
          (budgetedIterationReject budgetRecord) (budgetedIterationAccepted checked budgetRecord))
          reported o st (cTail+4) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
        exact Expr.eval_lt_true (x:=remaining) (y:=count)
          (by simp [Expr.eval,reported,afterC,afterBudget]) (by simp [Expr.eval,reported]) hlt hOne
      have hbranch : Runs w p ω branch reported o st (cTail+6) := by
        apply runs_cond_iff.mpr
        refine ⟨1,cTail+4,?_,by simpa using hinner,by simp [Expr.size]; omega⟩
        simp [Expr.eval,reported,hCaccept]
      refine ⟨o,st,cC+cTail+50,(A.detect s).2,mid,?_,?_,hRep,?_,?_⟩
      · simpa only [Nat.add_assoc] using hfull o st (cTail+6) hbranch
      · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        rw [ite_eq_right (fun hh => hfits hh.2)]
        exact ⟨trivial,hRecord⟩
      · exact fun z hz => ⟨hFoot z hz,(hCmeta z hz).2⟩
      · have ht : cTail+R.phi b mid st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := by
          dsimp only [reported,afterC] at hTailCost
          omega
        exact budgetedIteration_cost_sum hCcost ht
  · obtain ⟨o,st,cTail,hrTail,hRecord,hRep,hFoot,hTailCost⟩ := budgetedIterationReject_runs R himpl.1 hbudgetRecord
      reported ω remaining count oC.value b (by simp [reported,afterC,afterBudget]) hrejectWords hCzero hrecordSpace hCrep
      (fun z hz => (hCmeta z hz).1)
    have hzero : stC.mem (oC.value-1)=0 := by have hb := hd.2.1; omega
    have hbranch : Runs w p ω branch reported o st (cTail+2) := by
      apply runs_cond_iff.mpr
      refine ⟨0,cTail,?_,by simpa using hrTail,by simp [Expr.size]; omega⟩
      simp [Expr.eval,reported,hzero]
    refine ⟨o,st,cC+cTail+46,(A.detect s).2,mid,?_,?_,hRep,?_,?_⟩
    · simpa only [Nat.add_assoc] using hfull o st (cTail+2) hbranch
    · refine ⟨oC.value,stC.mem,mid,hCpost,hCrep,hCmeta,?_⟩
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ite_eq_right (fun hh => hCaccept hh.1)]
      exact ⟨trivial,hRecord⟩
    · exact fun z hz => ⟨hFoot z hz,(hCmeta z hz).2⟩
    · have ht : cTail+R.phi b mid st.mem≤count*(164*F.limbs+680)+rate I.m*(1+2*count)+R.phi b mid stC.mem+1092 := by
        dsimp only [reported,afterC] at hTailCost
        omega
      have hh := budgetedIteration_cost_sum hCcost ht
      exact (Nat.add_le_add_right (by omega : cC+cTail+46≤cC+cTail+50) _).trans hh

theorem budgetedIteration_runs_with_potential_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  budgetedIteration_runs_with_potential_at_range_upTo_on_at F A I U κ α Ψ eps rate allocation R s x
    hA D eta op T t hs hvalidHistory ht hop hG htBound hPD heps hformat himpl hrawDetect hdetect hstore
    hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate
    hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up f heap c r a one mn mx
    E ld gd source request neg maximum minimum mem pos ω capacity normalization hwords hBudgetWord
    hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi hn hx hm hk
    hprec hvalid hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

/-- The complete budgeted machine iteration stops before an over-budget
Update and retains the exact selected state transition and concrete
credit on every branch, for every tape. -/
theorem budgetedIteration_runs_with_potential_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
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
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect s).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity)
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
  budgetedIteration_runs_with_potential_at_range_upTo_on F A I U κ α Ψ eps rate allocation R s x
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hs hvalidHistory ht hop hG htBound (fun _ _ => trivial) heps hformat
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord names base lo up
    f heap c r a one mn mx E ld gd source request neg maximum minimum mem pos ω capacity normalization
    hwords hBudgetWord hpre hI hgraph hgraphEnd hgraphWords heEnd hnEnd hxEnd hmEnd hrequest heLo heHi
    hn hx hm hk hprec hvalid hrange hcapacity hsourceEnd hsource hell hcache hcoef hspace

end MinCostFlow.IPM.Machine
