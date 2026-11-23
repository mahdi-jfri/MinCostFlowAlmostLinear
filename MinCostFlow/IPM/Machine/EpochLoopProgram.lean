module

public import MinCostFlow.IPM.Machine.EpochConditionsIteration
public import MinCostFlow.IPM.Machine.EpochConditionsSuccess
import WordRAM.Tactic

/-!
# Executing the finite guarded epoch loop

Run the actual caller from each maintained loop point. An accepted call
writes a smaller report budget and advances the counter. A stopping
call returns immediately. The budget and concrete DS credit telescope
through those same runs.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual finite loop either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) P.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i P finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i P j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (P.machine.mem (P.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle P.credit P.machine.mem := by
  let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
    (budgetedIterationSpace F I.m L.exponent B) finish
  let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
  let price := budgetedIterationCharge F I.m L.exponent rate
  change ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P → _
  intro fuel
  induction fuel with
  | zero =>
    intro i P hremaining hInv
    have hi : i=finish := by omega
    subst i
    have hc := hInv.2.2.1
    have hn := hInv.2.1
    have hcond : (Expr.bin .lt (.reg 26) (.reg 25)).eval w P.machine=some 0 :=
      Expr.eval_lt_false (x:=finish) (y:=finish)
        (by simp [Expr.eval,hc]) (by simp [Expr.eval,hn]) le_rfl hOne
    refine ⟨.normal,P.machine,4,P.credit,?_,⟨P,.nil hInv,rfl,rfl⟩,?_⟩
    · exact runs_loop_iff.mpr (Or.inl ⟨hcond,rfl,rfl,rfl⟩)
    · simp
  | succ fuel ih =>
    intro i P hremaining hInv
    have hi : i<finish := by omega
    have hiWord := hi.trans hfinish
    have hc := hInv.2.2.1
    have hn := hInv.2.1
    have ht : (Expr.bin .lt (.reg 26) (.reg 25)).eval w P.machine=some 1 :=
      Expr.eval_lt_true (x:=i) (y:=finish)
        (by simp [Expr.eval,hc]) (by simp [Expr.eval,hn]) hi hOne
    obtain ⟨o,st,c,v,s',y,hRun,hOut,hRep,hFoot,hStatus,hFixed,hCard,hWord,hCost⟩ :=
      epochConditions_iteration_runs_upTo_at F A I U κ α Ψ eps rate allocation R hA L q K
        himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
        hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
        initialMem initialHeap finish i B P ω capacity normalization hstatic hInv halloc hspace hbudgetFit hOne hfinishLe
    let n := (A.detect (minRatioState A.eraseFailure P.history P.eta P.op (2*i))).1.card
    have hCharge : c+R.phi L.handle y st.mem≤(n+1)*price+37+R.phi L.handle P.credit P.machine.mem := hCost
    by_cases haccept : st.mem (v-1)=1
    · rw [ite_eq_left haccept] at hStatus
      obtain ⟨rfl,hv⟩ := hStatus
      let next : State := {st with regs := Function.update st.regs 26 (i+1)}
      have hcounter : st.regs 26=i := (hFixed 26 (by decide) (by decide) (by decide)).trans hc
      have hnWord : i+1<2^w := (Nat.succ_le_of_lt hi).trans_lt hfinish
      have hinc : Runs w p ω (.assign 26 (.bin .add (.reg 26) (.const 1))) st .normal next 4 :=
        runs_assign_iff.mpr ⟨i+1,by eval_expr,rfl,rfl,rfl⟩
      have hrunBody : Runs w p ω
          (epochIterationsStep iteration ;; .assign 26 (.bin .add (.reg 26) (.const 1)))
          P.machine .normal next (c+5) :=
        runs_seq_iff.mpr (Or.inr ⟨st,c,4,hRun,hinc,by omega⟩)
      obtain ⟨_,_,_,_,_,hArrays,hScalars,hGuards,_⟩ := hstatic
      have hheapNext : next.regs 8=v := by simpa [next] using hv
      have hcountNext : next.regs 25=finish := by
        simpa [next] using (hFixed 25 (by decide) (by decide) (by decide)).trans hn
      have hfixedNext : ∀ j<25,j≠8 → next.regs j=P.machine.regs j := by
        intro j hj hj8
        simpa only [next,Function.update_of_ne (by omega : j≠26)] using
          hFixed j hj8 (by omega) (by omega)
      obtain ⟨es,actual,hInvNext,hStep⟩ :=
        epochConditions_success_upTo F A I κ α Ψ eps hA rate allocation R L q K B initialHeap finish i initialMem
          P next s' y v hInv hi halloc hspace hOut haccept hRep hFoot hArrays hScalars
          (hGuards L.request (by simp)) hheapNext hcountNext (by simp [next]) hfixedNext
      let Q : EpochPoint R.τ :=
        {history := appendHistoryIteration P.history (2*i) es
          (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
         eta := appendHistoryIterationEta P.eta (2*i) actual
         op := appendHistoryIterationOp P.op (2*i)
         credit := y
         machine := next}
      obtain ⟨o',st',d,credit,hTail,hPost,hBound⟩ := ih (i+1) Q (by omega) hInvNext
      have hb := (budgetedIteration_output hOut).2.2 haccept
      rw [L.packet_heap] at hb
      have hRemain : Q.machine.mem (Q.machine.regs 8-3)+n=P.machine.mem (P.machine.regs 8-3) := by
        change next.mem (next.regs 8-3)+n=_
        rw [hheapNext]
        exact hb
      refine ⟨o',st',c+d+9,credit,?_,?_,?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨1,next,c+5,d,ht,by decide,hrunBody,hTail,by simp; omega⟩))
      · cases o' with
        | normal =>
          obtain ⟨Z,hPath,hState,hCredit⟩ := hPost
          exact ⟨Z,.cons hInv hStep hPath,hState,hCredit⟩
        | returned u =>
          obtain ⟨j,hj,Z,hPath,hInvEnd,hStop⟩ := hPost
          exact ⟨j,hj,Z,.cons hInv hStep hPath,hInvEnd,hStop⟩
      · let extra := match o' with | .normal => 0 | .returned _ => I.m
        change d+R.phi L.handle credit st'.mem≤
          (Q.machine.mem (Q.machine.regs 8-3)+fuel+extra)*price+46*fuel+4+R.phi L.handle y st.mem at hBound
        change c+d+9+R.phi L.handle credit st'.mem≤
          (P.machine.mem (P.machine.regs 8-3)+(fuel+1)+extra)*price+
            46*(fuel+1)+4+R.phi L.handle P.credit P.machine.mem
        have heq : P.machine.mem (P.machine.regs 8-3)+(fuel+1)+extra=
            (n+1)+(Q.machine.mem (Q.machine.regs 8-3)+fuel+extra) := by omega
        rw [heq,Nat.add_mul]
        omega
    · rw [ite_eq_right haccept] at hStatus
      subst o
      have hbit := (budgetedIteration_status hOut).1
      have hzero : st.mem (v-1)=0 := by omega
      have hrunBody : Runs w p ω
          (epochIterationsStep iteration ;; .assign 26 (.bin .add (.reg 26) (.const 1)))
          P.machine (.returned v) st (c+1) :=
        runs_seq_iff.mpr (Or.inl ⟨v,c,hRun,rfl,rfl⟩)
      refine ⟨.returned v,st,c+5,y,?_,⟨i,hi,P,.nil hInv,hInv,hzero,hWord,s',hOut,hRep,hFoot,hCard⟩,?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inl ⟨1,v,c+1,ht,by decide,hrunBody,rfl,by simp; omega⟩))
      · have hle : n+1≤P.machine.mem (P.machine.regs 8-3)+(fuel+1)+I.m := by
          change n≤I.m at hCard
          omega
        have hp := Nat.mul_le_mul_right price hle
        change c+5+R.phi L.handle y st.mem≤
          (P.machine.mem (P.machine.regs 8-3)+(fuel+1)+I.m)*price+
            46*(fuel+1)+4+R.phi L.handle P.credit P.machine.mem
        omega

theorem epochLoop_runs_with_potential_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) P.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i P finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i P j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (P.machine.mem (P.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle P.credit P.machine.mem :=
  epochLoop_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R hA L q K himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    initialMem initialHeap finish B ω capacity normalization hstatic halloc hspace hbudgetFit hOne
    hfinish hfinishLe

/-- The actual finite loop either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) P.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i P finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i P j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (P.machine.mem (P.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle P.credit P.machine.mem :=
  epochLoop_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R (hA.upTo I.m I.n) L q K
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord
    hbody initialMem initialHeap finish B ω capacity normalization hstatic halloc hspace
    hbudgetFit hOne hfinish hfinishLe

/-- The actual finite loop either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) P.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i P finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i P j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (P.machine.mem (P.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle P.credit P.machine.mem :=
  epochLoop_runs_with_potential_upTo F A I U κ α Ψ eps rate allocation R (hA.upTo I.m I.n) L q K
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord
    hbody initialMem initialHeap finish B ω capacity normalization hstatic halloc hspace
    hbudgetFit hOne hfinish hfinishLe

/-- The actual finite loop under `P` either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential_at_range_upTo_on_at {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n) (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (Pt : EpochPoint R.τ), i+fuel=finish → Inv i Pt →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) Pt.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i Pt finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i Pt j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (Pt.machine.mem (Pt.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle Pt.credit Pt.machine.mem := by
  let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
    (budgetedIterationSpace F I.m L.exponent B) finish
  let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
  let price := budgetedIterationCharge F I.m L.exponent rate
  change ∀ fuel i (Pt : EpochPoint R.τ), i+fuel=finish → Inv i Pt → _
  intro fuel
  induction fuel with
  | zero =>
    intro i Pt hremaining hInv
    have hi : i=finish := by omega
    subst i
    have hc := hInv.2.2.1
    have hn := hInv.2.1
    have hcond : (Expr.bin .lt (.reg 26) (.reg 25)).eval w Pt.machine=some 0 :=
      Expr.eval_lt_false (x:=finish) (y:=finish)
        (by simp [Expr.eval,hc]) (by simp [Expr.eval,hn]) le_rfl hOne
    refine ⟨.normal,Pt.machine,4,Pt.credit,?_,⟨Pt,.nil hInv,rfl,rfl⟩,?_⟩
    · exact runs_loop_iff.mpr (Or.inl ⟨hcond,rfl,rfl,rfl⟩)
    · simp
  | succ fuel ih =>
    intro i Pt hremaining hInv
    have hi : i<finish := by omega
    have hiWord := hi.trans hfinish
    have hc := hInv.2.2.1
    have hn := hInv.2.1
    have ht : (Expr.bin .lt (.reg 26) (.reg 25)).eval w Pt.machine=some 1 :=
      Expr.eval_lt_true (x:=i) (y:=finish)
        (by simp [Expr.eval,hc]) (by simp [Expr.eval,hn]) hi hOne
    obtain ⟨o,st,c,v,s',y,hRun,hOut,hRep,hFoot,hStatus,hFixed,hCard,hWord,hCost⟩ :=
      epochConditions_iteration_runs_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R hA hP L q K
        himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
        hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
        initialMem initialHeap finish i B Pt ω capacity normalization hWide hstatic hInv halloc hspace hbudgetFit hOne hfinishLe
    let n := (A.detect (minRatioState A.eraseFailure Pt.history Pt.eta Pt.op (2*i))).1.card
    have hCharge : c+R.phi L.handle y st.mem≤(n+1)*price+37+R.phi L.handle Pt.credit Pt.machine.mem := hCost
    by_cases haccept : st.mem (v-1)=1
    · rw [ite_eq_left haccept] at hStatus
      obtain ⟨rfl,hv⟩ := hStatus
      let next : State := {st with regs := Function.update st.regs 26 (i+1)}
      have hcounter : st.regs 26=i := (hFixed 26 (by decide) (by decide) (by decide)).trans hc
      have hnWord : i+1<2^w := (Nat.succ_le_of_lt hi).trans_lt hfinish
      have hinc : Runs w p ω (.assign 26 (.bin .add (.reg 26) (.const 1))) st .normal next 4 :=
        runs_assign_iff.mpr ⟨i+1,by eval_expr,rfl,rfl,rfl⟩
      have hrunBody : Runs w p ω
          (epochIterationsStep iteration ;; .assign 26 (.bin .add (.reg 26) (.const 1)))
          Pt.machine .normal next (c+5) :=
        runs_seq_iff.mpr (Or.inr ⟨st,c,4,hRun,hinc,by omega⟩)
      obtain ⟨_,_,_,_,_,hArrays,hScalars,hGuards,_⟩ := hstatic
      have hheapNext : next.regs 8=v := by simpa [next] using hv
      have hcountNext : next.regs 25=finish := by
        simpa [next] using (hFixed 25 (by decide) (by decide) (by decide)).trans hn
      have hfixedNext : ∀ j<25,j≠8 → next.regs j=Pt.machine.regs j := by
        intro j hj hj8
        simpa only [next,Function.update_of_ne (by omega : j≠26)] using
          hFixed j hj8 (by omega) (by omega)
      obtain ⟨es,actual,hInvNext,hStep⟩ :=
        epochConditions_success_upTo_on F A I κ α Ψ eps hA hP rate allocation R L q K B initialHeap finish i initialMem
          Pt next s' y v hInv hi halloc hspace hOut haccept hRep hFoot hArrays hScalars
          (hGuards L.request (by simp)) hheapNext hcountNext (by simp [next]) hfixedNext
      let Q : EpochPoint R.τ :=
        {history := appendHistoryIteration Pt.history (2*i) es
          (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
         eta := appendHistoryIterationEta Pt.eta (2*i) actual
         op := appendHistoryIterationOp Pt.op (2*i)
         credit := y
         machine := next}
      obtain ⟨o',st',d,credit,hTail,hPost,hBound⟩ := ih (i+1) Q (by omega) hInvNext
      have hb := (budgetedIteration_output hOut).2.2 haccept
      rw [L.packet_heap] at hb
      have hRemain : Q.machine.mem (Q.machine.regs 8-3)+n=Pt.machine.mem (Pt.machine.regs 8-3) := by
        change next.mem (next.regs 8-3)+n=_
        rw [hheapNext]
        exact hb
      refine ⟨o',st',c+d+9,credit,?_,?_,?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨1,next,c+5,d,ht,by decide,hrunBody,hTail,by simp; omega⟩))
      · cases o' with
        | normal =>
          obtain ⟨Z,hPath,hState,hCredit⟩ := hPost
          exact ⟨Z,.cons hInv hStep hPath,hState,hCredit⟩
        | returned u =>
          obtain ⟨j,hj,Z,hPath,hInvEnd,hStop⟩ := hPost
          exact ⟨j,hj,Z,.cons hInv hStep hPath,hInvEnd,hStop⟩
      · let extra := match o' with | .normal => 0 | .returned _ => I.m
        change d+R.phi L.handle credit st'.mem≤
          (Q.machine.mem (Q.machine.regs 8-3)+fuel+extra)*price+46*fuel+4+R.phi L.handle y st.mem at hBound
        change c+d+9+R.phi L.handle credit st'.mem≤
          (Pt.machine.mem (Pt.machine.regs 8-3)+(fuel+1)+extra)*price+
            46*(fuel+1)+4+R.phi L.handle Pt.credit Pt.machine.mem
        have heq : Pt.machine.mem (Pt.machine.regs 8-3)+(fuel+1)+extra=
            (n+1)+(Q.machine.mem (Q.machine.regs 8-3)+fuel+extra) := by omega
        rw [heq,Nat.add_mul]
        omega
    · rw [ite_eq_right haccept] at hStatus
      subst o
      have hbit := (budgetedIteration_status hOut).1
      have hzero : st.mem (v-1)=0 := by omega
      have hrunBody : Runs w p ω
          (epochIterationsStep iteration ;; .assign 26 (.bin .add (.reg 26) (.const 1)))
          Pt.machine (.returned v) st (c+1) :=
        runs_seq_iff.mpr (Or.inl ⟨v,c,hRun,rfl,rfl⟩)
      refine ⟨.returned v,st,c+5,y,?_,⟨i,hi,Pt,.nil hInv,hInv,hzero,hWord,s',hOut,hRep,hFoot,hCard⟩,?_⟩
      · exact runs_loop_iff.mpr (Or.inr (Or.inl ⟨1,v,c+1,ht,by decide,hrunBody,rfl,by simp; omega⟩))
      · have hle : n+1≤Pt.machine.mem (Pt.machine.regs 8-3)+(fuel+1)+I.m := by
          change n≤I.m at hCard
          omega
        have hp := Nat.mul_le_mul_right price hle
        change c+5+R.phi L.handle y st.mem≤
          (Pt.machine.mem (Pt.machine.regs 8-3)+(fuel+1)+I.m)*price+
            46*(fuel+1)+4+R.phi L.handle Pt.credit Pt.machine.mem
        omega

theorem epochLoop_runs_with_potential_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n) (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (Pt : EpochPoint R.τ), i+fuel=finish → Inv i Pt →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) Pt.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i Pt finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i Pt j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (Pt.machine.mem (Pt.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle Pt.credit Pt.machine.mem :=
  epochLoop_runs_with_potential_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R hA hP
    L q K himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    initialMem initialHeap finish B ω capacity normalization hWide hstatic halloc hspace hbudgetFit
    hOne hfinish hfinishLe

/-- The actual finite loop either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential_at_range_upTo_at {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {initPre : List ℕ → (ℕ → ℕ) → Prop}
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (Pt : EpochPoint R.τ), i+fuel=finish → Inv i Pt →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) Pt.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i Pt finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i Pt j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (Pt.machine.mem (Pt.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle Pt.credit Pt.machine.mem :=
  epochLoop_runs_with_potential_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L q K himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord hbody initialMem initialHeap finish B ω
    capacity normalization hWide hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe

/-- The actual finite loop either completes at the requested count or
returns the first failed call. Its bound charges at most the remaining
report budget and one graph-sized stopping batch, and retains final
DS credit in the same memory as the corresponding trace. -/
theorem epochLoop_runs_with_potential_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (L : EpochLayout) (q K : ℕ)
    {p : Program} {init rawDetect snapshot detect query store coefficient flag edge refresh record combined
      batch batchWriter update core rangeReport scalarRange status checked budgetRecord : ℕ}
    {iteration : ℕ}
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
    (hsnapshot : ∀ s : A.State, MeetsContract w p snapshot (detectSnapshotContract w (A.detect s).1))
    (hbatchBody : p.procs[batch]?=some (detectBatchBody batchWriter))
    (hbatch : ∀ s : A.State, MeetsContract w p batch (detectBatchContract w I (A.detect s).1))
    (hupdate : p.procs[update]?=some (minRatioUpdateBody (dsop 0)))
    (hcore : p.procs[core]?=some (batchUpdateBody batch update))
    (hstatus : p.procs[status]?=some (batchUpdateStatusBody core record))
    (hreportBody : p.procs[rangeReport]?=some (coefficientRangeReportBody scalarRange record))
    (hreport : ∀ s : A.State, MeetsContract w p rangeReport (coefficientRangeReportContract w F.fmt.limbBits (A.detect s).1))
    (hchecked : p.procs[checked]?=some (checkedUpdateBody rangeReport status))
    (hbudgetRecord : MeetsContract w p budgetRecord (epochBudgetRecordContract w))
    (hbody : p.procs[iteration]?=some (budgetedIterationBody combined checked budgetRecord))
    (initialMem : ℕ → ℕ) (initialHeap finish B : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization initialMem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∀ fuel i (P : EpochPoint R.τ), i+fuel=finish → Inv i P →
    ∃ o st c credit,
      Runs w p ω (forUp 26 (.reg 25) (epochIterationsStep iteration)) P.machine o st c ∧
      (match o with
      | .normal => ∃ Q, EpochAcceptedPrefix Inv Step i P finish Q ∧ st=Q.machine ∧ credit=Q.credit
      | .returned v => ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step i P j Q ∧
          Inv j Q ∧ EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      c+R.phi L.handle credit st.mem≤
        (P.machine.mem (P.machine.regs 8-3)+fuel+(match o with
          | .normal => 0
          | .returned _ => I.m))*price+46*fuel+4+R.phi L.handle P.credit P.machine.mem :=
  epochLoop_runs_with_potential_at_range_upTo_on F A I U E κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L q K himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord hbody initialMem initialHeap finish B ω
    capacity normalization hWide hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe

end MinCostFlow.IPM.Machine
