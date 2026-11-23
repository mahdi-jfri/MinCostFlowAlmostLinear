module

public import MinCostFlow.IPM.Machine.EpochLoopProgram
public import MinCostFlow.IPM.Machine.EpochConditionsInitial
public import MinCostFlow.IPM.Machine.EpochIterationsFinish

/-!
# The full finite epoch iteration entry

An actual call initializes the counter, executes the verified guarded
loop, and writes the final success flag only on normal completion.
The return retains the actual successful prefix and, if present, the
first failed call. Both outcomes retain the same concrete DS credit.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The entire finite epoch entry runs from its first-call inputs,
with exact success or stopping trace and a linear report charge. -/
theorem epochIterations_runs_with_potential_upTo_at {w : ℕ} (F : MinRatioFormat w)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem := by
  let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
    (budgetedIterationSpace F I.m L.exponent B) finish
  let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
  let price := budgetedIterationCharge F I.m L.exponent rate
  have hI := hstatic.2.1
  obtain ⟨P,hInit,hInv,hMem,hHeap,hCredit⟩ := epochConditions_initial_runs F A I κ α hI rate allocation R L
    q K heap (budgetedIterationSpace F I.m L.exponent B) finish x mem pos p ω hpre hbudget hcache hranges
  have hImm : P.machine.mem (P.machine.regs 8-3)=5*I.m := by rw [hMem,hHeap,hbudget]
  obtain ⟨o,st,c,credit,hLoop,hPost,hCost⟩ :=
    epochLoop_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R hA L q K
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
      hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
      mem heap finish B ω capacity normalization hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe
      finish 0 P (by simp) hInv
  rw [hImm,hMem,hCredit] at hCost
  cases o with
  | returned v =>
    obtain ⟨j,hj,Q,hPrefix,hEnd,hStop⟩ := hPost
    have hzero : st.mem (v-1)=0 := hStop.1
    have hWord : v<2^w := hStop.2.1
    refine ⟨P,v,st,c+4,credit,?_,hMem,hHeap,hCredit,?_,hWord,?_⟩
    · unfold epochIterationsBody
      apply runs_seq_iff.mpr
      refine Or.inr ⟨P.machine,2,c+1,hInit,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inl ⟨v,c,hLoop,rfl,rfl⟩)
    · rw [ite_eq_right (by omega : st.mem (v-1)≠1)]
      exact ⟨j,hj,Q,hPrefix,hEnd,hStop⟩
    · rw [ite_eq_right (by omega : st.mem (v-1)≠1)]
      change c+R.phi L.handle credit st.mem≤(5*I.m+finish+I.m)*price+46*finish+4+R.phi L.handle x mem at hCost
      dsimp only [price] at hCost ⊢
      omega
  | normal =>
    obtain ⟨Q,hPrefix,rfl,rfl⟩ := hPost
    have hEnd : Inv finish Q := hPrefix.end_inv
    let next := Q.machine.regs 8
    have hBlock := epoch_iteration_space_of_initial_bound w heap next
      (budgetedIterationSpace F I.m L.exponent B) finish finish le_rfl hEnd.2.2.2.2.1 hspace
    have hSpace : next+1<2^w := by
      have hPositive : 1≤budgetedIterationSpace F I.m L.exponent B := by
        unfold budgetedIterationSpace
        omega
      omega
    let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)
    have hPre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s Q.credit
        q K L.sourceEnd L.tableEnd).pre ((L.packet F I next).take 20) Q.machine.mem := hEnd.2.2.2.2.2.2.2.2.2.1
    have hData : R.rep L.handle s Q.credit Q.machine.mem ∧
        (∀ z,R.foot L.handle Q.credit z → z<next) ∧ ZeroFrom Q.machine.mem next := by
      obtain ⟨names,base,lo,up,f,h,cost,r,a,one,mn,mx,E,ld,gd,heq,hfull,_⟩ := hPre
      have hh : h=next := by
        have hh := congrArg (fun xs : List ℕ => xs.getD 8 0) heq
        exact hh.symm
      subst h
      obtain ⟨names',count',base',lo',up',f',h',cost',r',a',one',mn',mx',E',ld',gd',es,heq,
        _,_,_,_,_,hrep,hfoot,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hz,_⟩ := hfull
      have hh : h'=next := (congrArg (fun xs : List ℕ => xs.getD 8 0) heq).symm
      subst h'
      exact ⟨hrep,hfoot,hz⟩
    obtain ⟨v,final,d,hFinish,hFlag,hRep,hFinalCost⟩ :=
      epochIterations_finish_runs R himpl.1 hflag Q.machine ω rfl hData.2.2 hSpace hData.1 hData.2.1
    have hBit := flagRecord_output hFlag
    have hv : v=next+1 := hFlag.2
    refine ⟨P,v,final,c+d+4,Q.credit,?_,hMem,hHeap,hCredit,?_,by omega,?_⟩
    · unfold epochIterationsBody
      apply runs_seq_iff.mpr
      refine Or.inr ⟨P.machine,2,c+d+1,hInit,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inr ⟨Q.machine,c,d,hLoop,hFinish,rfl⟩)
    · rw [ite_eq_left hBit]
      exact ⟨Q,hPrefix,hEnd,rfl,hFlag,hRep⟩
    · rw [ite_eq_left hBit]
      change c+R.phi L.handle Q.credit Q.machine.mem≤(5*I.m+finish+0)*price+46*finish+4+R.phi L.handle x mem at hCost
      dsimp only [price] at hCost ⊢
      omega

theorem epochIterations_runs_with_potential_upTo {w : ℕ} (F : MinRatioFormat w)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem :=
  epochIterations_runs_with_potential_upTo_at F A I U κ α Ψ eps rate allocation R hA L q K himpl
    hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot
    hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody heap
    finish B x mem pos ω capacity normalization hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe hpre
    hbudget hcache hranges

/-- The entire finite epoch entry runs from its first-call inputs,
with exact success or stopping trace and a linear report charge. -/
theorem epochIterations_runs_with_potential {w : ℕ} (F : MinRatioFormat w)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hstatic : EpochStaticInputs F I U κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem :=
  epochIterations_runs_with_potential_upTo F A I U κ α Ψ eps rate allocation R (hA.upTo I.m I.n)
    L q K himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord
    hcombined hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked
    hbudgetRecord hbody heap finish B x mem pos ω capacity normalization hstatic halloc hspace
    hbudgetFit hOne hfinish hfinishLe hpre hbudget hcache hranges

/-- The entire finite epoch entry runs from its first-call inputs,
with exact success or stopping trace and a linear report charge. -/
theorem epochIterations_runs_at_range_upTo_on_at {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ α Ψ eps I.m I.n) (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem := by
  let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
    (budgetedIterationSpace F I.m L.exponent B) finish
  let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
  let price := budgetedIterationCharge F I.m L.exponent rate
  have hI := hstatic.2.1
  obtain ⟨P,hInit,hInv,hMem,hHeap,hCredit⟩ := epochConditions_initial_runs F A I κ α hI rate allocation R L
    q K heap (budgetedIterationSpace F I.m L.exponent B) finish x mem pos p ω hpre hbudget hcache hranges
  have hImm : P.machine.mem (P.machine.regs 8-3)=5*I.m := by rw [hMem,hHeap,hbudget]
  obtain ⟨o,st,c,credit,hLoop,hPost,hCost⟩ :=
    epochLoop_runs_with_potential_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R hA hPG L q K
      himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
      hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
      mem heap finish B ω capacity normalization hWide hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe
      finish 0 P (by simp) hInv
  rw [hImm,hMem,hCredit] at hCost
  cases o with
  | returned v =>
    obtain ⟨j,hj,Q,hPrefix,hEnd,hStop⟩ := hPost
    have hzero : st.mem (v-1)=0 := hStop.1
    have hWord : v<2^w := hStop.2.1
    refine ⟨P,v,st,c+4,credit,?_,hMem,hHeap,hCredit,?_,hWord,?_⟩
    · unfold epochIterationsBody
      apply runs_seq_iff.mpr
      refine Or.inr ⟨P.machine,2,c+1,hInit,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inl ⟨v,c,hLoop,rfl,rfl⟩)
    · rw [ite_eq_right (by omega : st.mem (v-1)≠1)]
      exact ⟨j,hj,Q,hPrefix,hEnd,hStop⟩
    · rw [ite_eq_right (by omega : st.mem (v-1)≠1)]
      change c+R.phi L.handle credit st.mem≤(5*I.m+finish+I.m)*price+46*finish+4+R.phi L.handle x mem at hCost
      dsimp only [price] at hCost ⊢
      omega
  | normal =>
    obtain ⟨Q,hPrefix,rfl,rfl⟩ := hPost
    have hEnd : Inv finish Q := hPrefix.end_inv
    let next := Q.machine.regs 8
    have hBlock := epoch_iteration_space_of_initial_bound w heap next
      (budgetedIterationSpace F I.m L.exponent B) finish finish le_rfl hEnd.2.2.2.2.1 hspace
    have hSpace : next+1<2^w := by
      have hPositive : 1≤budgetedIterationSpace F I.m L.exponent B := by
        unfold budgetedIterationSpace
        omega
      omega
    let s := minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)
    have hPre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s Q.credit
        q K L.sourceEnd L.tableEnd).pre ((L.packet F I next).take 20) Q.machine.mem := hEnd.2.2.2.2.2.2.2.2.2.1
    have hData : R.rep L.handle s Q.credit Q.machine.mem ∧
        (∀ z,R.foot L.handle Q.credit z → z<next) ∧ ZeroFrom Q.machine.mem next := by
      obtain ⟨names,base,lo,up,f,h,cost,r,a,one,mn,mx,E,ld,gd,heq,hfull,_⟩ := hPre
      have hh : h=next := by
        have hh := congrArg (fun xs : List ℕ => xs.getD 8 0) heq
        exact hh.symm
      subst h
      obtain ⟨names',count',base',lo',up',f',h',cost',r',a',one',mn',mx',E',ld',gd',es,heq,
        _,_,_,_,_,hrep,hfoot,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hz,_⟩ := hfull
      have hh : h'=next := (congrArg (fun xs : List ℕ => xs.getD 8 0) heq).symm
      subst h'
      exact ⟨hrep,hfoot,hz⟩
    obtain ⟨v,final,d,hFinish,hFlag,hRep,hFinalCost⟩ :=
      epochIterations_finish_runs R himpl.1 hflag Q.machine ω rfl hData.2.2 hSpace hData.1 hData.2.1
    have hBit := flagRecord_output hFlag
    have hv : v=next+1 := hFlag.2
    refine ⟨P,v,final,c+d+4,Q.credit,?_,hMem,hHeap,hCredit,?_,by omega,?_⟩
    · unfold epochIterationsBody
      apply runs_seq_iff.mpr
      refine Or.inr ⟨P.machine,2,c+d+1,hInit,?_,by omega⟩
      exact runs_seq_iff.mpr (Or.inr ⟨Q.machine,c,d,hLoop,hFinish,rfl⟩)
    · rw [ite_eq_left hBit]
      exact ⟨Q,hPrefix,hEnd,rfl,hFlag,hRep⟩
    · rw [ite_eq_left hBit]
      change c+R.phi L.handle Q.credit Q.machine.mem≤(5*I.m+finish+0)*price+46*finish+4+R.phi L.handle x mem at hCost
      dsimp only [price] at hCost ⊢
      omega

theorem epochIterations_runs_at_range_upTo_on {PG : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U E : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn PG A κ α Ψ eps I.m I.n) (hPG : StageAdmits PG (namedInstance I) F.rangeExponent)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem :=
  epochIterations_runs_at_range_upTo_on_at F A I U E κ α Ψ eps rate allocation R hA hPG L q K
    himpl hrawDetect hdetect hstore hquery hcoefficient hflag hedge hrefresh hrecord hcombined
    hsnapshot hbatchBody hbatch hupdate hcore hstatus hreportBody hreport hchecked hbudgetRecord hbody
    heap finish B x mem pos ω capacity normalization hWide hstatic halloc hspace hbudgetFit hOne
    hfinish hfinishLe hpre hbudget hcache hranges

/-- The entire finite epoch entry runs from its first-call inputs,
with exact success or stopping trace and a linear report charge. -/
theorem epochIterations_runs_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
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
    (heap finish B : ℕ) (x : R.τ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool)
    (capacity normalization : ℝ)
    (hWide : ipmRangeExponent I.m U≤E)
    (hstatic : EpochStaticInputsAt F I U E κ α eps L capacity normalization mem)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hbudgetFit : 5*I.m<2^w) (hOne : 1<2^w) (hfinish : finish<2^w) (hfinishLe : finish ≤ I.m)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (A.init (namedInstance I)
        (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)) x q K L.sourceEnd L.tableEnd).pre
        ((L.packet F I heap).take 20) mem)
    (hbudget : mem (heap-3)=5*I.m)
    (hcache : ∀ e<I.m,reportedCachePost F A (A.init (namedInstance I)
      (readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m))
      I.m q L.base L.lower L.upper L.flow L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hranges : ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :
    let Inv := EpochConditions F A I κ α rate allocation R L q K mem heap
      (budgetedIterationSpace F I.m L.exponent B) finish
    let Step := EpochAcceptedStep F A I κ α rate allocation R L q K
    let price := budgetedIterationCharge F I.m L.exponent rate
    ∃ P v st c credit,
      Runs w p ω (epochIterationsBody iteration flag) (startState (L.packet F I heap++[finish]) mem pos)
        (.returned v) st c ∧ P.machine.mem=mem ∧ P.machine.regs 8=heap ∧ P.credit=x ∧
      (if st.mem (v-1)=1 then
        ∃ Q, EpochAcceptedPrefix Inv Step 0 P finish Q ∧ Inv finish Q ∧ credit=Q.credit ∧
          (flagRecordContract w).post [1,Q.machine.regs 8] Q.machine.mem v st.mem ∧
          R.rep L.handle (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*finish)) credit st.mem
       else
        ∃ j<finish, ∃ Q, EpochAcceptedPrefix Inv Step 0 P j Q ∧ Inv j Q ∧
          EpochStoppedStep F A I κ α rate allocation R L q K j Q v st credit) ∧
      v<2^w ∧ c+R.phi L.handle credit st.mem≤
        (5*I.m+finish+(if st.mem (v-1)=1 then 0 else I.m))*price+46*finish+40+R.phi L.handle x mem :=
  epochIterations_runs_at_range_upTo_on F A I U E κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) L q K himpl hrawDetect hdetect hstore hquery
    hcoefficient hflag hedge hrefresh hrecord hcombined hsnapshot hbatchBody hbatch hupdate hcore
    hstatus hreportBody hreport hchecked hbudgetRecord hbody heap finish B x mem pos ω capacity
    normalization hWide hstatic halloc hspace hbudgetFit hOne hfinish hfinishLe hpre hbudget hcache hranges

end MinCostFlow.IPM.Machine
