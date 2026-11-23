module

public import MinCostFlow.IPM.Machine.TargetEpochInitRun
public import MinCostFlow.IPM.Machine.EpochCheckedStartup
public import MinCostFlow.IPM.Machine.EpochCheckedStartupWithV
public import MinCostFlow.IPM.Machine.TargetEpochArguments
import WordRAM.Tactic

/-!
# Calling checked startup from the target driver

The residual address is the last scalar of the base workspace.
The caller forwards the actual copy, held residual and named graph.
Its saved registers expose the startup endpoint and verdict to
the following branch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Outcome of the range-checked epoch startup call from `oldState`, with cost slack `overhead`
(`930` for 6-argument Init, `931` for `V`-passing Init). -/
abbrev TargetEpochStartupPost {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (p : Program) (initStmt : Stmt) (old : EpochLayout) (source oldHeap overhead : ℕ)
    (oldState : State) (ω : ℕ → Bool) : Prop :=
  let flow := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := flow+I.m*F.limbs
  let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
  let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
  let handle := heap+(la+ga)
  ∃ v after cost bit coeffMem,
    Runs w p ω initStmt oldState .normal after cost ∧
    (∀ j<23,after.regs j=oldState.regs j) ∧
    after.regs 23=flow ∧ after.regs 24=rp ∧ after.regs 25=v ∧ after.regs 26=bit ∧ after.regs 30=heap ∧
    (coefficientRefreshContract w F.fmt.limbBits q K).post
      (((old.next F I source rp flow heap 0).startPacket F I).take 14) oldState.mem handle coeffMem ∧
    (coefficientRangeFullContract w F.fmt.limbBits).post
      [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
      coeffMem bit coeffMem ∧
    bit≤1 ∧ ZeroFrom after.mem v ∧ heap≤v ∧
    v≤heap+epochStartSpace F I old.exponent old.initGraph heap allocation+I.m+4 ∧
    (∀ z<heap,after.mem z=oldState.mem z) ∧
    (bit=0 → cost≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
      Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
      I.m*(164*F.limbs+530)+overhead) ∧
    (bit=1 →
      ∃ s x initEnd initialized named,
        let L := old.next F I source rp flow heap initEnd
        let end_ := initEnd+I.m+3
        v=end_ ∧
        (epochStartContract F A I κ α rate allocation R q K).post (L.startPacket F I)
          oldState.mem initEnd initialized ∧
        (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
        (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ after.mem ∧
        ListAt after.mem initEnd (List.range I.m) ∧
        MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
        R.rep L.handle s x after.mem ∧
        s=A.init (namedInstance I)
          (readVector after.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector after.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
        (∀ z,R.foot L.handle x z → L.handle≤z ∧ z < initEnd) ∧
        (coefficientRangeListContract w F.fmt.limbBits).post
          [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs]
          after.mem 1 after.mem ∧
        cost+R.phi L.handle x after.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision L.exponent+
          Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision L.exponent+rate I.m*(I.m+1)+
          I.m*(164*F.limbs+530)+overhead)

/-- Link the actual range-checked startup body to the continuing residual branch,
retaining its refresh/scan postconditions, flag, frame and (on acceptance) concrete credit. -/
theorem targetEpoch_startup_call {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh fullScan initEntry initNames names budget flag startup : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBody init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBody initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBody refresh fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap : ℕ) (oldState : State) (ω : ℕ → Bool)
    (hregs : ∀ j<23,oldState.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hflow : oldState.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hheap : oldState.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : let flow := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) flow (flow+I.m*F.limbs) 0
      ∀ z∈L.startupPacket F I,z<2^w)
    (hI : I.IsValid)
    (hgraph : GraphAt oldState.mem old.initGraph (namedInstance I))
    (hgraphWords : ∀ z∈graphWords (namedInstance I),z<2^w)
    (hgraphEnd : old.initGraph+(graphWords (namedInstance I)).length≤
      epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprecision : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hRpre : let flow := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) flow (flow+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) oldState.mem)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : let heap := epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs
      heap+epochStartSpace F I old.exponent old.initGraph heap allocation+I.m+4<2^w)
    (hneg : old.gradientMin+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hmax : old.gradientMax+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hmin : old.lengthMin+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hsneg : ScalarAt oldState.mem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hsmax : ScalarAt oldState.mem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hsmin : ScalarAt oldState.mem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ)))) :
    let flow := epochResidualEnd I.m F.limbs oldHeap
    let rp := oldHeap+(8*I.m+3)*F.limbs
    let heap := flow+I.m*F.limbs
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
    let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
    let handle := heap+(la+ga)
    ∃ v after cost bit coeffMem,
      Runs w p ω (targetEpochInit startup) oldState .normal after cost ∧
      (∀ j<23,after.regs j=oldState.regs j) ∧
      after.regs 23=flow ∧ after.regs 24=rp ∧ after.regs 25=v ∧ after.regs 26=bit ∧ after.regs 30=heap ∧
      (coefficientRefreshContract w F.fmt.limbBits q K).post
        (((old.next F I source rp flow heap 0).startPacket F I).take 14) oldState.mem handle coeffMem ∧
      (coefficientRangeFullContract w F.fmt.limbBits).post
        [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
        coeffMem bit coeffMem ∧
      bit≤1 ∧ ZeroFrom after.mem v ∧ heap≤v ∧
      v≤heap+epochStartSpace F I old.exponent old.initGraph heap allocation+I.m+4 ∧
      (∀ z<heap,after.mem z=oldState.mem z) ∧
      (bit=0 → cost≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+930) ∧
      (bit=1 →
        ∃ s x initEnd initialized named,
          let L := old.next F I source rp flow heap initEnd
          let end_ := initEnd+I.m+3
          v=end_ ∧
          (epochStartContract F A I κ α rate allocation R q K).post (L.startPacket F I)
            oldState.mem initEnd initialized ∧
          (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
          (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ after.mem ∧
          ListAt after.mem initEnd (List.range I.m) ∧
          MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
          R.rep L.handle s x after.mem ∧
          s=A.init (namedInstance I)
            (readVector after.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
            (readVector after.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
          (∀ z,R.foot L.handle x z → L.handle≤z ∧ z < initEnd) ∧
          (coefficientRangeListContract w F.fmt.limbBits).post
            [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs]
            after.mem 1 after.mem ∧
          cost+R.phi L.handle x after.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision L.exponent+
            Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision L.exponent+rate I.m*(I.m+1)+
            I.m*(164*F.limbs+530)+930) := by
  dsimp only
  let flow := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := flow+I.m*F.limbs
  obtain ⟨v,st,c,bit,coeffMem,hRun,hRpost,hSpost,hb,hBit,hFitOut,hz,hLo,hHi,hFrame,hZeroCost,hSuccess⟩ :=
    epochCheckedStartup_runs_with_potential F A I κ α rate allocation R himpl hrefresh hfullScan
      hinit hinitNames hnames hbudget hflag old source rp flow heap oldState.mem oldState.pos ω
      hwords hI hgraph hgraphWords hgraphEnd hquality hprecision hRpre hfive hcount hspace
      hneg hmax hmin hsneg hsmax hsmin
  let first : State := {oldState with regs := Function.update oldState.regs 24 rp}
  have hargs := targetEpoch_startup_args (w:=w) F I old tp qp source oldHeap rp flow heap first
    (fun j hj => by simpa [first,Function.update_of_ne (by omega : j≠24)] using hregs j hj)
    (by simp [first]) (by simpa [first] using hflow) (by simpa [first] using hheap)
  have hFlowFit : flow<2^w :=
    hwords flow (by simp [flow,EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next])
  have hrp : (Expr.bin .sub (.reg 23) (.reg 15)).eval w oldState=some rp := by
    have hreg : oldState.regs 15=F.limbs := hregs 15 (by decide)
    have hsub : flow-F.limbs=rp := epoch_residual_end_sub I.m F.limbs oldHeap
    rw [← hsub]
    apply Expr.eval_sub (x:=flow) (y:=F.limbs)
    · simp only [Expr.eval,hflow,flow]
    · simp only [Expr.eval,hreg]
    · exact hFlowFit
  have hInit := targetEpochInit_runs hstartup hrp hargs hRun hFitOut (by omega) hBit hb
  let after : State := ⟨st.mem,Function.update (Function.update (Function.update oldState.regs 24 rp) 25 v) 26 bit,st.pos⟩
  refine ⟨v,after,c+30,bit,coeffMem,hInit,?_,?_,by simp [after,rp],
    by simp [after],by simp [after],?_,hRpost,hSpost,hb,hz,hLo,hHi,hFrame,fun h0 => ?_,fun h1 => ?_⟩
  · intro j hj
    simp only [after,Function.update_of_ne (by omega : j≠24),Function.update_of_ne (by omega : j≠25),
      Function.update_of_ne (by omega : j≠26)]
  · simpa [after] using hflow
  · simpa [after] using hheap
  · have hc := hZeroCost h0; omega
  · obtain ⟨s,x,initEnd,initialized,named,hv,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hListScan,hCost⟩ := hSuccess h1
    refine ⟨s,x,initEnd,initialized,named,hv,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hListScan,?_⟩
    change c+30+R.phi (old.next F I source rp flow heap initEnd).handle x st.mem≤_
    change c+R.phi (old.next F I source rp flow heap initEnd).handle x st.mem≤_ at hCost
    dsimp only [EpochLayout.next] at hCost ⊢
    omega

/-- `V`-passing variant of `targetEpoch_startup_call` for `minRatioMachineContractWithV`.
Assumes `oldState.regs 29 = V` and `V < 2^w`. -/
theorem targetEpoch_startup_call_withV {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (V : ℕ) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {p : Program} {init refresh fullScan initEntry initNames names budget flag startup : ℕ}
    {op : ℕ → ℕ}
    (himpl : R.Implements w p init op
      (minRatioMachineContractWithV F A (namedInstance I) I.m V κ α rate allocation))
    (hrefresh : MeetsContract w p refresh (coefficientRefreshContract w F.fmt.limbBits q K))
    (hfullScan : MeetsContract w p fullScan (coefficientRangeFullContract w F.fmt.limbBits))
    (hinit : p.procs[initEntry]?=some (minRatioInitBodyWithV init))
    (hinitNames : p.procs[initNames]?=some (epochInitNamesBudgetBodyWithV initEntry names budget))
    (hnames : MeetsContract w p names (vertexNamesContract w))
    (hbudget : MeetsContract w p budget (epochBudgetInitContract w))
    (hflag : MeetsContract w p flag (flagRecordContract w))
    (hstartup : p.procs[startup]?=some (epochCheckedStartupBodyWithV refresh fullScan initNames flag))
    (old : EpochLayout) (tp qp source oldHeap : ℕ) (oldState : State) (ω : ℕ → Bool)
    (hregs : ∀ j<23,oldState.regs j=(targetEpochPacket old F I tp qp source oldHeap).getD j 0)
    (hflow : oldState.regs 23=epochResidualEnd I.m F.limbs oldHeap)
    (hVreg : oldState.regs 29=V) (hVword : V<2^w)
    (hheap : oldState.regs 30=epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hwords : let flow := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) flow (flow+I.m*F.limbs) 0
      ∀ z∈L.startupPacket F I,z<2^w)
    (hI : I.IsValid)
    (hgraph : GraphAt oldState.mem old.initGraph (namedInstance I))
    (hgraphWords : ∀ z∈graphWords (namedInstance I),z<2^w)
    (hgraphEnd : old.initGraph+(graphWords (namedInstance I)).length≤
      epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hquality : (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α)
    (hprecision : 5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision)
    (hRpre : let flow := epochResidualEnd I.m F.limbs oldHeap
      let L := old.next F I source (oldHeap+(8*I.m+3)*F.limbs) flow (flow+I.m*F.limbs) 0
      (coefficientRefreshContract w F.fmt.limbBits q K).pre ((L.startPacket F I).take 14) oldState.mem)
    (hfive : 5<2^w) (hcount : 5*I.m<2^w)
    (hspace : let heap := epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs
      heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4<2^w)
    (hneg : old.gradientMin+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hmax : old.gradientMax+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hmin : old.lengthMin+F.limbs≤epochResidualEnd I.m F.limbs oldHeap+I.m*F.limbs)
    (hsneg : ScalarAt oldState.mem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hsmax : ScalarAt oldState.mem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hsmin : ScalarAt oldState.mem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ)))) :
    let flow := epochResidualEnd I.m F.limbs oldHeap
    let rp := oldHeap+(8*I.m+3)*F.limbs
    let heap := flow+I.m*F.limbs
    let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
    let ga := Num.IPM.gradientArraySpace I.m F.limbs F.fmt.precision old.exponent
    let handle := heap+(la+ga)
    ∃ v after cost bit coeffMem,
      Runs w p ω (targetEpochInitWithV startup) oldState .normal after cost ∧
      (∀ j<23,after.regs j=oldState.regs j) ∧
      after.regs 23=flow ∧ after.regs 24=rp ∧ after.regs 25=v ∧ after.regs 26=bit ∧ after.regs 30=heap ∧
      (coefficientRefreshContract w F.fmt.limbBits q K).post
        (((old.next F I source rp flow heap 0).startPacket F I).take 14) oldState.mem handle coeffMem ∧
      (coefficientRangeFullContract w F.fmt.limbBits).post
        [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
        coeffMem bit coeffMem ∧
      bit≤1 ∧ ZeroFrom after.mem v ∧ heap≤v ∧
      v≤heap+epochStartSpace F I old.exponent old.initGraph heap (allocationWithV V allocation)+I.m+4 ∧
      (∀ z<heap,after.mem z=oldState.mem z) ∧
      (bit=0 → cost≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision old.exponent+
        Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision old.exponent+rate I.m*(I.m+1)+
        I.m*(164*F.limbs+530)+931) ∧
      (bit=1 →
        ∃ s x initEnd initialized named,
          let L := old.next F I source rp flow heap initEnd
          let end_ := initEnd+I.m+3
          v=end_ ∧
          (epochStartContract F A I κ α rate (allocationWithV V allocation) R q K).post (L.startPacket F I)
            oldState.mem initEnd initialized ∧
          (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named ∧
          (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named end_ after.mem ∧
          ListAt after.mem initEnd (List.range I.m) ∧
          MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
          R.rep L.handle s x after.mem ∧
          s=A.init (namedInstance I)
            (readVector after.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
            (readVector after.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) ∧
          (∀ z,R.foot L.handle x z → L.handle≤z ∧ z < initEnd) ∧
          (coefficientRangeListContract w F.fmt.limbBits).post
            [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs]
            after.mem 1 after.mem ∧
          cost+R.phi L.handle x after.mem≤Num.IPM.lengthArrayCost I.m F.limbs F.fmt.precision L.exponent+
            Num.IPM.gradientArrayCost I.m F.limbs F.fmt.precision L.exponent+rate I.m*(I.m+1)+
            I.m*(164*F.limbs+530)+931) := by
  dsimp only
  let flow := epochResidualEnd I.m F.limbs oldHeap
  let rp := oldHeap+(8*I.m+3)*F.limbs
  let heap := flow+I.m*F.limbs
  have hwordsV : ∀ z ∈ (old.next F I source rp flow heap 0).startupPacket F I ++ [V], z < 2^w := by
    intro z hz
    simp only [List.mem_append,List.mem_singleton] at hz
    rcases hz with hz | rfl
    · exact hwords z hz
    · exact hVword
  obtain ⟨v,st,c,bit,coeffMem,hRun,hRpost,hSpost,hb,hBit,hFitOut,hz,hLo,hHi,hFrame,hZeroCost,hSuccess⟩ :=
    epochCheckedStartupWithV_runs_with_potential F A I V κ α rate allocation R himpl hrefresh hfullScan
      hinit hinitNames hnames hbudget hflag old source rp flow heap oldState.mem oldState.pos ω
      hwordsV hI hgraph hgraphWords hgraphEnd hquality hprecision hRpre hfive hcount hspace
      hneg hmax hmin hsneg hsmax hsmin
  let first : State := {oldState with regs := Function.update oldState.regs 24 rp}
  have hargs := targetEpoch_startupWithV_args (w:=w) F I old tp qp source oldHeap rp flow heap V first
    (fun j hj => by simpa [first,Function.update_of_ne (by omega : j≠24)] using hregs j hj)
    (by simp [first]) (by simpa [first] using hflow) (by simpa [first] using hheap)
    (by simpa [first] using hVreg)
  have hFlowFit : flow<2^w :=
    hwords flow (by simp [flow,EpochLayout.startupPacket,EpochLayout.startPacket,EpochLayout.next])
  have hrp : (Expr.bin .sub (.reg 23) (.reg 15)).eval w oldState=some rp := by
    have hreg : oldState.regs 15=F.limbs := hregs 15 (by decide)
    have hsub : flow-F.limbs=rp := epoch_residual_end_sub I.m F.limbs oldHeap
    rw [← hsub]
    apply Expr.eval_sub (x:=flow) (y:=F.limbs)
    · simp only [Expr.eval,hflow,flow]
    · simp only [Expr.eval,hreg]
    · exact hFlowFit
  have hInit := targetEpochInitWithV_runs hstartup hrp hargs hRun hFitOut (by omega) hBit hb
  let after : State := ⟨st.mem,Function.update (Function.update (Function.update oldState.regs 24 rp) 25 v) 26 bit,st.pos⟩
  refine ⟨v,after,c+31,bit,coeffMem,hInit,?_,?_,by simp [after,rp],
    by simp [after],by simp [after],?_,hRpost,hSpost,hb,hz,hLo,hHi,hFrame,fun h0 => ?_,fun h1 => ?_⟩
  · intro j hj
    simp only [after,Function.update_of_ne (by omega : j≠24),Function.update_of_ne (by omega : j≠25),
      Function.update_of_ne (by omega : j≠26)]
  · simpa [after] using hflow
  · simpa [after] using hheap
  · have hc := hZeroCost h0; omega
  · obtain ⟨s,x,initEnd,initialized,named,hv,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hListScan,hCost⟩ := hSuccess h1
    refine ⟨s,x,initEnd,initialized,named,hv,hOut,hN,hB,hList,hFit,hRep,hState,hFoot,hListScan,?_⟩
    change c+31+R.phi (old.next F I source rp flow heap initEnd).handle x st.mem≤_
    change c+R.phi (old.next F I source rp flow heap initEnd).handle x st.mem≤_ at hCost
    dsimp only [EpochLayout.next] at hCost ⊢
    omega

end MinCostFlow.IPM.Machine
