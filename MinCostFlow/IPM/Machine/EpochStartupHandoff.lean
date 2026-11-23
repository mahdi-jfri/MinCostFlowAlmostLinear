module

public import MinCostFlow.IPM.Machine.EpochStartupLoopInput
public import MinCostFlow.IPM.Machine.EpochStartupSources
public import MinCostFlow.IPM.Machine.EpochStartNamesBudgetInput
public import MinCostFlow.IPM.Machine.EpochStartupInitialCache
public import MinCostFlow.IPM.Machine.EpochNextLayout
public import MinCostFlow.IPM.Machine.BudgetedIterationSpace

/-!
# Joining the checked startup and the first lazy iteration

The new coefficient arrays and their scan come from the startup run.
The budget record gives the initial report budget. The old immutable
base and the freshly copied mutable base agree coordinate by coordinate.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

set_option maxHeartbeats 350000 in
/-- Unpack the actual checked startup into the concrete first-call
precondition and the exact initial coefficient cache. -/
theorem epochStartup_handoff_upTo_on {w q K : ℕ} {P : MGraph → (ℕ → ℝ) → Prop} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd B : ℕ)
    (x : R.τ) (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hFit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)))
    (hRep : R.rep (old.next F I base rp fp heap initEnd).handle
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) x started)
    (hFoot : ∀ z,R.foot (old.next F I base rp fp heap initEnd).handle x z →
      (old.next F I base rp fp heap initEnd).handle≤z ∧ z< initEnd)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started 1 started)
    (hguardMin : ScalarAt mem old.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^old.exponent))
    (hguardMax : ScalarAt mem old.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^old.exponent))
    (hmin : ScalarAt started old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt started old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt started old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hcoefficient : (coefficientRefreshContract w F.fmt.limbBits q K).pre
      (((old.next F I base rp fp heap initEnd).startPacket F I).take 14) mem)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hwidth : ∀ e<I.m,Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^old.exponent)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+budgetedIterationSpace F I.m old.exponent B<2^w) :
    let L := old.next F I base rp fp heap initEnd
    let end_ := initEnd+I.m+3
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s x q K
      L.sourceEnd L.tableEnd).pre ((L.packet F I end_).take 20) started ∧
    started (end_ - 3)=5*I.m ∧
    (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started) ∧
    (∀ e<I.m,Num.Valid started (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid started (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) := by
  let L := old.next F I base rp fp heap initEnd
  let end_ := initEnd+I.m+3
  let s := A.init (namedInstance I)
    (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
  have hsource := scalarCoefficientSourceConditions_of_coefficientRefresh hcoefficient hguardMin hguardMax
  have hlen := epochStartup_lengthsWithin F I L hList hmin hneg hmax hScan
  have hcache := epochStartup_initial_cache_upTo_on F A I κ α Ψ eps hA hI rate allocation R
    old base rp fp heap initEnd mem initialized named started hOut hN hB harrays hscalars hfEnd hvalid hbase hinside
    (hP _ hlen)
  obtain ⟨_,_,_,_,_,_,hlower,_⟩ := epochStart_output F A I κ α rate allocation R hOut
  have hinit : L.handle ≤ initEnd := hlower
  have hspace' := budgetedIteration_refresh_space F I.m old.exponent B L.handle end_ allocation halloc hspace
  have hpre := epochStartNamesBudget_refresh_pre_upTo_on F A I κ α Ψ eps hA heps hI rate allocation R
    (b:=L.handle) (base:=base) (one:=old.one) (x:=x) rfl hinit hList hB hFrame hRep hFit rfl hFoot
    hcache harrays hscalars hfEnd hsource hbaseValid hwidth hspace' (hP _ hlen)

  exact ⟨hpre,(epochBudgetRecord_output hB).1,hcache,epochStartup_loop_ranges F A I L s q hList hmin hneg hmax hcache hScan⟩

/-- Unpack the actual checked startup into the concrete first-call
precondition and the exact initial coefficient cache. -/
theorem epochStartup_handoff_upTo {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n) (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd B : ℕ)
    (x : R.τ) (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hFit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)))
    (hRep : R.rep (old.next F I base rp fp heap initEnd).handle
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) x started)
    (hFoot : ∀ z,R.foot (old.next F I base rp fp heap initEnd).handle x z →
      (old.next F I base rp fp heap initEnd).handle≤z ∧ z< initEnd)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started 1 started)
    (hguardMin : ScalarAt mem old.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^old.exponent))
    (hguardMax : ScalarAt mem old.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^old.exponent))
    (hmin : ScalarAt started old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt started old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt started old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hcoefficient : (coefficientRefreshContract w F.fmt.limbBits q K).pre
      (((old.next F I base rp fp heap initEnd).startPacket F I).take 14) mem)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hwidth : ∀ e<I.m,Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^old.exponent)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+budgetedIterationSpace F I.m old.exponent B<2^w) :
    let L := old.next F I base rp fp heap initEnd
    let end_ := initEnd+I.m+3
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s x q K
      L.sourceEnd L.tableEnd).pre ((L.packet F I end_).take 20) started ∧
    started (end_ - 3)=5*I.m ∧
    (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started) ∧
    (∀ e<I.m,Num.Valid started (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid started (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :=
  epochStartup_handoff_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True)) (stageAdmits_true _ _) heps hI
    rate allocation R old base rp fp heap initEnd B x mem initialized named started hOut hN hB
    hList hFrame hFit hRep hFoot hScan hguardMin hguardMax hmin hneg hmax hcoefficient harrays
    hscalars hfEnd hvalid hbaseValid hbase hinside hwidth halloc hspace

/-- Unpack the actual checked startup into the concrete first-call
precondition and the exact initial coefficient cache. -/
theorem epochStartup_handoff {w q K : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps) (heps : 0<eps) (hI : I.IsValid)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (old : EpochLayout) (base rp fp heap initEnd B : ℕ)
    (x : R.τ) (mem initialized named started : ℕ → ℕ)
    (hOut : (epochStartContract F A I κ α rate allocation R q K).post
      ((old.next F I base rp fp heap initEnd).startPacket F I) mem initEnd initialized)
    (hN : (vertexNamesContract w).post [I.m,initEnd] initialized (initEnd+I.m) named)
    (hB : (epochBudgetRecordContract w).post [5*I.m,0,1,initEnd+I.m] named (initEnd+I.m+3) started)
    (hList : ListAt started initEnd (List.range I.m)) (hFrame : ∀ z<heap,started z=mem z)
    (hFit : MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)))
    (hRep : R.rep (old.next F I base rp fp heap initEnd).handle
      (A.init (namedInstance I)
        (readVector started (old.next F I base rp fp heap initEnd).gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector started heap F.fmt.limbBits F.limbs F.fmt.precision I.m)) x started)
    (hFoot : ∀ z,R.foot (old.next F I base rp fp heap initEnd).handle x z →
      (old.next F I base rp fp heap initEnd).handle≤z ∧ z< initEnd)
    (hScan : let L := old.next F I base rp fp heap initEnd
      (coefficientRangeListContract w F.fmt.limbBits).post
        [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] started 1 started)
    (hguardMin : ScalarAt mem old.slackMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^old.exponent))
    (hguardMax : ScalarAt mem old.slackMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^old.exponent))
    (hmin : ScalarAt started old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt started old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt started old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hcoefficient : (coefficientRefreshContract w F.fmt.limbBits q K).pre
      (((old.next F I base rp fp heap initEnd).startPacket F I).take 14) mem)
    (harrays : ∀ p∈[base,old.cost,old.lower,old.upper],p+I.m*F.limbs≤fp)
    (hscalars : ∀ p∈[rp,old.alpha,old.one,old.slackMin,old.slackMax],p+F.limbs≤fp)
    (hfEnd : fp+I.m*F.limbs≤heap)
    (hvalid : ∀ e<I.m,Num.Valid mem (fp+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbaseValid : ∀ e<I.m,Num.Valid mem (base+e*F.limbs) F.fmt.limbBits F.limbs)
    (hbase : ∀ e<I.m,Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hinside : ∀ e<I.m,Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision ∧
      Num.fixVal mem (fp+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision<
        Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hwidth : ∀ e<I.m,Num.fixVal mem (old.upper+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (old.lower+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^old.exponent)
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initEnd+I.m+3+budgetedIterationSpace F I.m old.exponent B<2^w) :
    let L := old.next F I base rp fp heap initEnd
    let end_ := initEnd+I.m+3
    let s := A.init (namedInstance I)
      (readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle s x q K
      L.sourceEnd L.tableEnd).pre ((L.packet F I end_).take 20) started ∧
    started (end_ - 3)=5*I.m ∧
    (∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e started) ∧
    (∀ e<I.m,Num.Valid started (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid started (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector started L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector started L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) :=
  epochStartup_handoff_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) heps hI rate allocation R old base
    rp fp heap initEnd B x mem initialized named started hOut hN hB hList hFrame hFit hRep hFoot
    hScan hguardMin hguardMax hmin hneg hmax hcoefficient harrays hscalars hfEnd hvalid
    hbaseValid hbase hinside hwidth halloc hspace

end MinCostFlow.IPM.Machine
