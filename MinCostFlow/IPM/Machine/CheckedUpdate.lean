module

public import MinCostFlow.IPM.Machine.CheckedUpdateRanges

/-!
# Checking reported coefficients before one actual Update

The target-test continuation first checks the stable reported set's
coefficient ranges. A rejected check returns its status immediately.
Only acceptance prepares the fixed-graph batch and invokes Update.
The final word always says success or failure. The entry's range
invariant is required only outside the set checked by the program.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[handle,sourceGraph,report,gradientTable,lengthTable,eta,L,
heap,negativeMaximum,maximum,minimum]`. -/
def checkedUpdateBody (range update : ℕ) : Stmt :=
  .call 11 range [.reg 2,.reg 3,.reg 4,.reg 8,.reg 9,.reg 10,.reg 6,.reg 7] ;;
  .assign 12 (.load (.bin .sub (.reg 11) (.const 1))) ;;
  .cond (.reg 12)
    (.call 13 update [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 5,.reg 6,.reg 11] ;;
      .ret (.reg 13))
    (.ret (.reg 11))

/-- The checked branch contains no random instruction. -/
theorem checkedUpdateBody_noRand (range update : ℕ) : (checkedUpdateBody range update).NoRand := by
  simp [checkedUpdateBody,Stmt.NoRand]

/-- All input conditions are stored data and caller invariants. Bounds on
reported coefficient values are checked by the actual program. -/
def checkedUpdateContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (S : Finset ℕ) : Contract where
  pre args mem := ∃ source report g l eta heap neg mx mn,
    args=[b,source,report,g,l,eta,F.limbs,heap,neg,mx,mn] ∧
    (detectBatchContract w I S).pre [source,report,heap] mem ∧
    (coefficientRangeReportContract w F.fmt.limbBits S).pre [report,g,l,neg,mx,mn,F.limbs,heap] mem ∧
    R.rep b s x mem ∧ (∀ z,R.foot b x z → z<heap) ∧
    MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s ∧
    (2:ℝ)^(-(F.rangeExponent:ℤ))≤κ*α ∧
    5*F.rangeExponent+Nat.size I.m+30≤F.fmt.precision ∧
    (∀ e∈(namedInstance I).E,|A.query s e|≤(2:ℝ)^F.rangeExponent) ∧
    g+I.m*F.limbs≤heap ∧ l+I.m*F.limbs≤heap ∧ eta+F.limbs≤heap ∧
    Num.Valid mem eta F.fmt.limbBits F.limbs ∧
    (2:ℝ)^(-(F.rangeExponent:ℤ))≤Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision ∧
    Num.fixVal mem eta F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^F.rangeExponent ∧
    (∀ e<I.m,Num.Valid mem (g+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (l+e*F.limbs) F.fmt.limbBits F.limbs) ∧
    ScalarAt mem neg F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent) ∧
    ScalarAt mem mx F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent) ∧
    ScalarAt mem mn F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))) ∧
    (∀ e∈(namedInstance I).E,e∉S →
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) ∧
    (heap+2)+(1+6*S.card)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2<2^w ∧
    MinRatioDetectedWith A (namedInstance I) s (· ∈ S)
      (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m)
  post args mem v mem' := ∃ checkedEnd checkedMem,
    (coefficientRangeReportContract w F.fmt.limbBits S).post
      [args.getD 2 0,args.getD 3 0,args.getD 4 0,args.getD 8 0,args.getD 9 0,args.getD 10 0,F.limbs,args.getD 7 0]
      mem checkedEnd checkedMem ∧
    (if checkedMem (checkedEnd-1)=1 then
      (batchUpdateStatusContract F A I κ α rate allocation R b s x S).post
        [b,args.getD 1 0,args.getD 2 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,F.limbs,checkedEnd]
        checkedMem v mem'
    else v=checkedEnd ∧ mem'=checkedMem) ∧ mem' (v-1)≤1 ∧ ZeroFrom mem' v
  cost _ mem := S.card*(164*F.limbs+680)+rate I.m*(1+2*S.card)+R.phi b x mem+1000

end MinCostFlow.IPM.Machine
