module

public import MinCostFlow.IPM.Machine.DetectBatchUpdateInput

/-!
# Preparing the reported batch and applying the next Update

The target test invokes this entry only after accepting its coefficient
and capacity guards. The entry prepares exactly the stable report's
fixed-graph deletion/insertion batch and passes it, the checked tables
and the stored normalization to Update. It stops after that one Update,
including a failure answer, and reserves the complete normalization
output for the driver to inspect.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[handle,sourceGraph,report,gradientTable,lengthTable,eta,L,heap]`.
Prepare the batch at the incoming heap, then call the reserved Update. -/
def batchUpdateBody (batch update : ℕ) : Stmt :=
  .call 8 batch [.reg 1,.reg 2,.reg 7] ;;
  .call 9 update [.reg 0,.reg 7,.reg 3,.reg 4,.reg 5,
    .bin .add (.const 1) (.bin .mul (.const 2) (.reg 6)),.reg 8] ;;
  .ret (.reg 9)

/-- Preparing a batch and applying one Update contains no randomness. -/
theorem batchUpdateBody_noRand (batch update : ℕ) : (batchUpdateBody batch update).NoRand := by
  simp [batchUpdateBody,Stmt.NoRand]

/-- The complete local input and relational output of the batch/Update
entry. The explicit allocation depends only on its actual argument
packet. Numeric bounds are data invariants, not operation results. -/
def batchUpdateContract {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (S : Finset ℕ) : Contract where
  pre args mem := ∃ source report g l eta heap,
    args=[b,source,report,g,l,eta,F.limbs,heap] ∧
    (detectBatchContract w I S).pre [source,report,heap] mem ∧
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
    (∀ e∈(namedInstance I).E,
      |readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent) ∧
    heap+(1+6*S.card)+allocation 0 [b,heap,g,l,eta,heap+(1+6*S.card)]+(1+2*F.limbs)<2^w ∧
    MinRatioDetectedWith A (namedInstance I) s (· ∈ S)
      (readVector mem g F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector mem l F.fmt.limbBits F.limbs F.fmt.precision I.m)
  post args mem v mem' := ∃ batchEnd batchMem s' final,
    (detectBatchContract w I S).post [args.getD 1 0,args.getD 2 0,args.getD 7 0] mem batchEnd batchMem ∧
    (minRatioUpdateContract w R (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation) b s x).post
      [b,args.getD 7 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,1+2*F.limbs,batchEnd] batchMem v mem' ∧
    R.rep b s' final mem' ∧
    (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
      0 s [b,args.getD 7 0,args.getD 3 0,args.getD 4 0,args.getD 5 0,batchEnd] batchMem s' mem' ∧
    (∀ z,R.foot b final z → z<v ∧ (R.foot b x z ∨ args.getD 7 0≤z))
  cost _ mem := 180*S.card+rate I.m*(1+2*S.card)+R.phi b x mem+500

end MinCostFlow.IPM.Machine
