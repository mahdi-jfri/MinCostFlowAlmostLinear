module

public import MinCostFlow.IPM.Machine.DetectRefresh
public import MinCostFlow.IPM.Machine.CheckedUpdate
public import MinCostFlow.IPM.Machine.CheckedUpdateTransition

/-!
# Result and reported-size charge of one complete checked iteration

The iteration records the actual Detect/refresh result and its concrete
state. Rejection returns that result. Acceptance records the actual
checked-driver continuation, which either rejects a coefficient or
returns the one Update answer. All outcomes have a uniform last-word
status and fresh suffix. The charge is linear in one plus the report
size and includes both data-structure operations and numerical work.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Relational result of the actual twenty-five-argument iteration,
including its first failure boundary and concrete intermediate state. -/
def detectCheckedResult {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s : A.State) (x : R.τ) (q K sourceEnd tableEnd : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) (v : ℕ) (mem' : ℕ → ℕ) : Prop :=
  ∃ detectedEnd detectedMem detected,
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      (args.take 20) mem detectedEnd detectedMem ∧
    R.rep b (A.detect s).2 detected detectedMem ∧
    (∀ z,R.foot b detected z → z<detectedEnd ∧ (R.foot b x z ∨ args.getD 8 0≤z)) ∧
    (if detectedMem (detectedEnd-1)=1 then
      (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 detected (A.detect s).1).post
        [b,args.getD 20 0,detectedMem (detectedEnd-2),args.getD 18 0,args.getD 17 0,args.getD 21 0,
          F.limbs,detectedEnd,args.getD 22 0,args.getD 23 0,args.getD 24 0] detectedMem v mem'
    else v=detectedEnd ∧ mem'=detectedMem) ∧ mem' (v-1)≤1 ∧ ZeroFrom mem' v

/-- State-indexed trace of one iteration. The Detect output memory is
shared by its refresh result and the subsequent checked transition. -/
def detectCheckedTransition {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s s' : A.State) (x : R.τ) (q K sourceEnd tableEnd : ℕ)
    (args : List ℕ) (mem mem' : ℕ → ℕ) (v : ℕ) : Prop :=
  ∃ detectedEnd detectedMem,
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      (args.take 20) mem detectedEnd detectedMem ∧
    if detectedMem (detectedEnd-1)=1 then
      ∃ detected,
      (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 detected (A.detect s).1).pre
        [b,args.getD 20 0,detectedMem (detectedEnd-2),args.getD 18 0,args.getD 17 0,args.getD 21 0,
          F.limbs,detectedEnd,args.getD 22 0,args.getD 23 0,args.getD 24 0] detectedMem ∧
      checkedUpdateTransition F A I κ α rate allocation (A.detect s).1 b
        (args.getD 20 0) (detectedMem (detectedEnd-2)) (args.getD 18 0) (args.getD 17 0)
        (args.getD 21 0) detectedEnd (args.getD 22 0) (args.getD 23 0) (args.getD 24 0)
        (A.detect s).2 s' detectedMem mem' v
    else s'=(A.detect s).2 ∧ v=detectedEnd ∧ mem'=detectedMem

/-- Rate for one plus the actual report cardinality. There is no extra
graph-size factor per reported name. -/
def detectCheckedCharge {w : ℕ} (F : MinRatioFormat w) (m E : ℕ) (rate : ℕ → ℕ) : ℕ :=
  4*rate m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
    Num.IPM.gradientCost F.limbs F.fmt.precision E+1698*F.limbs+5400

end MinCostFlow.IPM.Machine
