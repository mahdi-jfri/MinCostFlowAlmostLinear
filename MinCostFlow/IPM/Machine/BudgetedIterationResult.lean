module

public import MinCostFlow.IPM.Machine.DetectCheckedResult
public import MinCostFlow.IPM.Machine.EpochBudgetRecord

/-!
# Trace and linear charge of a budgeted actual iteration

Retain the actual Detect memory and its concrete state. A fitting
successful refresh proceeds to the checked Update and records the
remaining budget. Every other branch stops before Update with zero
status. All result metadata are fresh, keeping the existing epoch-loop
packet and numerical table frames intact.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Actual intermediate calls and final fresh budget metadata. The
state parameter is the same state retained by the run's credit bound. -/
def budgetedIterationResult {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (b : ℕ) (s s' : A.State) (x : R.τ) (q K sourceEnd tableEnd : ℕ)
    (args : List ℕ) (mem : ℕ → ℕ) (v : ℕ) (final : ℕ → ℕ) : Prop :=
  let remaining := mem (args.getD 8 0-3)
  let count := (A.detect s).1.card
  ∃ cEnd cMem mid,
    (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
      (args.take 20) mem cEnd cMem ∧ R.rep b (A.detect s).2 mid cMem ∧
    (∀ z,R.foot b mid z → z<cEnd ∧ (R.foot b x z ∨ args.getD 8 0≤z)) ∧
    if cMem (cEnd-1)=1 ∧ count≤remaining then
      ∃ coreEnd coreMem,
        (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 mid (A.detect s).1).pre
          [b,args.getD 20 0,cMem (cEnd-2),args.getD 18 0,args.getD 17 0,args.getD 21 0,
            F.limbs,cEnd,args.getD 22 0,args.getD 23 0,args.getD 24 0] cMem ∧
        (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 mid (A.detect s).1).post
          [b,args.getD 20 0,cMem (cEnd-2),args.getD 18 0,args.getD 17 0,args.getD 21 0,
            F.limbs,cEnd,args.getD 22 0,args.getD 23 0,args.getD 24 0] cMem coreEnd coreMem ∧
        checkedUpdateTransition F A I κ α rate allocation (A.detect s).1 b
          (args.getD 20 0) (cMem (cEnd-2)) (args.getD 18 0) (args.getD 17 0) (args.getD 21 0)
          cEnd (args.getD 22 0) (args.getD 23 0) (args.getD 24 0) (A.detect s).2 s' cMem coreMem coreEnd ∧
        (epochBudgetRecordContract w).post [remaining-count,count,coreMem (coreEnd-1),coreEnd] coreMem v final
    else s'=(A.detect s).2 ∧
      (epochBudgetRecordContract w).post [remaining,count,0,cEnd] cMem v final

/-- One plus the actual report size pays all numerical calls, DS work,
budget comparisons and the final three fresh metadata words. -/
def budgetedIterationCharge {w : ℕ} (F : MinRatioFormat w) (m E : ℕ) (rate : ℕ → ℕ) : ℕ :=
  4*rate m+Num.IPM.lengthCost F.limbs F.fmt.precision E+
    Num.IPM.gradientCost F.limbs F.fmt.precision E+1698*F.limbs+6000

end MinCostFlow.IPM.Machine
