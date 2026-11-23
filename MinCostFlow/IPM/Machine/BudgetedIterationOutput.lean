module

public import MinCostFlow.IPM.Machine.BudgetedIterationResult
import MinCostFlow.IPM.Machine.CheckedUpdateOutput
import Lean.Elab.Tactic.Omega

/-!
# Budget accounting for actual iteration results

Every branch records the actual report count. A fitting report consumes
that count, even if the checked Update subsequently stops. Other branches
retain the old budget and return zero. Thus every successful iteration
pays for its report from the incoming budget.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Successful actual iterations decrease the remaining budget by exactly
the report count. A stopping iteration can only decrease that budget. -/
theorem budgetedIteration_output {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {b : ℕ} {s s' : A.State} {x : R.τ} {q K sourceEnd tableEnd : ℕ}
    {args : List ℕ} {mem final : ℕ → ℕ} {v : ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args mem v final) :
    final (v-2)=(A.detect s).1.card ∧
    final (v-3)≤mem (args.getD 8 0-3) ∧
    (final (v-1)=1 → final (v-3)+(A.detect s).1.card=mem (args.getD 8 0-3)) := by
  obtain ⟨cEnd,cMem,mid,_,_,_,hbranch⟩ := hout
  split_ifs at hbranch with hfit
  · obtain ⟨coreEnd,coreMem,_,_,_,hrecord⟩ := hbranch
    obtain ⟨hremaining,hcount,hbit⟩ := epochBudgetRecord_output hrecord
    refine ⟨hcount,?_,?_⟩
    · rw [hremaining]
      exact Nat.sub_le _ _
    · intro _
      rw [hremaining]
      exact Nat.sub_add_cancel hfit.2
  · obtain ⟨_,hrecord⟩ := hbranch
    obtain ⟨hremaining,hcount,hbit⟩ := epochBudgetRecord_output hrecord
    refine ⟨hcount,by omega,?_⟩
    intro hsuccess
    omega

/-- Every actual result has a bit, three allocated metadata words and a
fresh suffix, including a rejection before Update. -/
theorem budgetedIteration_status {w : ℕ} {F : MinRatioFormat w}
    {A : MinRatioDataStructureWithFailure} {I : Instance} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ} {R : DSRep A.State}
    {b : ℕ} {s s' : A.State} {x : R.τ} {q K sourceEnd tableEnd : ℕ}
    {args : List ℕ} {mem final : ℕ → ℕ} {v : ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args mem v final) :
    final (v-1)≤1 ∧ 3≤v ∧ ZeroFrom final v := by
  obtain ⟨cEnd,cMem,mid,_,_,_,hbranch⟩ := hout
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,_,hchecked,_,hrecord⟩ := hbranch
    have hbit := (checkedUpdate_status F A I κ α rate allocation R hchecked).1
    have hd := (epochBudgetRecord_output hrecord).2.2
    have hv : v=coreEnd+3 := hrecord.2
    exact ⟨by omega,by omega,hrecord.1.2.2.2.1⟩
  · obtain ⟨_,hrecord⟩ := hbranch
    have hd := (epochBudgetRecord_output hrecord).2.2
    have hv : v=cEnd+3 := hrecord.2
    exact ⟨by omega,by omega,hrecord.1.2.2.2.1⟩

/-- Fresh footprint growth preserves separation from the old coefficient
tables and full name list. These are the exact two avoidance conditions
needed by the next refresh input. -/
theorem iteration_footprint_separation {σ : Type} (R : DSRep σ)
    {b heap next tableEnd names m : ℕ} {x y : R.τ}
    (hmeta : ∀ z,R.foot b y z → z<next ∧ (R.foot b x z ∨ heap≤z))
    (htable : tableEnd≤heap) (hnames : names+m≤heap)
    (holdTable : ∀ z<tableEnd,¬R.foot b x z)
    (holdNames : ∀ i<m,¬R.foot b x (names+i)) :
    (∀ z<tableEnd,¬R.foot b y z) ∧ (∀ i<m,¬R.foot b y (names+i)) := by
  constructor
  · intro z hz hfoot
    rcases (hmeta z hfoot).2 with hold | hfresh
    · exact holdTable z hz hold
    · omega
  · intro i hi hfoot
    rcases (hmeta (names+i) hfoot).2 with hold | hfresh
    · exact holdNames i hi hold
    · omega

/-- Every actual outcome allocates its final three-word record beyond
the incoming heap, including either pre-Update rejection. -/
theorem budgetedIteration_end_ge {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
 : heap+3≤v := by
  obtain ⟨cEnd,cMem,mid,hC,_,_,hbranch⟩ := hout
  have hcopy := hC
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
  change heap≤cEnd at hLo
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,_,hQ,_,hrecord⟩ := hbranch
    have hend := checkedUpdate_end_ge F A I κ α rate allocation R hQ
    have hv : v=coreEnd+3 := hrecord.2
    omega
  · obtain ⟨_,hrecord⟩ := hbranch
    have hv : v=cEnd+3 := hrecord.2
    omega

end MinCostFlow.IPM.Machine
