module

public import MinCostFlow.IPM.Machine.EpochCompleteRun
public import MinCostFlow.IPM.Machine.BudgetedIterationSpace

/-!
# Address space for a complete epoch

Each attempted iteration uses one reserved block. The final success
flag and full read together fit in one further block.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete epoch's endpoint stays in its reserved memory on
every branch, including a rejected full read. -/
theorem epochComplete_end_le {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K heap B finish loopEnd : ℕ) (mem : ℕ → ℕ)
    (loopState : State) (loopCredit : R.τ) (certified : EpochPoint R.τ → Prop)
    {v : ℕ} {final : State} {credit : R.τ}
    (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hpost : EpochCompletePost F A I κ α rate allocation R L q K heap
      (budgetedIterationSpace F I.m L.exponent B) finish mem loopEnd loopState loopCredit certified v final credit)
    (hstopped : loopState.mem (loopEnd-1)≠1 →
      ∃ j<finish, ∃ Q : EpochPoint R.τ,
        EpochConditions F A I κ α rate allocation R L q K mem heap
          (budgetedIterationSpace F I.m L.exponent B) finish j Q ∧
        EpochStoppedStep F A I κ α rate allocation R L q K j Q loopEnd loopState loopCredit) :
    v≤heap+(finish+1)*budgetedIterationSpace F I.m L.exponent B := by
  let space := budgetedIterationSpace F I.m L.exponent B
  change v≤heap+(finish+1)*space
  unfold EpochCompletePost at hpost
  split at hpost
  · obtain ⟨Q,hcond,_,_,hflag,_,_,hout,_⟩ := hpost
    have hheap : Q.machine.regs 8≤heap+finish*space := hcond.2.2.2.2.1
    have hflagEnd : loopEnd=Q.machine.regs 8+1 := hflag.2
    obtain ⟨_,_,_,_,hEnd,_⟩ := hout
    change v≤loopEnd+I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+1 at hEnd
    have hq := queryAllocationBound_le (w:=w) (m:=I.m) (b:=L.handle) allocation
      (fun e _ h _ => halloc 1 (by decide) [L.handle,e,h])
    have hs : reportedEdgesScratch F I.m L.handle L.exponent allocation≤B+16*F.limbs+
        Num.IPM.lengthSpace F.limbs F.fmt.precision L.exponent+
        Num.IPM.gradientSpace F.limbs F.fmt.precision L.exponent+4 := by
      unfold reportedEdgesScratch
      omega
    have hs' := Nat.mul_le_mul_left I.m hs
    have hmaterial : I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+2≤space := by
      dsimp only [space,budgetedIterationSpace]
      simp only [Nat.mul_add] at hs' ⊢
      omega
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · rename_i hbit
    obtain ⟨j,hj,Q,hcond,hstop⟩ := hstopped hbit
    obtain ⟨rfl,_,_,_⟩ := hpost
    obtain ⟨_,_,_,hout,_,_,_⟩ := hstop
    have hheap : Q.machine.regs 8≤heap+j*space := hcond.2.2.2.2.1
    have hpre := hcond.2.2.2.2.2.2.2.2.2.1
    have hEnd : v≤Q.machine.regs 8+space :=
      budgetedIteration_space_output F A I κ α rate allocation R B halloc hpre hout
    have hsteps := Nat.mul_le_mul_right space (show j≤finish by omega)
    rw [Nat.add_mul,Nat.one_mul]
    omega

end MinCostFlow.IPM.Machine
