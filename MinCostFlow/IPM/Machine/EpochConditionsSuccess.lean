module

public import MinCostFlow.IPM.Machine.EpochLoopTrace
public import MinCostFlow.IPM.Machine.BudgetedIterationInvariant
public import MinCostFlow.IPM.Machine.BudgetedIterationSpace

/-!
# Advancing the finite epoch condition after actual success

Use the complete iteration's selected history extension and cache proof.
One reserved address block bounds its output, and the global reservation
supplies the next input block. The actual caller registers and counter
increment give the next loop point. The same concrete credit witness
and final memory are retained throughout.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- An actual successful entry and its caller continuation under `P` advance all
epoch conditions together, under the initial finite-loop space reservation. -/
theorem epochConditions_success_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K B initialHeap finish i : ℕ) (initialMem : ℕ → ℕ)
    (Pt : EpochPoint R.τ) (next : State) (s' : A.State) (y : R.τ) (v : ℕ)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i Pt)
    (hi : i<finish) (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure Pt.history Pt.eta Pt.op (2*i)) s' Pt.credit q K L.sourceEnd L.tableEnd
      (L.packet F I (Pt.machine.regs 8)) Pt.machine.mem v next.mem)
    (haccept : next.mem (v-1)=1) (hrep : R.rep L.handle s' y next.mem)
    (hmeta : ∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle Pt.credit z ∨ Pt.machine.regs 8≤z))
    (harrays : ∀ p∈[L.base,L.cost,L.lower,L.upper],p+I.m*F.limbs≤L.flow)
    (hscalars : ∀ p∈[L.residual,L.alpha,L.one,L.slackMin,L.slackMax],p+F.limbs≤L.flow)
    (heEnd : L.request+F.limbs≤L.flow)
    (hheap : next.regs 8=v) (hcount : next.regs 25=finish) (hcounter : next.regs 26=i+1)
    (hfixed : ∀ j<25,j≠8 → next.regs j=Pt.machine.regs j) :
    ∃ es actual,
      let Q : EpochPoint R.τ :=
        {history := appendHistoryIteration Pt.history (2*i) es
          (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
         eta := appendHistoryIterationEta Pt.eta (2*i) actual
         op := appendHistoryIterationOp Pt.op (2*i)
         credit := y
         machine := next}
      EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
        (budgetedIterationSpace F I.m L.exponent B) finish (i+1) Q ∧
      EpochAcceptedStep F A I κ α rate allocation R L q K i Pt Q := by
  obtain ⟨_,_,_,hregs,hHeapBound,hBudget,hPrefix,hvalid,hG,hpre,hgOld,hlOld,hcache,_,hhist⟩ := hcond
  have houtputSpace := budgetedIteration_space_output F A I κ α rate allocation R B halloc hpre hout
  have hnextHeap := epoch_iteration_heap_advance initialHeap (Pt.machine.regs 8) v
    (budgetedIterationSpace F I.m L.exponent B) i hHeapBound houtputSpace
  have hnextBlock := epoch_iteration_space_of_initial_bound w initialHeap v
    (budgetedIterationSpace F I.m L.exponent B) finish (i+1) (Nat.succ_le_of_lt hi) hnextHeap hspace
  have hnextSpace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s'
      [L.handle,v] next.mem+2*(I.m+1)+I.m*reportedEdgesScratch F I.m L.handle L.exponent allocation+4<2^w :=
    budgetedIteration_refresh_space F I.m L.exponent B L.handle v allocation halloc hnextBlock
  obtain ⟨es,actual,cEnd,cMem,hCpost,hCbit,hgSame,hlSame,hnd,hset,hNewValid,hNewG,hstate,hgNew,hlNew,hNewCache,hNewPre,hNewRanges,hnorm,hNewPrefix,hNewBudget,_⟩ :=
    budgetedIteration_success_invariant_upTo_on F A I κ α Ψ eps hA hP rate allocation R
      Pt.history Pt.eta Pt.op (2*i) hvalid hG (hP.history hG hhist) hpre hout haccept hrep hmeta
      harrays hscalars heEnd
      hgOld hlOld hcache hnextSpace
  let Q : EpochPoint R.τ :=
    {history := appendHistoryIteration Pt.history (2*i) es
      (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
      (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
     eta := appendHistoryIterationEta Pt.eta (2*i) actual
     op := appendHistoryIterationOp Pt.op (2*i)
     credit := y
     machine := next}
  have hstage : 2*i+1+1=2*(i+1) := by omega
  have hsNext : s'=minRatioState A.eraseFailure Q.history Q.eta Q.op (2*(i+1)) := by
    simpa only [Q,hstage] using hstate
  refine ⟨es,actual,?_,?_⟩
  swap
  · change next.mem (next.regs 8-1)=1 ∧ _ ∧ _
    rw [hheap]
    exact ⟨haccept,hsNext ▸ hout,es,actual,cEnd,cMem,hCpost,hCbit,hgSame,hlSame,hnd,hset,rfl,rfl,rfl,hnorm⟩
  change EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
    (budgetedIterationSpace F I.m L.exponent B) finish (i+1) Q
  refine ⟨Nat.succ_le_of_lt hi,hcount,hcounter,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hNewRanges,?_⟩
  · intro j hj
    change next.regs j=(L.packet F I (next.regs 8)).getD j 0
    rw [hheap]
    by_cases hj8 : j=8
    · subst j
      exact hheap.trans (L.packet_heap F I v).symm
    · exact (hfixed j hj hj8).trans ((hregs j hj).trans
        (L.packet_fixed F I (Pt.machine.regs 8) v j hj hj8))
  · change next.regs 8 ≤ initialHeap+(i+1)*budgetedIterationSpace F I.m L.exponent B
    rw [hheap]
    exact hnextHeap
  · change next.mem (next.regs 8-3)≤5*I.m
    rw [hheap]
    exact hNewBudget.trans hBudget
  · intro z hz
    exact (hNewPrefix z hz).trans (hPrefix z hz)
  · simpa only [Q,hstage] using hNewValid
  · simpa only [Q,hstage] using hNewG
  · change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R L.handle
      (minRatioState A.eraseFailure Q.history Q.eta Q.op (2*(i+1))) y q K L.sourceEnd L.tableEnd).pre
      ((L.packet F I (next.regs 8)).take 20) next.mem
    rw [hheap,← hsNext]
    exact hNewPre
  · simpa only [Q,hstage] using hgNew.symm
  · simpa only [Q,hstage] using hlNew.symm
  · simpa only [Q,hstage] using hNewCache
  · have hl : LengthsWithin (Pt.history.G (2*i)) F.rangeExponent
        (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
      rw [hG (2*i) le_rfl]
      intro e he
      exact ⟨(hNewRanges e (Finset.mem_range.mp he)).2.2.2.1,
        (hNewRanges e (Finset.mem_range.mp he)).2.2.2.2⟩
    simpa only [Q,hstage] using appendHistoryIteration_lengthsWithin es _ _ hhist hl

/-- An actual successful entry and its caller continuation advance all
epoch conditions together, under the initial finite-loop space reservation. -/
theorem epochConditions_success_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K B initialHeap finish i : ℕ) (initialMem : ℕ → ℕ)
    (P : EpochPoint R.τ) (next : State) (s' : A.State) (y : R.τ) (v : ℕ)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (hi : i<finish) (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit q K L.sourceEnd L.tableEnd
      (L.packet F I (P.machine.regs 8)) P.machine.mem v next.mem)
    (haccept : next.mem (v-1)=1) (hrep : R.rep L.handle s' y next.mem)
    (hmeta : ∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z))
    (harrays : ∀ p∈[L.base,L.cost,L.lower,L.upper],p+I.m*F.limbs≤L.flow)
    (hscalars : ∀ p∈[L.residual,L.alpha,L.one,L.slackMin,L.slackMax],p+F.limbs≤L.flow)
    (heEnd : L.request+F.limbs≤L.flow)
    (hheap : next.regs 8=v) (hcount : next.regs 25=finish) (hcounter : next.regs 26=i+1)
    (hfixed : ∀ j<25,j≠8 → next.regs j=P.machine.regs j) :
    ∃ es actual,
      let Q : EpochPoint R.τ :=
        {history := appendHistoryIteration P.history (2*i) es
          (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
         eta := appendHistoryIterationEta P.eta (2*i) actual
         op := appendHistoryIterationOp P.op (2*i)
         credit := y
         machine := next}
      EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
        (budgetedIterationSpace F I.m L.exponent B) finish (i+1) Q ∧
      EpochAcceptedStep F A I κ α rate allocation R L q K i P Q :=
  epochConditions_success_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    (stageAdmits_true _ _)

    rate allocation R L q K B initialHeap finish i initialMem P next s' y v hcond hi halloc
    hspace hout haccept hrep hmeta harrays hscalars heEnd hheap hcount hcounter hfixed

/-- An actual successful entry and its caller continuation advance all
epoch conditions together, under the initial finite-loop space reservation. -/
theorem epochConditions_success {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (L : EpochLayout) (q K B initialHeap finish i : ℕ) (initialMem : ℕ → ℕ)
    (P : EpochPoint R.τ) (next : State) (s' : A.State) (y : R.τ) (v : ℕ)
    (hcond : EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
      (budgetedIterationSpace F I.m L.exponent B) finish i P)
    (hi : i<finish) (halloc : ∀ j<4,∀ args,allocation j args≤B)
    (hspace : initialHeap+(finish+1)*budgetedIterationSpace F I.m L.exponent B<2^w)
    (hout : budgetedIterationResult F A I κ α rate allocation R L.handle
      (minRatioState A.eraseFailure P.history P.eta P.op (2*i)) s' P.credit q K L.sourceEnd L.tableEnd
      (L.packet F I (P.machine.regs 8)) P.machine.mem v next.mem)
    (haccept : next.mem (v-1)=1) (hrep : R.rep L.handle s' y next.mem)
    (hmeta : ∀ z,R.foot L.handle y z → z<v ∧ (R.foot L.handle P.credit z ∨ P.machine.regs 8≤z))
    (harrays : ∀ p∈[L.base,L.cost,L.lower,L.upper],p+I.m*F.limbs≤L.flow)
    (hscalars : ∀ p∈[L.residual,L.alpha,L.one,L.slackMin,L.slackMax],p+F.limbs≤L.flow)
    (heEnd : L.request+F.limbs≤L.flow)
    (hheap : next.regs 8=v) (hcount : next.regs 25=finish) (hcounter : next.regs 26=i+1)
    (hfixed : ∀ j<25,j≠8 → next.regs j=P.machine.regs j) :
    ∃ es actual,
      let Q : EpochPoint R.τ :=
        {history := appendHistoryIteration P.history (2*i) es
          (readVector next.mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector next.mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
         eta := appendHistoryIterationEta P.eta (2*i) actual
         op := appendHistoryIterationOp P.op (2*i)
         credit := y
         machine := next}
      EpochConditions F A I κ α rate allocation R L q K initialMem initialHeap
        (budgetedIterationSpace F I.m L.exponent B) finish (i+1) Q ∧
      EpochAcceptedStep F A I κ α rate allocation R L q K i P Q :=
  epochConditions_success_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) rate allocation R L q K B
    initialHeap finish i initialMem P next s' y v hcond hi halloc hspace hout haccept hrep hmeta
    harrays hscalars heEnd hheap hcount hcounter hfixed

end MinCostFlow.IPM.Machine
