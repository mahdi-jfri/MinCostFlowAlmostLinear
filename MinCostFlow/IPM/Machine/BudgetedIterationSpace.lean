module

public import MinCostFlow.IPM.Machine.BudgetedIterationResult
public import MinCostFlow.IPM.Machine.QueryAllocationBound
public import MinCostFlow.IPM.Machine.UpdateAllocationBound
import MinCostFlow.IPM.Machine.DetectRefreshDetectInput
import MinCostFlow.IPM.Machine.CheckedUpdateOutput

/-!
# A uniform address-space budget for actual epoch iterations

Bound each DS allocation by its supplied space allowance. The analysis
maxima for Query and Update inherit that allowance without a factor in
the word count. Reserve one worst-case iteration block. This is an
address-space bound, independent of the linear reported-size cost proof;
unused reserved words require no word-by-word initialization.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Fresh address space sufficient for one complete iteration, when each
DS operation allocates at most `B` words. This is not a time bound. -/
def budgetedIterationSpace {w : ℕ} (F : MinRatioFormat w) (m E B : ℕ) : ℕ :=
  2*B+m*(B+16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+12)+2*F.limbs+16

private theorem iteration_space_arith (L len grad B m count det query update : ℕ)
    (hc : count≤m) (hd : det≤B) (hq : query≤B+16*L+len+grad+4) (hu : update≤B) :
    det+2*(m+1)+m*query+4+2+(1+6*count)+update+(1+2*L)+2+3≤
      2*B+m*(B+16*L+len+grad+12)+2*L+16 := by
  have hm := Nat.mul_le_mul_left m hq
  simp only [Nat.mul_add] at hm ⊢
  omega

/-- A fitting reserved iteration block supplies the full call budget,
including the final three metadata words. -/
theorem budgetedIteration_space_input {w : ℕ} (F : MinRatioFormat w)
    (m E B b heap g l eta count : ℕ) (allocation : ℕ → List ℕ → ℕ)
    (halloc : ∀ i<4,∀ args,allocation i args≤B) (hcount : count≤m)
    (hspace : heap+budgetedIterationSpace F m E B<2^w) :
    (heap+allocation 2 [b,heap]+2*(m+1)+m*reportedEdgesScratch F m b E allocation+4+2)+
      (1+6*count)+updateAllocationBound w b g l eta allocation+(1+2*F.limbs)+2+3<2^w := by
  have hq := queryAllocationBound_le (w:=w) (m:=m) (b:=b) allocation
    (fun e _ h _ => halloc 1 (by decide) [b,e,h])
  have hu := updateAllocationBound_le (w:=w) (b:=b) (g:=g) (l:=l) (eta:=eta) allocation
    (fun batch _ h _ => halloc 0 (by decide) [b,batch,g,l,eta,h])
  have hs : reportedEdgesScratch F m b E allocation≤B+16*F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 := by
    unfold reportedEdgesScratch
    omega
  have hh := iteration_space_arith F.limbs _ _ B m count _ _ _ hcount (halloc 2 (by decide) [b,heap]) hs hu
  change heap+(2*B+m*(B+16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+12)+2*F.limbs+16)<2^w at hspace
  omega

/-- The same reserved block covers the next Detect/refresh precondition,
whose allocation does not depend on the abstract state or memory. -/
theorem budgetedIteration_refresh_space {w : ℕ} (F : MinRatioFormat w)
    (m E B b heap : ℕ) (allocation : ℕ → List ℕ → ℕ)
    (halloc : ∀ i<4,∀ args,allocation i args≤B)
    (hspace : heap+budgetedIterationSpace F m E B<2^w) :
    heap+allocation 2 [b,heap]+2*(m+1)+m*reportedEdgesScratch F m b E allocation+4<2^w := by
  have hh := budgetedIteration_space_input F m E B b heap 0 0 0 0 allocation halloc (Nat.zero_le m) hspace
  omega

/-- Every actual complete iteration advances by at most one reserved
block, including early rejection and a failed Update. -/
theorem budgetedIteration_space_output {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State) (B : ℕ)
    (halloc : ∀ i<4,∀ args,allocation i args≤B)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final) :
    v≤heap+budgetedIterationSpace F I.m E B := by
  have hcount := (detectRefresh_detect_pre F A (namedInstance I) I.m κ α rate allocation R hpre).2
  have hq := queryAllocationBound_le (w:=w) (m:=I.m) (b:=b) allocation
    (fun e _ h _ => halloc 1 (by decide) [b,e,h])
  have hu := updateAllocationBound_le (w:=w) (b:=b) (g:=gd) (l:=ld) (eta:=request) allocation
    (fun batch _ h _ => halloc 0 (by decide) [b,batch,gd,ld,request,h])
  have hs : reportedEdgesScratch F I.m b E allocation≤B+16*F.limbs+
      Num.IPM.lengthSpace F.limbs F.fmt.precision E+Num.IPM.gradientSpace F.limbs F.fmt.precision E+4 := by
    unfold reportedEdgesScratch
    omega
  have hbound := iteration_space_arith F.limbs _ _ B I.m (A.detect s).1.card _ _ _
    hcount (halloc 2 (by decide) [b,heap]) hs hu
  obtain ⟨cEnd,cMem,mid,hC,_,_,hbranch⟩ := hout
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hCupper⟩ := hC
  change cEnd≤heap+allocation 2 [b,heap]+2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4 at hCupper
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch
  change v≤heap+(2*B+I.m*(B+16*F.limbs+Num.IPM.lengthSpace F.limbs F.fmt.precision E+
    Num.IPM.gradientSpace F.limbs F.fmt.precision E+12)+2*F.limbs+16)
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,hQpre,hQpost,_,hrecord⟩ := hbranch
    have hQupper := checkedUpdate_end_le_of_pre F A I κ α rate allocation R hQpre hQpost
    have hv : v=coreEnd+3 := hrecord.2
    omega
  · obtain ⟨_,hrecord⟩ := hbranch
    have hv : v=cEnd+3 := hrecord.2
    omega

/-- One global address reservation supplies the next complete iteration
block at every finite-loop counter value, including the terminal input. -/
theorem epoch_iteration_space_of_initial_bound (w initialHeap heap space N i : ℕ)
    (hi : i≤N) (hheap : heap ≤ initialHeap+i*space)
    (hspace : initialHeap+(N+1)*space<2^w) : heap+space<2^w := by
  have hm := Nat.mul_le_mul_right space (Nat.succ_le_succ hi)
  simp only [Nat.succ_mul] at hm hspace
  omega

/-- The actual output bound advances the finite-loop heap invariant by
one block. It does not add any corresponding running-time charge. -/
theorem epoch_iteration_heap_advance (initialHeap heap next space i : ℕ)
    (hheap : heap ≤ initialHeap+i*space) (hnext : next≤heap+space) :
    next ≤ initialHeap+(i+1)*space := by
  simp only [Nat.add_mul,Nat.one_mul]
  omega

end MinCostFlow.IPM.Machine
