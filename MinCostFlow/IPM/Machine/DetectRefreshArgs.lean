module

public import MinCostFlow.IPM.Machine.DetectRefresh
import WordRAM.Tactic

/-!
# Evaluating the checked-refresh call inside the combined stage

The decoded pointer and count occupy registers 21 and 22; register 20
holds the current allocation endpoint. All table and shared numeric
registers retain their original values. The refresh input's word bounds
therefore justify the exact twenty evaluated arguments and their fixed
argument-evaluation cost.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual argument expression packet evaluates to the decoded
report and unchanged cached tables, with the new allocation endpoint. -/
theorem detectRefreshArgs_eval {w : ℕ} (parent : State)
    (b names base lo up f L heap c r a one mn mx P E ld gd m dHeap pointer count : ℕ)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,m,base,lo,up,f,L,heap,c,r,a,one,mn,mx,P,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 20=dHeap) (hpointer : parent.regs 21=pointer)
    (hcount : parent.regs 22=count)
    (hwords : ∀ z∈[b,pointer+1,count,base,lo,up,f,L,dHeap,c,r,a,one,mn,mx,P,E,ld,gd,m],z<2^w) :
    evalArgs w parent detectRefreshArgs=some
      [b,pointer+1,count,base,lo,up,f,L,dHeap,c,r,a,one,mn,mx,P,E,ld,gd,m] := by
  have h0 := hregs 0 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero] at h0
  have h3 := hregs 3 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h3
  have h4 := hregs 4 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h4
  have h5 := hregs 5 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h5
  have h6 := hregs 6 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h6
  have h7 := hregs 7 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h7
  have h9 := hregs 9 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h9
  have h10 := hregs 10 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h10
  have h11 := hregs 11 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h11
  have h12 := hregs 12 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h12
  have h13 := hregs 13 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h13
  have h14 := hregs 14 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h14
  have h15 := hregs 15 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h15
  have h16 := hregs 16 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h16
  have h17 := hregs 17 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h17
  have h18 := hregs 18 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h18
  have h19 := hregs 19 (by decide) (by decide) (by decide) (by decide)
  simp only [List.getD_cons_zero,List.getD_cons_succ] at h19
  have hw0 : b<2^w := hwords _ (by simp)
  have hw1 : pointer+1<2^w := hwords _ (by simp)
  have hw2 : count<2^w := hwords _ (by simp)
  have hw3 : base<2^w := hwords _ (by simp)
  have hw4 : lo<2^w := hwords _ (by simp)
  have hw5 : up<2^w := hwords _ (by simp)
  have hw6 : f<2^w := hwords _ (by simp)
  have hw7 : L<2^w := hwords _ (by simp)
  have hw8 : dHeap<2^w := hwords _ (by simp)
  have hw9 : c<2^w := hwords _ (by simp)
  have hw10 : r<2^w := hwords _ (by simp)
  have hw11 : a<2^w := hwords _ (by simp)
  have hw12 : one<2^w := hwords _ (by simp)
  have hw13 : mn<2^w := hwords _ (by simp)
  have hw14 : mx<2^w := hwords _ (by simp)
  have hw15 : P<2^w := hwords _ (by simp)
  have hw16 : E<2^w := hwords _ (by simp)
  have hw17 : ld<2^w := hwords _ (by simp)
  have hw18 : gd<2^w := hwords _ (by simp)
  have hw19 : m<2^w := hwords _ (by simp)
  have hpW : pointer<2^w := by omega
  have h1 : 1<2^w := by omega
  unfold detectRefreshArgs
  eval_expr

/-- Exact cost charged by the machine for the refresh argument packet. -/
theorem detectRefreshArgs_size : argsSize detectRefreshArgs=22 := by rfl

end MinCostFlow.IPM.Machine
