module

public import MinCostFlow.IPM.Machine.ReportedEdges
import WordRAM.Tactic
import Mathlib.Tactic.IntervalCases

/-!
# Evaluating a reported-edge call's table arguments

Each reported name selects the corresponding block of every dense table.
The fixed parent registers hold the table bases and shared scalars.
Check the actual argument expressions from these registers, using the
word bounds of the selected blocks. No semantic DS condition is needed
for this address calculation.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The per-edge call ignores the parent's name pointer, count and
initial heap arguments. Changing those three logical suffix fields
preserves every fixed register's expected value. -/
theorem reportedEdges_fixed_getD
    (b names count base lo up f L heap c r a one mn mx P E ld gd m
      names' count' heap' j : ℕ) (hj : j<20) (h1 : j≠1) (h2 : j≠2) (h8 : j≠8) :
    [b,names,count,base,lo,up,f,L,heap,c,r,a,one,mn,mx,P,E,ld,gd,m].getD j 0=
      [b,names',count',base,lo,up,f,L,heap',c,r,a,one,mn,mx,P,E,ld,gd,m].getD j 0 := by
  interval_cases j <;> simp_all

/-- The list entry's actual call arguments select exactly the reported
edge's base flow, capacities, cached flow and coefficient destinations. -/
theorem reportedEdgesCallArgs_eval {w : ℕ} (parent : State)
    (b names count base lo up f L initialHeap c r a one mn mx P E ld gd m heap e : ℕ)
    (hregs : ∀ j<20,j≠1 → j≠2 → j≠8 → parent.regs j=
      [b,names,count,base,lo,up,f,L,initialHeap,c,r,a,one,mn,mx,P,E,ld,gd,m].getD j 0)
    (hheap : parent.regs 21=heap) (hedge : parent.regs 22=e)
    (hoffset : parent.regs 23=e*L)
    (hwords : ∀ z∈[b,e,base+e*L,lo+e*L,up+e*L,f+e*L,L,heap,c+e*L,r,a,one,mn,mx,P,E,
      ld+e*L,gd+e*L,m],z<2^w) :
    evalArgs w parent reportedEdgesCallArgs=some
      [b,e,base+e*L,lo+e*L,up+e*L,f+e*L,L,heap,c+e*L,r,a,one,mn,mx,P,E,ld+e*L,gd+e*L,m] := by
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
  have hw1 : e<2^w := hwords _ (by simp)
  have hw2 : base+e*L<2^w := hwords _ (by simp)
  have hw3 : lo+e*L<2^w := hwords _ (by simp)
  have hw4 : up+e*L<2^w := hwords _ (by simp)
  have hw5 : f+e*L<2^w := hwords _ (by simp)
  have hw6 : L<2^w := hwords _ (by simp)
  have hw7 : heap<2^w := hwords _ (by simp)
  have hw8 : c+e*L<2^w := hwords _ (by simp)
  have hw9 : r<2^w := hwords _ (by simp)
  have hw10 : a<2^w := hwords _ (by simp)
  have hw11 : one<2^w := hwords _ (by simp)
  have hw12 : mn<2^w := hwords _ (by simp)
  have hw13 : mx<2^w := hwords _ (by simp)
  have hw14 : P<2^w := hwords _ (by simp)
  have hw15 : E<2^w := hwords _ (by simp)
  have hw16 : ld+e*L<2^w := hwords _ (by simp)
  have hw17 : gd+e*L<2^w := hwords _ (by simp)
  have hw18 : m<2^w := hwords _ (by simp)
  have : base<2^w := by omega
  have : lo<2^w := by omega
  have : up<2^w := by omega
  have : f<2^w := by omega
  have : c<2^w := by omega
  have : ld<2^w := by omega
  have : gd<2^w := by omega
  have : e*L<2^w := by omega
  unfold reportedEdgesCallArgs
  eval_expr

end MinCostFlow.IPM.Machine
