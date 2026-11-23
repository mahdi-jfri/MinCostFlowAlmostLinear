module

public import MinCostFlow.IPM.Machine.BudgetedIterationResult
import MinCostFlow.IPM.Machine.CheckedUpdateSuccess
import MinCostFlow.IPM.Machine.CheckedUpdateOutput
import MinCostFlow.IPM.Machine.VectorFrame
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Guarded numerical ranges after a successful actual iteration

The accepted coefficient scan checks every reported entry, and its
input condition covers the unreported entries. The checked continuation
and fresh budget record preserve all coefficient words. Thus the next
iteration receives valid coefficient blocks and their complete checked
ranges, even on a target whose optimum side is not yet known.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual successful entry preserves all coefficient word validity
and the complete gradient/positive-length range invariant. -/
theorem budgetedIteration_success_ranges {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1)
    (hbefore : tableEnd≤heap) (havoid : ∀ z<tableEnd,¬R.foot b x z)
    (hg : gd+I.m*F.limbs≤tableEnd) (hl : ld+I.m*F.limbs≤tableEnd) :
    ∀ e<I.m,Num.Valid final (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid final (ld+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  obtain ⟨cEnd,cMem,mid,hC,_,hmeta,hbranch⟩ := hout
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch hmeta
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,hpre,hQ,_,hrecord⟩ := hbranch
    have hcoreSuccess := (epochBudgetRecord_output hrecord).2.2.symm.trans haccept
    have hcopy := hC
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
    change heap≤cEnd at hLo
    have hnewAvoid : ∀ z<tableEnd,¬R.foot b mid z := by
      intro z hz hfoot
      rcases (hmeta z hfoot).2 with hold | hfresh
      · exact havoid z hz hold
      · omega
    have hranges := checkedUpdate_success_ranges F A I κ α rate allocation R hpre hQ hcoreSuccess
      hnewAvoid (hbefore.trans hLo) hg hl
    have hend := checkedUpdate_end_ge F A I κ α rate allocation R hQ
    have hrecordFrame := hrecord.1.2.2.1
    change ∀ z<coreEnd,final z=coreMem z at hrecordFrame
    have hwhole : ∀ z<tableEnd,final z=cMem z := by
      intro z hz
      exact (hrecordFrame z (by omega)).trans
        (checkedUpdate_frame F A I κ α rate allocation R hQ z (by omega) (hnewAvoid z hz))
    have hgSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision)
      hrecordFrame (by omega : gd+I.m*F.limbs≤coreEnd)
    have hlSame := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision)
      hrecordFrame (by omega : ld+I.m*F.limbs≤coreEnd)
    have hvalid : ∀ e<I.m,Num.Valid cMem (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid cMem (ld+e*F.limbs) F.fmt.limbBits F.limbs := by
      obtain ⟨source',report',g',l',eta',heap',neg',mx',mn',heq,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hvalid,_⟩ := hpre
      simp only [List.cons.injEq,and_true,true_and] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      exact hvalid
    intro e he
    refine ⟨Num.IPM.valid_frozen hwhole ((reported_entry_end gd F.limbs e I.m he).trans hg) (hvalid e he).1,
      Num.IPM.valid_frozen hwhole ((reported_entry_end ld F.limbs e I.m he).trans hl) (hvalid e he).2,?_⟩
    rw [hgSame,hlSame]
    exact hranges e (Finset.mem_range.mpr he)
  · obtain ⟨_,hrecord⟩ := hbranch
    have hzero := (epochBudgetRecord_output hrecord).2.2
    omega

end MinCostFlow.IPM.Machine
