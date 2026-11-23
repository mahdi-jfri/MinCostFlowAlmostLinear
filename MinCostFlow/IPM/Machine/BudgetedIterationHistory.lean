module

public import MinCostFlow.IPM.Machine.BudgetedIterationTrace
public import MinCostFlow.IPM.Machine.DetectCheckedHistory
import MinCostFlow.IPM.Machine.CheckedUpdateFrame
import MinCostFlow.IPM.Machine.CheckedUpdateOutput
import MinCostFlow.IPM.Machine.VectorFrame

/-!
# Extending the shared history after budgeted success

Recover the actual checked core before its fresh budget metadata and
apply the valid-history extension proved for that core. Retain the
actual scalar in the core memory and the metadata postcondition, so
later framing uses the same memory and the same credited state.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful budgeted iteration extends the valid shared history by
its actual Detect and rounded Update, retaining the exact returned state. -/
theorem budgetedIteration_success_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (htrace : budgetedIterationResult F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1)
    (hgEnd : gd+I.m*F.limbs≤heap) (hlEnd : ld+I.m*F.limbs≤heap)
    (heEnd : request+F.limbs≤f) (hfEnd : f≤heap)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T) :
    ∃ (coreEnd : ℕ) (coreMem : ℕ → ℕ),
      (epochBudgetRecordContract w).post
        [mem (heap-3)-(A.detect (minRatioState A.eraseFailure D eta op T)).1.card,
          (A.detect (minRatioState A.eraseFailure D eta op T)).1.card,1,coreEnd] coreMem v final ∧
    ∃ (cEnd : ℕ) (cMem : ℕ → ℕ) (es : List ℕ) (actual : ℝ) (answer : ℕ),
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
        (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      cMem (cEnd-1)=1 ∧
      readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m=
        readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m=
        readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      ScalarAt coreMem (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      let gradient := readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m
      let lengths := readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m
      MinRatioHistoryValid (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationOp op T) (T+1+1) ∧
      s'=minRatioState A.eraseFailure (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1+1) := by
  obtain ⟨cEnd,cMem,mid,hCpost,_,hmeta,hbranch⟩ := htrace
  change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
    (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem at hCpost
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch hmeta
  split_ifs at hbranch with hfit
  · obtain ⟨coreEnd,coreMem,hCheckedPre,hQpost,hchecked,hrecord⟩ := hbranch
    have hcoreSuccess := (epochBudgetRecord_output hrecord).2.2.symm.trans haccept
    obtain ⟨es,actual,answer,hdata⟩ := detectChecked_calls_history F A I κ α rate allocation R D eta op T
      hvalid hG hpre hCpost hCheckedPre hchecked hcoreSuccess hgEnd hlEnd heEnd hfEnd hgOld hlOld
    have hbounds : (∀ z<tableEnd,¬R.foot b x z) ∧ tableEnd≤heap ∧
        gd+I.m*F.limbs≤tableEnd ∧ ld+I.m*F.limbs≤tableEnd := by
      obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
      simp only [List.cons.injEq,and_true,true_and] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
        _,_,_,_,_,_,_,hprefix,_,_,htEnd,hnEnd,_,_,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
      simp only [List.cons.injEq,and_true,true_and] at heq
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
      exact ⟨hprefix,by omega,hgdEnd,hldEnd⟩
    have hcopy := hCpost
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
    change heap≤cEnd at hLo
    have hnewAvoid : ∀ z<tableEnd,¬R.foot b mid z := by
      intro z hz hfoot
      rcases (hmeta z hfoot).2 with hold | hfresh
      · exact hbounds.1 z hz hold
      · omega
    have hcoreArrays := checkedUpdate_coefficient_vectors F A I κ α rate allocation R hQpost hnewAvoid
      (hbounds.2.1.trans hLo) hbounds.2.2.1 hbounds.2.2.2
    have hend := checkedUpdate_end_ge F A I κ α rate allocation R hQpost
    have hframe := hrecord.1.2.2.1
    change ∀ z<coreEnd,final z=coreMem z at hframe
    have hgCore := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision)
      hframe (by omega : gd+I.m*F.limbs≤coreEnd)
    have hlCore := readVector_eq_of_agree_below (h:=F.fmt.limbBits) (P:=F.fmt.precision)
      hframe (by omega : ld+I.m*F.limbs≤coreEnd)
    have hgSame := hgCore.trans hcoreArrays.1
    have hlSame := hlCore.trans hcoreArrays.2
    refine ⟨coreEnd,coreMem,?_,cEnd,cMem,es,actual,answer,hCpost,hfit.1,hgSame,hlSame,?_⟩
    · simpa only [hcoreSuccess] using hrecord
    · simpa only [hgSame,hlSame] using hdata
  · obtain ⟨_,hrecord⟩ := hbranch
    have hzero := (epochBudgetRecord_output hrecord).2.2
    omega

end MinCostFlow.IPM.Machine
