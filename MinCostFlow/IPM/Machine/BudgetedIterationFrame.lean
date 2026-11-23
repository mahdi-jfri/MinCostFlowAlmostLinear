module

public import MinCostFlow.IPM.Machine.BudgetedIterationResult
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.IPM.Machine.CheckedUpdateFrame
import MinCostFlow.IPM.Machine.CheckedUpdateOutput

/-!
# Source memory through the complete budgeted iteration

Detect and refresh preserve the source prefix preceding the cached
flow table. The checked Update preserves that prefix outside the data
structure's footprint, which grows only into fresh memory. The final
budget record is fresh. Combining these facts keeps the graph and held
numeric parameters available for the next iteration on every branch.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Every source word before the cached flow table survives all actual
branches, including a report-budget rejection and a failed Update. -/
theorem budgetedIteration_source_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (hf : f≤heap) (havoid : ∀ z<f,¬R.foot b x z) :
    ∀ z<f,final z=mem z := by
  obtain ⟨cEnd,cMem,mid,hC,_,hmeta,hbranch⟩ := hout
  change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem at hC
  have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hC
  have hcopy := hC
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
  change heap≤cEnd at hLo
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch hmeta
  intro z hz
  split_ifs at hbranch
  · obtain ⟨coreEnd,coreMem,_,hQ,_,hrecord⟩ := hbranch
    have hnot : ¬R.foot b mid z := by
      intro hfoot
      rcases (hmeta z hfoot).2 with hold | hfresh
      · exact havoid z hz hold
      · omega
    have hq := checkedUpdate_frame F A I κ α rate allocation R hQ z (by omega) hnot
    have hend := checkedUpdate_end_ge F A I κ α rate allocation R hQ
    have hrecordFrame := hrecord.1.2.2.1
    change ∀ z<coreEnd,final z=coreMem z at hrecordFrame
    exact (hrecordFrame z (by omega)).trans (hq.trans (hframe z hz))
  · obtain ⟨_,hrecord⟩ := hbranch
    have hrecordFrame := hrecord.1.2.2.1
    change ∀ z<cEnd,final z=cMem z at hrecordFrame
    exact (hrecordFrame z (by omega)).trans (hframe z hz)

/-- The checked continuation preserves every old caller word outside
the old DS footprint, including full edge names after the tables. -/
theorem budgetedIteration_tail_frame_outside_foot {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
 :
    ∃ cEnd cMem,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      (final (v-1)=1 → cMem (cEnd-1)=1) ∧
      ∀ z<heap,¬R.foot b x z → final z=cMem z := by
  obtain ⟨cEnd,cMem,mid,hC,_,hmeta,hbranch⟩ := hout
  change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem at hC
  have hcopy := hC
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
  change heap≤cEnd at hLo
  simp only [List.getD_cons_zero,List.getD_cons_succ] at hbranch hmeta
  refine ⟨cEnd,cMem,hC,?_,?_⟩
  · intro hsuccess
    split_ifs at hbranch with hfit
    · exact hfit.1
    · obtain ⟨_,hrecord⟩ := hbranch
      have hbit := (epochBudgetRecord_output hrecord).2.2
      omega
  · intro z hz hnotOld
    split_ifs at hbranch
    · obtain ⟨coreEnd,coreMem,_,hQ,_,hrecord⟩ := hbranch
      have hnot : ¬R.foot b mid z := by
        intro hfoot
        rcases (hmeta z hfoot).2 with hold | hfresh
        · exact hnotOld hold
        · omega
      have hq := checkedUpdate_frame F A I κ α rate allocation R hQ z (by omega) hnot
      have hend := checkedUpdate_end_ge F A I κ α rate allocation R hQ
      have hrecordFrame := hrecord.1.2.2.1
      change ∀ z<coreEnd,final z=coreMem z at hrecordFrame
      exact (hrecordFrame z (by omega)).trans hq
    · obtain ⟨_,hrecord⟩ := hbranch
      have hrecordFrame := hrecord.1.2.2.1
      change ∀ z<cEnd,final z=cMem z at hrecordFrame
      exact hrecordFrame z (by omega)

/-- After Detect and refresh, neither the checked continuation nor the
fresh metadata changes any caller table below the original heap. -/
theorem budgetedIteration_tail_frame {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (hbefore : tableEnd≤heap) (havoid : ∀ z<tableEnd,¬R.foot b x z) :
    ∃ cEnd cMem,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      (final (v-1)=1 → cMem (cEnd-1)=1) ∧
      ∀ z<tableEnd,final z=cMem z := by
  obtain ⟨cEnd,cMem,hpost,hbit,hframe⟩ := budgetedIteration_tail_frame_outside_foot F A I κ α rate allocation R hout
  exact ⟨cEnd,cMem,hpost,hbit,fun z hz => hframe z (hz.trans_le hbefore) (havoid z hz)⟩

end MinCostFlow.IPM.Machine
