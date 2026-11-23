module

public import MinCostFlow.IPM.Machine.BudgetedIterationHistory
public import MinCostFlow.IPM.Machine.BudgetedIterationCacheFrame
public import MinCostFlow.IPM.Machine.BudgetedIterationNextInput
public import MinCostFlow.IPM.Machine.BudgetedIterationRanges
import MinCostFlow.IPM.Machine.EpochInitialFlow
import MinCostFlow.IPM.Machine.ReportedTableLayout

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# The successful actual iteration preserves the epoch conditions

Extend the same valid history using the actual final coefficient arrays.
Preserve the full cache at its new report times, derive the next report
inclusion from the original Detect specification, and reconstruct the
next complete refresh input. The coefficient scan supplies full word
validity and ranges. The global allocation bound remains a caller input.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Successful actual steps preserve the cache, valid fixed-graph history under `P`,
coefficient formats and complete next-call input together. Only the
next allocation budget is supplied by the enclosing finite loop. -/
theorem budgetedIteration_success_invariant_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (hP : StageAdmits P (namedInstance I) F.rangeExponent)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j))
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x y : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1) (hrep : R.rep b s' y final)
    (hmeta : ∀ z,R.foot b y z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (harrays : ∀ p∈[base,c,lo,up],p+I.m*F.limbs≤f)
    (hscalars : ∀ p∈[r,a,one,mn,mx],p+F.limbs≤f)
    (heEnd : request+F.limbs≤f)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T)
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op
      (minRatioLast A.eraseFailure D eta op T e)) I.m q base lo up f c r a ld gd e mem)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s' [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    let gradient := readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m
    let lengths := readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m
    ∃ es actual cEnd cMem,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
        (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      cMem (cEnd-1)=1 ∧
      gradient=readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      lengths=readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      let D' := appendHistoryIteration D T es gradient lengths
      let eta' := appendHistoryIterationEta eta T actual
      let op' := appendHistoryIterationOp op T
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      MinRatioHistoryValid D' op' (T+1+1) ∧
      (∀ j≤T+1+1,D'.G j=namedInstance I) ∧
      s'=minRatioState A.eraseFailure D' eta' op' (T+1+1) ∧
      D'.g (T+1+1)=gradient ∧ D'.ℓ (T+1+1)=lengths ∧
      (∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D' eta' op'
        (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e)) I.m q base lo up f c r a ld gd e final) ∧
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s' y q K sourceEnd tableEnd).pre
        [b,names,I.m,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] final ∧
      (∀ e<I.m,Num.Valid final (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid final (ld+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |gradient e|≤(2:ℝ)^F.rangeExponent ∧ (2:ℝ)^(-(F.rangeExponent:ℤ))≤lengths e ∧ lengths e≤(2:ℝ)^F.rangeExponent) ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      (∀ z<f,final z=mem z) ∧ final (v-3)≤mem (heap-3) ∧ heap+3≤v := by
  have hpreCopy := hpre
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,havoid,_,hsEnd,htEnd,hnEnd,hends,hshared,_,_,_,_,hldEnd,hgdEnd,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hbefore : tableEnd≤heap := by omega
  have hfEnd := hends f (by simp)
  have hfHeap : f≤heap := by omega
  have hgHeap := hgdEnd.trans hbefore
  have hlHeap := hldEnd.trans hbefore
  obtain ⟨coreEnd,coreMem,_,cEnd,cMem,es,actual,answer,hCpost,hCbit,hgSame,hlSame,hnd,hset,_,hnorm,hnewValid,hstate⟩ :=
    budgetedIteration_success_history F A I κ α rate allocation R D eta op T hvalid (hG T le_rfl)
      hpreCopy hout haccept hgHeap hlHeap heEnd hfHeap hgOld hlOld
  have hnewG := appendHistoryIteration_fixed_graph D (namedInstance I) T es
    (readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m) hG
  have hcacheFinal : ∀ e<I.m,reportedCachePost F A
      (minRatioState A.eraseFailure (appendHistoryIteration D T es
        (readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m))
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T)
        (minRatioLast A.eraseFailure (appendHistoryIteration D T es
          (readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
          (readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m))
          (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1+1) e))
        I.m q base lo up f c r a ld gd e final := by
    intro e he
    have sourceEnd (p : ℕ) (hp : p∈[base,c,lo,up]) : p+e*F.limbs+F.limbs≤f :=
      (reported_entry_end p F.limbs e I.m he).trans (harrays p hp)
    apply budgetedIteration_cache_at_last F A I κ α rate allocation R D eta op T es _ _ actual
      hpreCopy hout haccept he hbefore havoid
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with hp | hp | hp | hp | hp | hp
      all_goals subst p
      · exact sourceEnd base (by simp)
      · exact sourceEnd c (by simp)
      · exact hscalars r (by simp)
      · exact sourceEnd lo (by simp)
      · exact sourceEnd up (by simp)
      · exact hscalars a (by simp)
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
      all_goals subst p
      · exact ((reported_entry_end base F.limbs e I.m he).trans (hends base (by simp))).trans hsEnd
      · exact ((reported_entry_end c F.limbs e I.m he).trans (hends c (by simp))).trans hsEnd
      · exact (hshared r (by simp)).trans hsEnd
      · exact ((reported_entry_end lo F.limbs e I.m he).trans (hends lo (by simp))).trans hsEnd
      · exact ((reported_entry_end f F.limbs e I.m he).trans hfEnd).trans hsEnd
      · exact ((reported_entry_end up F.limbs e I.m he).trans (hends up (by simp))).trans hsEnd
      · exact (hshared a (by simp)).trans hsEnd
      · exact (reported_entry_end ld F.limbs e I.m he).trans hldEnd
      · exact (reported_entry_end gd F.limbs e I.m he).trans hgdEnd
    · exact hcache e he
  have hranges := budgetedIteration_success_ranges F A I κ α rate allocation R hout haccept hbefore havoid hgdEnd hldEnd
  have hnewP := appendHistoryIteration_stage_on es (readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m) hPD
    (by rw [hG T le_rfl]; exact hP _ (fun e he => ⟨(hranges e (Finset.mem_range.mp he)).2.2.2.1,
      (hranges e (Finset.mem_range.mp he)).2.2.2.2⟩))
  have hsubset : (A.detect s').1⊆(namedInstance I).E := by
    rw [hstate]
    have hh := minRatio_valid_detect_subset_upTo_on A κ α Ψ eps hA _ (appendHistoryIterationEta eta T actual) _ (T+1+1)
      hnewValid (namedHistory_bounded hnewG) hnewP
    simpa only [hnewG (T+1+1) le_rfl] using hh
  have hnext := budgetedIteration_next_pre F A I κ α rate allocation R hpreCopy hout haccept hrep hmeta
    (fun e he => (hcacheFinal e he).1) harrays hscalars hsubset hspace
  have hsource := budgetedIteration_source_frame F A I κ α rate allocation R hpreCopy hout hfHeap
    (fun z hz => havoid z (by omega))
  have hbudget : final (v-3)≤mem (heap-3) := (budgetedIteration_output hout).2.1
  have hheap := budgetedIteration_end_ge F A I κ α rate allocation R hout
  refine ⟨es,actual,cEnd,cMem,hCpost,hCbit,hgSame,hlSame,hnd,hset,hnewValid,hnewG,hstate,?_,?_,hcacheFinal,hnext,hranges,hnorm,hsource,hbudget,hheap⟩
  all_goals simp only [appendHistoryIteration,appendHistoryStage,Function.update_self]

/-- Successful actual steps preserve the cache, valid fixed-graph history,
coefficient formats and complete next-call input together. Only the
next allocation budget is supplied by the enclosing finite loop. -/
theorem budgetedIteration_success_invariant_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x y : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1) (hrep : R.rep b s' y final)
    (hmeta : ∀ z,R.foot b y z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (harrays : ∀ p∈[base,c,lo,up],p+I.m*F.limbs≤f)
    (hscalars : ∀ p∈[r,a,one,mn,mx],p+F.limbs≤f)
    (heEnd : request+F.limbs≤f)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T)
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op
      (minRatioLast A.eraseFailure D eta op T e)) I.m q base lo up f c r a ld gd e mem)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s' [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    let gradient := readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m
    let lengths := readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m
    ∃ es actual cEnd cMem,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
        (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      cMem (cEnd-1)=1 ∧
      gradient=readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      lengths=readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      let D' := appendHistoryIteration D T es gradient lengths
      let eta' := appendHistoryIterationEta eta T actual
      let op' := appendHistoryIterationOp op T
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      MinRatioHistoryValid D' op' (T+1+1) ∧
      (∀ j≤T+1+1,D'.G j=namedInstance I) ∧
      s'=minRatioState A.eraseFailure D' eta' op' (T+1+1) ∧
      D'.g (T+1+1)=gradient ∧ D'.ℓ (T+1+1)=lengths ∧
      (∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D' eta' op'
        (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e)) I.m q base lo up f c r a ld gd e final) ∧
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s' y q K sourceEnd tableEnd).pre
        [b,names,I.m,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] final ∧
      (∀ e<I.m,Num.Valid final (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid final (ld+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |gradient e|≤(2:ℝ)^F.rangeExponent ∧ (2:ℝ)^(-(F.rangeExponent:ℤ))≤lengths e ∧ lengths e≤(2:ℝ)^F.rangeExponent) ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      (∀ z<f,final z=mem z) ∧ final (v-3)≤mem (heap-3) ∧ heap+3≤v :=
  budgetedIteration_success_invariant_upTo_on F A I κ α Ψ eps (hA.upToOn (P := fun _ _ => True))
    (stageAdmits_true _ _) rate allocation R D eta op T hvalid hG (fun _ _ => trivial) hpre hout
    haccept hrep hmeta harrays hscalars

    heEnd hgOld hlOld hcache hspace

/-- Successful actual steps preserve the cache, valid fixed-graph history,
coefficient formats and complete next-call input together. Only the
next allocation budget is supplied by the enclosing finite loop. -/
theorem budgetedIteration_success_invariant {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x y : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1) (hrep : R.rep b s' y final)
    (hmeta : ∀ z,R.foot b y z → z<v ∧ (R.foot b x z ∨ heap≤z))
    (harrays : ∀ p∈[base,c,lo,up],p+I.m*F.limbs≤f)
    (hscalars : ∀ p∈[r,a,one,mn,mx],p+F.limbs≤f)
    (heEnd : request+F.limbs≤f)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T)
    (hcache : ∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D eta op
      (minRatioLast A.eraseFailure D eta op T e)) I.m q base lo up f c r a ld gd e mem)
    (hspace : v+(minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).space 2 s' [b,v] final+
      2*(I.m+1)+I.m*reportedEdgesScratch F I.m b E allocation+4<2^w) :
    let gradient := readVector final gd F.fmt.limbBits F.limbs F.fmt.precision I.m
    let lengths := readVector final ld F.fmt.limbBits F.limbs F.fmt.precision I.m
    ∃ es actual cEnd cMem,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
        (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      cMem (cEnd-1)=1 ∧
      gradient=readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      lengths=readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m ∧
      let D' := appendHistoryIteration D T es gradient lengths
      let eta' := appendHistoryIterationEta eta T actual
      let op' := appendHistoryIterationOp op T
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      MinRatioHistoryValid D' op' (T+1+1) ∧
      (∀ j≤T+1+1,D'.G j=namedInstance I) ∧
      s'=minRatioState A.eraseFailure D' eta' op' (T+1+1) ∧
      D'.g (T+1+1)=gradient ∧ D'.ℓ (T+1+1)=lengths ∧
      (∀ e<I.m,reportedCachePost F A (minRatioState A.eraseFailure D' eta' op'
        (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e)) I.m q base lo up f c r a ld gd e final) ∧
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s' y q K sourceEnd tableEnd).pre
        [b,names,I.m,base,lo,up,f,F.limbs,v,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] final ∧
      (∀ e<I.m,Num.Valid final (gd+e*F.limbs) F.fmt.limbBits F.limbs ∧
        Num.Valid final (ld+e*F.limbs) F.fmt.limbBits F.limbs ∧
        |gradient e|≤(2:ℝ)^F.rangeExponent ∧ (2:ℝ)^(-(F.rangeExponent:ℤ))≤lengths e ∧ lengths e≤(2:ℝ)^F.rangeExponent) ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      (∀ z<f,final z=mem z) ∧ final (v-3)≤mem (heap-3) ∧ heap+3≤v :=
  budgetedIteration_success_invariant_upTo F A I κ α Ψ eps (hA.upTo I.m I.n) rate allocation R D
    eta op T hvalid hG hpre hout haccept hrep hmeta harrays hscalars heEnd hgOld hlOld hcache
    hspace

end MinCostFlow.IPM.Machine
