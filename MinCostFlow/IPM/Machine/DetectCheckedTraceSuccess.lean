module

public import MinCostFlow.IPM.Machine.DetectCheckedResult
public import MinCostFlow.IPM.Machine.CheckedUpdateTraceSuccess
import MinCostFlow.IPM.Machine.DetectRefreshFrame

/-!
# The exact model Update of a successful complete iteration

A success bit forces both the Detect/refresh and coefficient-check
branches to have accepted. Decode the actual Update at the coefficient
memory produced by that refresh. The held request is below the cached
flow table and is preserved, so its effective normalization interval
still refers to the original machine-constructed request.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Success of the whole trace selects the actual successful refresh
and its state-indexed checked continuation. -/
theorem detectCheckedTransition_success {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b : ℕ} {s s' : A.State} {x : R.τ} {q K sourceEnd tableEnd : ℕ}
    {args : List ℕ} {mem final : ℕ → ℕ} {v : ℕ}
    (htrace : detectCheckedTransition F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      args mem final v) (haccept : final (v-1)=1) :
    ∃ cEnd cMem mid,
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        (args.take 20) mem cEnd cMem ∧ cMem (cEnd-1)=1 ∧
      (checkedUpdateContract F A I κ α rate allocation R b (A.detect s).2 mid (A.detect s).1).pre
        [b,args.getD 20 0,cMem (cEnd-2),args.getD 18 0,args.getD 17 0,args.getD 21 0,
          F.limbs,cEnd,args.getD 22 0,args.getD 23 0,args.getD 24 0] cMem ∧
      checkedUpdateTransition F A I κ α rate allocation (A.detect s).1 b
        (args.getD 20 0) (cMem (cEnd-2)) (args.getD 18 0) (args.getD 17 0)
        (args.getD 21 0) cEnd (args.getD 22 0) (args.getD 23 0) (args.getD 24 0)
        (A.detect s).2 s' cMem final v := by
  obtain ⟨cEnd,cMem,hCpost,hbranch⟩ := htrace
  by_cases hc : cMem (cEnd-1)=1
  · rw [ite_eq_left hc] at hbranch
    obtain ⟨mid,hpre,hstate⟩ := hbranch
    exact ⟨cEnd,cMem,mid,hCpost,hc,hpre,hstate⟩
  · rw [ite_eq_right hc] at hbranch
    obtain ⟨_,rfl,rfl⟩ := hbranch
    exact False.elim (hc haccept)

/-- A complete successful machine iteration performs one exact Update
at its actual refreshed coefficients, with the original held request
and a present circulation answer. Its state is the credited state. -/
theorem detectCheckedTransition_success_model {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (htrace : detectCheckedTransition F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem final v)
    (haccept : final (v-1)=1)
    (hgEnd : gd+I.m*F.limbs≤heap) (hlEnd : ld+I.m*F.limbs≤heap)
    (heEnd : request+F.limbs≤f) (hfEnd : f≤heap) :
    ∃ (cEnd : ℕ) (cMem : ℕ → ℕ) (es : List ℕ) (actual : ℝ) (answer : ℕ),
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      es.Nodup ∧ es.toFinset=(A.detect s).1 ∧ es.length=(A.detect s).1.card ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      MinRatioStateFits A (namedInstance I) F.fmt.limbBits F.limbs F.fmt.precision s' ∧
      let result := A.update (A.detect s).2 (refreshEdges (namedInstance I) es)
        (readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
      s'=result.1 ∧ result.2.isSome=true := by
  obtain ⟨cEnd,cMem,_,hCpost,_,_,hchecked⟩ := detectCheckedTransition_success F A I κ α rate allocation R htrace haccept
  change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).post
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem at hCpost
  have hcopy := hCpost
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
  change heap≤cEnd at hLo
  obtain ⟨es,actual,answer,hnd,hset,hlen,hscalar,hnorm,hfit,hmodel⟩ :=
    checkedUpdateTransition_success_model F A I κ α rate allocation (A.detect s).1
      (hgEnd.trans hLo) (hlEnd.trans hLo) (heEnd.trans (hfEnd.trans hLo)) hchecked haccept
  have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  have heSame := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd
  rw [heSame] at hnorm
  exact ⟨cEnd,cMem,es,actual,answer,hCpost,hnd,hset,hlen,hscalar,hnorm,hfit,hmodel⟩

end MinCostFlow.IPM.Machine
