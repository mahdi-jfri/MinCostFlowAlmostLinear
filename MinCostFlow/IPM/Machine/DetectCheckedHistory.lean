module

public import MinCostFlow.IPM.Machine.DetectCheckedTraceSuccess
public import MinCostFlow.IPM.Machine.HistoryIteration
import MinCostFlow.IPM.Machine.DetectRefreshUnreported
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Appending a successful actual iteration to a valid history

The actual successful trace gives its refreshed arrays and rounded
normalization. Its accepted scan proves positive new lengths. Every
unreported block retains its old words, so the input history's unchanged
edge condition holds. Append Detect and Update, and identify the exact
returned state with the resulting valid history without hidden stability.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- After scan acceptance, the selected refresh and Update extend
the shared history even when the chosen direction is absent. -/
theorem detectChecked_attempt_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x mid : R.τ} {mem final cMem checkedMem batchMem : ℕ → ℕ} {cEnd checkedEnd batchEnd : ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hCpost : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem)
    (hCheckedPre : (checkedUpdateContract F A I κ α rate allocation R b
      (A.detect (minRatioState A.eraseFailure D eta op T)).2 mid
      (A.detect (minRatioState A.eraseFailure D eta op T)).1).pre
      [b,source,cMem (cEnd-2),gd,ld,request,F.limbs,cEnd,neg,maximum,minimum] cMem)
    (hcheck : (coefficientRangeReportContract w F.fmt.limbBits
      (A.detect (minRatioState A.eraseFailure D eta op T)).1).post
      [cMem (cEnd-2),gd,ld,neg,maximum,minimum,F.limbs,cEnd] cMem checkedEnd checkedMem)
    (hscan : checkedMem (checkedEnd-1)=1)
    (hbatch : (detectBatchContract w I (A.detect (minRatioState A.eraseFailure D eta op T)).1).post
      [source,cMem (cEnd-2),checkedEnd] checkedMem batchEnd batchMem)
    (hupdate : (minRatioMachineContract F A (namedInstance I) I.m κ α rate allocation).post
      0 (A.detect (minRatioState A.eraseFailure D eta op T)).2
      [b,checkedEnd,gd,ld,request,batchEnd] batchMem s' final)
    (hheader : final (v-1)=final batchEnd)
    (hgEnd : gd+I.m*F.limbs≤heap) (hlEnd : ld+I.m*F.limbs≤heap)
    (heEnd : request+F.limbs≤f) (hfEnd : f≤heap)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T) :
    ∃ (es : List ℕ) (actual : ℝ) (answer : ℕ),
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      let gradient := readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m
      let lengths := readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m
      MinRatioHistoryValid (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationOp op T) (T+1+1) ∧
      s'=minRatioState A.eraseFailure (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1+1) ∧
      final (v-1)=(if (minRatioFailureDirection A (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1)).isSome then 1 else 0) := by
  change (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
    (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
    [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem at hCpost
  have hcopy := hCpost
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hLo,_⟩ := hcopy
  change heap≤cEnd at hLo
  have hranges := checkedUpdateCalls_input_ranges F A I κ α rate allocation R hCheckedPre hcheck hscan
  obtain ⟨es,actual,answer,hnd,hset,_,hscalar,hnorm,_,hmodel⟩ :=
    checkedUpdateCalls_model F A I κ α rate allocation _
      (hgEnd.trans hLo) (hlEnd.trans hLo) (heEnd.trans (hfEnd.trans hLo)) hcheck hbatch hupdate hheader
  have hsubset : (A.detect (minRatioState A.eraseFailure D eta op T)).1⊆(namedInstance I).E := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hs,_⟩ := hpre
    exact hs
  have hes : ∀ e∈es,e∈(D.G T).E := by
    intro e he
    rw [hG]
    exact hsubset (hset ▸ List.mem_toFinset.mpr he)
  have hl : ∀ e∈(D.G T).E,0<readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e := by
    intro e he
    have heI : e∈(namedInstance I).E := hG ▸ he
    exact (zpow_pos (zero_lt_two : (0:ℝ)<2) _).trans_le (hranges e heI).2.1
  have hunchanged : ∀ e∈(D.G T).E,e∉es →
      readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m e=D.g T e ∧
      readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m e=D.ℓ T e := by
    intro e he hn
    have heI : e∈(namedInstance I).E := hG ▸ he
    have heM : e<I.m := Finset.mem_range.mp heI
    have hne : e∉(A.detect (minRatioState A.eraseFailure D eta op T)).1 := by
      rw [← hset]
      exact fun hh => hn (List.mem_toFinset.mp hh)
    have hs := detectRefresh_unreported_coefficients F A (namedInstance I) I.m κ α rate allocation R hpre hCpost heM hne
    have hvalue (p : ℕ) (hp : p∈[ld,gd]) :
        Num.fixVal cMem (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      unfold Num.fixVal
      rw [Num.intVal_congr (hs p hp)]
    refine ⟨?_,?_⟩
    · rw [← congrFun hgOld e]
      simpa only [readVector,heM,ite_true] using hvalue gd (by simp)
    · rw [← congrFun hlOld e]
      simpa only [readVector,heM,ite_true] using hvalue ld (by simp)
  have hnewValid := appendHistoryIteration_valid D op T hvalid es _ _ hes hl hunchanged
  have hstate := appendHistoryIteration_state A.eraseFailure D eta op T es
    (readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m) actual
  have hstate' := hmodel.1.trans (by simpa only [hG,MinRatioDataStructureWithFailure.eraseFailure] using hstate.symm)
  have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hCpost
  rw [Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe heEnd] at hnorm
  refine ⟨es,actual,answer,hnd,hset,hscalar,hnorm,hnewValid,hstate',?_⟩
  have hdetectState :
      minRatioState A.eraseFailure (appendHistoryIteration D T es
        (readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m)
        (readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m))
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1)=
        (A.detect (minRatioState A.eraseFailure D eta op T)).2 := by
    unfold appendHistoryIteration appendHistoryIterationEta appendHistoryIterationOp
    rw [appendHistoryStage_past_state _ _ _ _ (T+1) _ _ _ _ true _ le_rfl,
      appendHistoryStage_detect_state]
    rfl
  unfold minRatioFailureDirection
  rw [hdetectState]
  simpa only [appendHistoryIteration,appendHistoryIterationEta,appendHistoryIterationOp,
    appendHistoryStage,Function.update_self,hG] using hmodel.2

/-- The selected actual refresh and checked calls extend the shared
history using exactly that refresh memory and the actual rounded step. -/
theorem detectChecked_calls_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x mid : R.τ} {mem final cMem : ℕ → ℕ} {cEnd : ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hCpost : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem)
    (hCheckedPre : (checkedUpdateContract F A I κ α rate allocation R b
      (A.detect (minRatioState A.eraseFailure D eta op T)).2 mid
      (A.detect (minRatioState A.eraseFailure D eta op T)).1).pre
      [b,source,cMem (cEnd-2),gd,ld,request,F.limbs,cEnd,neg,maximum,minimum] cMem)
    (hchecked : checkedUpdateTransition F A I κ α rate allocation
      (A.detect (minRatioState A.eraseFailure D eta op T)).1 b source (cMem (cEnd-2)) gd ld request
      cEnd neg maximum minimum (A.detect (minRatioState A.eraseFailure D eta op T)).2 s' cMem final v)
    (haccept : final (v-1)=1)
    (hgEnd : gd+I.m*F.limbs≤heap) (hlEnd : ld+I.m*F.limbs≤heap)
    (heEnd : request+F.limbs≤f) (hfEnd : f≤heap)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T) :
    ∃ (es : List ℕ) (actual : ℝ) (answer : ℕ),
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      let gradient := readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m
      let lengths := readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m
      MinRatioHistoryValid (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationOp op T) (T+1+1) ∧
      s'=minRatioState A.eraseFailure (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1+1) := by
  obtain ⟨checkedEnd,checkedMem,batchEnd,batchMem,hcheck,hscan,hbatch,hupdate,hbit⟩ :=
    checkedUpdateTransition_success F A I κ α rate allocation _ hchecked haccept
  obtain ⟨es,actual,answer,hnd,hset,hscalar,hnorm,hv,hs,_⟩ :=
    detectChecked_attempt_history F A I κ α rate allocation R D eta op T hvalid hG hpre hCpost hCheckedPre
      hcheck hscan hbatch hupdate (haccept.trans hbit.symm) hgEnd hlEnd heEnd hfEnd hgOld hlOld
  exact ⟨es,actual,answer,hnd,hset,hscalar,hnorm,hv,hs⟩

/-- Every successful actual iteration extends the valid history by its
actual Detect and refresh Update, using the actual decoded normalization.
The credited returned state is exactly the state of that extended history. -/
theorem detectChecked_success_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v : ℕ}
    {s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (htrace : detectCheckedTransition F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem final v)
    (haccept : final (v-1)=1)
    (hgEnd : gd+I.m*F.limbs≤heap) (hlEnd : ld+I.m*F.limbs≤heap)
    (heEnd : request+F.limbs≤f) (hfEnd : f≤heap)
    (hgOld : readVector mem gd F.fmt.limbBits F.limbs F.fmt.precision I.m=D.g T)
    (hlOld : readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision I.m=D.ℓ T) :
    ∃ (cEnd : ℕ) (cMem : ℕ → ℕ) (es : List ℕ) (actual : ℝ) (answer : ℕ),
      (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
        (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
        [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem cEnd cMem ∧
      es.Nodup ∧ es.toFinset=(A.detect (minRatioState A.eraseFailure D eta op T)).1 ∧
      ScalarAt final (answer+1) F.fmt.limbBits (2*F.limbs) (2*F.fmt.precision) actual ∧
      NormalizationWithin (Num.fixVal mem request F.fmt.limbBits F.limbs F.fmt.precision) actual ∧
      let gradient := readVector cMem gd F.fmt.limbBits F.limbs F.fmt.precision I.m
      let lengths := readVector cMem ld F.fmt.limbBits F.limbs F.fmt.precision I.m
      MinRatioHistoryValid (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationOp op T) (T+1+1) ∧
      s'=minRatioState A.eraseFailure (appendHistoryIteration D T es gradient lengths)
        (appendHistoryIterationEta eta T actual) (appendHistoryIterationOp op T) (T+1+1) := by
  obtain ⟨cEnd,cMem,mid,hCpost,_,hCheckedPre,hchecked⟩ :=
    detectCheckedTransition_success F A I κ α rate allocation R htrace haccept
  obtain ⟨es,actual,answer,hdata⟩ := detectChecked_calls_history F A I κ α rate allocation R D eta op T
    hvalid hG hpre hCpost hCheckedPre hchecked haccept hgEnd hlEnd heEnd hfEnd hgOld hlOld
  exact ⟨cEnd,cMem,es,actual,answer,hCpost,hdata⟩

end MinCostFlow.IPM.Machine
