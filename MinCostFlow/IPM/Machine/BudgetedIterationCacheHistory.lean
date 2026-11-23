module

public import MinCostFlow.IPM.Machine.BudgetedIterationFrame
public import MinCostFlow.IPM.Machine.DetectRefreshCacheHistory
import MinCostFlow.IPM.Machine.ReportedTableLayout
import MinCostFlow.IPM.Machine.PrecisionEdgeRange
import Mathlib.Tactic.Linarith

/-!
# Stored-flow timestamps after the complete budgeted entry

The actual refresh satisfies the timestamp invariant. Its checked
continuation and budget metadata preserve the flow table, so that same
invariant holds at the returned memory. This retains stale coordinates
only at their precise `last_e` times, without further Query calls.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A successful complete budgeted iteration preserves the exact stored
flow at each edge's new report timestamp in its actual final memory. -/
theorem budgetedIteration_cache_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v e : ℕ}
    {s' : A.State} {x : R.τ} {mem final : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v final)
    (haccept : final (v-1)=1) (he : e<I.m) (hbaseEnd : base+e*F.limbs+F.limbs≤f)
    (hcache : Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e) e) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    Num.fixVal final (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D' eta' op' (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e) e := by
  have hpreCopy := hpre
  obtain ⟨names',base',lo',up',f',heap',c',r',a',one',mn',mx',E',ld',gd',heq,hfull,_⟩ := hpre
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  obtain ⟨names0,count0,base0,lo0,up0,f0,heap0,c0,r0,a0,one0,mn0,mx0,E0,ld0,gd0,all,heq,
    _,_,_,_,_,_,_,hprefix,_,hsEnd,htEnd,hnEnd,hends,_⟩ := hfull
  simp only [List.cons.injEq,and_true,true_and] at heq
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ := heq
  have hbefore : tableEnd≤heap := by omega
  obtain ⟨cEnd,cMem,hCpost,hCsuccess,hframe⟩ := budgetedIteration_tail_frame F A I κ α rate allocation R
    hout hbefore hprefix
  have hcached := detectRefresh_cache_history F A I κ α Ψ eps hA rate allocation R D eta op T
    hvalid hG es g l actual hpreCopy hCpost (hCsuccess haccept) he hbaseEnd hcache
  have hend := (reported_entry_end f F.limbs e I.m he).trans (hends f (by simp))
  have hf : Num.fixVal final (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal cMem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    unfold Num.fixVal
    rw [Num.intVal_congr (fun i hi => hframe _ (by omega))]
  exact hf.trans hcached

/-- The stored-flow invariant bounds the next unreported Query source
using only the cached coordinate. This does not require hidden stability. -/
theorem storedFlow_query_bound {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : ∀ j≤T,D.G j=namedInstance I)
    {base f e : ℕ} {mem : ℕ → ℕ} {capacity : ℝ} (he : e<I.m)
    (hcache : Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e) e)
    (hbound : |Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity) :
    |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
      A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e)) e|≤capacity := by
  have hlast := minRatioLast_le A.eraseFailure D eta op T e
  have heG : e∈(D.G (minRatioLast A.eraseFailure D eta op T e)).E := by
    rw [hG _ hlast]
    exact Finset.mem_range.mpr he
  have hquery := (hA.1 D eta op T hvalid).1 _ hlast e heG
  have heq := (congrArg
    (fun z => Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+z) hquery).trans hcache.symm
  exact (congrArg abs heq).le.trans hbound

/-- Strict cached slacks and nonnegative lower capacities give the
capacity-based length lower bound used by unconditional Query recovery.
No potential or correct-target premise is needed. -/
theorem reportedCachePost_query_length_lower {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State)
    {m q base lo up f c r a ld gd e E : ℕ} {mem : ℕ → ℕ}
    (he : e<m) (hcache : reportedCachePost F A s m q base lo up f c r a ld gd e mem)
    (hlo : 0≤Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
    (hup : Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E)
    (ha : 0≤Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision)
    (ha' : Num.fixVal mem a F.fmt.limbBits F.limbs F.fmt.precision≤1) :
    1/(2:ℝ)^(2*E+1)≤readVector mem ld F.fmt.limbBits F.limbs F.fmt.precision m e := by
  have hin := hcache.2.2.2.2.2.2
  have hflowPos := hlo.trans_lt hin.1
  have hu : 0<Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := sub_pos.mpr hin.2
  have hd : 0<Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := sub_pos.mpr hin.1
  have hu' : Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision≤(2:ℝ)^E := by
    linarith only [hup,hflowPos]
  have happrox := hcache.2.2.2.1
  simp only [Num.IPM.arrayLength] at happrox
  have hbound := stored_length_lower_of_upper_slack hu hd hu' ha ha' happrox
  simpa only [readVector,he,ite_true] using hbound

end MinCostFlow.IPM.Machine
