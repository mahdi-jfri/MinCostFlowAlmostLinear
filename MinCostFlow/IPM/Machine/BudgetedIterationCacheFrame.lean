module

public import MinCostFlow.IPM.Machine.BudgetedIterationUnreported
public import MinCostFlow.IPM.Machine.ReportedCacheCongr
public import MinCostFlow.IPM.Machine.HistoryIteration
import MinCostFlow.IPM.Machine.DetectRefreshOutput

/-!
# Preserving unreported cache accuracy and strict slacks

An unreported edge retains its base, numeric source and three cached
blocks. The complete cache postcondition therefore survives, including
exact flow recovery at its held state, numerical length and gradient
accuracy, valid words and strict capacity inequalities. Other reported
coordinates may change during the same iteration.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The complete actual iteration preserves an unreported edge's cache
postcondition at its held state, with every numerical source framed. -/
theorem budgetedIteration_unreported_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v e : ℕ}
    {s s' cached : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v mem')
    (he : e<I.m) (hne : e∉(A.detect s).1)
    (hbefore : f≤heap) (havoid : ∀ z<f,¬R.foot b x z)
    (hsources : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,up+e*F.limbs,a],p+F.limbs≤f)
    (hcache : reportedCachePost F A cached I.m q base lo up f c r a ld gd e mem) :
    reportedCachePost F A cached I.m q base lo up f c r a ld gd e mem' := by
  have hsource := budgetedIteration_source_frame F A I κ α rate allocation R hpre hout hbefore havoid
  have hstored := budgetedIteration_unreported_blocks F A I κ α rate allocation R hpre hout he hne
  apply reportedCachePost_congr F A cached (mem:=mem) (mem':=mem') _ hcache
  intro p hp i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals subst p
  · have hend := hsources (base+e*F.limbs) (by simp)
    exact hsource _ (by omega)
  · have hend := hsources (c+e*F.limbs) (by simp)
    exact hsource _ (by omega)
  · have hend := hsources r (by simp)
    exact hsource _ (by omega)
  · have hend := hsources (lo+e*F.limbs) (by simp)
    exact hsource _ (by omega)
  · exact hstored f (by simp) i hi
  · have hend := hsources (up+e*F.limbs) (by simp)
    exact hsource _ (by omega)
  · have hend := hsources a (by simp)
    exact hsource _ (by omega)
  · exact hstored ld (by simp) i hi
  · exact hstored gd (by simp) i hi

/-- An accepted actual report supplies the complete cache postcondition
at the Detect state, and the checked continuation preserves every block. -/
theorem budgetedIteration_reported_cache {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v e : ℕ}
    {s s' : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b s x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b s s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v mem')
    (haccept : mem' (v-1)=1) (he : e∈(A.detect s).1)
    (hbefore : tableEnd≤heap) (havoid : ∀ z<tableEnd,¬R.foot b x z)
    (hends : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,f+e*F.limbs,
      up+e*F.limbs,a,ld+e*F.limbs,gd+e*F.limbs],p+F.limbs≤tableEnd) :
    reportedCachePost F A (A.detect s).2 I.m q base lo up f c r a ld gd e mem' := by
  obtain ⟨cEnd,cMem,hCpost,hCsuccess,hframe⟩ := budgetedIteration_tail_frame F A I κ α rate allocation R
    hout hbefore havoid
  have hcache := (detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hCpost).2.2.2.2
    (hCsuccess haccept) e he
  apply reportedCachePost_congr F A (A.detect s).2 (mem:=cMem) (mem':=mem') _ hcache
  intro p hp i hi
  have hend := hends p hp
  exact hframe _ (by omega)

/-- The complete successful actual entry maintains every part of the
cache condition at the new history's actual held state. Reported entries
use the Detect state, and all others keep the old held state. -/
theorem budgetedIteration_cache_at_last {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd source request neg maximum minimum v e : ℕ}
    {s' : A.State} {x : R.τ} {mem mem' : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : budgetedIterationResult F A I κ α rate allocation R b (minRatioState A.eraseFailure D eta op T) s' x q K sourceEnd tableEnd
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m,
        source,request,neg,maximum,minimum] mem v mem')
    (haccept : mem' (v-1)=1) (he : e<I.m)
    (hbefore : tableEnd≤heap) (havoid : ∀ z<tableEnd,¬R.foot b x z)
    (hsources : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,up+e*F.limbs,a],p+F.limbs≤f)
    (hends : ∀ p∈[base+e*F.limbs,c+e*F.limbs,r,lo+e*F.limbs,f+e*F.limbs,
      up+e*F.limbs,a,ld+e*F.limbs,gd+e*F.limbs],p+F.limbs≤tableEnd)
    (hcache : reportedCachePost F A (minRatioState A.eraseFailure D eta op
      (minRatioLast A.eraseFailure D eta op T e)) I.m q base lo up f c r a ld gd e mem) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    reportedCachePost F A (minRatioState A.eraseFailure D' eta' op'
      (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e)) I.m q base lo up f c r a ld gd e mem' := by
  dsimp only
  rw [appendHistoryIteration_last_state]
  rw [show A.eraseFailure.detect=A.detect from rfl]
  by_cases hreport : e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1
  · rw [ite_eq_left hreport]
    exact budgetedIteration_reported_cache F A I κ α rate allocation R hpre hout haccept hreport hbefore havoid hends
  · rw [ite_eq_right hreport]
    have hflowEnd := hends (f+e*F.limbs) (by simp)
    have hf : f≤tableEnd := by omega
    exact budgetedIteration_unreported_cache F A I κ α rate allocation R hpre hout he hreport
      (hf.trans hbefore) (fun z hz => havoid z (hz.trans_le hf)) hsources hcache

end MinCostFlow.IPM.Machine
