module

public import MinCostFlow.IPM.Machine.HistoryIteration
public import MinCostFlow.IPM.Machine.DetectRefresh
import MinCostFlow.IPM.Machine.DetectRefreshOutput
import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.IPM.Machine.DetectRefreshUnreportedFlow
import MinCostFlow.IPM.Machine.EpochMaterialization
import MinCostFlow.Num.IPM.FixedPointFacts

/-!
# Actual refreshed coordinates at their history timestamps

A reported coordinate is the base plus the actual flow before Update,
by Query correctness on a valid history. An unreported coordinate keeps
its exact old words. These are exactly the two cases of `last_e` after
the appended Detect and Update. Thus the actual refresh preserves the
stored-flow timestamp invariant without a hidden stability premise.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual successful refresh stores each coordinate at the report
time of the appended pair, whether or not that edge was reported. -/
theorem detectRefresh_cache_history {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (κ α Ψ eps : ℝ)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hG : D.G T=namedInstance I)
    (es : List ℕ) (g l : ℕ → ℝ) (actual : ℝ)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v e : ℕ}
    {x : R.τ} {mem refreshed : ℕ → ℕ}
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op T) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v refreshed)
    (haccept : refreshed (v-1)=1) (he : e<I.m) (hbaseEnd : base+e*F.limbs+F.limbs≤f)
    (hcache : Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op T e) e) :
    let D' := appendHistoryIteration D T es g l
    let eta' := appendHistoryIterationEta eta T actual
    let op' := appendHistoryIterationOp op T
    Num.fixVal refreshed (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        minRatioFlow A.eraseFailure D' eta' op' (minRatioLast A.eraseFailure D' eta' op' (T+1+1) e) e := by
  dsimp only
  rw [appendHistoryIteration_last_flow]
  rw [show A.eraseFailure.detect=A.detect from rfl]
  by_cases hreport : e∈(A.detect (minRatioState A.eraseFailure D eta op T)).1
  · rw [ite_eq_left hreport]
    have hd := detectRefresh_output F A (namedInstance I) I.m κ α rate allocation R hpre hout
    have hcoordinate := hd.2.2.2.2 haccept e hreport
    have heG : e∈(D.G T).E := by rw [hG]; exact Finset.mem_range.mpr he
    have hf := reportedCachePost_detect_flow F A κ α Ψ eps hA D eta op T hvalid heG hcoordinate
    have hframe := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
    have hb := Num.IPM.fixVal_frozen (h:=F.fmt.limbBits) (P:=F.fmt.precision) hframe hbaseEnd
    exact hf.trans (congrArg (fun z => z+minRatioFlow A.eraseFailure D eta op T e) hb)
  · rw [ite_eq_right hreport]
    have hblock := detectRefresh_unreported_flow F A (namedInstance I) I.m κ α rate allocation R hpre hout he hreport
    have hf : Num.fixVal refreshed (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
      unfold Num.fixVal
      rw [Num.intVal_congr hblock]
    exact hf.trans hcache

end MinCostFlow.IPM.Machine
