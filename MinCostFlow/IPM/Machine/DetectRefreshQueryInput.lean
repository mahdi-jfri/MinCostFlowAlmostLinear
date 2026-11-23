module

public import MinCostFlow.IPM.Machine.DetectRefreshQueryRange
public import MinCostFlow.IPM.Machine.DetectRefreshFrame
import MinCostFlow.Num.IPM.FixedPointFacts
import MinCostFlow.IPM.Machine.ReportedTableLayout

import MinCostFlow.IPM.Machine.EpochConditions

/-!
# Implicit-flow input safety from the preceding history and source memory

The base flow and capacity tables lie before the cached-flow table.
Their words survive Detect/refresh. Thus the old capacity and last-report
cache bounds supply the unconditional Query-range argument directly at
the actual returned memory. No assumption about the result of a future
operation is needed to prepare the next Update.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The pre-call source and last-report cache invariants establish the
whole implicit-flow range after actual accepted Detect/refresh. -/
theorem detectRefresh_query_range_of_sources_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (heps : eps≤1)
    (hR : F.rangeExponent=ipmRangeExponent I.m U)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ p∈[base,lo,up],p+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈(namedInstance I).E,
      |A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent := by
  have hf := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hs (p e : ℕ) (hp : p∈[base,lo,up]) (he : e∈(namedInstance I).E) :
      Num.fixVal mem' (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
    Num.IPM.fixVal_frozen hf ((reported_entry_end p F.limbs e I.m (Finset.mem_range.mp he)).trans (hsourceEnd p hp))
  apply detectRefresh_query_range_upTo F A (namedInstance I) I.m U κ α Ψ eps rate allocation R hA D eta op T t
    hvalid (namedHistory_bounded hG) ht hop hG heps hR capacity hpre hout haccept hcapacity
  · intro e he
    rw [hs base e (by simp) he,hs lo e (by simp) he,hs up e (by simp) he]
    exact hsource e he
  · exact hell
  · intro e he hne
    rw [hs base e (by simp) he]
    exact hcache e he hne

/-- The pre-call source and last-report cache invariants establish the
whole implicit-flow range after actual accepted Detect/refresh. -/
theorem detectRefresh_query_range_of_sources {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (heps : eps≤1)
    (hR : F.rangeExponent=ipmRangeExponent I.m U)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ p∈[base,lo,up],p+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈(namedInstance I).E,
      |A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent :=
  detectRefresh_query_range_of_sources_upTo F A I U κ α Ψ eps rate allocation R (hA.upTo I.m
    I.n) D eta op T t hvalid ht hop hG heps hR capacity hpre hout haccept hcapacity hsourceEnd
    hsource hell hcache

/-- The pre-call source and last-report cache invariants under `P` establish the
whole implicit-flow range after actual accepted Detect/refresh. -/
theorem detectRefresh_query_range_of_sources_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ}
    (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (heps : eps≤1)
    (hR : ipmRangeExponent I.m U≤F.rangeExponent)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ p∈[base,lo,up],p+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈(namedInstance I).E,
      |A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent := by
  have hf := detectRefresh_frame F A (namedInstance I) I.m κ α rate allocation R hpre hout
  have hs (p e : ℕ) (hp : p∈[base,lo,up]) (he : e∈(namedInstance I).E) :
      Num.fixVal mem' (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision=
        Num.fixVal mem (p+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision :=
    Num.IPM.fixVal_frozen hf ((reported_entry_end p F.limbs e I.m (Finset.mem_range.mp he)).trans (hsourceEnd p hp))
  apply detectRefresh_query_range_at_range_upTo_on F A (namedInstance I) I.m U κ α Ψ eps rate allocation R hA D eta op T t
    hvalid (namedHistory_bounded hG) ht hop hG hPD heps hR capacity hpre hout haccept hcapacity
  · intro e he
    rw [hs base e (by simp) he,hs lo e (by simp) he,hs up e (by simp) he]
    exact hsource e he
  · exact hell
  · intro e he hne
    rw [hs base e (by simp) he]
    exact hcache e he hne

/-- The pre-call source and last-report cache invariants establish the
whole implicit-flow range after actual accepted Detect/refresh. -/
theorem detectRefresh_query_range_of_sources_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps I.m I.n)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=namedInstance I) (heps : eps≤1)
    (hR : ipmRangeExponent I.m U≤F.rangeExponent)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem)
    (hout : (detectRefreshContract F A (namedInstance I) I.m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,I.m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,I.m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent I.m U))
    (hsourceEnd : ∀ p∈[base,lo,up],p+I.m*F.limbs≤f)
    (hsource : ∀ e∈(namedInstance I).E,
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent I.m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈(namedInstance I).E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈(namedInstance I).E,
      |A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent :=
  detectRefresh_query_range_of_sources_at_range_upTo_on F A I U κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hvalid ht hop hG (fun _ _ => trivial) heps hR
    capacity hpre hout haccept hcapacity hsourceEnd hsource hell hcache

end MinCostFlow.IPM.Machine
