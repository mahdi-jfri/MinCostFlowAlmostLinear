module

public import MinCostFlow.IPM.Machine.DetectRefreshOutput
public import MinCostFlow.IPM.Machine.ReportedQueryRange
public import MinCostFlow.IPM.Machine.UnreportedQueryRange

import MinCostFlow.IPM.Machine.MinRatioBridge

/-!
# The whole implicit flow fits Update's range after Detect and refresh

Split edges into reported and unreported ones. Reported coordinates
have passed the actual capacity guard, so subtracting the base bounds
Query. Unreported coordinates stay close to their last cached values by
Detect's unconditional semantics. The chosen range covers both bounds.
No hidden-stability condition is used in this input-safety argument.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The accepted actual combined stage and the last-report cache
invariant give Update's implicit-coordinate range premise everywhere under `P`. -/
theorem detectRefresh_query_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (heps : eps≤1)
    (hR : F.rangeExponent=ipmRangeExponent m U)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U))
    (hsource : ∀ e∈G.E,
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈G.E,|A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent := by
  have hdata := detectRefresh_output F A G m κ α rate allocation R hpre hout
  have hstate : (A.detect (minRatioState A.eraseFailure D eta op t)).2=
      minRatioState A.eraseFailure D eta op (t+1) := by
    simp only [minRatioState,hop,Bool.false_eq_true,↓reduceIte,MinRatioDataStructureWithFailure.eraseFailure]
  intro e he
  rw [hR]
  by_cases hin : e∈(A.detect (minRatioState A.eraseFailure D eta op t)).1
  · have hc := hdata.2.2.2.2 haccept e hin
    have hs := hsource e he
    have hbound := (reportedCachePost_query_bound F A _ hc hs.1 hs.2.1 hs.2.2).2
    have hmargin := ipm_query_range_margin m U hcapacity
    have hnonneg : (0:ℝ)≤2^(2*slackRangeExponent m U+1) := by positivity
    exact hbound.trans ((le_add_of_nonneg_right hnonneg).trans hmargin)
  · rw [hstate]
    exact (minRatio_unreported_query_range_on A.eraseFailure κ α Ψ eps D eta op T t e G m U
      (Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) capacity
      hvalid (hA D eta op T hvalid hsize hPD).1 ht hop hG he hin (hell e he hin) heps (hsource e he).1 (hcache e he hin) hcapacity).le

/-- The accepted actual combined stage and the last-report cache
invariant give Update's implicit-coordinate range premise everywhere.
The whole target-test invariant supplies the explicit history/cache
identifications; neither branch assumes progress for the target. -/
theorem detectRefresh_query_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (heps : eps≤1)
    (hR : F.rangeExponent=ipmRangeExponent m U)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U))
    (hsource : ∀ e∈G.E,
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈G.E,|A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent :=
  detectRefresh_query_range_upTo_on F A G m U κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hvalid hsize ht hop hG (fun _ _ => trivial) heps hR
    capacity hpre hout haccept hcapacity hsource hell hcache

/-- The accepted actual combined stage and the last-report cache
invariant give Update's implicit-coordinate range premise everywhere.
The whole target-test invariant supplies the explicit history/cache
identifications; neither branch assumes progress for the target. -/
theorem detectRefresh_query_range {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    (hA : MinRatioSpecWithFailure A κ α Ψ eps)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (heps : eps≤1)
    (hR : F.rangeExponent=ipmRangeExponent m U)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U))
    (hsource : ∀ e∈G.E,
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈G.E,|A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent := by
  obtain ⟨M,N,hsize⟩ := exists_minRatioHistoryBounded D T
  exact detectRefresh_query_range_upTo F A G m U κ α Ψ eps rate allocation R (hA.upTo M N) D eta
    op T t hvalid hsize ht hop hG heps hR capacity hpre hout haccept hcapacity hsource hell
    hcache

/-- The accepted actual combined stage and the last-report cache
invariant give Update's implicit-coordinate range premise everywhere under `P`. -/
theorem detectRefresh_query_range_at_range_upTo_on {P : MGraph → (ℕ → ℝ) → Prop} {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpToOn P A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G)
    (hPD : ∀ j ≤ T, P (D.G j) (D.ℓ j)) (heps : eps≤1)
    (hR : ipmRangeExponent m U≤F.rangeExponent)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U))
    (hsource : ∀ e∈G.E,
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈G.E,|A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent := by
  have hdata := detectRefresh_output F A G m κ α rate allocation R hpre hout
  have hstate : (A.detect (minRatioState A.eraseFailure D eta op t)).2=
      minRatioState A.eraseFailure D eta op (t+1) := by
    simp only [minRatioState,hop,Bool.false_eq_true,↓reduceIte,MinRatioDataStructureWithFailure.eraseFailure]
  intro e he
  apply le_trans ?_ (pow_le_pow_right₀ (by norm_num) hR)
  by_cases hin : e∈(A.detect (minRatioState A.eraseFailure D eta op t)).1
  · have hc := hdata.2.2.2.2 haccept e hin
    have hs := hsource e he
    have hbound := (reportedCachePost_query_bound F A _ hc hs.1 hs.2.1 hs.2.2).2
    have hmargin := ipm_query_range_margin m U hcapacity
    have hnonneg : (0:ℝ)≤2^(2*slackRangeExponent m U+1) := by positivity
    exact hbound.trans ((le_add_of_nonneg_right hnonneg).trans hmargin)
  · rw [hstate]
    exact (minRatio_unreported_query_range_on A.eraseFailure κ α Ψ eps D eta op T t e G m U
      (Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision) capacity
      hvalid (hA D eta op T hvalid hsize hPD).1 ht hop hG he hin (hell e he hin) heps (hsource e he).1 (hcache e he hin) hcapacity).le

/-- The accepted actual combined stage and the last-report cache
invariant give Update's implicit-coordinate range premise everywhere.
The whole target-test invariant supplies the explicit history/cache
identifications; neither branch assumes progress for the target. -/
theorem detectRefresh_query_range_at_range_upTo {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (G : MGraph) (m U : ℕ) (κ α Ψ eps : ℝ)
    (rate : ℕ → ℕ) (allocation : ℕ → List ℕ → ℕ) (R : DSRep A.State)
    {M N : ℕ} (hA : MinRatioSpecWithFailureUpTo A κ α Ψ eps M N)
    (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool) (T t : ℕ)
    (hvalid : MinRatioHistoryValid D op T) (hsize : MinRatioHistoryBounded D T M N) (ht : t+1≤T) (hop : op (t+1)=false)
    (hG : ∀ j≤T,D.G j=G) (heps : eps≤1)
    (hR : ipmRangeExponent m U≤F.rangeExponent)
    {b q K sourceEnd tableEnd names base lo up f heap c r a one mn mx E ld gd v : ℕ}
    {x : R.τ} {mem mem' : ℕ → ℕ} (capacity : ℝ)
    (hpre : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).pre
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem)
    (hout : (detectRefreshContract F A G m κ α rate allocation R b
      (minRatioState A.eraseFailure D eta op t) x q K sourceEnd tableEnd).post
      [b,names,m,base,lo,up,f,F.limbs,heap,c,r,a,one,mn,mx,F.fmt.precision,E,ld,gd,m] mem v mem')
    (haccept : mem' (v-1)=1)
    (hcapacity : capacity≤(2:ℝ)^(slackRangeExponent m U))
    (hsource : ∀ e∈G.E,
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |Num.fixVal mem' (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hell : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      1/(2:ℝ)^(2*slackRangeExponent m U+1)≤D.ℓ (t+1) e)
    (hcache : ∀ e∈G.E,e∉(A.detect (minRatioState A.eraseFailure D eta op t)).1 →
      |Num.fixVal mem' (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision+
        A.query (minRatioState A.eraseFailure D eta op (minRatioLast A.eraseFailure D eta op t e)) e|≤capacity) :
    ∀ e∈G.E,|A.query (A.detect (minRatioState A.eraseFailure D eta op t)).2 e|≤(2:ℝ)^F.rangeExponent :=
  detectRefresh_query_range_at_range_upTo_on F A G m U κ α Ψ eps rate allocation R
    (hA.upToOn (P := fun _ _ => True)) D eta op T t hvalid hsize ht hop hG (fun _ _ => trivial) heps hR
    capacity hpre hout haccept hcapacity hsource hell hcache

end MinCostFlow.IPM.Machine
