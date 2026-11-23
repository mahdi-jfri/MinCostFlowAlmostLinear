module

public import MinCostFlow.IPM.Machine.ReportedEdgesContract
import Mathlib.Tactic.Ring

/-!
# Bounded Query coordinates for accepted reported entries

The strengthened cache postcondition records the capacity guard's
strict inequalities. The stored flow is therefore bounded by the two
capacity endpoints. Subtracting the bounded base flow bounds the
implicit Query coordinate, with no hidden-stability or progress premise.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- Accepted cache feasibility and bounded capacity/base inputs give
an implicit Query bound twice the capacity bound. -/
theorem reportedCachePost_query_bound {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (s : A.State)
    {m q base lo up f c r a ld gd e : ℕ} {mem : ℕ → ℕ} {capacity : ℝ}
    (hcache : reportedCachePost F A s m q base lo up f c r a ld gd e mem)
    (hbase : |Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hlo : |Num.fixVal mem (lo+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity)
    (hup : |Num.fixVal mem (up+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity) :
    |Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity ∧
      |A.query s e|≤2*capacity := by
  have hin := hcache.2.2.2.2.2.2
  have hf : |Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|≤capacity :=
    abs_le.mpr ⟨(abs_le.mp hlo).1.trans hin.1.le,hin.2.le.trans (abs_le.mp hup).2⟩
  refine ⟨hf,?_⟩
  have hquery : A.query s e=Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision-
      Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision := by
    rw [hcache.2.1]
    ring
  rw [hquery,sub_eq_add_neg]
  calc
    _≤|Num.fixVal mem (f+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision|+
        |-(Num.fixVal mem (base+e*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)| := abs_add_le _ _
    _≤capacity+capacity := by rw [abs_neg]; exact add_le_add hf hbase
    _=2*capacity := by ring

end MinCostFlow.IPM.Machine
