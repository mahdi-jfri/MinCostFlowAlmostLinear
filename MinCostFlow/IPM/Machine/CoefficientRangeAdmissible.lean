module

public import MinCostFlow.IPM.Machine.StrictCoefficientRanges
public import MinCostFlow.IPM.Machine.CoefficientRangeListOutput

/-!
# The actual coefficient scan accepts admissible epoch coefficients

The potential-to-slack bound and the numerical tolerances place each
reported pair strictly inside the selected machine range. Decode the
actual scan's comparisons at those represented endpoints. Its returned
bit must be one. This connects the analytic range margin to a machine
run, without an acceptance hypothesis.
-/

noncomputable section
public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- A completed actual report scan accepts every epoch coefficient pair
satisfying the potential-derived ranges and numerical tolerances. -/
theorem coefficientRangeList_accepts_epoch (I : Instance) (U : ℕ)
    (a r : ℝ) (stored : Fin I.m → ℝ) (ha : 0≤a) (ha' : a≤1)
    (hnums : NumbersBounded I U)
    {w h report g l neg mx mn L P v : ℕ} {S : Finset ℕ} {mem mem' : ℕ → ℕ}
    (hreport : DetectAt mem report S) (hsubset : S⊆Finset.range I.m)
    (hout : (coefficientRangeListContract w h).post [report+1,S.card,g,l,neg,mx,mn,L] mem v mem')
    (hn : ScalarAt mem neg h L P (-(2:ℝ)^(ipmRangeExponent I.m U)))
    (hx : ScalarAt mem mx h L P ((2:ℝ)^(ipmRangeExponent I.m U)))
    (hm : ScalarAt mem mn h L P (1/(2:ℝ)^(ipmRangeExponent I.m U)))
    (hu : ∀ e,1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-stored e ∧
      (I.edge e).upper-stored e≤(2:ℝ)^(slackRangeExponent I.m U))
    (hd : ∀ e,1/(2:ℝ)^(slackRangeExponent I.m U)≤stored e-(I.edge e).lower ∧
      stored e-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U))
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hell : ∀ e : Fin I.m,e.val∈S → ScalarApprox 2 (Num.fixVal mem (l+e.val*L) h L P) (lengths I a stored e))
    (hz : ∀ e : Fin I.m,e.val∈S →
      |Num.fixVal mem (g+e.val*L) h L P-gradientWithResidual I a r stored e|≤lengths I a stored e) :
    v=1 := by
  apply coefficientRangeList_accepts hreport hout hn hx hm
  intro e he
  let edge : Fin I.m := ⟨e,Finset.mem_range.mp (hsubset he)⟩
  exact computed_epoch_coefficients_strict_range I U a r
    (Num.fixVal mem (g+e*L) h L P) (Num.fixVal mem (l+e*L) h L P)
    stored ha ha' hnums edge (hu edge) (hd edge) hr (hell edge he) (hz edge he)

end MinCostFlow.IPM.Machine
