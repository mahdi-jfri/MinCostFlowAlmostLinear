module

public import MinCostFlow.IPM.Machine.EpochStartRangeScan
public import MinCostFlow.IPM.Machine.EpochCoefficientGuard

/-!
# Acceptance of the actual startup scan on promised inputs

A new epoch computes its complete arrays at the same explicit flow.
The potential-derived slack and residual range leave a strict margin
for these coefficients, so the initialized scan accepts.
-/

public section
namespace MinCostFlow.IPM.Machine

/-- The decoded startup arrays meet the actual scan's strict bounds
whenever the new base has the potential-derived slack ranges. -/
theorem epochStartup_scan_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U q : ℕ)
    (L : EpochLayout) (s : A.State) (a r : ℝ) (mem : ℕ → ℕ) (bit : ℕ)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hsource : epochSourcesAt F I L a r mem)
    (hnums : NumbersBounded I U) (ha0 : 0≤a) (ha1 : a≤1)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hslacks : ∀ e : Fin I.m,
      let f := epochVector F I mem L.flow e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hnames : WordRAM.ListAt mem L.names (List.range I.m))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hout : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem bit mem) :
    bit=1 := by
  have hmin' := hmin
  rw [zpow_neg,zpow_natCast,← one_div] at hmin'
  apply (coefficientRangeList_full_output hnames hneg hmax hmin' hout).mpr
  intro j hj
  let e : Fin I.m := ⟨j,hj⟩
  obtain ⟨hl,hg,_⟩ := reportedCachePost_coefficients F I A L a r mem hsource q e s (hcache j hj)
  rw [hfmt]
  exact epoch_cache_coefficients_in_range I U q a r _ e _ _ ha0 ha1 hnums hr
    (hslacks e).1 (hslacks e).2 hl hg

/-- The decoded startup arrays meet the actual scan's strict bounds
whenever the new base has the potential-derived slack ranges. -/
theorem epochStartup_scan_accepts_at_range {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U q : ℕ)
    (L : EpochLayout) (s : A.State) (a r : ℝ) (mem : ℕ → ℕ) (bit : ℕ)
    (hfmt : ipmRangeExponent I.m U≤F.rangeExponent)
    (hsource : epochSourcesAt F I L a r mem)
    (hnums : NumbersBounded I U) (ha0 : 0≤a) (ha1 : a≤1)
    (hr : 1/(2:ℝ)^(slackRangeExponent I.m U)≤r)
    (hslacks : ∀ e : Fin I.m,
      let f := epochVector F I mem L.flow e
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤(I.edge e).upper-f ∧
        (I.edge e).upper-f≤(2:ℝ)^(slackRangeExponent I.m U)) ∧
      (1/(2:ℝ)^(slackRangeExponent I.m U)≤f-(I.edge e).lower ∧
        f-(I.edge e).lower≤(2:ℝ)^(slackRangeExponent I.m U)))
    (hnames : WordRAM.ListAt mem L.names (List.range I.m))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hout : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem bit mem) :
    bit=1 := by
  have hmin' := hmin
  rw [zpow_neg,zpow_natCast,← one_div] at hmin'
  apply (coefficientRangeList_full_output hnames hneg hmax hmin' hout).mpr
  intro j hj
  let e : Fin I.m := ⟨j,hj⟩
  obtain ⟨hl,hg,_⟩ := reportedCachePost_coefficients F I A L a r mem hsource q e s (hcache j hj)
  obtain ⟨hG,hL,hU⟩ := epoch_cache_coefficients_in_range I U q a r _ e _ _ ha0 ha1 hnums hr
    (hslacks e).1 (hslacks e).2 hl hg
  have hPow : (2:ℝ)^(ipmRangeExponent I.m U)≤(2:ℝ)^F.rangeExponent :=
    pow_le_pow_right₀ (by norm_num) hfmt
  have hInv := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^(ipmRangeExponent I.m U)) hPow
  exact ⟨hG.trans_le hPow,hInv.trans_lt hL,hU.trans_le hPow⟩

end MinCostFlow.IPM.Machine
