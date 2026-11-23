module

public import MinCostFlow.IPM.Machine.DetectRefresh
public import MinCostFlow.IPM.Machine.EpochStartRangeScan
public import MinCostFlow.IPM.Machine.EpochLayout

/-!
# First lazy call after checked epoch startup

A successful scan certifies the ranges required at the first lazy call
on the same initialized table memory.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Decode the initial cache and successful full scan into the loop's
per-edge validity and coefficient range conditions. -/
theorem epochStartup_loop_ranges {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (L : EpochLayout)
    (s : A.State) (q : ℕ) {mem : ℕ → ℕ}
    (hnames : ListAt mem L.names (List.range I.m))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hscan : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem 1 mem) :
    ∀ e<I.m,Num.Valid mem (L.gradient+e*F.limbs) F.fmt.limbBits F.limbs ∧
      Num.Valid mem (L.lengths+e*F.limbs) F.fmt.limbBits F.limbs ∧
      |readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m e|≤(2:ℝ)^F.rangeExponent ∧
      (2:ℝ)^(-(F.rangeExponent:ℤ))≤readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e ∧
      readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m e≤(2:ℝ)^F.rangeExponent := by
  intro e he
  have hmin' := hmin
  rw [zpow_neg,zpow_natCast,← one_div] at hmin'
  have hr := (coefficientRangeList_full_output hnames hneg hmax hmin' hscan).mp rfl e he
  rw [zpow_neg,zpow_natCast,← one_div]
  have hc := hcache e he
  simpa only [readVector,ite_eq_left he] using (show _ ∧ _ ∧ _ ∧ _ ∧ _ from
    ⟨hc.2.2.2.2.1,hc.2.2.1,hr.1.le,hr.2.1.le,hr.2.2.le⟩)

/-- A successful startup scan puts the initialized lengths in `[2^{-E}, 2^E]` for
`E = F.rangeExponent`. -/
theorem epochStartup_lengthsWithin {w : ℕ} (F : MinRatioFormat w) (I : Instance) (L : EpochLayout)
    {mem : ℕ → ℕ}
    (hnames : ListAt mem L.names (List.range I.m))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hscan : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem 1 mem) :
    LengthsWithin (namedInstance I) F.rangeExponent
      (readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m) := by
  intro e he
  have heM : e<I.m := Finset.mem_range.mp he
  have hmin' := hmin
  rw [zpow_neg,zpow_natCast,← one_div] at hmin'
  have hr := (coefficientRangeList_full_output hnames hneg hmax hmin' hscan).mp rfl e heM
  rw [zpow_neg,zpow_natCast,← one_div]
  simpa only [readVector,heM,ite_true] using (show _ ∧ _ from ⟨hr.2.1.le,hr.2.2.le⟩)

end MinCostFlow.IPM.Machine
