module

public import MinCostFlow.IPM.Machine.EpochStartupAcceptance
public import MinCostFlow.IPM.Machine.CoefficientRangeFull
public import MinCostFlow.IPM.Machine.CoefficientRefresh
public import MinCostFlow.IPM.Machine.EpochNextLayout
public import MinCostFlow.IPM.Machine.TargetEpochResult
public import MinCostFlow.IPM.Machine.EpochGuardRanges
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Starting a promised epoch with its exact held residual

The potential at the copied flow gives the smaller analytic slack
range. This leaves a strict margin for the wider machine
coefficient guards at the startup scan.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- The actual scan accepts if the copied flow has the upper-target
promise and its residual exceeds one quarter. -/
theorem targetEpoch_startup_accepts {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U q : ℕ)
    (L : EpochLayout) (s : A.State) (target r : ℝ) (mem : ℕ → ℕ) (bit : ℕ)
    (hfmt : F.rangeExponent=ipmRangeExponent I.m U)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem L.flow)=r) (hr : 1/4<r)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1)
    (hf : StrictlyInside I (epochVector F I mem L.flow)) (hroute : I.Routes (epochVector F I mem L.flow))
    (hnames : ListAt mem L.names (List.range I.m))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hout : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem bit mem)
    (hp : TargetStagePromise I U target (epochVector F I mem L.flow)) :
    bit=1 := by
  have hr' : 1/8≤residual I target (epochVector F I mem L.flow) := by
    rw [hres]
    linarith only [hr]
  obtain ⟨hresRange,hslacks⟩ := epoch_numeric_ranges I U target _ hm hU hsize hnums hf hroute hp.2 hFlo hr'
  rw [hres] at hresRange
  exact epochStartup_scan_accepts F A I U q L s _ r mem bit hfmt hsource hnums ha0 ha1
    hresRange.1 hslacks hnames hneg hmax hmin hcache hout

/-- The actual scan accepts if the copied flow has the upper-target
promise and its residual exceeds one quarter. -/
theorem targetEpoch_startup_accepts_at_range {w : ℕ} (F : MinRatioFormat w)
    (A : MinRatioDataStructureWithFailure) (I : Instance) (U q : ℕ)
    (L : EpochLayout) (s : A.State) (target r : ℝ) (mem : ℕ → ℕ) (bit : ℕ)
    (hfmt : ipmRangeExponent I.m U≤F.rangeExponent)
    (hsource : epochSourcesAt F I L (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem L.flow)=r) (hr : 1/4<r)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1)
    (hf : StrictlyInside I (epochVector F I mem L.flow)) (hroute : I.Routes (epochVector F I mem L.flow))
    (hnames : ListAt mem L.names (List.range I.m))
    (hneg : ScalarAt mem L.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem L.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem L.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hcache : ∀ e<I.m,reportedCachePost F A s I.m q L.base L.lower L.upper L.flow
      L.cost L.residual L.alpha L.lengths L.gradient e mem)
    (hout : (coefficientRangeListContract w F.fmt.limbBits).post
      [L.names,I.m,L.gradient,L.lengths,L.gradientMin,L.gradientMax,L.lengthMin,F.limbs] mem bit mem)
    (hp : TargetStagePromise I U target (epochVector F I mem L.flow)) :
    bit=1 := by
  have hr' : 1/8≤residual I target (epochVector F I mem L.flow) := by
    rw [hres]
    linarith only [hr]
  obtain ⟨hresRange,hslacks⟩ := epoch_numeric_ranges I U target _ hm hU hsize hnums hf hroute hp.2 hFlo hr'
  rw [hres] at hresRange
  exact epochStartup_scan_accepts_at_range F A I U q L s _ r mem bit hfmt hsource hnums ha0 ha1
    hresRange.1 hslacks hnames hneg hmax hmin hcache hout

/-- Direct pre-Init full-range scan accepts on a promised target without
requiring a data structure state or name list. -/
theorem targetEpoch_fullScan_accepts_at_range {w q K : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U : ℕ) (old : EpochLayout) (base rp fp heap bit : ℕ)
    (target r : ℝ) (mem coeffMem : ℕ → ℕ)
    (hfmt : ipmRangeExponent I.m U≤F.rangeExponent)
    (hsource : epochSourcesAt F I (old.next F I base rp fp heap 0) (Num.IPM.alphaPrime I.m U) r mem)
    (hres : residual I target (epochVector F I mem fp)=r) (hr : 1/4<r)
    (hm : 0<I.m) (hU : 1≤U) (hsize : 2≤I.m*U)
    (hnums : NumbersBounded I U) (hFlo : -(I.m*(U:ℝ)^2)≤target)
    (ha0 : 0≤Num.IPM.alphaPrime I.m U) (ha1 : Num.IPM.alphaPrime I.m U≤1)
    (hf : StrictlyInside I (epochVector F I mem fp)) (hroute : I.Routes (epochVector F I mem fp))
    (hnegEnd : old.gradientMin+F.limbs≤heap) (hmaxEnd : old.gradientMax+F.limbs≤heap)
    (hminEnd : old.lengthMin+F.limbs≤heap)
    (hneg : ScalarAt mem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent))
    (hmax : ScalarAt mem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent))
    (hmin : ScalarAt mem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^(-(F.rangeExponent:ℤ))))
    (hRpost : let L := old.next F I base rp fp heap 0
      (coefficientRefreshContract w F.fmt.limbBits q K).post ((L.startPacket F I).take 14)
        mem L.handle coeffMem)
    (hSpost : let la := Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent
      (coefficientRangeFullContract w F.fmt.limbBits).post
        [I.m,heap+la,heap,old.gradientMin,old.gradientMax,old.lengthMin,F.limbs]
        coeffMem bit coeffMem)
    (hp : TargetStagePromise I U target (epochVector F I mem fp)) :
    bit=1 := by
  have hr' : 1/8≤residual I target (epochVector F I mem fp) := by
    rw [hres]; linarith only [hr]
  obtain ⟨hresRange,hslacks⟩ := epoch_numeric_ranges I U target _ hm hU hsize hnums hf hroute hp.2 hFlo hr'
  rw [hres] at hresRange
  have hRframe : ∀ z<heap,coeffMem z=mem z := hRpost.1.2.2.1
  have hnegC : ScalarAt coeffMem old.gradientMin F.fmt.limbBits F.limbs F.fmt.precision (-(2:ℝ)^F.rangeExponent) :=
    ⟨Num.IPM.valid_frozen hRframe hnegEnd hneg.1,(Num.IPM.fixVal_frozen hRframe hnegEnd).trans hneg.2⟩
  have hmaxC : ScalarAt coeffMem old.gradientMax F.fmt.limbBits F.limbs F.fmt.precision ((2:ℝ)^F.rangeExponent) :=
    ⟨Num.IPM.valid_frozen hRframe hmaxEnd hmax.1,(Num.IPM.fixVal_frozen hRframe hmaxEnd).trans hmax.2⟩
  have hminC : ScalarAt coeffMem old.lengthMin F.fmt.limbBits F.limbs F.fmt.precision (1/(2:ℝ)^F.rangeExponent) := by
    have hm' := hmin
    rw [zpow_neg,zpow_natCast,← one_div] at hm'
    exact ⟨Num.IPM.valid_frozen hRframe hminEnd hm'.1,(Num.IPM.fixVal_frozen hRframe hminEnd).trans hm'.2⟩
  apply (coefficientRangeFull_output hnegC hmaxC hminC hSpost).mpr
  intro j hj
  let e : Fin I.m := ⟨j,hj⟩
  obtain ⟨haEq,hrEq,hEdges⟩ := hsource
  obtain ⟨hlo,hup,hcost⟩ := hEdges e
  dsimp only [EpochLayout.next] at haEq hrEq hlo hup hcost
  have hlEq : Num.IPM.arrayLength mem old.lower fp old.upper old.alpha
      F.fmt.limbBits F.limbs F.fmt.precision j=lengths I (Num.IPM.alphaPrime I.m U) (epochVector F I mem fp) e := by
    unfold Num.IPM.arrayLength lengths
    rw [haEq]
    change Real.rpow (epochVector F I mem old.upper e-epochVector F I mem fp e) (-1-Num.IPM.alphaPrime I.m U)+
      Real.rpow (epochVector F I mem fp e-epochVector F I mem old.lower e) (-1-Num.IPM.alphaPrime I.m U)=_
    rw [hlo,hup]
  have hgEq : Num.IPM.arrayGradient mem I.m old.cost rp old.lower fp old.upper old.alpha
      F.fmt.limbBits F.limbs F.fmt.precision j=gradientWithResidual I (Num.IPM.alphaPrime I.m U) r (epochVector F I mem fp) e := by
    unfold Num.IPM.arrayGradient gradientWithResidual
    rw [haEq,hrEq,hcost]
    change 20*(I.m:ℝ)*r⁻¹*(I.edge e).cost+
      Num.IPM.alphaPrime I.m U*(Real.rpow (epochVector F I mem old.upper e-epochVector F I mem fp e) (-1-Num.IPM.alphaPrime I.m U)-
        Real.rpow (epochVector F I mem fp e-epochVector F I mem old.lower e) (-1-Num.IPM.alphaPrime I.m U))=_
    rw [hlo,hup]
    ring
  have hlApprox : ScalarApprox (1+1/(2:ℝ)^q)
      (Num.fixVal coeffMem (heap+j*F.limbs) F.fmt.limbBits F.limbs F.fmt.precision)
      (lengths I (Num.IPM.alphaPrime I.m U) (epochVector F I mem fp) e) := by
    rw [← hlEq]; exact (hRpost.1.2.2.2.2.1 j hj).2
  have hgApprox : |Num.fixVal coeffMem (heap+Num.IPM.lengthArraySpace I.m F.limbs F.fmt.precision old.exponent+j*F.limbs)
      F.fmt.limbBits F.limbs F.fmt.precision-gradientWithResidual I (Num.IPM.alphaPrime I.m U) r (epochVector F I mem fp) e|≤
      (1/(2:ℝ)^q)*lengths I (Num.IPM.alphaPrime I.m U) (epochVector F I mem fp) e := by
    rw [← hgEq,← hlEq]; exact (hRpost.1.2.2.2.2.2 j hj).2
  obtain ⟨hG,hL,hU⟩ := epoch_cache_coefficients_in_range I U q (Num.IPM.alphaPrime I.m U) r _ e _ _
    ha0 ha1 hnums hresRange.1 (hslacks e).1 (hslacks e).2 hlApprox hgApprox
  have hPow : (2:ℝ)^(ipmRangeExponent I.m U)≤(2:ℝ)^F.rangeExponent :=
    pow_le_pow_right₀ (by norm_num) hfmt
  have hInv := one_div_le_one_div_of_le (by positivity : (0:ℝ)<2^(ipmRangeExponent I.m U)) hPow
  exact ⟨hG.trans_le hPow,hInv.trans_lt hL,hU.trans_le hPow⟩

end MinCostFlow.IPM.Machine
