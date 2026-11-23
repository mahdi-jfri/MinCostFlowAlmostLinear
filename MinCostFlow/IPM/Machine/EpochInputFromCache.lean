module

public import MinCostFlow.IPM.Machine.EpochHistoryAccuracy
public import MinCostFlow.IPM.Machine.EpochComputedTolerances
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Applying the computed-cache bounds to one history input

Both the old Detect coefficients and the refreshed Update coefficients
are arrays of fixed-point scalars. Their decoded cached coordinates,
slack lengths and held-residual gradients supply accuracy at the
corresponding input stage of the shared history.
-/

public section
namespace MinCostFlow.IPM.Machine

private theorem readVector_named_epochVector {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (mem : ℕ → ℕ) (ptr : ℕ) :
    readVector mem ptr F.fmt.limbBits F.limbs F.fmt.precision I.m=
      namedVector (epochVector F I mem ptr) := by
  funext e
  by_cases he : e<I.m <;> simp only [namedVector,readVector,epochVector,he,↓reduceDIte,ite_true,ite_false]

/-- Decode the actual coefficient and cache arrays at one input stage.
The exact-length displacement bound pays for Lemma 9.1's tolerances.
The supplied-length displacement bound pays for the hidden widths. -/
theorem epochInputAccuracyAt_of_cache {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U k : ℕ) (target a x r : ℝ) (A : MinRatioDataStructureWithFailure)
    (L : EpochLayout) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (t : ℕ) (base : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*qualitySlackExponent I.m U k)≤x) (hxhi : x≤1)
    (hg : D.g t=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ t=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hcache : epochHistoryCache I A D eta op t base=epochVector F I mem L.flow)
    (hinside : StrictlyInside I (epochVector F I mem L.flow))
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmQualityErrorBits I.m U k)) (epochVector F I mem L.lengths)
      (lengths I a (epochVector F I mem L.flow)))
    (hnumGradient : ∀ e,|epochVector F I mem L.gradient e-
      gradientWithResidual I a r (epochVector F I mem L.flow) e|≤
      (1/(2:ℝ)^(ipmQualityErrorBits I.m U k))*lengths I a (epochVector F I mem L.flow) e)
    (hrange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k))
    (hres : ScalarApprox (1+8*(x/1024)) r (residual I target (epochInputFlow I A D eta op t base)))
    (hclose : ∀ e,|lengths I a (epochVector F I mem L.flow) e*
      (epochInputFlow I A D eta op t base e-epochVector F I mem L.flow e)|≤8*(x/1024))
    (hweighted : ∀ e,|epochVector F I mem L.lengths e*
      (epochInputFlow I A D eta op t base e-epochVector F I mem L.flow e)|≤1/2) :
    EpochInputAccuracyAt I (ipmQualityRangeExponent I.m U k) target a r (x/32) A D eta op base t := by
  obtain ⟨_,hlen,hgrad⟩ := epoch_widened_computed_tolerances I U k target a x r (epochVector F I mem L.flow)
    (epochInputFlow I A D eta op t base) (epochVector F I mem L.gradient) (epochVector F I mem L.lengths)
    hm hsize hnums ha0 ha hxlo hxhi hinside hclose hres hnumLength hnumGradient
  have haG : (fun e : Fin I.m => D.g t e)=epochVector F I mem L.gradient := by
    rw [hg,readVector_named_epochVector]
    exact funext (namedVector_fin _)
  have haL : (fun e : Fin I.m => D.ℓ t e)=epochVector F I mem L.lengths := by
    rw [hl,readVector_named_epochVector]
    exact funext (namedVector_fin _)
  have hr : ScalarApprox (1+(x/32)/4) r (residual I target (epochInputFlow I A D eta op t base)) :=
    (show 1+8*(x/1024)=1+(x/32)/4 by ring) ▸ hres
  unfold EpochInputAccuracyAt
  dsimp only
  rw [hcache]
  refine ⟨?_,?_,hr,?_,?_,?_,?_⟩
  · rw [haG]
    exact hg.trans (readVector_named_epochVector F I mem L.gradient)
  · rw [haL]
    exact hl.trans (readVector_named_epochVector F I mem L.lengths)
  · rw [haL]
    exact hlen
  · change GradientTolerance _ (fun e => _*(fun j : Fin I.m => D.g t j) e) _ _
    rw [haG]
    exact hgrad
  · change ∀ e,1/(2:ℝ)^(ipmQualityRangeExponent I.m U k)≤(fun j : Fin I.m => D.ℓ t j) e ∧
      (fun j : Fin I.m => D.ℓ t j) e≤(2:ℝ)^(ipmQualityRangeExponent I.m U k)
    rw [haL]
    exact hrange
  · change ∀ e,|(fun j : Fin I.m => D.ℓ t j) e*_|≤1/2
    rw [haL]
    exact hweighted

/-- Decode the actual coefficient and cache arrays at one input stage.
The exact-length displacement bound pays for Lemma 9.1's tolerances.
The supplied-length displacement bound pays for the hidden widths. -/
theorem epochInputAccuracy_of_cache {w : ℕ} (F : MinRatioFormat w)
    (I : Instance) (U : ℕ) (target a x r : ℝ) (A : MinRatioDataStructureWithFailure)
    (L : EpochLayout) (D : DynamicInstance) (eta : ℕ → ℝ) (op : ℕ → Bool)
    (t : ℕ) (base : Fin I.m → ℝ) (mem : ℕ → ℕ)
    (hm : 0<I.m) (hsize : 2≤(I.m:ℝ)*U) (hnums : NumbersBounded I U)
    (ha0 : 0≤a) (ha : a≤alpha I U)
    (hxlo : 1/(2:ℝ)^(2*slackRangeExponent I.m U)≤x) (hxhi : x≤1)
    (hg : D.g t=readVector mem L.gradient F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hl : D.ℓ t=readVector mem L.lengths F.fmt.limbBits F.limbs F.fmt.precision I.m)
    (hcache : epochHistoryCache I A D eta op t base=epochVector F I mem L.flow)
    (hinside : StrictlyInside I (epochVector F I mem L.flow))
    (hnumLength : VectorApprox (1+1/(2:ℝ)^(ipmErrorBits I.m U)) (epochVector F I mem L.lengths)
      (lengths I a (epochVector F I mem L.flow)))
    (hnumGradient : ∀ e,|epochVector F I mem L.gradient e-
      gradientWithResidual I a r (epochVector F I mem L.flow) e|≤
      (1/(2:ℝ)^(ipmErrorBits I.m U))*lengths I a (epochVector F I mem L.flow) e)
    (hrange : ∀ e : Fin I.m,1/(2:ℝ)^(ipmRangeExponent I.m U)≤epochVector F I mem L.lengths e ∧
      epochVector F I mem L.lengths e≤(2:ℝ)^(ipmRangeExponent I.m U))
    (hres : ScalarApprox (1+8*(x/1024)) r (residual I target (epochInputFlow I A D eta op t base)))
    (hclose : ∀ e,|lengths I a (epochVector F I mem L.flow) e*
      (epochInputFlow I A D eta op t base e-epochVector F I mem L.flow e)|≤8*(x/1024))
    (hweighted : ∀ e,|epochVector F I mem L.lengths e*
      (epochInputFlow I A D eta op t base e-epochVector F I mem L.flow e)|≤1/2) :
    EpochInputAccuracy I U target a r (x/32) A D eta op base t := by
  obtain ⟨hR,hError,_,_,_⟩ := ipmQualityParameters_eq
    (m := I.m) (U := U) (Nat.zero_le (slackRangeExponent I.m U))
  have hLow : 1/(2:ℝ)^(2*qualitySlackExponent I.m U 0)≤x := by
    rwa [qualitySlackExponent_eq (Nat.zero_le _)]
  have hLength := hError.symm ▸ hnumLength
  have hGradient := hError.symm ▸ hnumGradient
  have hRange := hR.symm ▸ hrange
  have hAccuracy := epochInputAccuracyAt_of_cache F I U 0 target a x r A L D eta op t base mem
    hm hsize hnums ha0 ha hLow hxhi hg hl hcache hinside hLength hGradient hRange hres hclose hweighted
  simpa only [EpochInputAccuracy, hR] using hAccuracy

end MinCostFlow.IPM.Machine
