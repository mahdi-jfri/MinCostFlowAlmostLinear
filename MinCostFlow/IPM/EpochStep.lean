module

public import MinCostFlow.IPM.EpochQuery
public import MinCostFlow.IPM.EpochTolerances
public import MinCostFlow.IPM.StoredStep
import MinCostFlow.IPM.ResidualStep
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The data structure's Update is a permitted IPM step

This is the Update conversion in Chen et al., arXiv:2203.00671v2,
Lemma 9.3 (page 71), for Definition 4.5. The hidden prefix invokes the
data structure's ratio guarantee. Restricting its named circulation to
the fixed IPM graph and undoing the fixed gradient scale gives the
stored-gradient ratio. The epoch tolerances and `StoredStep` then give
a permitted IPM update, its exact represented flow, and its movement
bound. Hidden stability is an explicit input of this one-step
lemma. The epoch induction proves it (`EpochHidden.lean`), so the final
algorithm does not assume it.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- The circulation selected by the epoch's Update is the circulation
returned by the corresponding abstract history operation. -/
theorem epoch_direction (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) :
    minRatioDirection A (epochInstance I U κ r A base) (epochEta I U κ) epochIsUpdate (2*t) =
      (epochUpdate I U κ r A (epochState I U κ r A base t)).2 := by
  change (A.update (epochTrace I U κ r A base (2*t))
    ((epochInstance I U κ r A base).U (2*t+1))
    ((epochInstance I U κ r A base).g (2*t+1))
    ((epochInstance I U κ r A base).ℓ (2*t+1)) (epochEta I U κ (2*t+1))).2 = _
  rw [(epochTrace_pair I U κ r A base t).1]
  have hmod : (2*t+1)%2 = 1 := by omega
  have hidx : (2*t+1-1)/2 = t := by omega
  simp only [epochInstance, epochEta, hmod, hidx, ↓reduceIte, epochUpdate]

private theorem epoch_increment_formula (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hneg : dot (gradientWithResidual I (alpha I U) r (epochState I U κ r A base t).stored)
      (fun e => (epochUpdate I U κ r A (epochState I U κ r A base t)).2 e) < 0)
    (e : Fin I.m) :
    epochIncrement I U κ r A base t e =
      ((κ*alpha I U/32)^2/(50*|dot
        (gradientWithResidual I (alpha I U) r (epochState I U κ r A base t).stored)
        (fun e => (epochUpdate I U κ r A (epochState I U κ r A base t)).2 e)|))*
          (epochUpdate I U κ r A (epochState I U κ r A base t)).2 e := by
  have hop : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  have hmod : (2*t+1)%2 = 1 := by omega
  have hidx : (2*t+1-1)/2 = t := by omega
  unfold epochIncrement
  have heMem : (e : ℕ) ∈ ((epochInstance I U κ r A base).G (2*t+1)).E := Finset.mem_range.mpr e.2
  simp only [minRatioIncrement, hop, true_and, heMem, ↓reduceIte, epoch_direction]
  simp only [epochInstance, hidx, epochEta, hmod, ↓reduceIte]
  rw [namedInstance_inner_restrict]
  have hdot : dot (epochGradient I U r (epochState I U κ r A base t).stored)
      (fun e => (epochUpdate I U κ r A (epochState I U κ r A base t)).2 e) =
      ipmGradientScale I U*dot
        (gradientWithResidual I (alpha I U) r (epochState I U κ r A base t).stored)
        (fun e => (epochUpdate I U κ r A (epochState I U κ r A base t)).2 e) := by
    simp only [epochGradient, dot, Finset.mul_sum, mul_assoc]
  rw [hdot, abs_of_neg hneg]
  unfold ipmStepEta
  field_simp [(ipmGradientScale_pos I U hsize).ne', hneg.ne]

/-- The actual Update and Query calls of the epoch produce a permitted
IPM step. Its effective parameter lies between `κ α/64` and `κ α/16`,
and its weighted movement is at most `κ α/6400`. -/
theorem epoch_step_update (I : Instance) (U F κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (T t : ℕ)
    (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hvalid : MinRatioHistoryValid (epochInstance I U κ r A base) epochIsUpdate T)
    (ht : 2*(t+1) ≤ T)
    (hhidden : (epochInstance I U κ r A base).HiddenStable (2*t+1) (normalizedIpmAlpha I) (ipmPsi I U))
    (hs : StrictlyInside I (epochState I U κ r A base t).stored)
    (hclose : ∀ e, |lengths I (alpha I U) (epochState I U κ r A base t).stored e*
      (epochFlow I U κ r A base t e-(epochState I U κ r A base t).stored e)| ≤ 8*ipmDetectThreshold I U κ)
    (hr : ScalarApprox (1+8*ipmDetectThreshold I U κ) r (residual I F (epochFlow I U κ r A base t))) :
    ∃ p : ℝ, κ*alpha I U/64 ≤ p ∧ p ≤ κ*alpha I U/16 ∧
      ∃ u : Update I U F p (epochFlow I U κ r A base t),
        epochFlow I U κ r A base (t+1) = u.next ∧
        weightedLength (lengths I (alpha I U) (epochState I U κ r A base t).stored)
          (fun e => epochIncrement I U κ r A base t e) ≤ κ*alpha I U/6400 := by
  have hop : epochIsUpdate (2*t+1) = true := by
    unfold epochIsUpdate
    apply decide_eq_true
    omega
  have hspec := (hA _ (epochEta I U κ) epochIsUpdate T hvalid).2.1 (2*t) (by omega) hop
  rw [epoch_direction] at hspec
  let d := (epochUpdate I U κ r A (epochState I U κ r A base t)).2
  let g := gradientWithResidual I (alpha I U) r (epochState I U κ r A base t).stored
  let ℓ := lengths I (alpha I U) (epochState I U κ r A base t).stored
  have hc : IsCirculation I (fun e => d e) := namedInstance_restrict_circulation I d hspec.1
  have hratio := hspec.2 hhidden
  have hidx : (2*t+1-1)/2 = t := by omega
  change (namedInstance I).inner ((epochInstance I U κ r A base).g (2*t+1)) d /
    (namedInstance I).lnorm ((epochInstance I U κ r A base).ℓ (2*t+1)) d ≤ _ at hratio
  simp only [epochInstance, hidx, namedInstance_inner_restrict] at hratio
  change dot (epochGradient I U r (epochState I U κ r A base t).stored) (fun e => d e) /
    (namedInstance I).lnorm (namedVector ℓ) d ≤ _ at hratio
  rw [namedInstance_lnorm_restrict I ℓ d (lengths_pos I (alpha I U) _ hs)] at hratio
  have hdot : dot (epochGradient I U r (epochState I U κ r A base t).stored) (fun e => d e) =
      ipmGradientScale I U*dot g (fun e => d e) := by
    simp only [epochGradient, g, dot, Finset.mul_sum, mul_assoc]
  rw [hdot, mul_div_assoc, ← ipmGradientScale_mul_alpha I U hsize] at hratio
  have hraw : dot g (fun e => d e)/weightedLength ℓ (fun e => d e) ≤ -4*(κ*alpha I U/32) := by
    apply (mul_le_mul_iff_right₀ (ipmGradientScale_pos I U hsize)).mp
    convert hratio using 1; ring
  have hq : 0 < κ*alpha I U/32 := div_pos (mul_pos hk (alpha_pos I U hsize)) (by norm_num)
  have htol := epoch_stability_tolerances I U F κ r _ _ hm hU hsize hnums hs hk hk' hclose hr
  have hscale := epoch_residual_scale_bounds I U F κ r _ hsize hk hk' hr
  obtain ⟨p, hp, hp', u, hug, hul, hud, hus⟩ := stored_step_update I U F (κ*alpha I U/32)
    (r/residual I F (epochFlow I U κ r A base t)) (epochFlow I U κ r A base t) g ℓ (fun e => d e)
    hq hscale.1 hscale.2 htol.2 htol.1 hc hraw
  have hneg := (u.direction_sign (lt_of_lt_of_le (half_pos hq) hp)).2
  rw [hug, hud] at hneg
  have hdotid : dot (fun e => (r/residual I F (epochFlow I U κ r A base t))*g e) (fun e => d e) =
      (r/residual I F (epochFlow I U κ r A base t))*dot g (fun e => d e) := by
    simp only [dot, Finset.mul_sum, mul_assoc]
  rw [hdotid] at hneg
  have hnegraw : dot g (fun e => d e) < 0 := neg_of_mul_neg_right hneg
    (div_nonneg hr.1.le hr.2.1.le)
  have hdelta : (fun e : Fin I.m => epochIncrement I U κ r A base t e) =
      (fun e : Fin I.m => ((κ*alpha I U/32)^2/(50*|dot g (fun e => d e)|))*d e) := by
    funext e
    exact epoch_increment_formula I U κ r A base t hsize hnegraw e
  refine ⟨p, by linarith only [hp], by linarith only [hp'], u, ?_, ?_⟩
  · funext e
    rw [epoch_flow_step I U κ r (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ)
      A base T t hA hvalid ht]
    change _ = epochFlow I U κ r A base t e+u.stepSize*u.direction e
    rw [hud, hus]
    exact congrArg (fun z => epochFlow I U κ r A base t e+z) (congrFun hdelta e)
  · rw [hdelta]
    have hh := stored_step_movement (κ*alpha I U/32) g ℓ (fun e => d e) hq hraw
    convert hh using 1; ring

end MinCostFlow.IPM
