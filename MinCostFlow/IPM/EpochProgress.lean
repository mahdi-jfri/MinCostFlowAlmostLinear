module

public import MinCostFlow.IPM.EpochStep
public import MinCostFlow.IPM.EpochMemory
public import MinCostFlow.IPM.ResidualStep
import MinCostFlow.IPM.Parameters
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Progress of the actual epoch loop

The Update conversion for Chen et al., arXiv:2203.00671v2,
Lemma 9.3 (page 71), now applies to the causal loop itself. Input-history
validity follows from its previously stored coordinates. Detect supplies
the coordinate approximation, and the data structure supplies the cycle
ratio on a hidden stable prefix. Lemma 4.4 then proves strict feasibility,
routing, residual positivity, and a uniform potential decrease. The
residual drift estimate keeps the step parameter for the epoch analysis.
-/

noncomputable section
public section
namespace MinCostFlow.IPM

/-- Refreshing selected stored coordinates from the new interior flow
preserves strict interiority of the entire stored vector. -/
theorem epoch_stored_inside_succ (I : Instance) (U κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ)
    (hold : StrictlyInside I (epochState I U κ r A base t).stored)
    (hnew : StrictlyInside I (epochFlow I U κ r A base (t+1))) :
    StrictlyInside I (epochState I U κ r A base (t+1)).stored := by
  intro e
  change (I.edge e).lower < (if (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending then
      epochFlow I U κ r A base (t+1) e else (epochState I U κ r A base t).stored e) ∧
    (if (e : ℕ) ∈ (epochState I U κ r A base (t+1)).pending then
      epochFlow I U κ r A base (t+1) e else (epochState I U κ r A base t).stored e) < (I.edge e).upper
  split_ifs
  · exact hnew e
  · exact hold e

/-- A step of the actual epoch preserves routing and the analytic domain,
decreases potential by at least `(κ α/64)²/500`, and has relative residual
drift at most `κ α/(800m)`. No step or approximation oracle is assumed:
all operation guarantees come from `MinRatioSpec`, with hidden stability
and the residual snapshot still explicit inputs to this one-step lemma. -/
theorem epoch_progress (I : Instance) (U F κ r : ℝ) (A : MinRatioDataStructure)
    (base : Fin I.m → ℝ) (t : ℕ)
    (hI : I.IsValid) (hm : 0 < I.m) (hU : 0 ≤ U) (hsize : 2 ≤ (I.m : ℝ)*U)
    (hnums : NumbersBounded I U) (hk : 0 < κ) (hk' : κ ≤ 1)
    (hA : MinRatioSpec A κ (normalizedIpmAlpha I) (ipmPsi I U) (ipmDetectThreshold I U κ))
    (hstored : ∀ j ≤ t, StrictlyInside I (epochState I U κ r A base j).stored)
    (hf : StrictlyInside I (epochFlow I U κ r A base t))
    (hroute : I.Routes (epochFlow I U κ r A base t))
    (hr : ScalarApprox (1+8*ipmDetectThreshold I U κ) r (residual I F (epochFlow I U κ r A base t)))
    (hhidden : (epochInstance I U κ r A base).HiddenStable (2*t+1) (normalizedIpmAlpha I) (ipmPsi I U)) :
    I.Routes (epochFlow I U κ r A base (t+1)) ∧
      StrictlyInside I (epochFlow I U κ r A base (t+1)) ∧
      0 < residual I F (epochFlow I U κ r A base (t+1)) ∧
      StrictlyInside I (epochState I U κ r A base (t+1)).stored ∧
      potential I (alpha I U) F (epochFlow I U κ r A base (t+1)) ≤
        potential I (alpha I U) F (epochFlow I U κ r A base t)-(κ*alpha I U/64)^2/500 ∧
      |residual I F (epochFlow I U κ r A base (t+1))-residual I F (epochFlow I U κ r A base t)| /
        residual I F (epochFlow I U κ r A base t) ≤ κ*alpha I U/(800*I.m) ∧
      weightedLength (lengths I (alpha I U) (epochState I U κ r A base t).stored)
        (fun e => epochIncrement I U κ r A base t e) ≤ κ*alpha I U/6400 := by
  have hvalid := epoch_history_valid_prefix I U κ r A base (2*(t+1)) hI
    (by intro j hj; exact hstored j (by omega))
  have he := epoch_tolerance_bounds I U κ hsize hk hk'
  have herror := epoch_stored_error I U κ r (normalizedIpmAlpha I) (ipmPsi I U)
    (ipmDetectThreshold I U κ) A base (2*(t+1)) t hA hvalid (by omega) he.1.le
  obtain ⟨p, hp, hp', u, hnext, hmove⟩ := epoch_step_update I U F κ r A base (2*(t+1)) t
    hm hU hsize hnums hk hk' hA hvalid le_rfl hhidden (hstored t le_rfl)
    (by intro e; exact (herror e).trans (by linarith only [he.1])) hr
  have hamin := alpha_pos I U hsize
  have hq : 0 < κ*alpha I U/64 := div_pos (mul_pos hk hamin) (by norm_num)
  have hp0 : 0 < p := hq.trans_le hp
  have hkα := mul_le_mul_of_nonneg_right hk' hamin.le
  have hp1 : p < 1 := by linarith only [hp', hkα, alpha_le I U hsize]
  have hspec := u.spec hm hU hsize hnums hf hroute hr.2.1 hp0 hp1.le
  have hres := u.residual_change hm hsize hf hr.2.1 hp0 hp1
  have hsq : (κ*alpha I U/64)^2 ≤ p^2 := sq_le_sq' (by linarith only [hq, hp0]) hp
  have hmR : (0 : ℝ) < I.m := Nat.cast_pos.mpr hm
  have hresbound : p/(50*I.m) ≤ κ*alpha I U/(800*I.m) := by
    apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 800) hmR)).mpr
    have heq : p/(50*I.m)*(800*I.m) = 16*p := by field_simp; norm_num
    rw [heq]
    linarith only [hp']
  rw [hnext]
  refine ⟨hspec.1, hspec.2.1, hspec.2.2.1, ?_, ?_, ?_, hmove⟩
  · apply epoch_stored_inside_succ I U κ r A base t (hstored t le_rfl)
    rw [hnext]
    exact hspec.2.1
  · linarith only [hspec.2.2.2, hsq]
  · exact hres.trans hresbound

end MinCostFlow.IPM
