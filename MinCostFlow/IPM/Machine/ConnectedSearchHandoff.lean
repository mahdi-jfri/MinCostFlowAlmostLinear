module

public import MinCostFlow.IPM.Machine.SolverSearchInputs
public import MinCostFlow.IPM.Machine.ConnectedPairOrder
import MinCostFlow.IPM.Machine.PrecisionResidual
import Mathlib.Tactic

/-!
# Starting target search from the connected midpoint

The connected version of Lemma 4.12 supplies half-unit initial slacks.
These fit strictly inside the fixed-point guards of the target search.
-/

public section
namespace MinCostFlow.IPM.Machine
open WordRAM Scaling

/-- At the initial midpoint the guarded slack ranges are strict and the
decoded starting flow is the connected midpoint flow. -/
theorem connectedInitialFlow_stage {w : ℕ} (J : Circulation) (V k : ℕ) (source heap : ℕ)
    (mem : ℕ → ℕ) (hm : 0 < J.m) (hV : 0 < V) (hp : ∀ e,1≤J.capacity e)
    (hw : ipmQualityParameterWordBits (connectedInitialInstance J.toInstance (V:ℤ)).m V k≤w)
    (hEnd : source+(connectedInitialInstance J.toInstance (V:ℤ)).m*ipmQualityLimbs (connectedInitialInstance J.toInstance (V:ℤ)).m V k≤heap)
    (hNums : NumbersBounded (connectedInitialInstance J.toInstance (V:ℤ)) (V:ℝ))
    (hAt : ∀ e : Fin (connectedInitialInstance J.toInstance (V:ℤ)).m,
      ScalarAt mem (source+e.val*ipmQualityLimbs (connectedInitialInstance J.toInstance (V:ℤ)).m V k)
        4 (ipmQualityLimbs (connectedInitialInstance J.toInstance (V:ℤ)).m V k)
        (ipmQualityPrecision (connectedInitialInstance J.toInstance (V:ℤ)).m V k) (connectedInitialFlow J.toInstance (V:ℤ) e)) :
    let I := connectedInitialInstance J.toInstance (V:ℤ)
    let F := ipmQualityMinRatioFormat I.m V k hw
    TargetStageFlow F I F.rangeExponent source heap mem ∧
      ∀ e, (1/2:ℝ)≤epochVector F I mem source e-(I.edge e).lower ∧
        (1/2:ℝ)≤(I.edge e).upper-epochVector F I mem source e := by
  dsimp only
  let I := connectedInitialInstance J.toInstance (V:ℤ)
  let F := ipmQualityMinRatioFormat I.m V k hw
  let E := ipmQualityRangeExponent I.m V k
  let f := connectedInitialFlow J.toInstance (V:ℤ)
  have hM : 0 < I.m := hm.trans_le (connectedInitial_circulation_m_ge J hp _)
  have hEq : epochVector F I mem source=f := funext fun e => (hAt e).2
  have hFeas : I.IsFeasible f := by
    apply connectedInitialFlow_feasible J.toInstance (V:ℤ) J.toInstance_valid
    · intro e
      rw [Circulation.toInstance_edge]
      simp [Circulation.inputEdge]
    · simp [Instance.d]
  have hVE : slackRangeExponent I.m V≤E := by
    have hs := slackRangeExponent_le_qualitySlackExponent I.m V k
    unfold E ipmQualityRangeExponent
    omega
  have hMon := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hVE
  have hlo : 1/(2:ℝ)^E < 1/2 :=
    ((one_div_le_one_div_of_le (by positivity) hMon).trans (dyadic_le_quarter I.m V hM hV)).trans_lt (by norm_num)
  have hv : (0:ℝ)<V := Nat.cast_pos.mpr hV
  have hhi : (V:ℝ)<(2:ℝ)^E := by
    have hb := (twice_capacity_le_dyadic I.m V hM hV).trans hMon
    linarith only [hb,hv]
  change TargetStageFlow F I E source heap mem ∧ _
  have hHalf := connectedInitialFlow_slacks J.toInstance (V:ℤ)
  refine ⟨⟨hEnd,hEq.symm ▸ hFeas,?_⟩,?_⟩
  · intro e
    rw [hEq]
    have hs := hHalf e
    have hU := (le_abs_self ((I.edge e).upper:ℝ)).trans (hNums.2 e).2.1
    have hL : (I.edge e).lower=0 := ((connectedInitialInstance_zeroLower J hp V).1 e).1
    have hf₀ : (0:ℝ)≤f e := by rw [hL,Int.cast_zero] at hs; linarith only [hs.1]
    refine ⟨(hAt e).1,⟨hlo.trans_le hs.2,?_⟩,⟨hlo.trans_le hs.1,?_⟩⟩
    · linarith only [hU,hhi,hf₀]
    · rw [hL,Int.cast_zero,sub_zero]
      exact (hFeas.2 e).2.trans_lt (hU.trans_lt hhi)
  · intro e
    rw [hEq]
    exact hHalf e

end MinCostFlow.IPM.Machine
