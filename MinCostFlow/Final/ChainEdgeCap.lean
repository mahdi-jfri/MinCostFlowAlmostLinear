module

public import MinCostFlow.Final.ChainToolBounds
public import MinCostFlow.Final.TimeFactorBounds
public import MinCostFlow.Chain.ConcreteDefs
public import MinCostFlow.IPM.Machine.ConnectedSolverInitialize
import Mathlib.Tactic

/-!
# The edge cap for Theorem 5.1

Theorem 5.1 (page 15) accepts an upper bound on the graph size.
A fixed threshold increases the initial allowance and the rate by
constant factors in the almost-linear bound. The precision still
uses the actual edge count and penalty for its arithmetic.
-/

public noncomputable section
namespace MinCostFlow.Final
open Chain IPM.Machine Scaling

/-- The cap is at least the actual count and the concrete threshold. -/
@[expose] def chainEdgeCap (threshold M : ℕ) : ℕ := max M threshold

/-- Raising the cap preserves the vertex comparison, the degree-cap
inequality, and the game weight bound on the actual numeric format. -/
theorem chainEdgeCap_conditions (threshold M N V A D : ℕ)
    (hm : 0<M) (hn : N≤2*M+2) (hs : 2≤M*V) (hp : V≤16*M^81)
    {C : ℝ} (hC : 0≤C) (hD : (D:ℝ)≤Real.exp (C*chainLogPower (23/24) M)) :
    let cap := chainEdgeCap threshold M
    let k := integerQualityExponent A cap
    let Ψ := ((ipmQualityRangeExponent M V k+slackRangeExponent M V+6 : ℕ):ℝ)
    M≤cap ∧ threshold≤cap ∧
      1+Real.log ((N:ℝ)+2)≤4*Real.log ((cap:ℝ)+2) ∧
      (D:ℝ)≤Real.exp (C*chainLogPower (23/24) cap) ∧
      alg2PsiGame Ψ cap≤Real.exp (chainPsiConstant A*chainLogPower (23/24) cap) := by
  intro cap k Ψ
  have hM : M≤cap := le_max_left _ _
  have hpos := hm.trans_le hM
  have hN : N≤2*cap+2 := by omega
  have hlog : chainLog M≤chainLog cap := by
    unfold chainLog
    exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hM 2)
  have hlog0 : 0≤chainLog M := by unfold chainLog; exact Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) M])
  have hlog1 : 0≤chainLog cap := hlog0.trans hlog
  have hshape : chainLogPower (23/24) M≤chainLogPower (23/24) cap := by
    unfold chainLogPower
    exact mul_le_mul (Real.rpow_le_rpow hlog0 hlog (by norm_num))
      (Real.log_le_log (by linarith) (by linarith))
      (Real.log_nonneg (by linarith)) (Real.rpow_nonneg hlog1 _)
  exact ⟨hM,le_max_right _ _,chain_logVertexComparison_add_two hN,
    hD.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hshape hC)),
    widened_chain_game_bound_at M V A cap cap hm hs hp hM hpos le_rfl⟩

/-- The fixed cap multiplier bounds the shifted edge count. -/
theorem chainEdgeCap_add_two_le (threshold M : ℕ) :
    (chainEdgeCap threshold M:ℝ)+2 ≤ ((threshold:ℝ)+1)*((M:ℝ)+2) := by
  have hcast : (chainEdgeCap threshold M:ℝ) ≤ (M:ℝ)+threshold := by
    exact_mod_cast (max_le (Nat.le_add_right M threshold) (Nat.le_add_left threshold M))
  nlinarith only [hcast, Nat.cast_nonneg (α:=ℝ) threshold,
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) threshold) (Nat.cast_nonneg (α:=ℝ) M)]

/-- Both the initial allowance and the time factor retain their
dependence on the actual size, with explicit constants. -/
theorem chainEdgeCap_time (threshold M : ℕ) {C : ℝ} (hC : 0≤C) (Q : ℝ) (hQ : 0≤Q) :
    alg2TimeFactor C (47/48) (chainEdgeCap threshold M)*((chainEdgeCap threshold M:ℝ)+Q) ≤
      ((threshold:ℝ)+1)*(((M:ℝ)+2)+Q)*
        alg2TimeFactor (C*(logScale ((threshold:ℝ)+1))^(47/48:ℝ)*
          logScale (logScale ((threshold:ℝ)+1))) (47/48) M := by
  have hA : (1:ℝ)≤(threshold:ℝ)+1 := by linarith [Nat.cast_nonneg (α:=ℝ) threshold]
  have hRate := scalingTimeFactor_rescale hA hC M (chainEdgeCap threshold M)
    (chainEdgeCap_add_two_le threshold M)
  have hCharge : (chainEdgeCap threshold M:ℝ)+Q ≤ ((threshold:ℝ)+1)*((M:ℝ)+2+Q) := by
    have h := chainEdgeCap_add_two_le threshold M
    have hQ' := mul_le_mul_of_nonneg_right hA hQ
    nlinarith only [h,hQ']
  rw [mul_comm]
  exact mul_le_mul hCharge hRate (Real.exp_nonneg _)
    (by positivity)

/-- The concrete geometry uses the padded cap. The quality is computed
at that cap, while the IPM's precision and target stay at the actual
edge count. -/
@[expose] def cappedConcreteConfig
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (params : ℕ → DynSpanner.SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (threshold A D V : ℕ) (I : Instance) (hm : 0<I.m) : Alg2Config :=
  let cap := chainEdgeCap threshold I.m
  let hcap := hm.trans_le (le_max_left I.m threshold)
  let k := integerQualityExponent A cap
  let Ψ := ((ipmQualityRangeExponent I.m V k+slackRangeExponent I.m V+6 : ℕ):ℝ)
  let α := Num.IPM.alphaPrime I.m V
  concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t cap I.n
    (concreteBCap C_lsst Ψ cap I.n hcap) D hcap (α/8) Ψ ((1/(2:ℝ)^k)*α/1024)

end MinCostFlow.Final
