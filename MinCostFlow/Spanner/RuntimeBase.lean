module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Spanner.ToolCosts
public import MinCostFlow.Spanner.Algorithm
public import MinCostFlow.Spanner.WitnessBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

public import MinCostFlow.Spanner.Task2Base
public import MinCostFlow.Spanner.Task3Base

import MinCostFlow.Spanner.Subgraph
import MinCostFlow.Spanner.WitnessProps
import MinCostFlow.Spanner.WitnessLift
import MinCostFlow.Spanner.Claim87
import MinCostFlow.Spanner.Analysis2
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Runtime Accounting for Algorithm 4: Counts and Helper Bounds

This file holds the first part of the material of `Runtime.lean`, split off to keep files
small. `Runtime.lean` gives the overview.
-/

@[expose] public section

namespace MinCostFlow.Spanner

open MinCostFlow.Cited

/-! ## Operation count of Algorithm 4 -/

/-- Total operation count of `sparsifyLocal tools H' J embJH`, summing the model's internal steps
(Task 1 setup, loop/congestion/update counters in Tasks 2 and 3, and walk assembly) and the
per-call tool charges from `costs : SpannerToolCosts`. -/
noncomputable def sparsifyLocalCost {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk) : ℕ :=
  let out := sparsifyLocal tools H' J embJH
  let wd := out.wd
  let st := out.stats
  let setupSteps : ℕ := J.n + J.m + wd.W.m
  let decCharge : ℕ := costs.decompose.callCost wd.J0_strip.m
  let ceCharge : ℕ :=
    (wd.comps.map fun c =>
      let wSum := ∑ k ∈ Finset.range c.X.card,
        ((wd.decomp.graphAt wd.J0_strip c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (wd.φ_dec * (2 ^ c.level : ℝ))
      costs.constructExpander.callCost c.X.card wSum).sum
  let γJ := tools.pathDS.γ_query wd.φ_dec wd.J0_strip.m
  let γW := tools.pathDS.γ_query wd.φ_Const wd.M_W
  let dsJCharge : ℕ :=
    st.η₁ * (wd.comps.map fun c => costs.pathDS.updateCost c.J_sub.m γJ).sum +
    st.dsGetPathCountJ * costs.pathDS.queryCost γJ
  let task2Steps : ℕ :=
    st.dsInitCountJ + st.middleIters1 + st.innerIters1 + st.vcongUpdates
  let dsWCharge : ℕ :=
    st.η₂ * (wd.comps.map fun c => costs.pathDS.updateCost c.W_sub.m γW).sum +
    st.dsGetPathCountW * costs.pathDS.queryCost γW
  let task3Steps : ℕ :=
    st.dsInitCountW + st.middleIters2 + st.innerIters2 + st.econgUpdates
  let returnSteps : ℕ :=
    (∑ eW ∈ Finset.range wd.W.m, ((out.embWJ eW).edges.length + 1)) +
    (∑ eJ ∈ Finset.range J.m, ((out.embJJtilde eJ).edges.length + 1))
  setupSteps + decCharge + ceCharge + dsJCharge + task2Steps + dsWCharge + task3Steps + returnSteps

/-- Total operation count of `sparsify tools H' J embJH` with `SpannerToolCosts`. -/
noncomputable def sparsifyCost (tools : SpannerTools) (costs : SpannerToolCosts)
    (H' J : Graph) (embJH : ℕ → Walk) : ℕ :=
  let J0_strip := stripLoops J
  let φ_dec := tools.decompose.φ_dec J0_strip
  sparsifyLocalCost (tools.toLocal J.n (2 * (J.m : ℝ) / φ_dec)) costs H' J embJH

/-- Explicit leading constant (excluding `Decompose`) in the runtime bound of Theorem 8.1. -/
noncomputable def sparsifyBaseConst (c_deg : ℝ) (costs : SpannerToolCosts) : ℝ :=
  let C_eta1 := 1 + (2 * c_deg + 1) * ((c_deg + 2) / Real.log 2 + 1)
  let C_eta2 := 1 + 2 / Real.log 2
  let K_ce := costs.constructExpander.K_ce
  let K_u := costs.pathDS.K_dsUpdate
  let K_q := costs.pathDS.K_dsQuery
  (2 + c_deg / 2) + 2 * (K_ce + 1) +
    C_eta1 * (K_u + 1) + (1 + c_deg / 2) * (K_q + 1) +
    C_eta1 + (1 + c_deg / 2) + 4 * (1 + c_deg / 2) +
    C_eta2 * (K_u + 1) * (1 + c_deg / 2) + (K_q + 1) +
    C_eta2 + 1 + 2 + (4 + c_deg)

theorem sparsifyBaseConst_nonneg {c_deg : ℝ} (hc : 1 ≤ c_deg) (costs : SpannerToolCosts) :
    0 ≤ sparsifyBaseConst c_deg costs := by
  unfold sparsifyBaseConst
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKce : 0 ≤ costs.constructExpander.K_ce := costs.constructExpander.hK_ce
  have hKu : 0 ≤ costs.pathDS.K_dsUpdate := costs.pathDS.hK_dsUpdate
  have hKq : 0 ≤ costs.pathDS.K_dsQuery := costs.pathDS.hK_dsQuery
  positivity

theorem sparsifyBaseConst_ge_one {c_deg : ℝ} (hc : 1 ≤ c_deg) (costs : SpannerToolCosts) :
    1 ≤ sparsifyBaseConst c_deg costs := by
  unfold sparsifyBaseConst
  dsimp only
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKce : 0 ≤ costs.constructExpander.K_ce := costs.constructExpander.hK_ce
  have hKu : 0 ≤ costs.pathDS.K_dsUpdate := costs.pathDS.hK_dsUpdate
  have hKq : 0 ≤ costs.pathDS.K_dsQuery := costs.pathDS.hK_dsQuery
  have hC1 : 0 ≤ 1 + (2 * c_deg + 1) * ((c_deg + 2) / Real.log 2 + 1) := by positivity
  have hC2 : 0 ≤ 1 + 2 / Real.log 2 := by positivity
  have h1 : 0 ≤ 2 * (costs.constructExpander.K_ce + 1) := by linarith only [hKce]
  have h2 : 0 ≤ (1 + (2 * c_deg + 1) * ((c_deg + 2) / Real.log 2 + 1)) *
      (costs.pathDS.K_dsUpdate + 1) :=
    mul_nonneg hC1 (by linarith only [hKu])
  have h3 : 0 ≤ (1 + c_deg / 2) * (costs.pathDS.K_dsQuery + 1) :=
    mul_nonneg (by linarith only [hc]) (by linarith only [hKq])
  have h4 : 0 ≤ (1 + 2 / Real.log 2) * (costs.pathDS.K_dsUpdate + 1) * (1 + c_deg / 2) :=
    mul_nonneg (mul_nonneg hC2 (by linarith only [hKu])) (by linarith only [hc])
  linarith only [hc, hC1, hC2, h1, h2, h3, h4, hKq]

/-! ## Logarithmic, sparsity, and runtime helper bounds -/

lemma log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_two_le_one' : Real.log 2 ≤ 1 := by
  have h : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr h

lemma one_le_one_add_log (n m : ℕ) : 1 ≤ 1 + Real.log ((n : ℝ) + (m : ℝ) + 2) := by
  have h : 0 ≤ Real.log ((n : ℝ) + (m : ℝ) + 2) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  linarith

private lemma natLog2_add_one_le_log_div (a : ℕ) {x : ℝ} (hx : (a : ℝ) ≤ x) (ha : 1 ≤ a) :
    (Nat.log 2 a : ℝ) + 1 ≤ (1 / Real.log 2) * (1 + Real.log x) := by
  have hpow : (2 : ℝ) ^ (Nat.log 2 a) ≤ (a : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast ha
  have hlog : (Nat.log 2 a : ℝ) * Real.log 2 ≤ Real.log x := by
    calc (Nat.log 2 a : ℝ) * Real.log 2
        = Real.log ((2 : ℝ) ^ (Nat.log 2 a)) := (Real.log_pow 2 (Nat.log 2 a)).symm
      _ ≤ Real.log (a : ℝ) := Real.log_le_log (by positivity) hpow
      _ ≤ Real.log x := Real.log_le_log ha_pos hx
  have hl2 := log_two_pos'
  have hl2_le := log_two_le_one'
  have h1 : (Nat.log 2 a : ℝ) ≤ Real.log x / Real.log 2 := (le_div_iff₀ hl2).mpr hlog
  have h2 : (1 : ℝ) ≤ 1 / Real.log 2 := (one_le_div hl2).mpr hl2_le
  calc (Nat.log 2 a : ℝ) + 1
      ≤ Real.log x / Real.log 2 + 1 / Real.log 2 := by linarith
    _ = (1 / Real.log 2) * (1 + Real.log x) := by ring

private lemma real_log_le_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x :=
  le_trans (Real.log_le_sub_one_of_pos hx) (by linarith)

private lemma natLog2_ceil_le_eta1_factor {c_deg φ_dec γ_E : ℝ} {n m : ℕ}
    (hc : 1 ≤ c_deg) (hφ_pos : 0 < φ_dec) (hφ_le : φ_dec ≤ 1)
    (hγ_inv : 1 / φ_dec ≤ γ_E) (hγ_ge2 : 2 ≤ γ_E) (hm : 1 ≤ m) :
    (Nat.log 2 (Nat.ceil (c_deg * (m : ℝ) / (2 * φ_dec)) + 1) : ℝ) + 1 ≤
      ((c_deg + 2) / Real.log 2 + 1) * γ_E * (1 + Real.log ((n : ℝ) + (m : ℝ) + 2)) := by
  set a := Nat.ceil (c_deg * (m : ℝ) / (2 * φ_dec)) + 1
  have ha1 : 1 ≤ a := by omega
  have harg_nn : 0 ≤ c_deg * (m : ℝ) / (2 * φ_dec) := by positivity
  have hceil_lt : (Nat.ceil (c_deg * (m : ℝ) / (2 * φ_dec)) : ℝ) <
      c_deg * (m : ℝ) / (2 * φ_dec) + 1 := Nat.ceil_lt_add_one harg_nn
  have ha_le : (a : ℝ) ≤ c_deg * ((m : ℝ) + 2) / φ_dec := by
    have h1 : (a : ℝ) ≤ c_deg * (m : ℝ) / (2 * φ_dec) + 2 := by
      change ((Nat.ceil (c_deg * (m : ℝ) / (2 * φ_dec)) + 1 : ℕ) : ℝ) ≤ _
      push_cast; linarith
    have h2 : c_deg * (m : ℝ) / (2 * φ_dec) + 2 ≤ (c_deg * (m : ℝ) + 2 * c_deg) / φ_dec := by
      have hdiv : c_deg * (m : ℝ) / (2 * φ_dec) ≤ c_deg * (m : ℝ) / φ_dec :=
        div_le_div_of_nonneg_left (by positivity) hφ_pos (by linarith)
      have h2φ : 2 ≤ (2 * c_deg) / φ_dec := by
        rw [le_div_iff₀ hφ_pos]
        nlinarith
      linarith [show (c_deg * (m : ℝ) + 2 * c_deg) / φ_dec =
        c_deg * (m : ℝ) / φ_dec + (2 * c_deg) / φ_dec from by ring]
    have h3 : (c_deg * (m : ℝ) + 2 * c_deg) / φ_dec = c_deg * ((m : ℝ) + 2) / φ_dec := by ring
    linarith
  have hpow : (2 : ℝ) ^ (Nat.log 2 a) ≤ (a : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have hlog_a : Real.log (a : ℝ) ≤ Real.log (c_deg * ((m : ℝ) + 2) / φ_dec) :=
    Real.log_le_log (by exact_mod_cast ha1) ha_le
  have hm2_pos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hsplit : Real.log (c_deg * ((m : ℝ) + 2) / φ_dec) =
      Real.log c_deg + Real.log ((m : ℝ) + 2) + Real.log (1 / φ_dec) := by
    rw [div_eq_mul_inv, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by linarith) hm2_pos.ne', one_div]
  have hc_log : Real.log c_deg ≤ c_deg := real_log_le_self (by linarith)
  have hφ_log : Real.log (1 / φ_dec) ≤ γ_E :=
    le_trans (real_log_le_self (by positivity)) hγ_inv
  have hm_log : Real.log ((m : ℝ) + 2) ≤ Real.log ((n : ℝ) + (m : ℝ) + 2) :=
    Real.log_le_log hm2_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  set L := 1 + Real.log ((n : ℝ) + (m : ℝ) + 2)
  have hL1 : 1 ≤ L := one_le_one_add_log n m
  have hlog_tot : Real.log (a : ℝ) ≤ (c_deg + 2) * γ_E * L := by
    have h1 : c_deg ≤ c_deg * γ_E * L := by
      have : 1 ≤ γ_E * L := by nlinarith
      nlinarith
    have h2 : Real.log ((m : ℝ) + 2) ≤ 1 * γ_E * L := by
      have : Real.log ((m : ℝ) + 2) ≤ L := by linarith
      nlinarith
    have h3 : γ_E ≤ 1 * γ_E * L := by nlinarith
    linarith
  have hl2 := log_two_pos'
  have hnatlog : (Nat.log 2 a : ℝ) ≤ (c_deg + 2) / Real.log 2 * γ_E * L := by
    have h1 : (Nat.log 2 a : ℝ) * Real.log 2 ≤ Real.log (a : ℝ) := by
      calc (Nat.log 2 a : ℝ) * Real.log 2
          = Real.log ((2 : ℝ) ^ (Nat.log 2 a)) := (Real.log_pow 2 (Nat.log 2 a)).symm
        _ ≤ Real.log (a : ℝ) := Real.log_le_log (by positivity) hpow
    calc (Nat.log 2 a : ℝ) ≤ Real.log (a : ℝ) / Real.log 2 := (le_div_iff₀ hl2).mpr h1
      _ ≤ ((c_deg + 2) * γ_E * L) / Real.log 2 := div_le_div_of_nonneg_right hlog_tot hl2.le
      _ = (c_deg + 2) / Real.log 2 * γ_E * L := by ring
  have h1_le : (1 : ℝ) ≤ 1 * γ_E * L := by nlinarith
  linarith

lemma eta1Bound_le_explicit {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    (hm : 1 ≤ J.m) :
    let wd := buildWitness tools H' J embJH
    (eta1Bound wd J : ℝ) ≤
      (1 + (2 * wd.c_deg + 1) * ((wd.c_deg + 2) / Real.log 2 + 1)) *
        wd.γ_ExpPath * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro wd
  have hc : 1 ≤ wd.c_deg := hw.c_deg_ge
  have hφ_pos : 0 < wd.φ_dec := hw.φ_dec_pos
  have hφ_le : wd.φ_dec ≤ 1 := hw.φ_dec_le
  have hγ_inv : 1 / wd.φ_dec ≤ wd.γ_ExpPath := by
    have h1 : 1 / wd.φ_dec ≤ 1 / wd.φ_ds :=
      one_div_le_one_div_of_le hw.φ_ds_pos hw.φ_ds_le_dec
    exact le_trans h1 hw.γ_ExpPath_ge
  have hγ_ge2 : 2 ≤ wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
    exact le_trans h1 hw.γ_ExpPath_ge
  have hlog := natLog2_ceil_le_eta1_factor (n := J.n) hc hφ_pos hφ_le hγ_inv hγ_ge2 hm
  have hceil : (Nat.ceil (2 * wd.c_deg) : ℝ) ≤ 2 * wd.c_deg + 1 :=
    (Nat.ceil_lt_add_one (by positivity)).le
  set L := 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)
  have hL1 : 1 ≤ L := one_le_one_add_log J.n J.m
  have h1 : (1 : ℝ) ≤ wd.γ_ExpPath * L := by nlinarith
  have hprod : (Nat.ceil (2 * wd.c_deg) : ℝ) *
      ((Nat.log 2 (Nat.ceil (wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) + 1) : ℝ) + 1) ≤
      (2 * wd.c_deg + 1) * (((wd.c_deg + 2) / Real.log 2 + 1) * wd.γ_ExpPath * L) :=
    mul_le_mul hceil hlog (by positivity) (by positivity)
  have heta : (eta1Bound wd J : ℝ) = 1 + (Nat.ceil (2 * wd.c_deg) : ℝ) *
      ((Nat.log 2 (Nat.ceil (wd.c_deg * (J.m : ℝ) / (2 * wd.φ_dec)) + 1) : ℝ) + 1) := by
    unfold eta1Bound
    push_cast
    ring
  rw [heta]
  linarith

lemma eta2Bound_le_explicit (J : Graph) :
    (eta2Bound J : ℝ) ≤ (1 + 2 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  unfold eta2Bound
  have h1 : (Nat.log 2 (J.m + 1) : ℝ) + 1 ≤
      (1 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
    natLog2_add_one_le_log_div (J.m + 1)
      (by have : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n; push_cast; linarith) (by omega)
  have hL1 : 1 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := one_le_one_add_log J.n J.m
  have h2 : (1 + 2 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) =
      (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) +
        2 * ((1 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) := by ring
  push_cast
  linarith only [h1, hL1, h2]

/-- Explicit **Theorem 8.1 item 3** (`|E(J̃)| = Õ(|V(J)| γ_ℓ)`):
`(Jtilde.m : ℝ) ≤ (1 + c_ℓ * c_deg / Real.log 2) * (J.n : ℝ) * wd.γ_ExpPath ^ 2 * (1 + Real.log (J.n + J.m + 2))`. -/
theorem sparsifySparsity_le {N_max : ℕ} {W_max : ℝ}
    (tools : LocalSpannerTools N_max W_max) (H' J : Graph) (embJH : ℕ → Walk)
    (hJ : J.IsValid)
    (hw : WitnessOK tools H' J embJH (buildWitness tools H' J embJH))
    {Jtilde_m : ℝ}
    (hm_le : Jtilde_m ≤
      ((J.n : ℝ) + (buildWitness tools H' J embJH).decomp.ℓ *
        (buildWitness tools H' J embJH).c_deg * (J.n : ℝ) /
        (buildWitness tools H' J embJH).φ_dec) *
      (buildWitness tools H' J embJH).γ_ExpPath) :
    let wd := buildWitness tools H' J embJH
    Jtilde_m ≤ (1 + tools.decompose.c_ℓ * wd.c_deg / Real.log 2) *
      (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
  intro wd
  have hdec := tools.decompose.decompose_spec wd.J0_strip (stripLoops_isValid hJ) (stripLoops_isLoopless J)
  have hℓ_spec : (wd.decomp.ℓ : ℝ) ≤ tools.decompose.c_ℓ * ((Nat.log 2 (wd.J0_strip.m + 2) : ℝ) + 1) :=
    hdec.1
  have hm_strip : wd.J0_strip.m ≤ J.m := stripLoops_m_le J
  have hlog_mono : Nat.log 2 (wd.J0_strip.m + 2) ≤ Nat.log 2 (J.m + 2) :=
    Nat.log_mono_right (by omega)
  have hlog_le : (Nat.log 2 (J.m + 2) : ℝ) + 1 ≤
      (1 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
    natLog2_add_one_le_log_div (J.m + 2)
      (by have : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n; push_cast; linarith) (by omega)
  have hℓ_le : (wd.decomp.ℓ : ℝ) ≤
      (tools.decompose.c_ℓ / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have hcℓ : 0 ≤ tools.decompose.c_ℓ := le_trans (by norm_num) tools.decompose.hc_ℓ
    have hnat : (Nat.log 2 (wd.J0_strip.m + 2) : ℝ) + 1 ≤ (Nat.log 2 (J.m + 2) : ℝ) + 1 := by
      have : (Nat.log 2 (wd.J0_strip.m + 2) : ℝ) ≤ (Nat.log 2 (J.m + 2) : ℝ) := by
        exact_mod_cast hlog_mono
      linarith
    calc (wd.decomp.ℓ : ℝ)
        ≤ tools.decompose.c_ℓ * ((Nat.log 2 (J.m + 2) : ℝ) + 1) :=
          le_trans hℓ_spec (mul_le_mul_of_nonneg_left hnat hcℓ)
      _ ≤ tools.decompose.c_ℓ * ((1 / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) :=
          mul_le_mul_of_nonneg_left hlog_le hcℓ
      _ = (tools.decompose.c_ℓ / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by ring
  have hφ_inv : 1 / wd.φ_dec ≤ wd.γ_ExpPath := by
    exact le_trans (one_div_le_one_div_of_le hw.φ_ds_pos hw.φ_ds_le_dec) hw.γ_ExpPath_ge
  have hγ_ge2 : 2 ≤ wd.γ_ExpPath := by
    have h1 : (2 : ℝ) ≤ 1 / wd.φ_ds := by rw [le_div_iff₀ hw.φ_ds_pos]; nlinarith [hw.φ_ds_half]
    exact le_trans h1 hw.γ_ExpPath_ge
  have hL1 : 1 ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) := one_le_one_add_log J.n J.m
  have hn_nn : (0 : ℝ) ≤ J.n := Nat.cast_nonneg J.n
  have hcdeg_nn : 0 ≤ wd.c_deg := le_trans (by norm_num) hw.c_deg_ge
  have hterm1 : (J.n : ℝ) * wd.γ_ExpPath ≤
      1 * (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have h1 : wd.γ_ExpPath ≤ wd.γ_ExpPath ^ 2 := by nlinarith
    have h2 : (J.n : ℝ) * wd.γ_ExpPath ≤ (J.n : ℝ) * wd.γ_ExpPath ^ 2 :=
      mul_le_mul_of_nonneg_left h1 hn_nn
    nlinarith [mul_nonneg hn_nn (sq_nonneg wd.γ_ExpPath)]
  have hterm2 : (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec * wd.γ_ExpPath ≤
      (tools.decompose.c_ℓ * wd.c_deg / Real.log 2) *
        (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by
    have h1 : (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec * wd.γ_ExpPath =
        (wd.decomp.ℓ : ℝ) * (wd.c_deg * (J.n : ℝ)) * (1 / wd.φ_dec) * wd.γ_ExpPath := by ring
    rw [h1]
    have h_ell_inv : (wd.decomp.ℓ : ℝ) * (wd.c_deg * (J.n : ℝ)) * (1 / wd.φ_dec) ≤
        ((tools.decompose.c_ℓ / Real.log 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2))) *
          (wd.c_deg * (J.n : ℝ)) * wd.γ_ExpPath := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hℓ_le (mul_nonneg hcdeg_nn hn_nn)) hφ_inv
        (div_nonneg zero_le_one hw.φ_dec_pos.le)
        (by have := log_two_pos'; have := tools.decompose.hc_ℓ; positivity)
    have hmul := mul_le_mul_of_nonneg_right h_ell_inv (by linarith : 0 ≤ wd.γ_ExpPath)
    exact le_trans hmul (le_of_eq (by ring))
  calc Jtilde_m
      ≤ (J.n : ℝ) * wd.γ_ExpPath +
          (wd.decomp.ℓ : ℝ) * wd.c_deg * (J.n : ℝ) / wd.φ_dec * wd.γ_ExpPath := by
        linarith [hm_le]
    _ ≤ 1 * (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) +
          (tools.decompose.c_ℓ * wd.c_deg / Real.log 2) *
            (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) :=
        add_le_add hterm1 hterm2
    _ = (1 + tools.decompose.c_ℓ * wd.c_deg / Real.log 2) *
          (J.n : ℝ) * (wd.γ_ExpPath ^ 2) * (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) := by ring

private lemma sum_map_le_of_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem a hx))

private lemma sum_map_nat_cast_eq {α : Type*} (l : List α) (f : α → ℕ) :
    ((l.map f).sum : ℝ) = (l.map fun x => (f x : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]

private lemma sum_map_mul_const {α : Type*} (l : List α) (f : α → ℝ) (c : ℝ) :
    (l.map fun x => c * f x).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih, mul_add]

private lemma sum_map_add {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih => simp [ih]; ring

lemma r_ceCharge_le (K_ce : ℝ) (callCost : ℕ → ℝ → ℕ)
    (hK_ce : 0 ≤ K_ce)
    (hcall : ∀ n w, 1 ≤ n → 0 ≤ w → (callCost n w : ℝ) ≤ (K_ce + 1) * ((n : ℝ) + w))
    (decomp : DecomposeOutput) (J0 : Graph) (φ_dec : ℝ) (comps : List CompInfo)
    (Jm : ℕ) (γ_E M_main : ℝ)
    (hX2 : ∀ c ∈ comps, 2 ≤ c.X.card)
    (hφ_pos : 0 < φ_dec) (hφ_inv : 1 / φ_dec ≤ γ_E) (hγ_ge2 : 2 ≤ γ_E)
    (hvert_m : (comps.map fun c => c.X.card).sum ≤ 2 * Jm)
    (hwsum : (comps.map fun c => ∑ k ∈ Finset.range c.X.card,
        ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (φ_dec * (2 ^ c.level : ℝ))).sum ≤ (Jm : ℝ) / φ_dec)
    (hM_le : (Jm : ℝ) * γ_E ≤ M_main) :
    ((comps.map fun c =>
      callCost c.X.card
        (∑ k ∈ Finset.range c.X.card,
          ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
            (φ_dec * (2 ^ c.level : ℝ)))).sum : ℝ) ≤
      2 * (K_ce + 1) * M_main := by
  rw [sum_map_nat_cast_eq]
  have hpt : ∀ c ∈ comps,
      (callCost c.X.card
        (∑ k ∈ Finset.range c.X.card,
          ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
            (φ_dec * (2 ^ c.level : ℝ))) : ℝ) ≤
      (K_ce + 1) * ((c.X.card : ℝ) +
        ∑ k ∈ Finset.range c.X.card,
          ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
            (φ_dec * (2 ^ c.level : ℝ))) := by
    intro c hc
    have hc2 := hX2 c hc
    have hw_nn : 0 ≤ ∑ k ∈ Finset.range c.X.card,
        ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
          (φ_dec * (2 ^ c.level : ℝ)) :=
      Finset.sum_nonneg fun k _ =>
        div_nonneg (Nat.cast_nonneg _) (mul_nonneg hφ_pos.le (pow_nonneg (by norm_num) _))
    exact hcall c.X.card _ (by omega) hw_nn
  have hsum1 := sum_map_le_of_le comps _ _ hpt
  rw [sum_map_mul_const, sum_map_add] at hsum1
  have hm_nn : (0 : ℝ) ≤ Jm := Nat.cast_nonneg Jm
  have hv_r : (comps.map fun c => (c.X.card : ℝ)).sum ≤ 2 * (Jm : ℝ) := by
    rw [← sum_map_nat_cast_eq]; exact_mod_cast hvert_m
  have hw_r : (comps.map fun c => ∑ k ∈ Finset.range c.X.card,
      ((decomp.graphAt J0 c.level).degIn c.X (c.verts.getD k 0) : ℝ) /
        (φ_dec * (2 ^ c.level : ℝ))).sum ≤ (Jm : ℝ) * γ_E := by
    calc _ ≤ (Jm : ℝ) / φ_dec := hwsum
      _ = (Jm : ℝ) * (1 / φ_dec) := by ring
      _ ≤ (Jm : ℝ) * γ_E := mul_le_mul_of_nonneg_left hφ_inv hm_nn
  have hKce_nn : 0 ≤ K_ce + 1 := by linarith only [hK_ce]
  have hJm_add : 2 * (Jm : ℝ) + (Jm : ℝ) * γ_E ≤ 2 * ((Jm : ℝ) * γ_E) := by
    have h1 : 2 * (Jm : ℝ) ≤ (Jm : ℝ) * γ_E := by
      calc 2 * (Jm : ℝ) = (Jm : ℝ) * 2 := by ring
        _ ≤ (Jm : ℝ) * γ_E := mul_le_mul_of_nonneg_left hγ_ge2 hm_nn
    linarith only [h1]
  have hsum2 : (K_ce + 1) * (2 * (Jm : ℝ) + (Jm : ℝ) * γ_E) ≤
      2 * (K_ce + 1) * ((Jm : ℝ) * γ_E) := by
    calc (K_ce + 1) * (2 * (Jm : ℝ) + (Jm : ℝ) * γ_E)
        ≤ (K_ce + 1) * (2 * ((Jm : ℝ) * γ_E)) := mul_le_mul_of_nonneg_left hJm_add hKce_nn
      _ = 2 * (K_ce + 1) * ((Jm : ℝ) * γ_E) := by ring
  calc _ ≤ (K_ce + 1) * (2 * (Jm : ℝ) + (Jm : ℝ) * γ_E) :=
        le_trans hsum1 (mul_le_mul_of_nonneg_left (add_le_add hv_r hw_r) hKce_nn)
    _ ≤ 2 * (K_ce + 1) * ((Jm : ℝ) * γ_E) := hsum2
    _ ≤ 2 * (K_ce + 1) * M_main :=
        mul_le_mul_of_nonneg_left hM_le (mul_nonneg (by norm_num) hKce_nn)

private lemma r_dsJCharge_le (dsCost : PathDSCost)
    (comps : List CompInfo) (η₁ gpJ Jm : ℕ) (γJ γ_E c_deg C_eta1 L_log M_main : ℝ)
    (hγJ_ge1 : 1 ≤ γJ) (hγJ_le : γJ ≤ γ_E) (hγ_nn : 0 ≤ γ_E)
    (hsum_jm : (comps.map fun c => c.J_sub.m).sum ≤ Jm)
    (hη_le : (η₁ : ℝ) ≤ C_eta1 * γ_E * L_log) (hC_nn : 0 ≤ C_eta1)
    (hL_log : 0 ≤ L_log) (hcdeg_nn : 0 ≤ 1 + c_deg / 2)
    (hgp_le : (gpJ : ℝ) ≤ (1 + c_deg / 2) * γ_E * (Jm : ℝ))
    (hJLL : (Jm : ℝ) * γ_E ^ 2 * L_log ≤ M_main)
    (hJsq : (Jm : ℝ) * γ_E ^ 2 ≤ M_main) :
    ((η₁ * (comps.map fun c => dsCost.updateCost c.J_sub.m γJ).sum +
        gpJ * dsCost.queryCost γJ : ℕ) : ℝ) ≤
      (C_eta1 * (dsCost.K_dsUpdate + 1) + (1 + c_deg / 2) * (dsCost.K_dsQuery + 1)) * M_main := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hKu : 0 ≤ dsCost.K_dsUpdate + 1 := by linarith only [dsCost.hK_dsUpdate]
  have hKq : 0 ≤ dsCost.K_dsQuery + 1 := by linarith only [dsCost.hK_dsQuery]
  have hupd_sum : ((comps.map fun c => dsCost.updateCost c.J_sub.m γJ).sum : ℝ) ≤
      (dsCost.K_dsUpdate + 1) * (Jm : ℝ) * γ_E := by
    rw [sum_map_nat_cast_eq]
    have hpt : ∀ c ∈ comps, (dsCost.updateCost c.J_sub.m γJ : ℝ) ≤
        (dsCost.K_dsUpdate + 1) * (c.J_sub.m : ℝ) * γ_E := fun c _ =>
      le_trans (dsCost.updateCost_le c.J_sub.m hγJ_ge1)
        (mul_le_mul_of_nonneg_left hγJ_le (mul_nonneg hKu (Nat.cast_nonneg _)))
    have hsum := sum_map_le_of_le comps _ _ hpt
    have hfact : (comps.map fun c => (dsCost.K_dsUpdate + 1) * (c.J_sub.m : ℝ) * γ_E).sum =
        ((dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.J_sub.m : ℝ)).sum := by
      rw [← sum_map_mul_const]
      congr 1
      apply List.map_congr_left
      intro c _
      ring
    have hjm_r : (comps.map fun c => (c.J_sub.m : ℝ)).sum ≤ (Jm : ℝ) := by
      rw [← sum_map_nat_cast_eq]; exact_mod_cast hsum_jm
    calc _ ≤ ((dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.J_sub.m : ℝ)).sum :=
          le_trans hsum (le_of_eq hfact)
      _ ≤ ((dsCost.K_dsUpdate + 1) * γ_E) * (Jm : ℝ) :=
          mul_le_mul_of_nonneg_left hjm_r (mul_nonneg hKu hγ_nn)
      _ = (dsCost.K_dsUpdate + 1) * (Jm : ℝ) * γ_E := by ring
  have hterm1 : (η₁ : ℝ) * ((comps.map fun c => dsCost.updateCost c.J_sub.m γJ).sum : ℝ) ≤
      C_eta1 * (dsCost.K_dsUpdate + 1) * M_main := by
    have hmul := mul_le_mul hη_le hupd_sum (Nat.cast_nonneg _) (by positivity)
    have heq : (C_eta1 * γ_E * L_log) * ((dsCost.K_dsUpdate + 1) * (Jm : ℝ) * γ_E) =
        C_eta1 * (dsCost.K_dsUpdate + 1) * ((Jm : ℝ) * γ_E ^ 2 * L_log) := by ring
    rw [heq] at hmul
    exact le_trans hmul (mul_le_mul_of_nonneg_left hJLL (mul_nonneg hC_nn hKu))
  have hq_le : (dsCost.queryCost γJ : ℝ) ≤ (dsCost.K_dsQuery + 1) * γ_E :=
    le_trans (dsCost.queryCost_le hγJ_ge1) (mul_le_mul_of_nonneg_left hγJ_le hKq)
  have hterm2 : (gpJ : ℝ) * (dsCost.queryCost γJ : ℝ) ≤
      (1 + c_deg / 2) * (dsCost.K_dsQuery + 1) * M_main := by
    have hmul := mul_le_mul hgp_le hq_le (Nat.cast_nonneg _) (by positivity)
    have heq : ((1 + c_deg / 2) * γ_E * (Jm : ℝ)) * ((dsCost.K_dsQuery + 1) * γ_E) =
        (1 + c_deg / 2) * (dsCost.K_dsQuery + 1) * ((Jm : ℝ) * γ_E ^ 2) := by ring
    rw [heq] at hmul
    exact le_trans hmul (mul_le_mul_of_nonneg_left hJsq (mul_nonneg hcdeg_nn hKq))
  linarith only [hterm1, hterm2]

private lemma r_dsWCharge_le (dsCost : PathDSCost)
    (comps : List CompInfo) (η₂ gpW Wm Jm : ℕ) (γW γ_E c_deg C_eta2 L_log M_main : ℝ)
    (hγW_ge1 : 1 ≤ γW) (hγW_le : γW ≤ γ_E) (hγ_nn : 0 ≤ γ_E)
    (hsum_Wm : (comps.map fun c => c.W_sub.m).sum ≤ Wm)
    (hWm_gamma : (Wm : ℝ) ≤ (1 + c_deg / 2) * γ_E * (Jm : ℝ))
    (hη_le : (η₂ : ℝ) ≤ C_eta2 * L_log) (hC_nn : 0 ≤ C_eta2) (hL_log : 0 ≤ L_log)
    (hcdeg_nn : 0 ≤ 1 + c_deg / 2) (hgp_le : (gpW : ℝ) ≤ (Jm : ℝ))
    (hJLL : (Jm : ℝ) * γ_E ^ 2 * L_log ≤ M_main) (hJM : (Jm : ℝ) * γ_E ≤ M_main) :
    ((η₂ * (comps.map fun c => dsCost.updateCost c.W_sub.m γW).sum +
        gpW * dsCost.queryCost γW : ℕ) : ℝ) ≤
      (C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) + (dsCost.K_dsQuery + 1)) * M_main := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hKu : 0 ≤ dsCost.K_dsUpdate + 1 := by linarith only [dsCost.hK_dsUpdate]
  have hKq : 0 ≤ dsCost.K_dsQuery + 1 := by linarith only [dsCost.hK_dsQuery]
  have hupd_sum : ((comps.map fun c => dsCost.updateCost c.W_sub.m γW).sum : ℝ) ≤
      (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * γ_E ^ 2 * (Jm : ℝ) := by
    rw [sum_map_nat_cast_eq]
    have hpt : ∀ c ∈ comps, (dsCost.updateCost c.W_sub.m γW : ℝ) ≤
        (dsCost.K_dsUpdate + 1) * (c.W_sub.m : ℝ) * γ_E := fun c _ =>
      le_trans (dsCost.updateCost_le c.W_sub.m hγW_ge1)
        (mul_le_mul_of_nonneg_left hγW_le (mul_nonneg hKu (Nat.cast_nonneg _)))
    have hsum := sum_map_le_of_le comps _ _ hpt
    have hfact : (comps.map fun c => (dsCost.K_dsUpdate + 1) * (c.W_sub.m : ℝ) * γ_E).sum =
        ((dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.W_sub.m : ℝ)).sum := by
      rw [← sum_map_mul_const]
      congr 1
      apply List.map_congr_left
      intro c _
      ring
    have hWm_r : (comps.map fun c => (c.W_sub.m : ℝ)).sum ≤ (Wm : ℝ) := by
      rw [← sum_map_nat_cast_eq]; exact_mod_cast hsum_Wm
    have hKuE : 0 ≤ (dsCost.K_dsUpdate + 1) * γ_E := mul_nonneg hKu hγ_nn
    calc _ ≤ ((dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.W_sub.m : ℝ)).sum :=
          le_trans hsum (le_of_eq hfact)
      _ ≤ ((dsCost.K_dsUpdate + 1) * γ_E) * (Wm : ℝ) := mul_le_mul_of_nonneg_left hWm_r hKuE
      _ ≤ ((dsCost.K_dsUpdate + 1) * γ_E) * ((1 + c_deg / 2) * γ_E * (Jm : ℝ)) :=
          mul_le_mul_of_nonneg_left hWm_gamma hKuE
      _ = (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * γ_E ^ 2 * (Jm : ℝ) := by ring
  have hterm1 : (η₂ : ℝ) * ((comps.map fun c => dsCost.updateCost c.W_sub.m γW).sum : ℝ) ≤
      C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * M_main := by
    have hmul := mul_le_mul hη_le hupd_sum (Nat.cast_nonneg _) (by positivity)
    have heq : (C_eta2 * L_log) *
          ((dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * γ_E ^ 2 * (Jm : ℝ)) =
        C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * ((Jm : ℝ) * γ_E ^ 2 * L_log) := by ring
    rw [heq] at hmul
    exact le_trans hmul (mul_le_mul_of_nonneg_left hJLL (mul_nonneg (mul_nonneg hC_nn hKu) hcdeg_nn))
  have hq_le : (dsCost.queryCost γW : ℝ) ≤ (dsCost.K_dsQuery + 1) * γ_E :=
    le_trans (dsCost.queryCost_le hγW_ge1) (mul_le_mul_of_nonneg_left hγW_le hKq)
  have hterm2 : (gpW : ℝ) * (dsCost.queryCost γW : ℝ) ≤ (dsCost.K_dsQuery + 1) * M_main := by
    have hmul := mul_le_mul hgp_le hq_le (Nat.cast_nonneg _) (by positivity)
    have heq : (Jm : ℝ) * ((dsCost.K_dsQuery + 1) * γ_E) =
        (dsCost.K_dsQuery + 1) * ((Jm : ℝ) * γ_E) := by ring
    rw [heq] at hmul
    exact le_trans hmul (mul_le_mul_of_nonneg_left hJM hKq)
  linarith only [hterm1, hterm2]

lemma r_returnSteps_le (Wm Jm : ℕ) (embWJ embJJtilde : ℕ → Walk)
    (c_deg γ_E M_main : ℝ) (hγ_ge2 : 2 ≤ γ_E) (hc_nn : 0 ≤ 2 + c_deg)
    (hlen_WJ : ∀ eW < Wm, ((embWJ eW).edges.length : ℝ) ≤ γ_E)
    (hlen_JJtilde : ∀ eJ < Jm, ((embJJtilde eJ).edges.length : ℝ) ≤ γ_E ^ 2)
    (hWm_gamma : (Wm : ℝ) ≤ (1 + c_deg / 2) * γ_E * (Jm : ℝ))
    (hJsq : (Jm : ℝ) * γ_E ^ 2 ≤ M_main) :
    (((∑ eW ∈ Finset.range Wm, ((embWJ eW).edges.length + 1)) +
        (∑ eJ ∈ Finset.range Jm, ((embJJtilde eJ).edges.length + 1)) : ℕ) : ℝ) ≤
      (4 + c_deg) * M_main := by
  push_cast
  have hsum_W : (∑ eW ∈ Finset.range Wm, (((embWJ eW).edges.length : ℝ) + 1)) ≤
      (Wm : ℝ) * (γ_E + 1) := by
    calc ∑ eW ∈ Finset.range Wm, (((embWJ eW).edges.length : ℝ) + 1)
        ≤ ∑ _eW ∈ Finset.range Wm, (γ_E + 1) :=
          Finset.sum_le_sum fun eW heW =>
            add_le_add (hlen_WJ eW (Finset.mem_range.mp heW)) le_rfl
      _ = (Wm : ℝ) * (γ_E + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hsum_J : (∑ eJ ∈ Finset.range Jm, (((embJJtilde eJ).edges.length : ℝ) + 1)) ≤
      (Jm : ℝ) * (γ_E ^ 2 + 1) := by
    calc ∑ eJ ∈ Finset.range Jm, (((embJJtilde eJ).edges.length : ℝ) + 1)
        ≤ ∑ _eJ ∈ Finset.range Jm, (γ_E ^ 2 + 1) :=
          Finset.sum_le_sum fun eJ heJ =>
            add_le_add (hlen_JJtilde eJ (Finset.mem_range.mp heJ)) le_rfl
      _ = (Jm : ℝ) * (γ_E ^ 2 + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hW_bound : (Wm : ℝ) * (γ_E + 1) ≤ (2 + c_deg) * M_main := by
    have h1 : γ_E + 1 ≤ 2 * γ_E := by linarith only [hγ_ge2]
    have hc2_nn : 0 ≤ (1 + c_deg / 2) * γ_E * (Jm : ℝ) :=
      mul_nonneg (mul_nonneg (by linarith only [hc_nn]) (by linarith only [hγ_ge2])) (Nat.cast_nonneg _)
    have h2 : (Wm : ℝ) * (γ_E + 1) ≤ ((1 + c_deg / 2) * γ_E * (Jm : ℝ)) * (2 * γ_E) :=
      mul_le_mul hWm_gamma h1 (by linarith only [hγ_ge2]) hc2_nn
    have heq : ((1 + c_deg / 2) * γ_E * (Jm : ℝ)) * (2 * γ_E) =
        (2 + c_deg) * ((Jm : ℝ) * γ_E ^ 2) := by ring
    rw [heq] at h2
    exact le_trans h2 (mul_le_mul_of_nonneg_left hJsq hc_nn)
  have hJ_bound : (Jm : ℝ) * (γ_E ^ 2 + 1) ≤ 2 * M_main := by
    have h1 : γ_E ^ 2 + 1 ≤ 2 * γ_E ^ 2 := by
      have : (1 : ℝ) ≤ γ_E ^ 2 := by nlinarith only [hγ_ge2]
      linarith only [this]
    have h2 : (Jm : ℝ) * (γ_E ^ 2 + 1) ≤ 2 * ((Jm : ℝ) * γ_E ^ 2) := by
      calc (Jm : ℝ) * (γ_E ^ 2 + 1) ≤ (Jm : ℝ) * (2 * γ_E ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
        _ = 2 * ((Jm : ℝ) * γ_E ^ 2) := by ring
    exact le_trans h2 (mul_le_mul_of_nonneg_left hJsq (by norm_num))
  linarith only [hsum_W, hsum_J, hW_bound, hJ_bound]

private lemma r_list_map_sum_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))

private lemma r_list_sum_cast {α : Type*} (l : List α) (f : α → ℕ) :
    ((l.map f).sum : ℝ) = (l.map fun a => (f a : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih]

private lemma r_list_sum_mul {α : Type*} (l : List α) (K : ℝ) (f : α → ℝ) :
    (l.map fun a => K * f a).sum = K * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma r_dsJCharge_le_with_time (dsCost : PathDSCost) (comps : List CompInfo)
    (η₁ gpJ mJ : ℕ) (γJq γ_E c_deg C_eta1 L_log M_main γ_t : ℝ)
    (hγJq_ge1 : 1 ≤ γJq) (hγJq_le : γJq ≤ γ_t * γ_E) (hγt : 1 ≤ γ_t)
    (hγE_nn : 0 ≤ γ_E)
    (hsum_jm : (comps.map fun c => c.J_sub.m).sum ≤ mJ)
    (heta1 : (η₁ : ℝ) ≤ C_eta1 * γ_E * L_log) (hC : 0 ≤ C_eta1)
    (hL : 0 ≤ L_log) (hcdeg : 0 ≤ c_deg)
    (hgpJ : (gpJ : ℝ) ≤ (1 + c_deg / 2) * γ_E * (mJ : ℝ))
    (hJE2L : (mJ : ℝ) * γ_E ^ 2 * L_log ≤ M_main)
    (hJsq : (mJ : ℝ) * γ_E ^ 2 ≤ M_main) :
    ((η₁ * (comps.map fun c => dsCost.updateCost c.J_sub.m γJq).sum +
        gpJ * dsCost.queryCost γJq : ℕ) : ℝ) ≤
      γ_t * (C_eta1 * (dsCost.K_dsUpdate + 1) +
        (1 + c_deg / 2) * (dsCost.K_dsQuery + 1)) * M_main := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hKu : 0 ≤ dsCost.K_dsUpdate + 1 := by linarith [dsCost.hK_dsUpdate]
  have hKq : 0 ≤ dsCost.K_dsQuery + 1 := by linarith [dsCost.hK_dsQuery]
  have hupd_sum : ((comps.map fun c => dsCost.updateCost c.J_sub.m γJq).sum : ℝ) ≤
      γ_t * (dsCost.K_dsUpdate + 1) * (mJ : ℝ) * γ_E := by
    have hpt : ∀ c ∈ comps, (dsCost.updateCost c.J_sub.m γJq : ℝ) ≤
        γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.J_sub.m : ℝ) := by
      intro c _
      have h1 := dsCost.updateCost_le c.J_sub.m hγJq_ge1
      have h2 := mul_le_mul_of_nonneg_left hγJq_le
        (mul_nonneg hKu (Nat.cast_nonneg c.J_sub.m))
      linarith [le_trans h1 h2]
    have hs := r_list_map_sum_le comps
      (fun c => (dsCost.updateCost c.J_sub.m γJq : ℝ))
      (fun c => γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.J_sub.m : ℝ)) hpt
    have hcast : ((comps.map fun c => dsCost.updateCost c.J_sub.m γJq).sum : ℝ) =
        (comps.map fun c => (dsCost.updateCost c.J_sub.m γJq : ℝ)).sum :=
      r_list_sum_cast comps _
    have hpull : (comps.map fun c => γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.J_sub.m : ℝ)).sum =
        (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.J_sub.m : ℝ)).sum :=
      r_list_sum_mul comps _ _
    have hsumR : (comps.map fun c => (c.J_sub.m : ℝ)).sum ≤ (mJ : ℝ) := by
      rw [← r_list_sum_cast comps]
      exact_mod_cast hsum_jm
    rw [hcast]
    calc (comps.map fun c => (dsCost.updateCost c.J_sub.m γJq : ℝ)).sum
        ≤ (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) *
            (comps.map fun c => (c.J_sub.m : ℝ)).sum := by rw [← hpull]; exact hs
      _ ≤ (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) * (mJ : ℝ) :=
          mul_le_mul_of_nonneg_left hsumR (by positivity)
      _ = γ_t * (dsCost.K_dsUpdate + 1) * (mJ : ℝ) * γ_E := by ring
  have hterm1 : (η₁ : ℝ) * ((comps.map fun c => dsCost.updateCost c.J_sub.m γJq).sum : ℝ) ≤
      γ_t * (C_eta1 * (dsCost.K_dsUpdate + 1)) * M_main := by
    have hprod := mul_le_mul heta1 hupd_sum (Nat.cast_nonneg _) (by positivity)
    have heq : (C_eta1 * γ_E * L_log) * (γ_t * (dsCost.K_dsUpdate + 1) * (mJ : ℝ) * γ_E) =
        γ_t * (C_eta1 * (dsCost.K_dsUpdate + 1)) * ((mJ : ℝ) * γ_E ^ 2 * L_log) := by ring
    rw [heq] at hprod
    exact le_trans hprod (mul_le_mul_of_nonneg_left hJE2L (by positivity))
  have hq_le : (dsCost.queryCost γJq : ℝ) ≤ γ_t * (dsCost.K_dsQuery + 1) * γ_E := by
    have h1 := dsCost.queryCost_le hγJq_ge1
    have h2 := mul_le_mul_of_nonneg_left hγJq_le hKq
    linarith [le_trans h1 h2]
  have hterm2 : (gpJ : ℝ) * (dsCost.queryCost γJq : ℝ) ≤
      γ_t * ((1 + c_deg / 2) * (dsCost.K_dsQuery + 1)) * M_main := by
    have hprod := mul_le_mul hgpJ hq_le (Nat.cast_nonneg _) (by positivity)
    have heq : ((1 + c_deg / 2) * γ_E * (mJ : ℝ)) * (γ_t * (dsCost.K_dsQuery + 1) * γ_E) =
        γ_t * ((1 + c_deg / 2) * (dsCost.K_dsQuery + 1)) * ((mJ : ℝ) * γ_E ^ 2) := by ring
    rw [heq] at hprod
    exact le_trans hprod (mul_le_mul_of_nonneg_left hJsq (by positivity))
  have _ := hγt
  linarith

lemma r_dsWCharge_le_with_time (dsCost : PathDSCost) (comps : List CompInfo)
    (η₂ gpW Wm Jm : ℕ) (γWq γ_E c_deg C_eta2 L_log M_main γ_t : ℝ)
    (hγWq_ge1 : 1 ≤ γWq) (hγWq_le : γWq ≤ γ_t * γ_E) (hγt : 1 ≤ γ_t)
    (hγE_nn : 0 ≤ γ_E)
    (hsum_Wm : (comps.map fun c => c.W_sub.m).sum ≤ Wm)
    (hWm_le : (Wm : ℝ) ≤ (1 + c_deg / 2) * γ_E * (Jm : ℝ))
    (heta2 : (η₂ : ℝ) ≤ C_eta2 * L_log) (hC : 0 ≤ C_eta2)
    (hL : 0 ≤ L_log) (hcdeg : 0 ≤ c_deg)
    (hgpW : (gpW : ℝ) ≤ (Jm : ℝ))
    (hJE2L : (Jm : ℝ) * γ_E ^ 2 * L_log ≤ M_main)
    (hJE : (Jm : ℝ) * γ_E ≤ M_main) :
    ((η₂ * (comps.map fun c => dsCost.updateCost c.W_sub.m γWq).sum +
        gpW * dsCost.queryCost γWq : ℕ) : ℝ) ≤
      γ_t * (C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) +
        (dsCost.K_dsQuery + 1)) * M_main := by
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  have hKu : 0 ≤ dsCost.K_dsUpdate + 1 := by linarith [dsCost.hK_dsUpdate]
  have hKq : 0 ≤ dsCost.K_dsQuery + 1 := by linarith [dsCost.hK_dsQuery]
  have hupd_sum : ((comps.map fun c => dsCost.updateCost c.W_sub.m γWq).sum : ℝ) ≤
      γ_t * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * (Jm : ℝ) * γ_E ^ 2 := by
    have hpt : ∀ c ∈ comps, (dsCost.updateCost c.W_sub.m γWq : ℝ) ≤
        γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.W_sub.m : ℝ) := by
      intro c _
      have h1 := dsCost.updateCost_le c.W_sub.m hγWq_ge1
      have h2 := mul_le_mul_of_nonneg_left hγWq_le
        (mul_nonneg hKu (Nat.cast_nonneg c.W_sub.m))
      linarith [le_trans h1 h2]
    have hs := r_list_map_sum_le comps
      (fun c => (dsCost.updateCost c.W_sub.m γWq : ℝ))
      (fun c => γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.W_sub.m : ℝ)) hpt
    have hcast : ((comps.map fun c => dsCost.updateCost c.W_sub.m γWq).sum : ℝ) =
        (comps.map fun c => (dsCost.updateCost c.W_sub.m γWq : ℝ)).sum :=
      r_list_sum_cast comps _
    have hpull : (comps.map fun c => γ_t * (dsCost.K_dsUpdate + 1) * γ_E * (c.W_sub.m : ℝ)).sum =
        (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) * (comps.map fun c => (c.W_sub.m : ℝ)).sum :=
      r_list_sum_mul comps _ _
    have hsumR : (comps.map fun c => (c.W_sub.m : ℝ)).sum ≤ (Wm : ℝ) := by
      rw [← r_list_sum_cast comps]
      exact_mod_cast hsum_Wm
    rw [hcast]
    calc (comps.map fun c => (dsCost.updateCost c.W_sub.m γWq : ℝ)).sum
        ≤ (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) *
            (comps.map fun c => (c.W_sub.m : ℝ)).sum := by rw [← hpull]; exact hs
      _ ≤ (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) * (Wm : ℝ) :=
          mul_le_mul_of_nonneg_left hsumR (by positivity)
      _ ≤ (γ_t * (dsCost.K_dsUpdate + 1) * γ_E) * ((1 + c_deg / 2) * γ_E * (Jm : ℝ)) :=
          mul_le_mul_of_nonneg_left hWm_le (by positivity)
      _ = γ_t * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * (Jm : ℝ) * γ_E ^ 2 := by ring
  have hterm1 : (η₂ : ℝ) * ((comps.map fun c => dsCost.updateCost c.W_sub.m γWq).sum : ℝ) ≤
      γ_t * (C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2)) * M_main := by
    have hprod := mul_le_mul heta2 hupd_sum (Nat.cast_nonneg _) (by positivity)
    have heq : (C_eta2 * L_log) * (γ_t * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2) * (Jm : ℝ) * γ_E ^ 2) =
        γ_t * (C_eta2 * (dsCost.K_dsUpdate + 1) * (1 + c_deg / 2)) * ((Jm : ℝ) * γ_E ^ 2 * L_log) := by ring
    rw [heq] at hprod
    exact le_trans hprod (mul_le_mul_of_nonneg_left hJE2L (by positivity))
  have hq_le : (dsCost.queryCost γWq : ℝ) ≤ γ_t * (dsCost.K_dsQuery + 1) * γ_E := by
    have h1 := dsCost.queryCost_le hγWq_ge1
    have h2 := mul_le_mul_of_nonneg_left hγWq_le hKq
    linarith [le_trans h1 h2]
  have hterm2 : (gpW : ℝ) * (dsCost.queryCost γWq : ℝ) ≤
      γ_t * (dsCost.K_dsQuery + 1) * M_main := by
    have hprod := mul_le_mul hgpW hq_le (Nat.cast_nonneg _) (by positivity)
    have heq : (Jm : ℝ) * (γ_t * (dsCost.K_dsQuery + 1) * γ_E) =
        γ_t * (dsCost.K_dsQuery + 1) * ((Jm : ℝ) * γ_E) := by ring
    rw [heq] at hprod
    exact le_trans hprod (mul_le_mul_of_nonneg_left hJE (by positivity))
  have _ := hγt
  linarith

end MinCostFlow.Spanner
