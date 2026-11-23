module

public import MinCostFlow.Spanner.Tools
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Expander.ConstructExpander
public import MinCostFlow.Expander.Decompose
public import MinCostFlow.Expander.PathDS
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import MinCostFlow.Expander.DecrementalPaths
import MinCostFlow.Expander.PathDSBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spanner Tools from Cited Results

Assembles `MinCostFlow.Spanner.SpannerTools` (`ConstructExpanderTool`, `DecomposeTool`,
`PathDSTool`) from three expander algorithms. The first is proved in this project, and the other
two are cited:

* `ConstructExpanderTool` from `theorem_8_4` (`Cited.ExplicitExpander`, proved as
  `MinCostFlow.ExplicitExpander.explicitExpander`), rounding real vertex
  weights `w v ≥ 1` via `Nat.ceil (w v)` (`c_deg = 36`, `φ_Const = α₀ / 9`), together with
  size and `constructExpanderCost` operation-count bounds.
* `DecomposeTool` from `theorem_8_5` (`Cited.ExpanderDecomposition`), setting `c_ℓ = 1` and
  `φ_dec G = φ G.m` (`1 / φ m ≤ exp(O(log^{2/3} m · log log m))`), together with
  `decomposeModelCost` operation-count bounds.
* `PathDSTool` from `pathDSOfCS` (`PathDS.lean`, Theorem 8.6 from `Cited.DecrementalExpanderPaths`),
  choosing `c` so that `10 * csPhi Kγ c (3 * m) ≤ min φ_Const (φ m)` for every `m`, and proving
  monotonicity of `φ_out` / `γ_ExpPath` / `γ_del` in `(φ_in, M)` as well as
  `exp(O(log^{7/8} (M + 2)))` bounds for both Algorithm 4 parameter regimes.
-/

namespace MinCostFlow.Expander

open MinCostFlow.Cited MinCostFlow.Spanner WordRAM

@[expose] public section

/-- Convert a global `SpannerTools` bundle into a `LocalSpannerTools N_max W_max` bundle. -/
noncomputable def toLocalSpannerTools (tools : Spanner.SpannerTools)
    (N_max : ℕ) (W_max : ℝ) : Spanner.LocalSpannerTools N_max W_max where
  constructExpander := tools.constructExpander.toBounded N_max W_max
  decompose := tools.decompose
  pathDS := tools.pathDS

end

section

private lemma edges_eq_map_range (L : List (ℕ × ℕ)) :
    ((List.range L.length).map fun j => L.getD j (0, 0)) = L := by
  induction L with
  | nil => simp
  | cons a as ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [List.getD_cons_zero]
    congr 1

private lemma exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hsq : Real.exp (1 / 2 : ℝ) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hpow : Real.exp (1 / 2 : ℝ) ^ 2 < (2 : ℝ) ^ 2 := by
    rw [hsq]
    linarith
  nlinarith [Real.exp_pos (1 / 2 : ℝ)]

private lemma half_le_log_add_two (M : ℕ) : (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) := by
  have hM : (2 : ℝ) ≤ (M : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have h1 : Real.exp (1 / 2 : ℝ) ≤ (M : ℝ) + 2 := le_trans exp_half_le_two hM
  have h2 := Real.log_le_log (Real.exp_pos _) h1
  rwa [Real.log_exp] at h2

private lemma half_le_log_rpow_seven_eighths (M : ℕ) :
    (1 / 2 : ℝ) ≤ Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) := by
  have hL := half_le_log_add_two M
  by_cases h1 : 1 ≤ Real.log ((M : ℝ) + 2)
  · have := Real.one_le_rpow h1 (by norm_num : (0 : ℝ) ≤ 7 / 8)
    linarith
  · have hlt : Real.log ((M : ℝ) + 2) ≤ 1 := le_of_not_ge h1
    have hpow1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (7 / 8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have hpow2 : (1 / 2 : ℝ) ^ (7 / 8 : ℝ) ≤ Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) hL (by norm_num)
    simpa using le_trans hpow1 hpow2

private lemma ten_le_exp_four : (10 : ℝ) ≤ Real.exp 4 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := by
    gcongr
  have hexp4 : Real.exp 1 ^ 4 = Real.exp 4 := by
    rw [← Real.exp_nat_mul (1 : ℝ) 4]
    norm_num
  have h16 : (10 : ℝ) ≤ (2 : ℝ) ^ 4 := by norm_num
  linarith

private lemma ceil_real_bounds {x : ℝ} (hx : 1 ≤ x) :
    x ≤ (Nat.ceil x : ℝ) ∧ (Nat.ceil x : ℝ) ≤ 2 * x := by
  refine ⟨Nat.le_ceil x, ?_⟩
  have hlt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  linarith

private lemma csPhi_pos_of_pos_c {Kγ c : ℕ} (hc : 1 ≤ c) (m : ℕ) :
    0 < Cited.csPhi Kγ c m := by
  unfold Cited.csPhi Cited.csGamma
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  positivity

private lemma csPhiOut_mono_phi {Kγ c : ℕ} {φ₁ φ₂ : ℝ} (hφ : φ₁ ≤ φ₂) (M : ℕ) :
    csPhiOut Kγ c φ₁ M ≤ csPhiOut Kγ c φ₂ M :=
  min_le_min hφ le_rfl

private lemma csPhiOut_anti_m {Kγ c : ℕ} (hc : 1 ≤ c) (φ_in : ℝ) {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) :
    csPhiOut Kγ c φ_in M₂ ≤ csPhiOut Kγ c φ_in M₁ :=
  min_le_min le_rfl (min_le_min le_rfl (csPhi_anti_m hc (by omega : 3 * M₁ ≤ 3 * M₂)))

private lemma csGammaExpPath_anti_phi {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ)
    {φ₁ φ₂ : ℝ} (hφ₁ : 0 < φ₁) (hφ : φ₁ ≤ φ₂) (M : ℕ) :
    csGammaExpPath Kγ c K φ₂ M ≤ csGammaExpPath Kγ c K φ₁ M := by
  dsimp only [csGammaExpPath]
  refine max_le_max le_rfl ?_
  have hpos₁ : 0 < csPhiOut Kγ c φ₁ M := by
    dsimp only [csPhiOut]
    exact lt_min hφ₁ (lt_min (by norm_num) (csPhi_pos_of_pos_c hc _))
  have hnum : 0 ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) := by
    have : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
    linarith
  exact div_le_div_of_nonneg_left hnum hpos₁ (csPhiOut_mono_phi hφ M)

private lemma csGammaExpPath_mono_m {Kγ c : ℕ} (hc : 1 ≤ c) (K : ℝ)
    {φ_in : ℝ} (hφ : 0 < φ_in) {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) :
    csGammaExpPath Kγ c K φ_in M₁ ≤ csGammaExpPath Kγ c K φ_in M₂ := by
  dsimp only [csGammaExpPath]
  have hγ_ge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (3 * M₁) : ℝ) := by
    unfold Cited.csGamma
    exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
  have hγ_mono : (Cited.csGamma Kγ (3 * M₁) : ℝ) ≤ (Cited.csGamma Kγ (3 * M₂) : ℝ) := by
    exact_mod_cast csGamma_mono (by omega : 3 * M₁ ≤ 3 * M₂)
  have hq_mono : max K 1 * (qOf M₁ : ℝ) ≤ max K 1 * (qOf M₂ : ℝ) :=
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (qOf_mono hM)) (by positivity)
  have hpow1 : (Cited.csGamma Kγ (3 * M₁) : ℝ) ^ (max K 1 * (qOf M₁ : ℝ)) ≤
      (Cited.csGamma Kγ (3 * M₁) : ℝ) ^ (max K 1 * (qOf M₂ : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hγ_ge1 hq_mono
  have hpow2 : (Cited.csGamma Kγ (3 * M₁) : ℝ) ^ (max K 1 * (qOf M₂ : ℝ)) ≤
      (Cited.csGamma Kγ (3 * M₂) : ℝ) ^ (max K 1 * (qOf M₂ : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hγ_mono (by positivity)
  have hpos₂ : 0 < csPhiOut Kγ c φ_in M₂ := by
    dsimp only [csPhiOut]
    exact lt_min hφ (lt_min (by norm_num) (csPhi_pos_of_pos_c hc _))
  have hnum_le : 25 * (Real.log (2 * (M₁ : ℝ) + 2) + 1) ≤
      25 * (Real.log (2 * (M₂ : ℝ) + 2) + 1) := by
    have hlog : Real.log (2 * (M₁ : ℝ) + 2) ≤ Real.log (2 * (M₂ : ℝ) + 2) := by
      apply Real.log_le_log (by linarith [Nat.cast_nonneg (α := ℝ) M₁])
      have hle : (M₁ : ℝ) ≤ (M₂ : ℝ) := Nat.cast_le.mpr hM
      linarith
    linarith
  have hnum_nn : 0 ≤ 25 * (Real.log (2 * (M₁ : ℝ) + 2) + 1) := by
    have : 0 ≤ Real.log (2 * (M₁ : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M₁])
    linarith
  have hdiv1 : 25 * (Real.log (2 * (M₁ : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M₁ ≤
      25 * (Real.log (2 * (M₁ : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M₂ :=
    div_le_div_of_nonneg_left hnum_nn hpos₂ (csPhiOut_anti_m hc φ_in hM)
  have hdiv2 : 25 * (Real.log (2 * (M₁ : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M₂ ≤
      25 * (Real.log (2 * (M₂ : ℝ) + 2) + 1) / csPhiOut Kγ c φ_in M₂ :=
    div_le_div_of_nonneg_right hnum_le hpos₂.le
  exact max_le_max (le_trans hpow1 hpow2) (le_trans hdiv1 hdiv2)

end

public section

/-- Construct a `Spanner.ConstructExpanderTool` from `theorem_8_4` (`Cited.ExplicitExpander`),
rounding real weights `w v ≥ 1` up via `Nat.ceil (w v)` (`c_deg = 36`), together with the
underlying `constructExpanderModel` and `constructExpanderCost` operation-count bound. -/
theorem exists_constructExpanderTool :
    ∃ (ce : Spanner.ConstructExpanderTool) (P : WordRAM.Program) (c_w : ℕ)
      (K_cited K_run : ℝ) (buildH : (N : ℕ) → 1 < N → Cited.Graph)
      (citedCost : (N : ℕ) → 1 < N → ℕ),
      ce.c_deg = 36 ∧ 0 < ce.φ_Const ∧ ce.φ_Const ≤ 1 ∧ 0 ≤ K_cited ∧ 0 ≤ K_run ∧
      (∀ n w, ce.construct n w = constructExpanderModel buildH n (fun v => (Nat.ceil (w v) : ℚ))) ∧
      (∀ (N : ℕ) (hN : 1 < N),
        WordRAM.RunsTo (WordRAM.wordSize c_w [N]) P [N] (fun _ => false)
          (buildH N hN).encode (citedCost N hN) ∧
        (citedCost N hN : ℝ) ≤ K_cited * N) ∧
      (∀ (n : ℕ) (w : ℕ → ℝ), (∀ v < n, 1 ≤ w v) →
        let W := ce.construct n w
        let cost := constructExpanderCost buildH citedCost n (fun v => (Nat.ceil (w v) : ℚ))
        W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts ce.φ_Const ∧
        (∀ v < n, w v ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ 36 * w v) ∧
        ((W.m : ℝ) ≤ 36 * ∑ v ∈ Finset.range n, w v) ∧
        (cost : ℝ) ≤ (2 * K_run) * (n + ∑ v ∈ Finset.range n, w v)) := by
  classical
  rcases theorem_8_4 with
    ⟨φ_Const, P, c_w, K_cited, K_run, buildH, citedCost, hφ0, hφ1, hKc, hKr, hbuildH, hmodel⟩
  have hspec_all : ∀ (n : ℕ) (w : ℕ → ℝ), (∀ v < n, 1 ≤ w v) →
      let W := constructExpanderModel buildH n (fun v => (Nat.ceil (w v) : ℚ))
      let cost := constructExpanderCost buildH citedCost n (fun v => (Nat.ceil (w v) : ℚ))
      W.n = n ∧ W.IsValid ∧ W.IsConductanceExpanderOn W.verts φ_Const ∧
      (∀ v < n, w v ≤ (W.deg v : ℝ) ∧ (W.deg v : ℝ) ≤ 36 * w v) ∧
      ((W.m : ℝ) ≤ 36 * ∑ v ∈ Finset.range n, w v) ∧
      (cost : ℝ) ≤ (2 * K_run) * (n + ∑ v ∈ Finset.range n, w v) := by
    intro n w hw
    let wQ : ℕ → ℚ := fun v => (Nat.ceil (w v) : ℚ)
    have hwQ : ∀ v < n, 1 ≤ wQ v := by
      intro v hv
      have h1 : (1 : ℕ) ≤ Nat.ceil (w v) := Nat.ceil_pos.mpr (lt_of_lt_of_le (by norm_num) (hw v hv))
      dsimp only [wQ]
      exact_mod_cast h1
    rcases hmodel n wQ hwQ with ⟨hWn, hWv, hWexp, hWdeg, hWm, hcost⟩
    have hsum_ceil : ∑ v ∈ Finset.range n, (wQ v : ℝ) ≤ 2 * ∑ v ∈ Finset.range n, w v := by
      calc ∑ v ∈ Finset.range n, (wQ v : ℝ)
          = ∑ v ∈ Finset.range n, (Nat.ceil (w v) : ℝ) := by
            apply Finset.sum_congr rfl
            intro v _
            simp [wQ]
        _ ≤ ∑ v ∈ Finset.range n, 2 * w v :=
            Finset.sum_le_sum fun v hv => (ceil_real_bounds (hw v (Finset.mem_range.mp hv))).2
        _ = 2 * ∑ v ∈ Finset.range n, w v := by rw [← Finset.mul_sum]
    refine ⟨hWn, hWv, hWexp, ?_, ?_, ?_⟩
    · intro v hv
      have hd := hWdeg v hv
      have hc := ceil_real_bounds (hw v hv)
      have hwQv : (wQ v : ℝ) = (Nat.ceil (w v) : ℝ) := by simp [wQ]
      rw [hwQv] at hd
      exact ⟨le_trans hc.1 hd.1, le_trans hd.2 (by linarith [hc.2])⟩
    · calc ((constructExpanderModel buildH n wQ).m : ℝ)
          ≤ 18 * ∑ v ∈ Finset.range n, (wQ v : ℝ) := by
            simpa [wQ] using hWm
        _ ≤ 18 * (2 * ∑ v ∈ Finset.range n, w v) := by linarith
        _ = 36 * ∑ v ∈ Finset.range n, w v := by ring
    · have hsum_le : ∑ v ∈ Finset.range n, (wQ v : ℝ) ≤ 2 * ∑ v ∈ Finset.range n, w v := hsum_ceil
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
      have hcost_r : ((constructExpanderCost buildH citedCost n wQ : ℕ) : ℝ) ≤
          K_run * ((n : ℝ) + ∑ v ∈ Finset.range n, (wQ v : ℝ)) := by
        simpa [wQ] using hcost
      calc ((constructExpanderCost buildH citedCost n wQ : ℕ) : ℝ)
          ≤ K_run * ((n : ℝ) + ∑ v ∈ Finset.range n, (wQ v : ℝ)) := hcost_r
        _ ≤ K_run * (2 * (n : ℝ) + 2 * ∑ v ∈ Finset.range n, w v) := by
            apply mul_le_mul_of_nonneg_left _ hKr
            linarith
        _ = (2 * K_run) * ((n : ℝ) + ∑ v ∈ Finset.range n, w v) := by ring
  let ce : Spanner.ConstructExpanderTool :=
    { φ_Const := φ_Const
      c_deg := 36
      construct := fun n w => constructExpanderModel buildH n (fun v => (Nat.ceil (w v) : ℚ))
      hφ_pos := hφ0
      hφ_le := hφ1
      hc_deg := by norm_num
      construct_spec := fun n w _ hw =>
        let h := hspec_all n w hw
        ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩ }
  exact ⟨ce, P, c_w, K_cited, K_run, buildH, citedCost, rfl, hφ0, hφ1, hKc, hKr,
    fun _ _ => rfl, hbuildH, hspec_all⟩

/-- Construct a `Spanner.DecomposeTool` from `theorem_8_5` (`Cited.ExpanderDecomposition`),
with `c_ℓ = 1`, antitone `φ_dec G = φ G.m` satisfying
`1 / φ m ≤ C₁ * exp(C₀ * log(m + 2)^{2/3} * log(log(m + 2) + 2))`,
and explicit `decomposeModelCost` upper bound. -/
theorem exists_decomposeTool (hDec : Cited.ExpanderDecomposition) :
    ∃ (dt : Spanner.DecomposeTool) (φ : ℕ → ℝ) (C₀ C₁ C_cost : ℝ) (P : WordRAM.Program)
      (c_w thr : ℕ) (K_dec cr_dec : ℝ) (citedOut : ℕ → ℕ → Cited.Graph → List ℕ)
      (citedCost : ℕ → ℕ → Cited.Graph → ℕ),
      dt.c_ℓ = 1 ∧ 0 < C₀ ∧ 0 < C₁ ∧ 0 < C_cost ∧ 0 < K_dec ∧ 0 < cr_dec ∧
      (∀ m : ℕ, 0 < φ m ∧ φ m ≤ 1 ∧
        1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → φ m₂ ≤ φ m₁) ∧
      (∀ G : Cited.Graph, dt.φ_dec G = φ G.m) ∧
      (∀ (G : Cited.Graph) (M : ℕ), G.m ≤ M → φ M ≤ dt.φ_dec G) ∧
      (∀ a b (G : Cited.Graph), G.IsValid → G.IsLoopless → 1 ≤ a → a ≤ b → thr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [a, b, rOf G.m])) P
          (G.encode ++ [a, b, rOf G.m]) (fun _ => false) (citedOut a b G) (citedCost a b G)) ∧
      (∀ G : Cited.Graph, G.IsValid → G.IsLoopless →
        let decomp := decompModel citedOut thr
        let decompC := decompModelCost citedCost thr
        let φ_level := phiB1 K_dec cr_dec 1 200
        let cost := decomposeModelCost decomp decompC φ_level G
        ((cost : ℝ) ≤ C_cost * (G.m : ℝ) *
          Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)))) := by
  classical
  rcases theorem_8_5 hDec with
    ⟨φ, C₀, C₁, C_cost, P, c_w, thr, K_dec, cr_dec, citedOut, citedCost,
      hC₀, hC₁, hCc, hKd, hcrd, hφ_spec, hφ_anti, hruns, hchain⟩
  let decomp := decompModel citedOut thr
  let decompC := decompModelCost citedCost thr
  let φ_level := phiB1 K_dec cr_dec 1 200
  let decFn : Cited.Graph → Spanner.DecomposeOutput := fun G =>
    let gs := decomposeModel decomp φ_level G
    let metaOut := decomposeChainMeta decomp φ_level G (decomposeEll G)
    { ℓ := gs.length - 1
      level := fun j => metaOut.2 (G.edges.getD j (0, 0))
      comps := metaOut.1 }
  have hspec : ∀ G : Cited.Graph, G.IsValid → G.IsLoopless →
      let d := decFn G
      (d.ℓ : ℝ) ≤ (1 : ℝ) * ((Nat.log 2 (G.m + 2) : ℝ) + 1) ∧
      (∀ j < G.m, d.level j ≤ d.ℓ) ∧
      (∀ i ≤ d.ℓ, (Spanner.DecomposeOutput.graphAt G d i).m ≤ 2 ^ i * G.n) ∧
      (∀ i : ℕ, 0 < i → i ≤ d.ℓ →
        (d.comps i).Pairwise Disjoint ∧
        (∀ X ∈ d.comps i, X ⊆ G.verts ∧ 2 ≤ X.card ∧
          (Spanner.DecomposeOutput.graphAt G d i).IsConductanceExpanderOn X (φ G.m) ∧
          (∀ x ∈ X, φ G.m * 2 ^ i ≤ ((Spanner.DecomposeOutput.graphAt G d i).degIn X x : ℝ)) ∧
          (∀ e ∈ (Spanner.DecomposeOutput.graphAt G d i).edges, e.1 ∈ X ↔ e.2 ∈ X)) ∧
        (∀ e ∈ (Spanner.DecomposeOutput.graphAt G d i).edges, ∃ X ∈ d.comps i, e.1 ∈ X ∧ e.2 ∈ X)) := by
    intro G hV hL
    have hc := hchain G hV hL
    dsimp only at hc
    set gs := decomposeModel decomp φ_level G
    cases hmeta : decomposeChainMeta decomp φ_level G (decomposeEll G) with
    | mk compsFn lvlFn =>
      rw [hmeta] at hc
      dsimp only at hc
      rcases hc with ⟨hgs_len, hℓ_eq, hℓ_log, _, hGi_all, _, hm_le, _, hlvl_le, hedges_eq, hcomps_spec, _⟩
      have hd_ℓ : (decFn G).ℓ = gs.length - 1 := rfl
      have hgraphAt_eq : ∀ (i : ℕ) (hi_lt : i < gs.length),
          Spanner.DecomposeOutput.graphAt G (decFn G) i = gs[i] := by
        intro i hi_lt
        have hGi_n : gs[i].n = G.n := (hGi_all gs[i] (List.getElem_mem hi_lt)).1
        have hedges_at : (Spanner.DecomposeOutput.graphAt G (decFn G) i).edges =
            G.edges.filter (fun e => decide (lvlFn e = i)) := by
          dsimp only [Spanner.DecomposeOutput.graphAt, Spanner.DecomposeOutput.edgesAt, decFn]
          rw [hmeta]
          have hmap : G.edges = (List.range G.m).map fun j => G.edges.getD j (0, 0) :=
            (edges_eq_map_range G.edges).symm
          conv_rhs => rw [hmap]
          rw [List.filter_map]
          rfl
        have hedges_gs : gs[i].edges = G.edges.filter (fun e => decide (lvlFn e = i)) :=
          hedges_eq i hi_lt
        cases hgs : gs[i] with
        | mk n_i edges_i =>
          have hn' : (Spanner.DecomposeOutput.graphAt G (decFn G) i).n = n_i := by
            have : gs[i].n = n_i := by rw [hgs]
            rw [← this, hGi_n]; rfl
          have he' : (Spanner.DecomposeOutput.graphAt G (decFn G) i).edges = edges_i := by
            rw [hedges_at, ← hedges_gs, hgs]
          cases hga : Spanner.DecomposeOutput.graphAt G (decFn G) i with
          | mk n_ga edges_ga =>
            have hn'' : n_ga = n_i := by rw [← hn', hga]
            have he'' : edges_ga = edges_i := by rw [← he', hga]
            subst hn'' he''
            rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hd_ℓ, one_mul]
        exact_mod_cast hℓ_log
      · intro j _
        dsimp only [decFn]
        rw [hmeta]
        exact hlvl_le (G.edges.getD j (0, 0))
      · intro i hi
        have hi_lt : i < gs.length := by rw [hd_ℓ] at hi; omega
        rw [hgraphAt_eq i hi_lt]
        exact hm_le i hi_lt
      · intro i hi0 hi
        have hi_lt : i < gs.length := by rw [hd_ℓ] at hi; omega
        rw [hgraphAt_eq i hi_lt]
        dsimp only [decFn]
        rw [hmeta]
        exact hcomps_spec i hi_lt hi0
  let dt : Spanner.DecomposeTool :=
    { c_ℓ := 1
      φ_dec := fun G => φ G.m
      decompose := decFn
      hc_ℓ := le_rfl
      hφ_pos := fun G _ _ => (hφ_spec G.m).1
      hφ_le := fun G _ _ => (hφ_spec G.m).2.1
      decompose_spec := fun G hV hL => hspec G hV hL }
  refine ⟨dt, φ, C₀, C₁, C_cost, P, c_w, thr, K_dec, cr_dec, citedOut, citedCost,
    rfl, hC₀, hC₁, hCc, hKd, hcrd, hφ_spec, hφ_anti, fun _ => rfl,
    fun G M hGM => hφ_anti G.m M hGM, hruns, ?_⟩
  intro G hV hL
  have hc := hchain G hV hL
  dsimp only at hc
  cases hmeta : decomposeChainMeta decomp φ_level G (decomposeEll G) with
  | mk compsFn lvlFn =>
    rw [hmeta] at hc
    exact hc.2.2.2.2.2.2.2.2.2.2.2

/-- Construct a `Spanner.PathDSTool` from `Cited.DecrementalExpanderPaths` (`pathDSOfCS`,
Theorem 8.6), choosing `c` so that `10 * csPhi Kγ c (3 * m)` lies below both `φ_Const` and
`1 / (C₁ * exp(C₀ * log(m+2)^{2/3} * log(log(m+2)+2)))`, and proving monotonicity and
`exp(O(log^{7/8} (M + 2)))` bounds on `γ_ExpPath`, `1 / φ_out`, `csTotal`, and `csQuery`. -/
theorem exists_pathDSTool_for_params (hCS : Cited.DecrementalExpanderPaths)
    {C₀ C₁ φ_Const : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hφ_Const : 0 < φ_Const) :
    ∃ (pds : Spanner.PathDSTool) (Kγ c cw : ℕ) (K C_p C_tot C_lin C_q C_k : ℝ)
      (mk : ℕ → List WordRAM.Stmt) (R : WordRAM.DSRep Cited.PrunedExpander),
      1 ≤ Kγ ∧ 20 ≤ c ∧ 0 < C_p ∧ 0 < C_tot ∧ 0 < C_lin ∧ 0 < C_q ∧ 0 < C_k ∧
      (∀ w b (p : WordRAM.Program), p.HasAt b (mk b) →
        R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K cw w)) ∧
      pds.φ_out = csPhiOut Kγ c ∧
      pds.γ_ExpPath = csGammaExpPath Kγ c K ∧
      (∀ φ M, pds.γ_del φ M = csGammaDel K) ∧
      (∀ φ₁ φ₂ M, φ₁ ≤ φ₂ → pds.φ_out φ₁ M ≤ pds.φ_out φ₂ M) ∧
      (∀ φ_in M₁ M₂, M₁ ≤ M₂ → pds.φ_out φ_in M₂ ≤ pds.φ_out φ_in M₁) ∧
      (∀ φ₁ φ₂ M, 0 < φ₁ → φ₁ ≤ φ₂ → pds.γ_ExpPath φ₂ M ≤ pds.γ_ExpPath φ₁ M) ∧
      (∀ φ_in M₁ M₂, 0 < φ_in → M₁ ≤ M₂ → pds.γ_ExpPath φ_in M₁ ≤ pds.γ_ExpPath φ_in M₂) ∧
      (∀ φ_in M, 7 ≤ pds.γ_del φ_in M) ∧
      (∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤ φ_Const) ∧
      (∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤
        1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2)))) ∧
      (∀ (φ_in : ℝ) (M : ℕ), Cited.csPhi Kγ c (3 * M) ≤ φ_in →
        pds.φ_out φ_in M = Cited.csPhi Kγ c (3 * M) ∧
        pds.γ_ExpPath φ_in M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        1 / pds.φ_out φ_in M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ {G : Cited.Graph} {M : ℕ}, G.IsValid → 1 ≤ G.m → G.m ≤ M → (∀ v < G.n, 1 ≤ G.deg v) →
        let G_s := subdivGraph G
        (Cited.csTotal Kγ K G_s.n G_s.m (qOf M) : ℝ) ≤
          C_lin * (G.m : ℝ) * Real.exp (C_tot * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ M : ℕ, (Cited.csQuery Kγ K (3 * M) (qOf M) : ℝ) ≤
        C_k * Real.exp (C_q * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ φ_in M, pds.γ_query φ_in M =
        pds.γ_ExpPath φ_in M + (PathDSProg.fbCostBound (Nat.ceil (1 / φ_in)) : ℝ)) := by
  classical
  rcases hCS with ⟨Kγ, c₀, hKγ, hc₀, hCS_inst⟩
  have hKγ1 : 1 ≤ Kγ := hKγ
  rcases csGamma_dominates_sb hKγ1 C₀ C₁ hC₀ hC₁ with ⟨c₁, hc₁, hdom_sb⟩
  let c₂ : ℕ := Nat.ceil (10 / φ_Const) + 1
  let c : ℕ := max c₀ (max c₁ (max c₂ 20))
  have hc_c₀ : c₀ ≤ c := le_max_left _ _
  have hc_c₁ : c₁ ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hc_c₂ : c₂ ≤ c := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hc20 : 20 ≤ c := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hc1 : 1 ≤ c := by omega
  rcases hCS_inst c hc_c₀ with ⟨K, cw, mk, R, hImpl⟩
  let pds : Spanner.PathDSTool := pathDSOfCS hc1 K cw mk R hImpl
  rcases pathDS_gamma_exp_seven_eighths Kγ c K with ⟨C_p0, hCp0, hgamma_p0⟩
  let C_p : ℝ := C_p0 + 8
  have hCp : 0 < C_p := by linarith
  let Kpos : ℝ := max K 1
  have hKpos : 0 < Kpos := by positivity
  rcases csTotal_subdiv_le_exp_seven_eighths Kγ hKpos with ⟨C_tot, C_lin, hCtot, hClin, htot_bd⟩
  rcases csQuery_subdiv_le_exp_seven_eighths Kγ hKpos with ⟨C_q, C_k, hCq, hCk, hq_bd⟩
  have hdom_const : ∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤ φ_Const := by
    intro m
    have hγ1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := by
      unfold Cited.csGamma
      exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
    have hden_ge : (10 / φ_Const : ℝ) ≤ (c : ℝ) := by
      have hceil : 10 / φ_Const ≤ (Nat.ceil (10 / φ_Const) : ℝ) := Nat.le_ceil _
      have hc2_le : (Nat.ceil (10 / φ_Const) : ℝ) ≤ (c₂ : ℝ) := by
        dsimp only [c₂]; push_cast; linarith
      have hc2_c : (c₂ : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc_c₂
      exact le_trans hceil (le_trans hc2_le hc2_c)
    have hpos_den : 0 < (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by
      have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
      positivity
    have hmul_ge : 10 / φ_Const ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by
      calc 10 / φ_Const ≤ (c : ℝ) := hden_ge
        _ = (c : ℝ) * 1 := by ring
        _ ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by gcongr
    have hcsPhi_eq : Cited.csPhi Kγ c (3 * m) = 1 / ((c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ)) := rfl
    rw [hcsPhi_eq]
    have h1 : 10 * (1 / ((c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ))) =
        10 / ((c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ)) := by ring
    rw [h1, div_le_iff₀ hpos_den]
    have h2 := (div_le_iff₀ hφ_Const).mp hmul_ge
    linarith
  have hdom_dec : ∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤
      1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
        Real.log (Real.log ((m : ℝ) + 2) + 2))) := by
    intro m
    have hle_c1 : Cited.csPhi Kγ c (3 * m) ≤ Cited.csPhi Kγ c₁ (3 * m) :=
      csPhi_anti_c hc₁ hc_c₁
    have h10 : 10 * Cited.csPhi Kγ c (3 * m) ≤ 10 * Cited.csPhi Kγ c₁ (3 * m) := by linarith
    have hd := hdom_sb m
    have hd10 : 10 * (1 / ((c₁ : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ))) ≤
        1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) := by linarith
    exact le_trans h10 hd10
  have hdom_half : ∀ m : ℕ, Cited.csPhi Kγ c (3 * m) ≤ (1 / 2 : ℝ) := by
    intro m
    have hγ1 : (1 : ℝ) ≤ (Cited.csGamma Kγ (3 * m) : ℝ) := by
      unfold Cited.csGamma
      exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
    have hden : (2 : ℝ) ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by
      have hc_r : (20 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc20
      calc (2 : ℝ) ≤ (20 : ℝ) := by norm_num
        _ ≤ (c : ℝ) := hc_r
        _ = (c : ℝ) * 1 := by ring
        _ ≤ (c : ℝ) * (Cited.csGamma Kγ (3 * m) : ℝ) := by gcongr
    unfold Cited.csPhi
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hden)
  have hregime : ∀ (φ_in : ℝ) (M : ℕ), Cited.csPhi Kγ c (3 * M) ≤ φ_in →
      pds.φ_out φ_in M = Cited.csPhi Kγ c (3 * M) ∧
      pds.γ_ExpPath φ_in M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      1 / pds.φ_out φ_in M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
    intro φ_in M hφ_ge
    have hhalf := hdom_half M
    have hmin2 : min (1 / 2 : ℝ) (Cited.csPhi Kγ c (3 * M)) = Cited.csPhi Kγ c (3 * M) :=
      min_eq_right hhalf
    have hφout_eq : pds.φ_out φ_in M = Cited.csPhi Kγ c (3 * M) := by
      rw [pathDSOfCS_φ_out hc1 K cw mk R hImpl]
      dsimp only [csPhiOut]
      rw [hmin2, min_eq_right hφ_ge]
    have hinv_eq : 1 / pds.φ_out φ_in M = (c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) := by
      rw [hφout_eq]
      unfold Cited.csPhi
      simp [one_div]
    have hL := half_le_log_rpow_seven_eighths M
    have hexp_abs : 10 * Real.exp (C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      have h4 : (4 : ℝ) ≤ 8 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) := by linarith
      calc 10 * Real.exp (C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))
          ≤ Real.exp 4 * Real.exp (C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
            mul_le_mul_of_nonneg_right ten_le_exp_four (Real.exp_pos _).le
        _ = Real.exp (C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) + 4) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp (C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) +
              8 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) :=
            Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
            dsimp only [C_p]; ring_nf
    have hbd := hgamma_p0 M
    have hterm2 : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / pds.φ_out φ_in M ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      have hrw : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / pds.φ_out φ_in M =
          10 * (25 * (Real.log (2 * (M : ℝ) + 2) + 1) *
            ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) / 10)) := by
        rw [div_eq_mul_one_div, hinv_eq]; ring
      rw [hrw]
      exact le_trans (mul_le_mul_of_nonneg_left hbd.2 (by norm_num)) hexp_abs
    have hterm1 : (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      have harg : C_p0 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) ≤
          C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ) := by
        dsimp only [C_p]; linarith
      exact le_trans hbd.1 (Real.exp_le_exp.mpr harg)
    have hγ_le : pds.γ_ExpPath φ_in M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
      rw [pathDSOfCS_γ_ExpPath hc1 K cw mk R hImpl]
      dsimp only [csGammaExpPath]
      have hφ_out_eq' : csPhiOut Kγ c φ_in M = pds.φ_out φ_in M :=
        (pathDSOfCS_φ_out hc1 K cw mk R hImpl).symm ▸ rfl
      rw [hφ_out_eq']
      exact max_le hterm1 hterm2
    have hdiv_inv : 1 / pds.φ_out φ_in M ≤ 25 * (Real.log (2 * (M : ℝ) + 2) + 1) / pds.φ_out φ_in M := by
      have hlog : 1 ≤ Real.log (2 * (M : ℝ) + 2) + 1 := by
        have : 0 ≤ Real.log (2 * (M : ℝ) + 2) :=
          Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M])
        linarith
      have hφ_pos : 0 < pds.φ_out φ_in M := by
        rw [hφout_eq]; exact csPhi_pos_of_pos_c hc1 _
      exact div_le_div_of_nonneg_right (by linarith) hφ_pos.le
    exact ⟨hφout_eq, hγ_le, le_trans hdiv_inv hterm2⟩
  have hcsTotal_monoK : ∀ n m q : ℕ, (Cited.csTotal Kγ K n m q : ℝ) ≤ (Cited.csTotal Kγ Kpos n m q : ℝ) := by
    intro n m q
    by_cases hK0 : K ≤ 0
    · unfold Cited.csTotal
      have hnonpos : K * ((m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (K * (q : ℝ)) + 1) ≤ 0 := by
        have h1 : 0 ≤ (m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (K * (q : ℝ)) + 1 := by
          positivity
        exact mul_nonpos_of_nonpos_of_nonneg hK0 h1
      rw [Nat.ceil_eq_zero.mpr hnonpos]
      exact_mod_cast Nat.zero_le (Cited.csTotal Kγ Kpos n m q)
    · have hK_pos : 0 < K := lt_of_not_ge hK0
      have hK_le : K ≤ Kpos := le_max_left K 1
      have hγ_ge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ n : ℝ) := by
        unfold Cited.csGamma
        exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
      have hexp_le : K * (q : ℝ) ≤ Kpos * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg q)
      have hinner :
          K * ((m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (K * (q : ℝ)) + 1) ≤
          Kpos * ((m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (Kpos * (q : ℝ)) + 1) := by
        have hpow : (Cited.csGamma Kγ n : ℝ) ^ (K * (q : ℝ)) ≤ (Cited.csGamma Kγ n : ℝ) ^ (Kpos * (q : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hγ_ge1 hexp_le
        have hm0 : 0 ≤ (m : ℝ) ^ (1 + 1 / (q : ℝ)) := by positivity
        have hmul1 : (m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (K * (q : ℝ)) + 1 ≤
            (m : ℝ) ^ (1 + 1 / (q : ℝ)) * (Cited.csGamma Kγ n : ℝ) ^ (Kpos * (q : ℝ)) + 1 := by
          linarith [mul_le_mul_of_nonneg_left hpow hm0]
        exact mul_le_mul hK_le hmul1 (by positivity) hKpos.le
      exact_mod_cast Nat.ceil_mono hinner
  have hcsQuery_monoK : ∀ m q : ℕ, (Cited.csQuery Kγ K m q : ℝ) ≤ (Cited.csQuery Kγ Kpos m q : ℝ) := by
    intro m q
    by_cases hK0 : K ≤ 0
    · unfold Cited.csQuery
      have hnonpos : K * ((Cited.csGamma Kγ m : ℝ) ^ (K * (q : ℝ)) + 1) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hK0 (by positivity)
      rw [Nat.ceil_eq_zero.mpr hnonpos]
      exact_mod_cast Nat.zero_le (Cited.csQuery Kγ Kpos m q)
    · have hK_le : K ≤ Kpos := le_max_left K 1
      have hγ_ge1 : (1 : ℝ) ≤ (Cited.csGamma Kγ m : ℝ) := by
        unfold Cited.csGamma
        exact_mod_cast Nat.one_le_pow _ 2 (by norm_num)
      have hexp_le : K * (q : ℝ) ≤ Kpos * (q : ℝ) :=
        mul_le_mul_of_nonneg_right hK_le (Nat.cast_nonneg q)
      have hinner : K * ((Cited.csGamma Kγ m : ℝ) ^ (K * (q : ℝ)) + 1) ≤
          Kpos * ((Cited.csGamma Kγ m : ℝ) ^ (Kpos * (q : ℝ)) + 1) := by
        have hpow := Real.rpow_le_rpow_of_exponent_le hγ_ge1 hexp_le
        exact mul_le_mul hK_le (by linarith) (by positivity) hKpos.le
      exact_mod_cast Nat.ceil_mono hinner
  refine ⟨pds, Kγ, c, cw, K, C_p, C_tot, C_lin, C_q, C_k, mk, R,
    hKγ1, hc20, hCp, hCtot, hClin, hCq, hCk, hImpl,
    pathDSOfCS_φ_out hc1 K cw mk R hImpl,
    pathDSOfCS_γ_ExpPath hc1 K cw mk R hImpl,
    fun _ _ => by rw [pathDSOfCS_γ_del hc1 K cw mk R hImpl],
    ?_, ?_, ?_, ?_, ?_, hdom_const, hdom_dec, hregime, ?_, ?_, ?_⟩
  · intro φ₁ φ₂ M hφ
    rw [pathDSOfCS_φ_out hc1 K cw mk R hImpl]
    exact csPhiOut_mono_phi hφ M
  · intro φ_in M₁ M₂ hM
    rw [pathDSOfCS_φ_out hc1 K cw mk R hImpl]
    exact csPhiOut_anti_m hc1 φ_in hM
  · intro φ₁ φ₂ M hφ₁ hφ
    rw [pathDSOfCS_γ_ExpPath hc1 K cw mk R hImpl]
    exact csGammaExpPath_anti_phi hc1 K hφ₁ hφ M
  · intro φ_in M₁ M₂ hφ hM
    rw [pathDSOfCS_γ_ExpPath hc1 K cw mk R hImpl]
    exact csGammaExpPath_mono_m hc1 K hφ hM
  · intro φ_in M
    rw [pathDSOfCS_γ_del hc1 K cw mk R hImpl]
    exact le_max_right _ 7
  · intro G M hV hm1 hmM hiso
    let G_s := subdivGraph G
    exact le_trans (hcsTotal_monoK G_s.n G_s.m (qOf M)) (htot_bd hV hm1 hmM hiso)
  · intro M
    exact le_trans (hcsQuery_monoK (3 * M) (qOf M)) (hq_bd M)
  · intro φ_in M
    rw [pathDSOfCS_γ_query hc1 K cw mk R hImpl, pathDSOfCS_γ_ExpPath hc1 K cw mk R hImpl]
    rfl

/-- Assemble the complete `Spanner.SpannerTools` record from the explicit expander
(`MinCostFlow.ExplicitExpander.explicitExpander`) and the two cited expander results
(`ExpanderDecomposition`, `DecrementalExpanderPaths`), together with
all quantitative parameter bounds (`c_deg = 36`, `c_ℓ = 1`, `φ` antitone and
`1 / φ m ≤ C₁ * exp(C₀ * log^{2/3}(m+2) * log(log(m+2)+2))`, `φ_out` / `γ_ExpPath`
monotonicity, and `exp(O(log^{7/8}(M+2)))` bounds for both Algorithm 4 parameter regimes),
plus `constructExpanderCost` / `decomposeModelCost` / `R.Implements` links. -/
theorem exists_spannerTools (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (tools : Spanner.SpannerTools) (φ : ℕ → ℝ) (C₀ C₁ C_cost K_run C_p C_tot C_lin C_q C_k : ℝ)
      (Kγ c cw : ℕ) (K_cs : ℝ) (mk : ℕ → List WordRAM.Stmt)
      (R : WordRAM.DSRep Cited.PrunedExpander),
      tools.constructExpander.c_deg = 36 ∧
      0 < tools.constructExpander.φ_Const ∧ tools.constructExpander.φ_Const ≤ 1 ∧
      tools.decompose.c_ℓ = 1 ∧
      0 < C₀ ∧ 0 < C₁ ∧ 0 < C_cost ∧ 0 ≤ K_run ∧
      1 ≤ Kγ ∧ 20 ≤ c ∧ 0 < C_p ∧ 0 < C_tot ∧ 0 < C_lin ∧ 0 < C_q ∧ 0 < C_k ∧
      (∀ m : ℕ, 0 < φ m ∧ φ m ≤ 1 ∧
        1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → φ m₂ ≤ φ m₁) ∧
      (∀ G : Cited.Graph, tools.decompose.φ_dec G = φ G.m) ∧
      (∀ (G : Cited.Graph) (M : ℕ), G.m ≤ M → φ M ≤ tools.decompose.φ_dec G) ∧
      (∀ φ₁ φ₂ M, φ₁ ≤ φ₂ → tools.pathDS.φ_out φ₁ M ≤ tools.pathDS.φ_out φ₂ M) ∧
      (∀ φ_in M₁ M₂, M₁ ≤ M₂ → tools.pathDS.φ_out φ_in M₂ ≤ tools.pathDS.φ_out φ_in M₁) ∧
      (∀ φ₁ φ₂ M, 0 < φ₁ → φ₁ ≤ φ₂ → tools.pathDS.γ_ExpPath φ₂ M ≤ tools.pathDS.γ_ExpPath φ₁ M) ∧
      (∀ φ_in M₁ M₂, 0 < φ_in → M₁ ≤ M₂ → tools.pathDS.γ_ExpPath φ_in M₁ ≤ tools.pathDS.γ_ExpPath φ_in M₂) ∧
      (∀ φ_in M, tools.pathDS.γ_del φ_in M = csGammaDel K_cs) ∧
      (∀ φ_in M, 7 ≤ tools.pathDS.γ_del φ_in M) ∧
      (∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤ tools.constructExpander.φ_Const) ∧
      (∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤
        1 / (C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2)))) ∧
      (∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤ φ m) ∧
      (∀ (m M : ℕ), m ≤ M →
        tools.pathDS.φ_out (φ m) M = Cited.csPhi Kγ c (3 * M) ∧
        tools.pathDS.γ_ExpPath (φ m) M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        1 / tools.pathDS.φ_out (φ m) M ≤ Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ M : ℕ,
        tools.pathDS.φ_out tools.constructExpander.φ_Const M = Cited.csPhi Kγ c (3 * M) ∧
        tools.pathDS.γ_ExpPath tools.constructExpander.φ_Const M ≤
          Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        1 / tools.pathDS.φ_out tools.constructExpander.φ_Const M ≤
          Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ w b (p : WordRAM.Program), p.HasAt b (mk b) →
        R.Implements w p b (fun i => b + 1 + i) (Cited.prunedExpanderDS Kγ c K_cs cw w)) ∧
      (∀ {G : Cited.Graph} {M : ℕ}, G.IsValid → 1 ≤ G.m → G.m ≤ M → (∀ v < G.n, 1 ≤ G.deg v) →
        let G_s := subdivGraph G
        (Cited.csTotal Kγ K_cs G_s.n G_s.m (qOf M) : ℝ) ≤
          C_lin * (G.m : ℝ) * Real.exp (C_tot * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ M : ℕ, (Cited.csQuery Kγ K_cs (3 * M) (qOf M) : ℝ) ≤
        C_k * Real.exp (C_q * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ))) ∧
      (∀ φ_in M, tools.pathDS.γ_query φ_in M = tools.pathDS.γ_ExpPath φ_in M +
        (PathDSProg.fbCostBound (Nat.ceil (1 / φ_in)) : ℝ)) := by
  classical
  rcases exists_constructExpanderTool with
    ⟨ce, _, _, _, K_run, _, _, hce_deg, hce_φ0, hce_φ1, _, hKr, _, _, _⟩
  rcases exists_decomposeTool hDec with
    ⟨dt, φ, C₀, C₁, C_cost, _, _, _, _, _, _, _, hdt_cl, hC₀, hC₁, hCc, _, _,
      hφ_spec, hφ_anti, hφ_dec_eq, hφ_dec_mono, _, _⟩
  rcases exists_pathDSTool_for_params hPaths hC₀ hC₁ hce_φ0 with
    ⟨pds, Kγ, c, cw, K_cs, C_p, C_tot, C_lin, C_q, C_k, mk, R,
      hKγ, hc20, hCp, hCtot, hClin, hCq, hCk, hImpl, _, _, hγ_del_eq,
      hφ_mono, hφ_antiM, hγ_anti, hγ_monoM, hγ_del, hdom_const, hdom_dec, hreg, htot, hq, hγq⟩
  have hc1 : 1 ≤ c := by omega
  have h10_dec : ∀ m : ℕ, 10 * Cited.csPhi Kγ c (3 * m) ≤ φ m := by
    intro m
    have hm_pos := (hφ_spec m).1
    have hbd := (hφ_spec m).2.2
    set B := C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
      Real.log (Real.log ((m : ℝ) + 2) + 2))
    have hB_pos : 0 < B := by positivity
    have h1 : 1 / B ≤ φ m := by
      have hmul : 1 ≤ B * φ m := by
        have := (div_le_iff₀ hm_pos).mp hbd
        linarith
      exact (div_le_iff₀ hB_pos).mpr (by linarith)
    exact le_trans (hdom_dec m) h1
  let tools : Spanner.SpannerTools := ⟨ce, dt, pds⟩
  refine ⟨tools, φ, C₀, C₁, C_cost, K_run, C_p, C_tot, C_lin, C_q, C_k,
    Kγ, c, cw, K_cs, mk, R, hce_deg, hce_φ0, hce_φ1, hdt_cl, hC₀, hC₁, hCc, hKr,
    hKγ, hc20, hCp, hCtot, hClin, hCq, hCk,
    hφ_spec, hφ_anti, hφ_dec_eq, hφ_dec_mono,
    hφ_mono, hφ_antiM, hγ_anti, hγ_monoM, hγ_del_eq, hγ_del, hdom_const, hdom_dec, h10_dec, ?_, ?_, hImpl, htot, hq, hγq⟩
  · intro m M hmM
    have h1 : Cited.csPhi Kγ c (3 * M) ≤ 10 * Cited.csPhi Kγ c (3 * M) := by
      have h0 : 0 ≤ Cited.csPhi Kγ c (3 * M) := (csPhi_pos_of_pos_c hc1 _).le
      linarith
    have h2 : 10 * Cited.csPhi Kγ c (3 * M) ≤ φ M := h10_dec M
    have h3 : φ M ≤ φ m := hφ_anti m M hmM
    exact hreg (φ m) M (le_trans h1 (le_trans h2 h3))
  · intro M
    have h1 : Cited.csPhi Kγ c (3 * M) ≤ 10 * Cited.csPhi Kγ c (3 * M) := by
      have h0 : 0 ≤ Cited.csPhi Kγ c (3 * M) := (csPhi_pos_of_pos_c hc1 _).le
      linarith
    exact hreg ce.φ_Const M (le_trans h1 (hdom_const M))

end

end MinCostFlow.Expander
