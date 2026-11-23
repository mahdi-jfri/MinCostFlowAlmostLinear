module

public import MinCostFlow.ExpanderDecomp.Twin
public import MinCostFlow.Expander.SpannerTools
import all MinCostFlow.Expander.Decompose
import all MinCostFlow.Expander.SpannerTools
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Model-Side Bridges from `ExpanderDecompositionUsed` (`SwapBridge`)

Bridges `ExpanderDecompositionUsed` (via `Twin.expanderDecomp_of_used`) across the model-side
expander decomposition hierarchy:
* `theorem_8_5_of_used`: the `(1, 200)` twin of `MinCostFlow.Expander.theorem_8_5`
  (`MinCostFlow/Expander/Decompose.lean`).
* `exists_decomposeTool_of_used`: the `(1, 200)` twin of `MinCostFlow.Expander.exists_decomposeTool`
  (`MinCostFlow/Expander/SpannerTools.lean`).
* `exists_spannerTools_of_used`: the exact statement of `MinCostFlow.Expander.exists_spannerTools`
  (`MinCostFlow/Expander/SpannerTools.lean`), taking `ExpanderDecompositionUsed` in place of
  `Cited.ExpanderDecomposition`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander WordRAM

/-- Twin of **Theorem 8.5** (`MinCostFlow.Expander.theorem_8_5`, page 29 / Appendix B page 49)
taking `ExpanderDecompositionUsed` instead of `Cited.ExpanderDecomposition`: specializes the
auxiliary `RunsTo` conjunct to `(a, b) = (1, 200)` while keeping the exact same `decomposeModel`,
`decomposeChainMeta`, `decomposeModelCost`, and conductance/cost guarantees. -/
theorem theorem_8_5_of_used (hDec : ExpanderDecompositionUsed) :
    ∃ (φ : ℕ → ℝ) (C₀ C₁ C_cost : ℝ)
      (P : WordRAM.Program) (c_w thr : ℕ) (K_dec cr_dec : ℝ)
      (citedOut : ℕ → ℕ → Cited.Graph → List ℕ)
      (citedCost : ℕ → ℕ → Cited.Graph → ℕ),
      0 < C₀ ∧ 0 < C₁ ∧ 0 < C_cost ∧ 0 < K_dec ∧ 0 < cr_dec ∧
      (∀ m : ℕ, 0 < φ m ∧ φ m ≤ 1 ∧
        1 / φ m ≤ C₁ * Real.exp (C₀ * Real.log ((m : ℝ) + 2) ^ (2 / 3 : ℝ) *
          Real.log (Real.log ((m : ℝ) + 2) + 2))) ∧
      (∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → φ m₂ ≤ φ m₁) ∧
      (∀ G : Cited.Graph, G.IsValid → G.IsLoopless →
        thr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [1, 200, rOf G.m])) P
          (G.encode ++ [1, 200, rOf G.m]) (fun _ => false) (citedOut 1 200 G)
          (citedCost 1 200 G)) ∧
      let decomp := decompModel citedOut thr
      let decompC := decompModelCost citedCost thr
      let φ_level := phiB1 K_dec cr_dec 1 200
      ∀ (G : Cited.Graph), G.IsValid → G.IsLoopless →
        let gs := decomposeModel decomp φ_level G
        let (compsFn, lvlFn) := decomposeChainMeta decomp φ_level G (decomposeEll G)
        let cost := decomposeModelCost decomp decompC φ_level G
        let ℓ := gs.length - 1
        1 ≤ gs.length ∧
        ℓ = decomposeEll G ∧
        ℓ ≤ Nat.log 2 (G.m + 2) + 1 ∧
        (G.IsSimple → ℓ ≤ 2 * Nat.log 2 (G.n + 2) + 2) ∧
        (∀ Gi ∈ gs, Gi.n = G.n ∧ Gi.IsValid ∧ Gi.IsLoopless) ∧
        (gs.map Cited.Graph.edges).flatten.Perm G.edges ∧
        (∀ i : ℕ, (hi : i < gs.length) → (gs[i]).m ≤ 2 ^ i * G.n) ∧
        (∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          ∀ X ∈ Cited.partsOf (gs[i]) (compLabels (gs[i])), 2 ≤ X.card →
            (gs[i]).IsConductanceExpanderOn X (φ G.m) ∧
            ∀ x ∈ X, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).deg x : ℝ)) ∧
        (∀ e, lvlFn e ≤ ℓ) ∧
        (∀ i : ℕ, (hi : i < gs.length) →
          (gs[i]).edges = G.edges.filter fun e => decide (lvlFn e = i)) ∧
        (∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          (compsFn i).Pairwise Disjoint ∧
          (∀ R ∈ compsFn i, R ⊆ G.verts ∧ 2 ≤ R.card ∧
            (gs[i]).IsConductanceExpanderOn R (φ G.m) ∧
            (∀ x ∈ R, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).degIn R x : ℝ)) ∧
            (∀ e ∈ (gs[i]).edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
          (∀ e ∈ (gs[i]).edges, ∃ R ∈ compsFn i, e.1 ∈ R ∧ e.2 ∈ R)) ∧
        (cost : ℝ) ≤
          C_cost * (G.m : ℝ) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
  rcases expanderDecomp_of_used hDec with
    ⟨K, cr, C₀_dec, K_cost, P, c_w, citedOut, citedCost, hK, hcr, hC₀_dec, hKc, hcitedRuns, hdec1200_raw⟩
  rcases subpoly_exp_bounds hK hcr with ⟨C_sub, hC_sub, hsub_phi, _⟩
  set C_base := max C₀_dec C_sub
  have hC_base : 0 < C_base := lt_of_lt_of_le hC₀_dec (le_max_left _ _)
  set C₀ := 18 * C_base + 2
  have hC₀ : 0 < C₀ := by positivity
  set M_phi : ℝ := max 1 (max ((thresholdB1 cr : ℝ) + 1) (K * 200))
  have hM_phi : 1 ≤ M_phi := le_max_left _ _
  set C₁ : ℝ := 3 * M_phi
  have hC₁ : 0 < C₁ := by linarith
  set B_const : ℝ := (1366 * M_phi) ^ 2
  set C_cost : ℝ := 16 + 9 * B_const + K_cost * (2 + 400000)
  have hC_cost : 0 < C_cost := by
    have hB : 1 ≤ B_const := by
      have : 1 ≤ 1366 * M_phi := by linarith
      nlinarith
    positivity
  let φ : ℕ → ℝ := fun m => 1 / (C₁ * sb (9 * C_base) m)
  refine ⟨φ, C₀, C₁, C_cost, P, c_w, thresholdB1 cr, K, cr, citedOut, citedCost,
    hC₀, hC₁, hC_cost, hK, hcr, ?_, ?_, ?_, ?_⟩
  · intro m
    have hsb1 : 1 ≤ sb (9 * C_base) m := one_le_sb (by positivity) m
    have hden_ge_three : 3 ≤ C₁ * sb (9 * C_base) m := by nlinarith
    have hden_pos : 0 < C₁ * sb (9 * C_base) m := by linarith
    refine ⟨div_pos one_pos hden_pos, div_le_one_of_le₀ (by linarith) hden_pos.le, ?_⟩
    rw [one_div_one_div]
    change C₁ * sb (9 * C_base) m ≤ C₁ * sb C₀ m
    exact mul_le_mul_of_nonneg_left (sb_mono_C (by dsimp [C₀]; linarith) m) hC₁.le
  · intro m₁ m₂ hm
    have hsb_pos : 0 < sb (9 * C_base) m₁ := sb_pos _ _
    have hsb_le : sb (9 * C_base) m₁ ≤ sb (9 * C_base) m₂ := by
      change subpolyB1 (9 * C_base) m₁ ≤ subpolyB1 (9 * C_base) m₂
      exact subpolyB1_mono_m (by positivity) hm
    dsimp only [φ]
    exact one_div_le_one_div_of_le (mul_pos hC₁ hsb_pos) (mul_le_mul_of_nonneg_left hsb_le hC₁.le)
  · intro G hGv hGl hm
    exact (hcitedRuns G hGv hGl hm).1
  · dsimp only
    intro G hV hL
    dsimp only [decomposeModel, decomposeModelCost]
    set ℓ := decomposeEll G
    by_cases hm_le_n : G.m ≤ G.n
    · have hℓ0 : ℓ = 0 := by simp only [ℓ, decomposeEll, hm_le_n, ↓reduceIte]
      simp only [hm_le_n, ↓reduceIte]
      rw [hℓ0]
      dsimp only [decomposeChain, decomposeChainMeta, decomposeChainCost]
      refine ⟨le_refl 1, ?_, ?_, ?_, ?_, by simp, ?_, ?_, fun _ => le_rfl, ?_, ?_, ?_⟩
      · simp
      · simp
      · intro _; simp
      · intro Gi hGi
        simp only [List.mem_singleton] at hGi
        subst hGi
        exact ⟨rfl, hV, hL⟩
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        change G.m ≤ 2 ^ 0 * G.n
        simp only [pow_zero, one_mul]
        exact hm_le_n
      · intro j hj hj1
        simp only [List.length_singleton] at hj
        omega
      · intro j hj
        have hj0 : j = 0 := by simpa using hj
        subst hj0
        change G.edges = G.edges.filter fun _ => decide (0 = 0)
        exact (List.filter_eq_self.mpr fun _ _ => rfl).symm
      · intro j hj hj1
        simp only [List.length_singleton] at hj
        omega
      · have hsb_ge1 : 1 ≤ Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := one_le_sb hC₀.le G.m
        have hC_ge1 : 1 ≤ C_cost := by
          have : 0 ≤ 9 * B_const + K_cost * (2 + 400000) := by positivity
          dsimp only [C_cost]
          linarith
        calc (G.m : ℝ) = 1 * (G.m : ℝ) * 1 := by ring
          _ ≤ C_cost * (G.m : ℝ) * Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
                Real.log (Real.log ((G.m : ℝ) + 2) + 2)) := by
              apply mul_le_mul (mul_le_mul_of_nonneg_right hC_ge1 (Nat.cast_nonneg _))
                hsb_ge1 (by norm_num) (by positivity)
    · have hm_gt_n : G.n < G.m := Nat.lt_of_not_le hm_le_n
      have hℓ_eq : ℓ = Nat.log 2 (G.m / G.n) + 1 := by
        simp only [ℓ, decomposeEll, hm_le_n, ↓reduceIte]
      have hn_pos : 1 ≤ G.n := by
        have hm_pos : 1 ≤ G.m := by omega
        rcases List.length_pos_iff_exists_mem.mp hm_pos with ⟨e, he⟩
        have := (hV e he).1
        omega
      have hq_pos : 1 ≤ G.m / G.n := (Nat.le_div_iff_mul_le hn_pos).mpr (by omega)
      have hm_le_powℓ : G.m ≤ 2 ^ ℓ * G.n := by
        have hlt : G.m / G.n < 2 ^ ℓ := by
          rw [hℓ_eq]
          exact Nat.lt_pow_succ_log_self (by norm_num) (G.m / G.n)
        have hmul_lt : G.m / G.n * G.n < 2 ^ ℓ * G.n := Nat.mul_lt_mul_of_pos_right hlt hn_pos
        have hdiv : G.m < (G.m / G.n + 1) * G.n := by
          have := Nat.div_add_mod G.m G.n
          have := Nat.mod_lt G.m hn_pos
          nlinarith
        nlinarith
      have hpowℓ_le_2m : 2 ^ ℓ * G.n ≤ 2 * G.m := by
        have h1 : 2 ^ Nat.log 2 (G.m / G.n) ≤ G.m / G.n :=
          Nat.pow_log_le_self 2 (by omega)
        have h2 : 2 ^ ℓ = 2 * 2 ^ Nat.log 2 (G.m / G.n) := by
          rw [hℓ_eq, pow_succ']
        have h3 : (G.m / G.n) * G.n ≤ G.m := Nat.div_mul_le_self G.m G.n
        calc 2 ^ ℓ * G.n = 2 * ((2 ^ Nat.log 2 (G.m / G.n)) * G.n) := by rw [h2]; ring
          _ ≤ 2 * ((G.m / G.n) * G.n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right G.n h1)
          _ ≤ 2 * G.m := Nat.mul_le_mul_left 2 h3
      have hmmax_le : 2 * 2 ^ ℓ * G.n ≤ 4 * G.m := by rw [Nat.mul_assoc]; omega
      have hℓ_logm : ℓ ≤ Nat.log 2 (G.m + 2) + 1 := by
        rw [hℓ_eq]
        exact Nat.add_le_add_right
          (Nat.log_mono_right (le_trans (Nat.div_le_self G.m G.n) (by omega))) 1
      have hℓ_logn : G.IsSimple → ℓ ≤ 2 * Nat.log 2 (G.n + 2) + 2 := by
        intro hS
        have hm_sq : G.m ≤ G.n * G.n := isSimple_m_le_n_sq hV hS
        have hdiv_n : G.m / G.n ≤ G.n := Nat.div_le_of_le_mul hm_sq
        rw [hℓ_eq]
        have hlogn : Nat.log 2 (G.m / G.n) ≤ Nat.log 2 (G.n + 2) :=
          Nat.log_mono_right (le_trans hdiv_n (by omega : G.n ≤ G.n + 2))
        omega
      have hℓ_mul_n : ℓ * G.n ≤ G.m := by
        have h1 : ℓ ≤ G.m / G.n := by
          rw [hℓ_eq]
          exact natLog2_add_one_le_self hq_pos
        exact le_trans (Nat.mul_le_mul_right G.n h1) (Nat.div_mul_le_self G.m G.n)
      have hφ_min_spec : ∀ m' ≤ 4 * G.m, φ G.m ≤ phiB1 K cr 1 200 m' / 3 := by
        intro m' hm'
        have hφ_b_pos : 0 < phiB1 K cr 1 200 m' := phiB1_pos hK hcr (by omega) (by omega) m'
        have hsub := hsub_phi 1 200 m' (by omega) (by omega)
        have hmax_le : max ((thresholdB1 cr : ℝ) + 1) (K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤
            M_phi := by
          have heq : K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = K * 200 := by norm_num
          rw [heq]
          exact le_max_right _ _
        have hsb1 : sb C_sub m' ≤ sb C_base m' := sb_mono_C (le_max_right _ _) m'
        have hsb2 : sb C_base m' ≤ sb (9 * C_base) G.m := sb_four_mul hC_base.le hm'
        have hinv : 1 / (phiB1 K cr 1 200 m' / 3) ≤ C₁ * sb (9 * C_base) G.m := by
          calc 1 / (phiB1 K cr 1 200 m' / 3) = 3 * (1 / phiB1 K cr 1 200 m') := by ring
            _ ≤ 3 * (M_phi * sb C_sub m') := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                refine le_trans hsub (mul_le_mul_of_nonneg_right hmax_le (sb_pos _ _).le)
            _ ≤ 3 * (M_phi * sb (9 * C_base) G.m) := by
                apply mul_le_mul_of_nonneg_left _ (by norm_num)
                exact mul_le_mul_of_nonneg_left (le_trans hsb1 hsb2) (by linarith)
            _ = C₁ * sb (9 * C_base) G.m := by ring
        rw [show φ G.m = 1 / (C₁ * sb (9 * C_base) G.m) from rfl]
        have hdiv := one_div_le_one_div_of_le (one_div_pos.mpr (by linarith)) hinv
        rwa [one_div_one_div] at hdiv
      have hC_step_bound : ∀ {cG : Cited.Graph} {m_t : ℕ}, cG.m ≤ 4 * G.m → m_t ≤ 4 * G.m →
          let φ_b := phiB1 K cr 1 200 m_t
          let C_max := max 7 (Nat.ceil (4 / φ_b) + 2)
          let H_max := 4 * C_max * (Nat.log 2 (2 * cG.m + 1) + 1) + 2
          ((4 * H_max + 14) * (4 * H_max + 4) : ℝ) ≤
            B_const * sb (18 * C_base + 2) G.m := by
        intro cG m_t hcG hm_t
        dsimp only
        have hφ_pos : 0 < phiB1 K cr 1 200 m_t := phiB1_pos hK hcr (by omega) (by omega) m_t
        have hsub := hsub_phi 1 200 m_t (by omega) (by omega)
        have hmax_le : max ((thresholdB1 cr : ℝ) + 1) (K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ)) ≤
            M_phi := by
          have heq : K * ((200 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) = K * 200 := by norm_num
          rw [heq]
          exact le_max_right _ _
        have hsb_mt : sb C_sub m_t ≤ sb (9 * C_base) G.m :=
          le_trans (sb_mono_C (le_max_right _ _) m_t) (sb_four_mul hC_base.le hm_t)
        have hinv_le : 1 / phiB1 K cr 1 200 m_t ≤ M_phi * sb (9 * C_base) G.m :=
          le_trans hsub (mul_le_mul hmax_le hsb_mt (sb_pos _ _).le (by linarith))
        set S := M_phi * sb (9 * C_base) G.m
        have hS1 : 1 ≤ S := by
          have hsb1 := one_le_sb (by positivity : 0 ≤ 9 * C_base) G.m
          nlinarith
        have h4φ_le : 4 / phiB1 K cr 1 200 m_t ≤ 4 * S := by
          calc 4 / phiB1 K cr 1 200 m_t = 4 * (1 / phiB1 K cr 1 200 m_t) := by ring
            _ ≤ 4 * S := mul_le_mul_of_nonneg_left hinv_le (by norm_num)
        have hceil_lt : (Nat.ceil (4 / phiB1 K cr 1 200 m_t) : ℝ) <
            4 / phiB1 K cr 1 200 m_t + 1 := Nat.ceil_lt_add_one (by positivity)
        have hCmax_le : ((max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) : ℕ) : ℝ) ≤ 7 * S := by
          push_cast
          apply max_le (by linarith)
          linarith
        have hlog_le : ((Nat.log 2 (2 * cG.m + 1) + 1 : ℕ) : ℝ) ≤ 12 * sb 1 G.m := by
          push_cast
          exact natLog2_eight_mul_add_one_le hcG
        have hsb1_ge : 1 ≤ sb 1 G.m := one_le_sb zero_le_one G.m
        have hSsb_ge : 1 ≤ S * sb 1 G.m := by nlinarith
        have hHmax_le : ((4 * max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) *
            (Nat.log 2 (2 * cG.m + 1) + 1) + 2 : ℕ) : ℝ) ≤ 338 * (S * sb 1 G.m) := by
          push_cast
          have hprod : 4 * ((max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) : ℕ) : ℝ) *
              ((Nat.log 2 (2 * cG.m + 1) + 1 : ℕ) : ℝ) ≤ 4 * (7 * S) * (12 * sb 1 G.m) := by
            push_cast at hCmax_le hlog_le ⊢
            apply mul_le_mul (mul_le_mul_of_nonneg_left hCmax_le (by norm_num)) hlog_le
              (by positivity) (by positivity)
          push_cast at hprod
          linarith
        set H := ((4 * max 7 (Nat.ceil (4 / phiB1 K cr 1 200 m_t) + 2) *
            (Nat.log 2 (2 * cG.m + 1) + 1) + 2 : ℕ) : ℝ)
        have h4H14 : 4 * H + 14 ≤ 1366 * (S * sb 1 G.m) := by linarith
        have h4H4 : 4 * H + 4 ≤ 1366 * (S * sb 1 G.m) := by linarith
        have hH0 : 0 ≤ 4 * H + 4 := by positivity
        have hprodH : (4 * H + 14) * (4 * H + 4) ≤ (1366 * (S * sb 1 G.m)) ^ 2 := by
          calc (4 * H + 14) * (4 * H + 4) ≤ (1366 * (S * sb 1 G.m)) * (1366 * (S * sb 1 G.m)) :=
                mul_le_mul h4H14 h4H4 hH0 (by positivity)
            _ = (1366 * (S * sb 1 G.m)) ^ 2 := by ring
        have hsq_eq : (1366 * (S * sb 1 G.m)) ^ 2 = B_const * sb (18 * C_base + 2) G.m := by
          have h1 : (sb (9 * C_base) G.m * sb 1 G.m) ^ 2 = sb (18 * C_base + 2) G.m := by
            rw [sb_mul_sb, sb_sq]
            congr 1; ring
          calc (1366 * (S * sb 1 G.m)) ^ 2 =
                (1366 * M_phi) ^ 2 * (sb (9 * C_base) G.m * sb 1 G.m) ^ 2 := by
                dsimp only [S]; ring
            _ = B_const * sb (18 * C_base + 2) G.m := by rw [h1]
        exact le_trans hprodH (le_of_eq hsq_eq)
      have hφ_pos : 0 < φ G.m := div_pos one_pos (mul_pos hC₁ (sb_pos _ _))
      have hdec1200 : ∀ (G' : Cited.Graph), G'.IsValid → G'.IsLoopless →
          let label := decompModel citedOut (thresholdB1 cr) 1 200 G'
          Cited.IsExpanderDecomposition G' (1 / 200 : ℝ) (phiB1 K cr 1 200 G'.m) label ∧
            ((G'.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
              (1 / 200 : ℝ) * (G'.m : ℝ) ∧
            (decompModelCost citedCost (thresholdB1 cr) 1 200 G' : ℝ) ≤
              K_cost * (G'.n + (200 : ℝ) ^ 2 * (G'.m + 2) * sb C₀_dec G'.m) := by
        intro G' hG'V hG'L
        simpa [sb] using hdec1200_raw G' hG'V hG'L
      have hchain := decomposeChain_spec hK hcr hC₀_dec hKc hdec1200 (m_max := 4 * G.m)
        hφ_pos hC_step_bound ℓ G hV hL hm_le_powℓ (by omega) hmmax_le hφ_min_spec
      set chain := decomposeChain (decompModel citedOut (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ
      set gs := chain.1
      set pruneSteps := chain.2
      set metaOut := decomposeChainMeta (decompModel citedOut (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ
      set compsFn := metaOut.1
      set lvlFn := metaOut.2
      rw [show chain = (gs, pruneSteps) from rfl, show metaOut = (compsFn, lvlFn) from rfl] at hchain
      dsimp only at hchain
      rcases hchain with ⟨hlen, hvalid, hperm, hm_gs, hcomps, hprune, hlvl_le, hgs_edges,
        hcomps_meta, htotalCost⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · change 1 ≤ gs.length; omega
      · change gs.length - 1 = ℓ; rw [hlen, Nat.add_sub_cancel]
      · change gs.length - 1 ≤ Nat.log 2 (G.m + 2) + 1
        rw [hlen, Nat.add_sub_cancel]; exact hℓ_logm
      · intro hS
        change gs.length - 1 ≤ 2 * Nat.log 2 (G.n + 2) + 2
        rw [hlen, Nat.add_sub_cancel]
        exact hℓ_logn hS
      · change ∀ Gi ∈ gs, Gi.n = G.n ∧ Gi.IsValid ∧ Gi.IsLoopless; exact hvalid
      · change (gs.map Cited.Graph.edges).flatten.Perm G.edges; exact hperm
      · change ∀ i : ℕ, (hi : i < gs.length) → (gs[i]).m ≤ 2 ^ i * G.n; exact hm_gs
      · change ∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          ∀ X ∈ Cited.partsOf (gs[i]) (compLabels (gs[i])), 2 ≤ X.card →
            (gs[i]).IsConductanceExpanderOn X (φ G.m) ∧
            ∀ x ∈ X, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).deg x : ℝ)
        exact hcomps
      · intro e
        change lvlFn e ≤ gs.length - 1
        rw [hlen, Nat.add_sub_cancel]
        exact hlvl_le e
      · change ∀ i : ℕ, (hi : i < gs.length) →
          (gs[i]).edges = G.edges.filter fun e => decide (lvlFn e = i)
        exact hgs_edges
      · change ∀ i : ℕ, (hi : i < gs.length) → 1 ≤ i →
          (compsFn i).Pairwise Disjoint ∧
          (∀ R ∈ compsFn i, R ⊆ G.verts ∧ 2 ≤ R.card ∧
            (gs[i]).IsConductanceExpanderOn R (φ G.m) ∧
            (∀ x ∈ R, φ G.m * (2 : ℝ) ^ i ≤ ((gs[i]).degIn R x : ℝ)) ∧
            (∀ e ∈ (gs[i]).edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
          (∀ e ∈ (gs[i]).edges, ∃ R ∈ compsFn i, e.1 ∈ R ∧ e.2 ∈ R)
        exact hcomps_meta
      · have htw1 : (2 ^ (ℓ + 1) - 2) * G.n ≤ 4 * G.m := by
          have h1 : 2 ^ (ℓ + 1) - 2 ≤ 2 * 2 ^ ℓ := by rw [pow_succ']; omega
          calc (2 ^ (ℓ + 1) - 2) * G.n ≤ (2 * 2 ^ ℓ) * G.n := Nat.mul_le_mul_right G.n h1
            _ = 2 * (2 ^ ℓ * G.n) := by ring
            _ ≤ 2 * (2 * G.m) := Nat.mul_le_mul_left 2 hpowℓ_le_2m
            _ = 4 * G.m := by ring
        have htw_le : 2 * (2 ^ (ℓ + 1) - 2) * G.n ≤ 8 * G.m := by
          calc 2 * (2 ^ (ℓ + 1) - 2) * G.n = 2 * ((2 ^ (ℓ + 1) - 2) * G.n) := by ring
            _ ≤ 2 * (4 * G.m) := Nat.mul_le_mul_left 2 htw1
            _ = 8 * G.m := by ring
        have htw3_le : 3 * (2 ^ (ℓ + 1) - 2) * G.n ≤ 12 * G.m := by
          calc 3 * (2 ^ (ℓ + 1) - 2) * G.n = 3 * ((2 ^ (ℓ + 1) - 2) * G.n) := by ring
            _ ≤ 3 * (4 * G.m) := Nat.mul_le_mul_left 3 htw1
            _ = 12 * G.m := by ring
        have h9m : 2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n ≤ 9 * G.m := by omega
        have h16m : 3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n ≤ 16 * G.m := by
          have h3ℓ : 3 * ℓ * G.n = 3 * (ℓ * G.n) := by ring
          omega
        have h2ℓ : 2 * ℓ ≤ 2 * G.m := by
          calc 2 * ℓ = 2 * (ℓ * 1) := by ring
            _ ≤ 2 * (ℓ * G.n) := Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left ℓ hn_pos)
            _ ≤ 2 * G.m := Nat.mul_le_mul_left 2 hℓ_mul_n
        have h10m : 2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ ≤ 10 * G.m := by omega
        have h9mR : ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) ≤ 9 * (G.m : ℝ) := by
          exact_mod_cast h9m
        have h16mR : ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) ≤
            16 * (G.m : ℝ) := by exact_mod_cast h16m
        have h2ℓn : 2 * ℓ * G.n ≤ 2 * G.m := by rw [Nat.mul_assoc]; omega
        have h2ℓnR : ((2 * ℓ * G.n : ℕ) : ℝ) ≤ 2 * (G.m : ℝ) := by exact_mod_cast h2ℓn
        have h10mR : ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) ≤ 10 * (G.m : ℝ) := by
          exact_mod_cast h10m
        have hsb_dec : sb C₀_dec (4 * G.m) ≤ sb C₀ G.m := by
          refine le_trans (sb_mono_C (le_max_left C₀_dec C_sub) (4 * G.m)) ?_
          refine le_trans (sb_four_mul hC_base.le (le_refl (4 * G.m))) ?_
          exact sb_mono_C (by dsimp [C₀]; linarith) G.m
        have hsb0_ge : 1 ≤ sb C₀ G.m := one_le_sb hC₀.le G.m
        have hover' : ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) ≤
            16 * (G.m : ℝ) * sb C₀ G.m := by
          calc ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ)
              ≤ 16 * (G.m : ℝ) := h16mR
            _ = (16 * (G.m : ℝ)) * 1 := by ring
            _ ≤ (16 * (G.m : ℝ)) * sb C₀ G.m := mul_le_mul_of_nonneg_left hsb0_ge (by positivity)
            _ = 16 * (G.m : ℝ) * sb C₀ G.m := by ring
        have hB0 : 0 ≤ B_const := by positivity
        change (pruneSteps : ℝ) ≤ (B_const * sb C₀ G.m) *
          ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) at hprune
        have hprune' : (pruneSteps : ℝ) ≤ 9 * B_const * (G.m : ℝ) * sb C₀ G.m := by
          calc (pruneSteps : ℝ)
              ≤ (B_const * sb C₀ G.m) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + ℓ * G.n : ℕ) : ℝ) := hprune
            _ ≤ (B_const * sb C₀ G.m) * (9 * (G.m : ℝ)) :=
                mul_le_mul_of_nonneg_left h9mR (mul_nonneg hB0 (sb_pos _ _).le)
            _ = 9 * B_const * (G.m : ℝ) * sb C₀ G.m := by ring
        have hdecomp' : K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
              (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) *
                sb C₀_dec (4 * G.m)) ≤
            K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by
          have h1 : (2 : ℝ) * (G.m : ℝ) ≤ 2 * (G.m : ℝ) * sb C₀ G.m := by
            calc (2 : ℝ) * (G.m : ℝ) = (2 * (G.m : ℝ)) * 1 := by ring
              _ ≤ (2 * (G.m : ℝ)) * sb C₀ G.m := mul_le_mul_of_nonneg_left hsb0_ge (by positivity)
          have h2 : (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) *
                sb C₀_dec (4 * G.m) ≤
              400000 * (G.m : ℝ) * sb C₀ G.m := by
            calc (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) *
                  sb C₀_dec (4 * G.m)
                ≤ (40000 : ℝ) * (10 * (G.m : ℝ)) * sb C₀_dec (4 * G.m) := by
                  apply mul_le_mul_of_nonneg_right _ (sb_pos _ _).le
                  linarith
              _ ≤ (40000 : ℝ) * (10 * (G.m : ℝ)) * sb C₀ G.m := by
                  apply mul_le_mul_of_nonneg_left hsb_dec (by positivity)
              _ = 400000 * (G.m : ℝ) * sb C₀ G.m := by ring
          calc K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) *
                    sb C₀_dec (4 * G.m))
              ≤ K_cost * (2 * (G.m : ℝ) + 400000 * (G.m : ℝ) * sb C₀ G.m) := by
                apply mul_le_mul_of_nonneg_left _ hKc.le
                linarith
            _ ≤ K_cost * (2 * (G.m : ℝ) * sb C₀ G.m + 400000 * (G.m : ℝ) * sb C₀ G.m) := by
                apply mul_le_mul_of_nonneg_left (by linarith) hKc.le
            _ = K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by ring
        calc (decomposeChainCost (decompModel citedOut (thresholdB1 cr))
                (decompModelCost citedCost (thresholdB1 cr)) (phiB1 K cr 1 200) G ℓ : ℝ)
            ≤ ((3 * (2 ^ (ℓ + 1) - 2) * G.n + 3 * ℓ * G.n + G.n : ℕ) : ℝ) +
                (pruneSteps : ℝ) +
                K_cost * (((2 * ℓ * G.n : ℕ) : ℝ) +
                  (40000 : ℝ) * ((2 * (2 ^ (ℓ + 1) - 2) * G.n + 2 * ℓ : ℕ) : ℝ) *
                    sb C₀_dec (4 * G.m)) :=
              htotalCost
          _ ≤ 16 * (G.m : ℝ) * sb C₀ G.m + 9 * B_const * (G.m : ℝ) * sb C₀ G.m +
                K_cost * (2 + 400000) * (G.m : ℝ) * sb C₀ G.m := by linarith
          _ = C_cost * (G.m : ℝ) * sb C₀ G.m := by dsimp only [C_cost]; ring

/-- Twin of `MinCostFlow.Expander.exists_decomposeTool` taking `ExpanderDecompositionUsed`, with
the `RunsTo` conjunct specialized to `(a, b) = (1, 200)`. -/
theorem exists_decomposeTool_of_used (hDec : ExpanderDecompositionUsed) :
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
      (∀ G : Cited.Graph, G.IsValid → G.IsLoopless → thr ≤ G.m →
        WordRAM.RunsTo (WordRAM.wordSize c_w (G.encode ++ [1, 200, rOf G.m])) P
          (G.encode ++ [1, 200, rOf G.m]) (fun _ => false) (citedOut 1 200 G)
          (citedCost 1 200 G)) ∧
      (∀ G : Cited.Graph, G.IsValid → G.IsLoopless →
        let decomp := decompModel citedOut thr
        let decompC := decompModelCost citedCost thr
        let φ_level := phiB1 K_dec cr_dec 1 200
        let cost := decomposeModelCost decomp decompC φ_level G
        ((cost : ℝ) ≤ C_cost * (G.m : ℝ) *
          Real.exp (C₀ * Real.log ((G.m : ℝ) + 2) ^ (2 / 3 : ℝ) *
            Real.log (Real.log ((G.m : ℝ) + 2) + 2)))) := by
  classical
  rcases theorem_8_5_of_used hDec with
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
  exact hc.2.2.2.2.2.2.2.2.2.2.2

/-- Exact bridge for `MinCostFlow.Expander.exists_spannerTools`: produces the identical conclusion
of `exists_spannerTools` from `ExpanderDecompositionUsed` and `Cited.DecrementalExpanderPaths`. -/
theorem exists_spannerTools_of_used (hDec : ExpanderDecompositionUsed)
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
  rcases exists_decomposeTool_of_used hDec with
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
    hφ_mono, hφ_antiM, hγ_anti, hγ_monoM, hγ_del_eq, hγ_del, hdom_const, hdom_dec, h10_dec,
    ?_, ?_, hImpl, htot, hq, hγq⟩
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

end MinCostFlow.ExpanderDecomp
