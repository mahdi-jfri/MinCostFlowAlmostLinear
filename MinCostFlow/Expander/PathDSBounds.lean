module

public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Spanner.Embedding
public import MinCostFlow.Expander.DecrementalPaths

import MinCostFlow.Expander.GraphHelpers
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Walk Extraction and `exp(O(log^{7/8} m))` Parameter Bounds for Theorem 8.6

1. `projWalk` / `projWalk_spec`: converts any simple path `P_s` in `(subdivGraph G) \ subdivDel del \ S_s`
   between original vertices `u, v < G.n` into a `Spanner.Walk` in `G` avoiding `projSet G.n S_s`
   and deleted edges `del`, with `W.edges.length ≤ (P_s.length - 1) / 3`.
2. `qOf M`: the balancing choice `Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.log 2 (M + 2)))) + 2 = Θ(log^{1/8} M)`,
   together with `exp(O(log^{7/8}(M + 2)))` bounds for `M^{1/q}`, `csGamma Kγ (4*M)^{K q}`,
   `csTotal`, `csQuery`, and the query path-length / inverse-conductance terms of `PathDSTool`.
-/

namespace MinCostFlow.Expander

@[expose] public section

/-- Decodes a path `P_s` returned on `subdivGraph G` into a `Spanner.Walk` in `G`.
Returns `Spanner.Walk.empty` when `u = v`, and pairs `projPath G.n P_s` with `projEdges G.n P_s`
otherwise. -/
def projWalk (G : Cited.Graph) (u v : ℕ) (P_s : List ℕ) : Spanner.Walk :=
  if u = v then Spanner.Walk.empty else ⟨projPath G.n P_s, projEdges G.n P_s⟩

/-- Balancing parameter `q(M) = ⌊log₂(M + 2)^{1/8}⌋ + 2 = Θ(log^{1/8} M)` for Theorem 8.6. -/
def qOf (M : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (Nat.log 2 (M + 2)))) + 2

end

section

private lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
  exact (Real.log_le_iff_le_exp (by norm_num)).mpr this

private lemma log_add_two_ge_half (m : ℕ) : (0.5 : ℝ) ≤ Real.log ((m : ℝ) + 2) := by
  have h1 : (2 : ℝ) ≤ (m : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) m]
  have h2 : Real.log 2 ≤ Real.log ((m : ℝ) + 2) := Real.log_le_log (by norm_num) h1
  linarith [Real.log_two_gt_d9]

end

public section

/-- `projWalk_spec`: any simple path `P_s` in `subdivGraph G \ subdivDel del \ S_s` from `u` to
`v` (`u, v < G.n`) projects to a valid `u`-`v` walk `W` in `G` whose vertices avoid
`projSet G.n S_s`, whose edges lie in `(List.range G.m)` outside `del`, and whose length satisfies
`3 * W.edges.length ≤ P_s.length - 1`. -/
lemma projWalk_spec {G : Cited.Graph} (hV : G.IsValid) {q : ℕ} (del : List ℕ) (S_s : Finset ℕ)
    {u v : ℕ} (hu : u < G.n) (hv : v < G.n) {P_s : List ℕ}
    (hnd : P_s.Nodup) (hnotS : ∀ w ∈ P_s, w ∉ S_s)
    (hP : Cited.IsPathAlong
      (Cited.PrunedExpander.currentEdges ⟨subdivGraph G, q, subdivDel del, S_s⟩) u v P_s) :
    let W := projWalk G u v P_s
    W.IsWalk G u v ∧
    W.verts.Nodup ∧
    (∀ x ∈ W.verts, x ∉ projSet G.n S_s) ∧
    (∀ j ∈ W.edges, j < G.m ∧ j ∉ del) ∧
    3 * W.edges.length ≤ P_s.length - 1 := by
  by_cases huv : u = v
  · subst huv
    simp only [projWalk, ↓reduceIte]
    refine ⟨⟨hu, hu, Or.inl ⟨rfl, rfl, rfl⟩⟩, by simp [Spanner.Walk.empty],
      by simp [Spanner.Walk.empty], by simp [Spanner.Walk.empty], ?_⟩
    simp [Spanner.Walk.empty]
  · simp only [projWalk, huv, ↓reduceIte]
    have hp := projPath_spec hV del S_s hu hv hnd hnotS hP
    have he := projEdges_spec hV del S_s hu hv hnd hP
    set vs := projPath G.n P_s
    set es := projEdges G.n P_s
    have hhead : vs.head? = some u := hp.2.2.1.1
    have hlast : vs.getLast? = some v := hp.2.2.1.2.1
    have hvs_ge2 : 2 ≤ vs.length := by
      cases hvs : vs with
      | nil => simp [hvs] at hhead
      | cons a rest =>
        rw [hvs] at hhead hlast
        cases rest with
        | nil =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          exact absurd (hhead.symm.trans hlast) huv
        | cons b bs =>
          simp only [List.length_cons]
          omega
    have hes_ne : es ≠ [] := by
      intro hes0
      have := he.1
      rw [hes0] at this
      simp only [List.length_nil] at this
      omega
    have hwalk : (⟨vs, es⟩ : Spanner.Walk).IsWalk G u v := by
      refine ⟨hu, hv, Or.inr ⟨hes_ne, he.1, hhead, hlast, fun j hj => (he.2.1 j hj).1, ?_⟩⟩
      intro i hi
      exact he.2.2 i hi
    refine ⟨hwalk, hp.1, hp.2.1, he.2.1, ?_⟩
    have hlen_eq : vs.length - 1 = es.length := by omega
    rw [← hlen_eq, hp.2.2.2.1]

/-- `qOf M` is always at least `2`. -/
lemma qOf_ge_two (M : ℕ) : 2 ≤ qOf M := by
  dsimp only [qOf]
  omega

/-- `qOf` is monotone in `M`. -/
lemma qOf_mono {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) : qOf M₁ ≤ qOf M₂ := by
  dsimp only [qOf]
  have h1 : Nat.log 2 (M₁ + 2) ≤ Nat.log 2 (M₂ + 2) := Nat.log_mono_right (by omega)
  exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt (Nat.sqrt_le_sqrt h1))) 2

/-- `Real.log (M + 2) ^ (1 / 8 : ℝ) ≤ qOf M ≤ 6 * Real.log (M + 2) ^ (1 / 8 : ℝ)`. -/
lemma qOf_bounds (M : ℕ) :
    Real.log ((M : ℝ) + 2) ^ (1 / 8 : ℝ) ≤ (qOf M : ℝ) ∧
    (qOf M : ℝ) ≤ 6 * Real.log ((M : ℝ) + 2) ^ (1 / 8 : ℝ) := by
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (0.5 : ℝ) ≤ L := log_add_two_ge_half M
  have hL_pos : 0 < L := by linarith
  set k := Nat.log 2 (M + 2)
  set a₁ := Nat.sqrt k
  set a₂ := Nat.sqrt a₁
  set a₃ := Nat.sqrt a₂
  have hq_eq : qOf M = a₃ + 2 := rfl
  constructor
  · have hlt : M + 2 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) (M + 2)
    have hL_le : L ≤ ((k + 1 : ℕ) : ℝ) := by
      have hpowR : ((M : ℝ) + 2) ≤ (2 : ℝ) ^ (k + 1) := by exact_mod_cast hlt.le
      have h1 : L ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by
        calc L ≤ Real.log ((2 : ℝ) ^ (k + 1)) := Real.log_le_log (by positivity) hpowR
          _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 := Real.log_pow 2 (k + 1)
      have h2 := mul_le_mul_of_nonneg_left log_two_le_one (Nat.cast_nonneg (k + 1))
      linarith
    have hk_le8 : k + 1 ≤ (a₃ + 2) ^ 8 := by
      have h1 : k + 1 ≤ (a₁ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt k
      have h2 : a₁ + 1 ≤ (a₂ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt a₁
      have h3 : a₂ + 1 ≤ (a₃ + 1) ^ 2 := by rw [sq]; exact Nat.lt_succ_sqrt a₂
      calc k + 1 ≤ (a₁ + 1) ^ 2 := h1
        _ ≤ ((a₂ + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left h2 2
        _ = (a₂ + 1) ^ 4 := by ring
        _ ≤ ((a₃ + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left h3 4
        _ = (a₃ + 1) ^ 8 := by ring
        _ ≤ (a₃ + 2) ^ 8 := Nat.pow_le_pow_left (by omega) 8
    have hpow8 : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) ≤ (qOf M : ℝ) ^ (8 : ℕ) := by
      have hlhs : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = L := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
        norm_num
      have hrhs : ((k + 1 : ℕ) : ℝ) ≤ (qOf M : ℝ) ^ (8 : ℕ) := by
        rw [hq_eq]
        exact_mod_cast hk_le8
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) (Nat.cast_nonneg _) hpow8
  · have hk_ge_pow : 2 ^ k ≤ M + 2 := Nat.pow_log_le_self 2 (by omega)
    have hk_le : (k : ℝ) ≤ 2 * L := by
      have hpowR : (2 : ℝ) ^ k ≤ (M : ℝ) + 2 := by exact_mod_cast hk_ge_pow
      have hlog : (k : ℝ) * Real.log 2 ≤ L := by
        calc (k : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ k) := (Real.log_pow 2 k).symm
          _ ≤ L := Real.log_le_log (by positivity) hpowR
      have hl2 : (0.5 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hmul := mul_le_mul_of_nonneg_left hl2.le (Nat.cast_nonneg k)
      linarith
    have ha3_8 : a₃ ^ 8 ≤ k := by
      have h3 : a₃ ^ 2 ≤ a₂ := by rw [sq]; exact Nat.sqrt_le a₂
      have h2 : a₂ ^ 2 ≤ a₁ := by rw [sq]; exact Nat.sqrt_le a₁
      have h1 : a₁ ^ 2 ≤ k := by rw [sq]; exact Nat.sqrt_le k
      calc a₃ ^ 8 = ((a₃ ^ 2) ^ 2) ^ 2 := by ring
        _ ≤ (a₂ ^ 2) ^ 2 := Nat.pow_le_pow_left (Nat.pow_le_pow_left h3 2) 2
        _ ≤ a₁ ^ 2 := Nat.pow_le_pow_left h2 2
        _ ≤ k := h1
    have ha3_le : (a₃ : ℝ) ≤ 2 * L ^ (1 / 8 : ℝ) := by
      have hpow8 : (a₃ : ℝ) ^ (8 : ℕ) ≤ (2 * L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := by
        have ha3R : (a₃ : ℝ) ^ (8 : ℕ) ≤ (k : ℝ) := by exact_mod_cast ha3_8
        have hrhs : (2 * L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = 256 * L := by
          rw [mul_pow, ← Real.rpow_natCast (L ^ (1 / 8 : ℝ)), ← Real.rpow_mul hL_pos.le]
          norm_num
        linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) hpow8
    have hhalf : (1 / 2 : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
      have hpow8 : ((1 / 2 : ℝ)) ^ (8 : ℕ) ≤ (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := by
        have : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = L := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
          norm_num
        linarith [show ((1 / 2 : ℝ)) ^ (8 : ℕ) = 1 / 256 by norm_num]
      exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hL_pos.le _) hpow8
    rw [hq_eq]
    push_cast
    linarith

/-- `csGamma Kγ x` is monotone in `x`. -/
lemma csGamma_mono {Kγ : ℕ} {x y : ℕ} (hxy : x ≤ y) :
    Cited.csGamma Kγ x ≤ Cited.csGamma Kγ y := by
  unfold Cited.csGamma
  apply Nat.pow_le_pow_right (by norm_num)
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.sqrt_le_sqrt
  apply Nat.sqrt_le_sqrt
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.log_mono_right hxy) 1

/-- `csPhi Kγ c m` is antitone in `c`. -/
lemma csPhi_anti_c {Kγ c₁ c₂ m : ℕ} (hc₁ : 1 ≤ c₁) (hc : c₁ ≤ c₂) :
    Cited.csPhi Kγ c₂ m ≤ Cited.csPhi Kγ c₁ m := by
  unfold Cited.csPhi
  have hγ : (0 : ℝ) < (Cited.csGamma Kγ m : ℝ) := by unfold Cited.csGamma; positivity
  exact one_div_le_one_div_of_le (mul_pos (by exact_mod_cast hc₁) hγ)
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hγ.le)

/-- `csPhi Kγ c m` is antitone in `m`. -/
lemma csPhi_anti_m {Kγ c m₁ m₂ : ℕ} (hc : 1 ≤ c) (hm : m₁ ≤ m₂) :
    Cited.csPhi Kγ c m₂ ≤ Cited.csPhi Kγ c m₁ := by
  unfold Cited.csPhi
  have hγ : (0 : ℝ) < (Cited.csGamma Kγ m₁ : ℝ) := by unfold Cited.csGamma; positivity
  have hle : (Cited.csGamma Kγ m₁ : ℝ) ≤ (Cited.csGamma Kγ m₂ : ℝ) := by
    exact_mod_cast csGamma_mono hm
  exact one_div_le_one_div_of_le (mul_pos (by exact_mod_cast hc) hγ)
    (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg c))

/-- `Cited.csGamma Kγ (4 * m) ≤ exp(C_γ' · log(m + 2)^{3/4})`, proved by monotonicity from
`csGamma_le_exp_three_quarters` at `2 * m` since `4 * m ≤ 3 * (2 * m)`. -/
lemma csGamma_four_mul_le_exp_three_quarters (Kγ : ℕ) :
    ∃ C_γ' : ℝ, 0 < C_γ' ∧ ∀ m : ℕ,
      (Cited.csGamma Kγ (4 * m) : ℝ) ≤
        Real.exp (C_γ' * Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ)) := by
  rcases csGamma_le_exp_three_quarters Kγ with ⟨C_γ, hC_γ, hup⟩
  refine ⟨2 * C_γ, by positivity, ?_⟩
  intro m
  have hmono : (Cited.csGamma Kγ (4 * m) : ℝ) ≤ (Cited.csGamma Kγ (3 * (2 * m)) : ℝ) := by
    exact_mod_cast csGamma_mono (by omega : 4 * m ≤ 3 * (2 * m))
  refine le_trans hmono (le_trans (hup (2 * m)) ?_)
  rw [Real.exp_le_exp]
  have hL : (0.5 : ℝ) ≤ Real.log ((m : ℝ) + 2) := log_add_two_ge_half m
  have hlog2 : Real.log ((2 * m : ℕ) + 2 : ℝ) ≤ 2 * Real.log ((m : ℝ) + 2) := by
    have hpow : ((2 * m : ℕ) + 2 : ℝ) ≤ ((m : ℝ) + 2) ^ (2 : ℕ) := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      push_cast
      nlinarith
    calc Real.log ((2 * m : ℕ) + 2 : ℝ) ≤ Real.log (((m : ℝ) + 2) ^ (2 : ℕ)) :=
          Real.log_le_log (by positivity) hpow
      _ = 2 * Real.log ((m : ℝ) + 2) := by rw [Real.log_pow]; norm_num
  have hrpow : Real.log ((2 * m : ℕ) + 2 : ℝ) ^ (3 / 4 : ℝ) ≤
      (2 * Real.log ((m : ℝ) + 2)) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow (Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (2 * m)])) hlog2 (by norm_num)
  have hmul : (2 * Real.log ((m : ℝ) + 2)) ^ (3 / 4 : ℝ) ≤
      2 * Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by linarith)]
    have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have hnn : 0 ≤ Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
    nlinarith
  have hchain : Real.log ((2 * m : ℕ) + 2 : ℝ) ^ (3 / 4 : ℝ) ≤
      2 * Real.log ((m : ℝ) + 2) ^ (3 / 4 : ℝ) := le_trans hrpow hmul
  nlinarith

/-- `(4 * M + 4)^{1 / qOf M} ≤ exp(3 · log(M + 2)^{7/8})`. -/
lemma pow_inv_qOf_le (M : ℕ) :
    ((4 * M + 4 : ℕ) : ℝ) ^ (1 / (qOf M : ℝ)) ≤
      Real.exp (3 * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (0.5 : ℝ) ≤ L := log_add_two_ge_half M
  have hL_pos : 0 < L := by linarith
  have hq_pos : (0 : ℝ) < (qOf M : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega) (qOf_ge_two M)
  have hm_pow3 : ((4 * M + 4 : ℕ) : ℝ) ≤ ((M : ℝ) + 2) ^ (3 : ℕ) := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    have hpow : ((M : ℝ) + 2) ^ (3 : ℕ) = (M : ℝ) ^ 3 + 6 * (M : ℝ) ^ 2 + 12 * (M : ℝ) + 8 := by ring
    push_cast
    nlinarith [sq_nonneg (M : ℝ), pow_nonneg hM0 3]
  have hrpow1 : ((4 * M + 4 : ℕ) : ℝ) ^ (1 / (qOf M : ℝ)) ≤
      (((M : ℝ) + 2) ^ (3 : ℕ)) ^ (1 / (qOf M : ℝ)) :=
    Real.rpow_le_rpow (by positivity) hm_pow3 (by positivity)
  have hbase_pos : (0 : ℝ) < ((M : ℝ) + 2) ^ (3 : ℕ) := by positivity
  have hrpow2 : (((M : ℝ) + 2) ^ (3 : ℕ)) ^ (1 / (qOf M : ℝ)) =
      Real.exp (3 * L / (qOf M : ℝ)) := by
    rw [Real.rpow_def_of_pos hbase_pos, Real.log_pow]
    congr 1
    push_cast
    ring
  refine le_trans hrpow1 ?_
  rw [hrpow2, Real.exp_le_exp]
  have hL_split : L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) = L := by
    rw [← Real.rpow_add hL_pos]
    norm_num
  have hq_low := (qOf_bounds M).1
  have hdiv : L / (qOf M : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
    rw [div_le_iff₀ hq_pos]
    calc L = L ^ (7 / 8 : ℝ) * L ^ (1 / 8 : ℝ) := hL_split.symm
      _ ≤ L ^ (7 / 8 : ℝ) * (qOf M : ℝ) :=
          mul_le_mul_of_nonneg_left hq_low (Real.rpow_nonneg hL_pos.le _)
  have hmul3 : 3 * (L / (qOf M : ℝ)) ≤ 3 * L ^ (7 / 8 : ℝ) := by linarith
  calc 3 * L / (qOf M : ℝ) = 3 * (L / (qOf M : ℝ)) := by ring
    _ ≤ 3 * L ^ (7 / 8 : ℝ) := hmul3

/-- `(csGamma Kγ (4 * M))^{K_exp · qOf M} ≤ exp(C · log(M + 2)^{7/8})`. -/
lemma csGamma_pow_qOf_le (Kγ : ℕ) {K_exp : ℝ} (hK : 0 ≤ K_exp) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ,
      (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K_exp * (qOf M : ℝ)) ≤
        Real.exp (C * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases csGamma_four_mul_le_exp_three_quarters Kγ with ⟨C_γ', hC_γ', hup⟩
  refine ⟨6 * C_γ' * K_exp + 1, by positivity, ?_⟩
  intro M
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (0.5 : ℝ) ≤ L := log_add_two_ge_half M
  have hL_pos : 0 < L := by linarith
  have hγ_pos : (0 : ℝ) < (Cited.csGamma Kγ (4 * M) : ℝ) := by
    unfold Cited.csGamma; positivity
  have hq_nn : 0 ≤ K_exp * (qOf M : ℝ) := by positivity
  have h1 : (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K_exp * (qOf M : ℝ)) ≤
      (Real.exp (C_γ' * L ^ (3 / 4 : ℝ))) ^ (K_exp * (qOf M : ℝ)) :=
    Real.rpow_le_rpow hγ_pos.le (hup M) hq_nn
  have h2 : (Real.exp (C_γ' * L ^ (3 / 4 : ℝ))) ^ (K_exp * (qOf M : ℝ)) =
      Real.exp ((C_γ' * L ^ (3 / 4 : ℝ)) * (K_exp * (qOf M : ℝ))) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  refine le_trans h1 ?_
  rw [h2, Real.exp_le_exp]
  have hq_up := (qOf_bounds M).2
  have hL_mul : L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
    rw [← Real.rpow_add hL_pos]
    norm_num
  have hL78_nn : 0 ≤ L ^ (7 / 8 : ℝ) := Real.rpow_nonneg hL_pos.le _
  calc (C_γ' * L ^ (3 / 4 : ℝ)) * (K_exp * (qOf M : ℝ))
      ≤ (C_γ' * L ^ (3 / 4 : ℝ)) * (K_exp * (6 * L ^ (1 / 8 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq_up hK)
        exact mul_nonneg hC_γ'.le (Real.rpow_nonneg hL_pos.le _)
    _ = 6 * C_γ' * K_exp * (L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ)) := by ring
    _ = 6 * C_γ' * K_exp * L ^ (7 / 8 : ℝ) := by rw [hL_mul]
    _ ≤ (6 * C_γ' * K_exp + 1) * L ^ (7 / 8 : ℝ) := by nlinarith

/-- `[CS21]` total update bound on `subdivGraph G` with `q := qOf M` (`1 ≤ G.m ≤ M`, no isolated
vertices) is `O(G.m · exp(O(log(M + 2)^{7/8})))`. -/
lemma csTotal_subdiv_le_exp_seven_eighths (Kγ : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ C_tot C_lin : ℝ, 0 < C_tot ∧ 0 < C_lin ∧
      ∀ {G : Cited.Graph} {M : ℕ},
        G.IsValid → 1 ≤ G.m → G.m ≤ M → (∀ v < G.n, 1 ≤ G.deg v) →
        let G_s := subdivGraph G
        (Cited.csTotal Kγ K G_s.n G_s.m (qOf M) : ℝ) ≤
          C_lin * (G.m : ℝ) * Real.exp (C_tot * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases csGamma_pow_qOf_le Kγ hK.le with ⟨C_g, hC_g, hγ_up⟩
  refine ⟨3 + C_g, 3 * K + K + 1, by positivity, by positivity, ?_⟩
  intro G M hV hm1 hmM hnoIso
  set G_s := subdivGraph G
  have hn_le_2m : G.n ≤ 2 * G.m := by
    have hvol : G.vol G.verts = 2 * G.m := vol_verts_of_isValid hV
    have hsum : G.verts.card ≤ ∑ v ∈ G.verts, G.deg v := by
      have : G.verts.card = ∑ _v ∈ G.verts, 1 := by simp
      rw [this]
      refine Finset.sum_le_sum fun v hv => hnoIso v ?_
      simpa [Cited.Graph.verts] using hv
    have hcard : G.verts.card = G.n := by simp [Cited.Graph.verts]
    have hvol_eq : ∑ v ∈ G.verts, G.deg v = G.vol G.verts := rfl
    omega
  have hSn_le : G_s.n ≤ 4 * M := by
    have : G_s.n = G.n + 2 * G.m := subdivGraph_n G
    omega
  have hSm_eq : G_s.m = 3 * G.m := subdivGraph_m G
  have hSm_le : G_s.m + 1 ≤ 4 * M + 4 := by omega
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (0.5 : ℝ) ≤ L := log_add_two_ge_half M
  have hL_pos : 0 < L := by linarith
  have hexp_ge1 : 1 ≤ Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hL_pos.le _)
  have hGm_pos : (0 : ℝ) < (G.m : ℝ) := by exact_mod_cast hm1
  have hceil : (Cited.csTotal Kγ K G_s.n G_s.m (qOf M) : ℝ) <
      K * ((G_s.m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
        (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ)) + 1) + 1 := by
    unfold Cited.csTotal
    exact Nat.ceil_lt_add_one (by positivity)
  have hSm_pos : (0 : ℝ) < (G_s.m : ℝ) := by rw [hSm_eq]; positivity
  have hq_pos : (0 : ℝ) < (qOf M : ℝ) := by exact_mod_cast lt_of_lt_of_le (by omega) (qOf_ge_two M)
  have hrpow_split : (G_s.m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) =
      (G_s.m : ℝ) * (G_s.m : ℝ) ^ (1 / (qOf M : ℝ)) := by
    rw [Real.rpow_add hSm_pos, Real.rpow_one]
  have hbase_le : (G_s.m : ℝ) ^ (1 / (qOf M : ℝ)) ≤
      ((4 * M + 4 : ℕ) : ℝ) ^ (1 / (qOf M : ℝ)) :=
    Real.rpow_le_rpow hSm_pos.le (by exact_mod_cast (by omega : G_s.m ≤ 4 * M + 4)) (by positivity)
  have hinv_le : (G_s.m : ℝ) ^ (1 / (qOf M : ℝ)) ≤ Real.exp (3 * L ^ (7 / 8 : ℝ)) :=
    le_trans hbase_le (pow_inv_qOf_le M)
  have hγ_mono : (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ)) ≤
      (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K * (qOf M : ℝ)) := by
    apply Real.rpow_le_rpow (by unfold Cited.csGamma; positivity)
    · exact_mod_cast csGamma_mono hSn_le
    · positivity
  have hγ_exp := le_trans hγ_mono (hγ_up M)
  have hprod_exp : Real.exp (3 * L ^ (7 / 8 : ℝ)) * Real.exp (C_g * L ^ (7 / 8 : ℝ)) =
      Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hterm1 : (G_s.m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
      (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ)) ≤
      3 * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
    rw [hrpow_split]
    have hGm_le : (G_s.m : ℝ) ≤ 3 * (G.m : ℝ) := by exact_mod_cast hSm_eq.le
    calc (G_s.m : ℝ) * (G_s.m : ℝ) ^ (1 / (qOf M : ℝ)) *
          (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ))
        ≤ (3 * (G.m : ℝ)) * Real.exp (3 * L ^ (7 / 8 : ℝ)) *
            Real.exp (C_g * L ^ (7 / 8 : ℝ)) := by
          apply mul_le_mul
          · exact mul_le_mul hGm_le hinv_le (Real.rpow_nonneg hSm_pos.le _) (by positivity)
          · exact hγ_exp
          · positivity
          · positivity
      _ = 3 * (G.m : ℝ) * (Real.exp (3 * L ^ (7 / 8 : ℝ)) * Real.exp (C_g * L ^ (7 / 8 : ℝ))) := by
          ring
      _ = 3 * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by rw [hprod_exp]
  have hGm_ge1 : (1 : ℝ) ≤ (G.m : ℝ) := by exact_mod_cast hm1
  have hone : (K + 1 : ℝ) ≤ (K + 1) * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
    calc (K + 1 : ℝ) = (K + 1) * 1 * 1 := by ring
      _ ≤ (K + 1) * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hGm_ge1 (by positivity))
          hexp_ge1 (by norm_num) (by positivity)
  have hbound : K * ((G_s.m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
      (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ)) + 1) + 1 ≤
      (3 * K + K + 1) * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
    calc K * ((G_s.m : ℝ) ^ (1 + 1 / (qOf M : ℝ)) *
            (Cited.csGamma Kγ G_s.n : ℝ) ^ (K * (qOf M : ℝ)) + 1) + 1
        ≤ K * (3 * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ))) + (K + 1) := by
          linarith [mul_le_mul_of_nonneg_left hterm1 hK.le]
      _ ≤ 3 * K * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) +
            (K + 1) * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by
          nlinarith
      _ = (3 * K + K + 1) * (G.m : ℝ) * Real.exp ((3 + C_g) * L ^ (7 / 8 : ℝ)) := by ring
  exact le_trans hceil.le hbound

/-- `[CS21]` query bound `csQuery Kγ K (3 * M) (qOf M)` is `exp(O(log(M + 2)^{7/8}))`. -/
lemma csQuery_subdiv_le_exp_seven_eighths (Kγ : ℕ) {K : ℝ} (hK : 0 < K) :
    ∃ C_q C_k : ℝ, 0 < C_q ∧ 0 < C_k ∧ ∀ M : ℕ,
      (Cited.csQuery Kγ K (3 * M) (qOf M) : ℝ) ≤
        C_k * Real.exp (C_q * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  rcases csGamma_pow_qOf_le Kγ hK.le with ⟨C_g, hC_g, hγ_up⟩
  refine ⟨C_g, 2 * K + 1, hC_g, by positivity, ?_⟩
  intro M
  set L := Real.log ((M : ℝ) + 2)
  have hL_pos : 0 < L := by linarith [log_add_two_ge_half M]
  have hexp_ge1 : 1 ≤ Real.exp (C_g * L ^ (7 / 8 : ℝ)) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hC_g.le (Real.rpow_nonneg hL_pos.le _)
  have hceil : (Cited.csQuery Kγ K (3 * M) (qOf M) : ℝ) <
      K * ((Cited.csGamma Kγ (3 * M) : ℝ) ^ (K * (qOf M : ℝ)) + 1) + 1 := by
    unfold Cited.csQuery
    exact Nat.ceil_lt_add_one (by positivity)
  have hγ_mono : (Cited.csGamma Kγ (3 * M) : ℝ) ^ (K * (qOf M : ℝ)) ≤
      (Cited.csGamma Kγ (4 * M) : ℝ) ^ (K * (qOf M : ℝ)) := by
    apply Real.rpow_le_rpow (by unfold Cited.csGamma; positivity)
    · exact_mod_cast csGamma_mono (by omega : 3 * M ≤ 4 * M)
    · positivity
  have hγ_exp := le_trans hγ_mono (hγ_up M)
  calc (Cited.csQuery Kγ K (3 * M) (qOf M) : ℝ)
      ≤ K * (Real.exp (C_g * L ^ (7 / 8 : ℝ)) + 1) + 1 := by
        linarith [mul_le_mul_of_nonneg_left (add_le_add_right hγ_exp 1) hK.le]
    _ ≤ K * (Real.exp (C_g * L ^ (7 / 8 : ℝ)) + Real.exp (C_g * L ^ (7 / 8 : ℝ))) +
          1 * Real.exp (C_g * L ^ (7 / 8 : ℝ)) := by
        nlinarith
    _ = (2 * K + 1) * Real.exp (C_g * L ^ (7 / 8 : ℝ)) := by ring

/-- Both the `[CS21]` query path bound `(csGamma Kγ (3*M))^{max K 1 · qOf M}` and the fallback
BFS diameter bound `(25 · (log(2*M + 2) + 1) · c · csGamma Kγ (3*M) / 10)` are bounded by
`exp(C · log(M + 2)^{7/8})`. -/
lemma pathDS_gamma_exp_seven_eighths (Kγ c : ℕ) (K : ℝ) :
    ∃ C_p : ℝ, 0 < C_p ∧ ∀ M : ℕ,
      (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) / 10) ≤
        Real.exp (C_p * Real.log ((M : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  have hKmax : 0 ≤ max K 1 := le_trans zero_le_one (le_max_right K 1)
  rcases csGamma_pow_qOf_le Kγ hKmax with ⟨C_g, hC_g, hγ_up⟩
  rcases csGamma_le_exp_three_quarters Kγ with ⟨C_γ, hC_γ, hγ34⟩
  set C_c : ℝ := (Real.log (3 * ((c : ℝ) + 1)) + 20) * 2
  set C_p : ℝ := max C_g (2 * C_γ + C_c)
  refine ⟨C_p, lt_of_lt_of_le hC_g (le_max_left _ _), ?_⟩
  intro M
  set L := Real.log ((M : ℝ) + 2)
  have hL_ge : (0.5 : ℝ) ≤ L := log_add_two_ge_half M
  have hL_pos : 0 < L := by linarith
  have hL78_pos : 0 < L ^ (7 / 8 : ℝ) := Real.rpow_pos_of_pos hL_pos _
  have hL78_ge_half : (1 / 2 : ℝ) ≤ L ^ (7 / 8 : ℝ) := by
    have hpow : (1 / 2 : ℝ) ^ (8 : ℕ) ≤ (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) := by
      have hr8 : (L ^ (7 / 8 : ℝ)) ^ (8 : ℕ) = L ^ (7 : ℕ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]
        norm_num
      have hLpow : (1 / 2 : ℝ) ^ (7 : ℕ) ≤ L ^ (7 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith : (1 / 2 : ℝ) ≤ L) 7
      have : (1 / 2 : ℝ) ^ (8 : ℕ) ≤ (1 / 2 : ℝ) ^ (7 : ℕ) := by norm_num
      linarith
    exact le_of_pow_le_pow_left₀ (by decide : (8 : ℕ) ≠ 0) hL78_pos.le hpow
  constructor
  · have hγ_mono : (Cited.csGamma Kγ (3 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)) ≤
        (Cited.csGamma Kγ (4 * M) : ℝ) ^ (max K 1 * (qOf M : ℝ)) := by
      apply Real.rpow_le_rpow (by unfold Cited.csGamma; positivity)
      · exact_mod_cast csGamma_mono (by omega : 3 * M ≤ 4 * M)
      · positivity
    have h1 := le_trans hγ_mono (hγ_up M)
    have hexp : C_g * L ^ (7 / 8 : ℝ) ≤ C_p * L ^ (7 / 8 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hL78_pos.le
    exact le_trans h1 (Real.exp_le_exp.mpr hexp)
  · have hlog2M : Real.log (2 * (M : ℝ) + 2) ≤ 3 * L := by
      have h2m : 2 * (M : ℝ) + 2 ≤ ((M : ℝ) + 2) ^ (2 : ℕ) := by
        have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
        nlinarith
      calc Real.log (2 * (M : ℝ) + 2) ≤ Real.log (((M : ℝ) + 2) ^ (2 : ℕ)) :=
            Real.log_le_log (by positivity) h2m
        _ = 2 * L := by rw [Real.log_pow]; simp [L]
        _ ≤ 3 * L := by linarith
    have hfac_le : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10) ≤
        13 * ((c : ℝ) + 1) * L := by
      have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
      have hlog1 : Real.log (2 * (M : ℝ) + 2) + 1 ≤ 5 * L := by linarith
      have hmul : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10) ≤
          25 * (5 * L) * ((c : ℝ) / 10) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlog1 (by norm_num)
      nlinarith [mul_nonneg hc0 hL_pos.le]
    have hL_le_exp : L ≤ Real.exp (2 * L ^ (7 / 8 : ℝ)) := by
      have h1 : Real.log (L ^ (7 / 8 : ℝ)) ≤ L ^ (7 / 8 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos hL78_pos
      have h2 : Real.log (L ^ (7 / 8 : ℝ)) = (7 / 8 : ℝ) * Real.log L :=
        Real.log_rpow hL_pos _
      have h3 : Real.log L ≤ 2 * L ^ (7 / 8 : ℝ) := by linarith [hL78_pos.le]
      calc L = Real.exp (Real.log L) := (Real.exp_log hL_pos).symm
        _ ≤ Real.exp (2 * L ^ (7 / 8 : ℝ)) := Real.exp_le_exp.mpr h3
    have h25_le_exp : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10) ≤
        Real.exp (C_c * L ^ (7 / 8 : ℝ)) := by
      have hc1_pos : (0 : ℝ) < 3 * ((c : ℝ) + 1) := by positivity
      have he4 : (16 : ℝ) ≤ Real.exp 4 := by
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)]
        have hpow : (2 : ℝ) ^ (4 : ℕ) ≤ (Real.exp 1) ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) he1 4
        have hexp4 : Real.exp ((4 : ℕ) : ℝ) = (Real.exp 1) ^ (4 : ℕ) := by
          rw [← Real.exp_nat_mul]; simp
        norm_num at hpow hexp4 ⊢
        linarith
      have hc_le : 13 * ((c : ℝ) + 1) ≤ Real.exp (Real.log (3 * ((c : ℝ) + 1)) + 4) := by
        rw [Real.exp_add, Real.exp_log hc1_pos]
        nlinarith [show (0 : ℝ) ≤ (c : ℝ) + 1 by positivity]
      have hprod : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10) ≤
          Real.exp (Real.log (3 * ((c : ℝ) + 1)) + 4 + 2 * L ^ (7 / 8 : ℝ)) := by
        rw [Real.exp_add]
        calc 25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10)
            ≤ 13 * ((c : ℝ) + 1) * L := hfac_le
          _ ≤ Real.exp (Real.log (3 * ((c : ℝ) + 1)) + 4) * Real.exp (2 * L ^ (7 / 8 : ℝ)) :=
              mul_le_mul hc_le hL_le_exp hL_pos.le (by positivity)
      have hexp_c : Real.log (3 * ((c : ℝ) + 1)) + 4 + 2 * L ^ (7 / 8 : ℝ) ≤
          C_c * L ^ (7 / 8 : ℝ) := by
        have hlg_nn : 0 ≤ Real.log (3 * ((c : ℝ) + 1)) := by
          apply Real.log_nonneg
          have : (0 : ℝ) ≤ c := Nat.cast_nonneg c
          linarith
        dsimp only [C_c]
        nlinarith
      exact le_trans hprod (Real.exp_le_exp.mpr hexp_c)
    have hL34_le : L ^ (3 / 4 : ℝ) ≤ 2 * L ^ (7 / 8 : ℝ) := by
      have h18_ge : (1 / 2 : ℝ) ≤ L ^ (1 / 8 : ℝ) := by
        have hpow : (1 / 2 : ℝ) ^ (8 : ℕ) ≤ (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) := by
          have : (L ^ (1 / 8 : ℝ)) ^ (8 : ℕ) = L := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL_pos.le]; norm_num
          linarith [show ((1 / 2 : ℝ)) ^ (8 : ℕ) = 1 / 256 by norm_num]
        exact le_of_pow_le_pow_left₀ (by decide : (8 : ℕ) ≠ 0) (Real.rpow_nonneg hL_pos.le _) hpow
      have hmul : L ^ (3 / 4 : ℝ) * (1 / 2) ≤ L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left h18_ge (Real.rpow_nonneg hL_pos.le _)
      have hadd : L ^ (3 / 4 : ℝ) * L ^ (1 / 8 : ℝ) = L ^ (7 / 8 : ℝ) := by
        rw [← Real.rpow_add hL_pos]; norm_num
      linarith
    have hγ_le' : (Cited.csGamma Kγ (3 * M) : ℝ) ≤ Real.exp (2 * C_γ * L ^ (7 / 8 : ℝ)) := by
      refine le_trans (hγ34 M) (Real.exp_le_exp.mpr ?_)
      nlinarith
    have hmul_eq : 25 * (Real.log (2 * (M : ℝ) + 2) + 1) *
        ((c : ℝ) * (Cited.csGamma Kγ (3 * M) : ℝ) / 10) =
        (25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10)) *
          (Cited.csGamma Kγ (3 * M) : ℝ) := by ring
    rw [hmul_eq]
    calc (25 * (Real.log (2 * (M : ℝ) + 2) + 1) * ((c : ℝ) / 10)) *
          (Cited.csGamma Kγ (3 * M) : ℝ)
        ≤ Real.exp (C_c * L ^ (7 / 8 : ℝ)) * Real.exp (2 * C_γ * L ^ (7 / 8 : ℝ)) := by
          apply mul_le_mul h25_le_exp hγ_le' (by unfold Cited.csGamma; positivity) (Real.exp_pos _).le
      _ = Real.exp ((2 * C_γ + C_c) * L ^ (7 / 8 : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (C_p * L ^ (7 / 8 : ℝ)) := by
          rw [Real.exp_le_exp]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hL78_pos.le

end

end MinCostFlow.Expander
