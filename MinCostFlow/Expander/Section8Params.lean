module

public import MinCostFlow.Expander.Section8Bound
public import MinCostFlow.Expander.ExpanderDecomp
public import MinCostFlow.Expander.PathDSBounds
public import MinCostFlow.Statement.Cited.ChuzhoyEtAl
public import MinCostFlow.Statement.Cited.ChuzhoySaranurak
public import MinCostFlow.Spanner.Runtime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 8.2 Concrete Parameter Choice and `m = 2^64` Evaluation

Exports the final Section 8 dynamic-spanner theorems and concrete numerical check at `m = 2^64`
built atop `Section8Static.lean` (`Theorem 8.1`), `Section8Asymptotics.lean` (`chosenL`), and
`Section8Bound.lean` (`theorem_8_2_absorbed_at`):

* `theorem_8_2_concrete_of_poly`: Concrete Theorem 8.2 (page 39) with `L = chosenL mMax` under any
  polynomial vertex/split cap `G₀.n + splitBound ≤ C_n * (mMax + 2)^{r_n}`, giving subpolynomial
  factor `exp(C_dyn * log(mMax + 2)^{23/24})` (`a = 23 / 24 < 1`).
* `theorem_8_2_concrete`: Unconditional Concrete Theorem 8.2 (page 39) at scale parameter
  `M = max mMax (G₀.n + splitBound)` and `L = chosenL M`, with no hypothesis on `splitBound`.
* `section8_params_at_2_pow_64`: Evaluates `qOf (2 ^ 64) = 3`, `rOf (2 ^ 64) = 4`,
  `Spanner.capEta2 (2 ^ 64) = 131`, `chosenL (2 ^ 64) = 2`, `32 < log(2 ^ 64 + 2) ≤ 65`,
  `csGamma Kγ (3 * 2 ^ 64) = 2 ^ (24 * Kγ)`, `csPhi Kγ c (3 * 2 ^ 64)`, and instantiates both
  `theorem_8_1_concrete` and `theorem_8_2_concrete_of_poly` at `mMax = 2 ^ 64`.
-/

namespace MinCostFlow.Expander

private lemma nat_log2_eq_of_bounds {n k : ℕ} (h1 : 2 ^ k ≤ n) (h2 : n < 2 ^ (k + 1)) :
    Nat.log 2 n = k := by
  have hle : k ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) h1
  have hlt : Nat.log 2 n < k + 1 := Nat.log_lt_of_lt_pow (by omega) h2
  omega

private lemma nat_sqrt_eq_of_bounds {n r : ℕ} (h1 : r ^ 2 ≤ n) (h2 : n < (r + 1) ^ 2) :
    Nat.sqrt n = r := by
  have hle := Nat.sqrt_le n
  have hlt := Nat.lt_succ_sqrt n
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : (Nat.sqrt n + 1) * (Nat.sqrt n + 1) ≤ r * r := Nat.mul_le_mul h h
    nlinarith only [h1, hlt, this]
  · have : (r + 1) * (r + 1) ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul h h
    nlinarith only [h2, hle, this]

public section

noncomputable section

lemma log_at_2_pow_64 :
    32 < Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ∧ Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ≤ 65 := by
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h32_exp : Real.exp 32 < ((2 ^ 64 : ℕ) : ℝ) + 2 := by
    calc Real.exp 32 = (Real.exp 1) ^ 32 := by rw [← Real.exp_nat_mul]; norm_num
      _ < (4 : ℝ) ^ 32 := by gcongr
      _ < ((2 ^ 64 : ℕ) : ℝ) + 2 := by norm_num
  have hlt : 32 < Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) := by
    have h := Real.log_lt_log (Real.exp_pos 32) h32_exp
    rwa [Real.log_exp] at h
  have h65_exp : ((2 ^ 64 : ℕ) : ℝ) + 2 ≤ Real.exp 65 := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    calc ((2 ^ 64 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ 65 := by norm_num
      _ ≤ (Real.exp 1) ^ 65 := pow_le_pow_left₀ (by norm_num) h2e 65
      _ = Real.exp 65 := by rw [← Real.exp_nat_mul]; norm_num
  have hle : Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ≤ 65 := by
    have h := Real.log_le_log (by positivity) h65_exp
    rwa [Real.log_exp] at h
  exact ⟨hlt, hle⟩

lemma chosenL_at_2_pow_64 : chosenL (2 ^ 64) = 2 := by
  have hexp1 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp1_lt : Real.exp 1 < ((2 ^ 64 : ℕ) : ℝ) + 2 :=
    lt_trans hexp1 (by norm_num)
  have h1_lt_log : (1 : ℝ) < Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) := by
    have h := Real.log_lt_log (Real.exp_pos 1) hexp1_lt
    rwa [Real.log_exp] at h
  have h1_lt_rpow : (1 : ℝ) < Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) := by
    have h := Real.rpow_lt_rpow zero_le_one h1_lt_log (by norm_num : (0 : ℝ) < 1 / 24)
    rwa [Real.one_rpow] at h
  have hexp24 : ((2 ^ 64 : ℕ) : ℝ) + 2 ≤ Real.exp ((2 : ℝ) ^ 24) := by
    have h65 : ((2 ^ 64 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ 65 := by norm_num
    have hpow : (2 : ℝ) ^ 65 ≤ (2 : ℝ) ^ (2 ^ 24) :=
      pow_le_pow_right₀ (by norm_num) (by norm_num : 65 ≤ 2 ^ 24)
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1 : ℝ)]
    have h24 : ((2 ^ 24 : ℕ) : ℝ) = (2 : ℝ) ^ 24 := by norm_num
    calc ((2 ^ 64 : ℕ) : ℝ) + 2 ≤ (2 : ℝ) ^ 65 := h65
      _ ≤ (2 : ℝ) ^ (2 ^ 24) := hpow
      _ ≤ (Real.exp 1) ^ (2 ^ 24) := pow_le_pow_left₀ (by norm_num) h2e (2 ^ 24)
      _ = Real.exp ((2 : ℝ) ^ 24) := by rw [← Real.exp_nat_mul, mul_one, h24]
  have hlog_le_24 : Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ≤ (2 : ℝ) ^ (24 : ℝ) := by
    have h := Real.log_le_log (by positivity) hexp24
    rw [Real.log_exp] at h
    exact le_trans h (le_of_eq (by norm_num))
  have hrpow_le_2 : Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ) ≤ 2 := by
    calc Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (1 / 24 : ℝ)
        ≤ ((2 : ℝ) ^ (24 : ℝ)) ^ (1 / 24 : ℝ) :=
          Real.rpow_le_rpow (by linarith only [h1_lt_log]) hlog_le_24 (by norm_num)
      _ = (2 : ℝ) ^ ((24 : ℝ) * (1 / 24 : ℝ)) := by rw [← Real.rpow_mul (by norm_num)]
      _ = 2 := by norm_num
  unfold chosenL
  exact (Nat.ceil_eq_iff (by norm_num : 2 ≠ 0)).mpr
    ⟨by push_cast; linarith only [h1_lt_rpow], by push_cast; exact hrpow_le_2⟩

/-- **Concrete Theorem 8.2 (page 39) under polynomial vertex bound**:
connects `theorem_8_1_concrete` (`Section8Static.lean`) and `DynSpanner.theorem_8_2` with
`L = chosenL mMax = ⌈(log (mMax + 2))^{1/24}⌉`. For every `(C_n, r_n)` with `nMax = G₀.n + splitBound
≤ C_n * (mMax + 2)^{r_n}`, all nine dynamic-spanner bounds hold with `exp(C_dyn * log(mMax + 2)^{23/24})`
(`a = 23 / 24 < 1`), preserving `G₀.maxDeg` separation in congestion and runtime. -/
theorem theorem_8_2_concrete_of_poly
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧ K_s = 1 + 36 / Real.log 2 ∧ 0 ≤ K_s ∧ 0 ≤ K_t ∧
      (∀ mMax : ℕ, (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧ (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      (∀ (C_n r_n : ℝ), 0 < C_n → 0 ≤ r_n →
        ∃ C_dyn : ℝ, 0 < C_dyn ∧
        ∀ {G₀ : MGraph} {mMax splitBound : ℕ} {Us : List (List Update)},
          G₀.IsValid → G₀.m ≤ mMax →
          ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * ((mMax : ℝ) + 2) ^ r_n →
          G₀.BatchIsValid Us.flatten →
          (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
          DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
          let L := chosenL mMax
          let nMax := G₀.n + splitBound
          let q := DynSpanner.phaseBase nMax L
          let initOut := DynSpanner.init G₀ L q sparsify
          let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
          let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
          let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
          let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
            | some U => ((st t').G.batchEnc U : ℝ)
            | none => 0
          let B := Real.exp (C_dyn * Real.log ((mMax : ℝ) + 2) ^ (23 / 24 : ℝ))
          ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
          ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
          (∀ t ≤ Us.length,
            (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
            (st t).G.IsSubgraph (st t).H ∧
            ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
            Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
            (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
            Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
              B * (G₀.maxDeg : ℝ)) ∧
          (∀ t < Us.length, ∀ U, Us[t]? = some U →
            res t = DynSpanner.update
                (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten
                  (DynSpanner.batchPrefixLen Us t))
                U sparsify ∧
            (res t).state = st (t + 1) ∧
            (st t).H.BatchIsValid (res t).UH ∧
            (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
            (res t).D ⊆ (st (t + 1)).H.E ∧
            (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
              eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
              eH ∉ (res t).D →
              eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
          (∀ t ≤ Us.length,
            (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
            (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
              B * ((G₀.n : ℝ) + batchTotal t)) ∧
            (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
            (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
              B * ((G₀.maxDeg : ℝ) + 1) * encTotal t))) := by
  obtain ⟨sparsify, params, C_γ, K_s, K_t, hCγ, hKs_eq, hKs, hKt, hSpecAll⟩ :=
    theorem_8_1_concrete hDec hPaths
  refine ⟨sparsify, params, C_γ, K_s, K_t, hCγ, hKs_eq, hKs, hKt, hSpecAll, ?_⟩
  intro C_n r_n hCn hrn
  let C_n' : ℝ := max C_n 1
  let r_n' : ℝ := max r_n 1
  have hCn' : 1 ≤ C_n' := le_max_right C_n 1
  have hrn' : 1 ≤ r_n' := le_max_right r_n 1
  obtain ⟨hCdyn_pos, hAll⟩ :=
    theorem_8_2_absorbed_at hCγ hKs hKt hCn' hrn' hSpecAll
  refine ⟨_, hCdyn_pos, ?_⟩
  intro G₀ mMax splitBound Us hVG₀ hGm₀ hnCap hBV hds hSplits
  have hm2_ge1 : (1 : ℝ) ≤ (mMax : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) mMax]
  have hnCap' : ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n' * ((mMax : ℝ) + 2) ^ r_n' := by
    have hpow : ((mMax : ℝ) + 2) ^ r_n ≤ ((mMax : ℝ) + 2) ^ r_n' :=
      Real.rpow_le_rpow_of_exponent_le hm2_ge1 (le_max_left r_n 1)
    have hrn_nn : 0 ≤ ((mMax : ℝ) + 2) ^ r_n' := Real.rpow_nonneg (by linarith only [hm2_ge1]) _
    calc ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * ((mMax : ℝ) + 2) ^ r_n := hnCap
      _ ≤ C_n * ((mMax : ℝ) + 2) ^ r_n' := mul_le_mul_of_nonneg_left hpow hCn.le
      _ ≤ C_n' * ((mMax : ℝ) + 2) ^ r_n' := mul_le_mul_of_nonneg_right (le_max_left C_n 1) hrn_nn
  exact hAll hVG₀ hGm₀ le_rfl hnCap' hBV hds hSplits

/-- **Unconditional Concrete Theorem 8.2 (page 39)**:
at scale parameter `M := max mMax (G₀.n + splitBound)` and depth `L = chosenL M`, every valid
initial graph `G₀` and deletion/split batch sequence satisfies all nine dynamic-spanner bounds
with `exp(C_dyn * log(M + 2) ^ (23 / 24))` (`a = 23 / 24 < 1`), with no extra bound on `G₀.n` or
`splitBound`. Each `GetPath` of the path data structure is charged its query time `γ_query`, so the
static sparsifier carries the time factor `γ_t ≤ exp(C_q · log^{8/9}(mMax + 2) ·
log(log(mMax + 2) + 2)^{4/3})`; since `8/9 < 23/24` it is absorbed into `C_dyn`. -/
theorem theorem_8_2_concrete
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_q C_dyn : ℝ),
      0 < C_γ ∧ K_s = 1 + 36 / Real.log 2 ∧ 0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_q ∧ 0 < C_dyn ∧
      (∀ mMax : ℕ, (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧ (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_t ≤ Real.exp (C_q * Real.log ((mMax : ℝ) + 2) ^ (8 / 9 : ℝ) *
          Real.log (Real.log ((mMax : ℝ) + 2) + 2) ^ (4 / 3 : ℝ)) ∧
        DynSpanner.SparsifySpecWithTime mMax (params mMax) sparsify) ∧
      (∀ {G₀ : MGraph} {mMax splitBound : ℕ} {Us : List (List Update)},
        G₀.IsValid → G₀.m ≤ mMax →
        G₀.BatchIsValid Us.flatten →
        (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
        DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
        let M := max mMax (G₀.n + splitBound)
        let L := chosenL M
        let nMax := G₀.n + splitBound
        let q := DynSpanner.phaseBase nMax L
        let initOut := DynSpanner.init G₀ L q sparsify
        let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
        let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
        let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
        let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
          | some U => ((st t').G.batchEnc U : ℝ)
          | none => 0
        let B := Real.exp (C_dyn * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
        ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
        ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
        (∀ t ≤ Us.length,
          (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
          (st t).G.IsSubgraph (st t).H ∧
          ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
          Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
          (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
          Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
            B * (G₀.maxDeg : ℝ)) ∧
        (∀ t < Us.length, ∀ U, Us[t]? = some U →
          res t = DynSpanner.update
              (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten
                (DynSpanner.batchPrefixLen Us t))
              U sparsify ∧
          (res t).state = st (t + 1) ∧
          (st t).H.BatchIsValid (res t).UH ∧
          (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
          (res t).D ⊆ (st (t + 1)).H.E ∧
          (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
            eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
            eH ∉ (res t).D →
            eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
        (∀ t ≤ Us.length,
          (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
          (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
            B * ((G₀.n : ℝ) + batchTotal t)) ∧
          (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
          (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
            B * ((G₀.maxDeg : ℝ) + 1) * encTotal t))) := by
  obtain ⟨sparsify, params, C_γ, K_s, K_t, C_q, hCγ, hKs_eq, hKs, hKt, hCq, hSpecAll⟩ :=
    theorem_8_1_concrete_with_time hDec hPaths
  obtain ⟨hCdyn_pos, hAll⟩ :=
    theorem_8_2_absorbed_at_with_time (C_n := 1) (r_n := 1) hCγ hKs hKt hCq.le (le_refl 1)
      (le_refl 1) hSpecAll
  refine ⟨sparsify, params, C_γ, K_s, K_t, C_q, _, hCγ, hKs_eq, hKs, hKt, hCq, hCdyn_pos,
    hSpecAll, ?_⟩
  intro G₀ mMax splitBound Us hVG₀ hGm₀ hBV hds hSplits
  have hn_le : ((G₀.n + splitBound : ℕ) : ℝ) ≤
      1 * (((max mMax (G₀.n + splitBound) : ℕ) : ℝ) + 2) ^ (1 : ℝ) := by
    have h1 : G₀.n + splitBound ≤ max mMax (G₀.n + splitBound) :=
      le_max_right mMax (G₀.n + splitBound)
    have h2 : ((G₀.n + splitBound : ℕ) : ℝ) ≤ ((max mMax (G₀.n + splitBound) : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [one_mul, Real.rpow_one]
    linarith only [h2]
  exact hAll hVG₀ hGm₀ (le_max_left mMax (G₀.n + splitBound)) hn_le hBV hds hSplits

/-- **Unconditional Concrete Theorem 8.2 (page 39), with each `GetPath` charged `γ_ExpPath`**
(built on `theorem_8_1_concrete`; see `theorem_8_2_concrete` for the query time of Theorem 8.6):
at scale parameter `M := max mMax (G₀.n + splitBound)` and depth `L = chosenL M`, every valid
initial graph `G₀` and deletion/split batch sequence satisfies all nine dynamic-spanner bounds
with `exp(C_dyn * log(M + 2) ^ (23 / 24))` (`a = 23 / 24 < 1`), with no extra bound on `G₀.n` or
`splitBound`. -/
theorem theorem_8_2_concrete_cs
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths) :
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t C_dyn : ℝ),
      0 < C_γ ∧ K_s = 1 + 36 / Real.log 2 ∧ 0 ≤ K_s ∧ 0 ≤ K_t ∧ 0 < C_dyn ∧
      (∀ mMax : ℕ, (params mMax).K_s = K_s ∧ (params mMax).p_s = 1 ∧
        (params mMax).K_t = K_t ∧ (params mMax).p_t = 1 ∧
        (params mMax).γ_ℓ ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        (params mMax).γ_c ≤ Real.exp (C_γ * Real.log ((mMax : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
        DynSpanner.SparsifySpec mMax (params mMax) sparsify) ∧
      (∀ {G₀ : MGraph} {mMax splitBound : ℕ} {Us : List (List Update)},
        G₀.IsValid → G₀.m ≤ mMax →
        G₀.BatchIsValid Us.flatten →
        (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
        DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
        let M := max mMax (G₀.n + splitBound)
        let L := chosenL M
        let nMax := G₀.n + splitBound
        let q := DynSpanner.phaseBase nMax L
        let initOut := DynSpanner.init G₀ L q sparsify
        let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
        let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
        let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
        let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
          | some U => ((st t').G.batchEnc U : ℝ)
          | none => 0
        let B := Real.exp (C_dyn * Real.log ((M : ℝ) + 2) ^ (23 / 24 : ℝ))
        ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
        ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
        (∀ t ≤ Us.length,
          (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
          (st t).G.IsSubgraph (st t).H ∧
          ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
          Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
          (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
          Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
            B * (G₀.maxDeg : ℝ)) ∧
        (∀ t < Us.length, ∀ U, Us[t]? = some U →
          res t = DynSpanner.update
              (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten
                (DynSpanner.batchPrefixLen Us t))
              U sparsify ∧
          (res t).state = st (t + 1) ∧
          (st t).H.BatchIsValid (res t).UH ∧
          (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
          (res t).D ⊆ (st (t + 1)).H.E ∧
          (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
            eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
            eH ∉ (res t).D →
            eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
        (∀ t ≤ Us.length,
          (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
          (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
            B * ((G₀.n : ℝ) + batchTotal t)) ∧
          (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
          (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
            B * ((G₀.maxDeg : ℝ) + 1) * encTotal t))) := by
  obtain ⟨sparsify, params, C_γ, K_s, K_t, hCγ, hKs_eq, hKs, hKt, hSpecAll⟩ :=
    theorem_8_1_concrete hDec hPaths
  obtain ⟨hCdyn_pos, hAll⟩ :=
    theorem_8_2_absorbed_at (C_n := 1) (r_n := 1) hCγ hKs hKt (le_refl 1) (le_refl 1) hSpecAll
  refine ⟨sparsify, params, C_γ, K_s, K_t, _, hCγ, hKs_eq, hKs, hKt, hCdyn_pos, hSpecAll, ?_⟩
  intro G₀ mMax splitBound Us hVG₀ hGm₀ hBV hds hSplits
  have hn_le : ((G₀.n + splitBound : ℕ) : ℝ) ≤
      1 * (((max mMax (G₀.n + splitBound) : ℕ) : ℝ) + 2) ^ (1 : ℝ) := by
    have h1 : G₀.n + splitBound ≤ max mMax (G₀.n + splitBound) :=
      le_max_right mMax (G₀.n + splitBound)
    have h2 : ((G₀.n + splitBound : ℕ) : ℝ) ≤ ((max mMax (G₀.n + splitBound) : ℕ) : ℝ) := by
      exact_mod_cast h1
    rw [one_mul, Real.rpow_one]
    linarith only [h2]
  exact hAll hVG₀ hGm₀ (le_max_left mMax (G₀.n + splitBound)) hn_le hBV hds hSplits

/-- **Concrete evaluation at `m = 2 ^ 64`**:
evaluates all Section 8 parameters (`qOf (2 ^ 64) = 3`, `rOf (2 ^ 64) = 4`,
`capEta2 (2 ^ 64) = 131`, `chosenL (2 ^ 64) = 2`, `32 < log(2 ^ 64 + 2) ≤ 65`,
`csGamma Kγ (3 * 2 ^ 64) = 2 ^ (24 * Kγ)`, `csPhi Kγ c (3 * 2 ^ 64)`) and instantiates both the
static sparsifier (`theorem_8_1_concrete`) and the dynamic spanner (`theorem_8_2_concrete_of_poly`)
at `mMax = 2 ^ 64`. -/
theorem section8_params_at_2_pow_64
    (hDec : Cited.ExpanderDecomposition)
    (hPaths : Cited.DecrementalExpanderPaths) :
    qOf (2 ^ 64) = 3 ∧
    rOf (2 ^ 64) = 4 ∧
    Spanner.capEta2 (2 ^ 64) = 131 ∧
    chosenL (2 ^ 64) = 2 ∧
    (32 < Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ∧ Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ≤ 65) ∧
    (∀ Kγ : ℕ, Cited.csGamma Kγ (3 * 2 ^ 64) = 2 ^ (24 * Kγ)) ∧
    (∀ Kγ c : ℕ, Cited.csPhi Kγ c (3 * 2 ^ 64) = 1 / ((c : ℝ) * ((2 ^ (24 * Kγ) : ℕ) : ℝ))) ∧
    ∃ (sparsify : MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
      (params : ℕ → DynSpanner.SparsifyParams) (C_γ K_s K_t : ℝ),
      0 < C_γ ∧ K_s = 1 + 36 / Real.log 2 ∧
      (params (2 ^ 64)).K_s = K_s ∧ (params (2 ^ 64)).p_s = 1 ∧
      (params (2 ^ 64)).K_t = K_t ∧ (params (2 ^ 64)).p_t = 1 ∧
      (params (2 ^ 64)).γ_ℓ ≤ Real.exp (C_γ * Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params (2 ^ 64)).γ_c ≤ Real.exp (C_γ * Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      DynSpanner.SparsifySpec (2 ^ 64) (params (2 ^ 64)) sparsify ∧
      (∀ (C_n r_n : ℝ), 0 < C_n → 0 ≤ r_n →
        ∃ C_dyn : ℝ, 0 < C_dyn ∧
        ∀ {G₀ : MGraph} {splitBound : ℕ} {Us : List (List Update)},
          G₀.IsValid → G₀.m ≤ 2 ^ 64 →
          ((G₀.n + splitBound : ℕ) : ℝ) ≤ C_n * (((2 ^ 64 : ℕ) : ℝ) + 2) ^ r_n →
          G₀.BatchIsValid Us.flatten →
          (∀ u ∈ Us.flatten, DynSpanner.isDelOrSplit u) →
          DynSpanner.batchSplitCount Us.flatten ≤ splitBound →
          let L := 2
          let nMax := G₀.n + splitBound
          let q := DynSpanner.phaseBase nMax L
          let initOut := DynSpanner.init G₀ L q sparsify
          let st := fun t => DynSpanner.runBatchState (L := L) G₀ q sparsify Us t
          let res := fun t => DynSpanner.runBatchStepOut (L := L) G₀ q sparsify Us t
          let batchTotal := fun t => ((Us.take t).flatten.length : ℝ)
          let encTotal := fun t => ∑ t' ∈ Finset.range t, match Us[t']? with
            | some U => ((st t').G.batchEnc U : ℝ)
            | none => 0
          let B := Real.exp (C_dyn * Real.log (((2 ^ 64 : ℕ) : ℝ) + 2) ^ (23 / 24 : ℝ))
          ((initOut.state.H.m : ℝ) ≤ B * (G₀.n : ℝ)) ∧
          ((initOut.cost : ℝ) ≤ B * ((G₀.n : ℝ) + (G₀.m : ℝ) + 1)) ∧
          (∀ t ≤ Us.length,
            (st t).G = G₀.applyBatch (Us.flatten.take (DynSpanner.batchPrefixLen Us t)) ∧
            (st t).G.IsSubgraph (st t).H ∧
            ((st t).H.m : ℝ) ≤ B * (nMax : ℝ) ∧
            Embedding.IsEmbedding (DynSpanner.piTotal (st t)) (st t).G (st t).H ∧
            (Embedding.length (DynSpanner.piTotal (st t)) (st t).G : ℝ) ≤ B ∧
            Embedding.vcong (DynSpanner.piTotal (st t)) (st t).G (st t).H (fun _ => 1) ≤
              B * (G₀.maxDeg : ℝ)) ∧
          (∀ t < Us.length, ∀ U, Us[t]? = some U →
            res t = DynSpanner.update
                (DynSpanner.runState (L := L) G₀ q sparsify Us.flatten
                  (DynSpanner.batchPrefixLen Us t))
                U sparsify ∧
            (res t).state = st (t + 1) ∧
            (st t).H.BatchIsValid (res t).UH ∧
            (st t).H.applyBatch (res t).UH = (st (t + 1)).H ∧
            (res t).D ⊆ (st (t + 1)).H.E ∧
            (∀ eG ∈ (st (t + 1)).G.E, ∀ eH,
              eH ∈ walkEdges (DynSpanner.piTotal (st (t + 1)) eG) →
              eH ∉ (res t).D →
              eH ∈ walkEdges (DynSpanner.piTotal (st t) eG))) ∧
          (∀ t ≤ Us.length,
            (∑ t' ∈ Finset.range t, ((res t').UH.length : ℝ) ≤ B * batchTotal t) ∧
            (∑ t' ∈ Finset.range t, ((st t').H.batchEnc (res t').UH : ℝ) ≤
              B * ((G₀.n : ℝ) + batchTotal t)) ∧
            (∑ t' ∈ Finset.range t, ((res t').D.card : ℝ) ≤ B * batchTotal t) ∧
            (∑ t' ∈ Finset.range t, ((res t').cost : ℝ) ≤
              B * ((G₀.maxDeg : ℝ) + 1) * encTotal t))) := by
  have hq64 : qOf (2 ^ 64) = 3 := by
    unfold qOf
    have hlog : Nat.log 2 (2 ^ 64 + 2) = 64 :=
      nat_log2_eq_of_bounds (by norm_num) (by norm_num)
    have hs1 : Nat.sqrt 64 = 8 := nat_sqrt_eq_of_bounds (by norm_num) (by norm_num)
    have hs2 : Nat.sqrt 8 = 2 := nat_sqrt_eq_of_bounds (by norm_num) (by norm_num)
    have hs3 : Nat.sqrt 2 = 1 := nat_sqrt_eq_of_bounds (by norm_num) (by norm_num)
    rw [hlog, hs1, hs2, hs3]
  have hr64 : rOf (2 ^ 64) = 4 := by
    have hlog : Nat.log 2 (2 ^ 64) = 64 := Nat.log_pow (by norm_num) 64
    have hle := rOf_pow_le (2 ^ 64)
    have hlt := lt_rOf_succ_pow (2 ^ 64)
    rw [hlog] at hle hlt
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt4 | hgt4
    · have hpow : (rOf (2 ^ 64) + 1) ^ 3 ≤ 4 ^ 3 := Nat.pow_le_pow_left hlt4 3
      omega
    · have hpow : 5 ^ 3 ≤ rOf (2 ^ 64) ^ 3 := Nat.pow_le_pow_left hgt4 3
      omega
  have heta64 : Spanner.capEta2 (2 ^ 64) = 131 := by
    unfold Spanner.capEta2
    have hlog : Nat.log 2 (2 ^ 64 + 1) = 64 :=
      nat_log2_eq_of_bounds (by norm_num) (by norm_num)
    rw [hlog]
  have hgamma64 : ∀ Kγ : ℕ, Cited.csGamma Kγ (3 * 2 ^ 64) = 2 ^ (24 * Kγ) := by
    intro Kγ
    unfold Cited.csGamma
    have hlog : Nat.log 2 (3 * 2 ^ 64) = 65 :=
      nat_log2_eq_of_bounds (by norm_num) (by norm_num)
    have hs1 : Nat.sqrt ((65 + 1) ^ 3) = 536 :=
      nat_sqrt_eq_of_bounds (by norm_num) (by norm_num)
    have hs2 : Nat.sqrt 536 = 23 :=
      nat_sqrt_eq_of_bounds (by norm_num) (by norm_num)
    rw [hlog, hs1, hs2, mul_comm Kγ]
  have hphi64 : ∀ Kγ c : ℕ,
      Cited.csPhi Kγ c (3 * 2 ^ 64) = 1 / ((c : ℝ) * ((2 ^ (24 * Kγ) : ℕ) : ℝ)) := by
    intro Kγ c
    unfold Cited.csPhi
    rw [hgamma64 Kγ]
  obtain ⟨sparsify, params, C_γ, K_s, K_t, hCγ, hKs_eq, _, _, hSpecAll, hPoly⟩ :=
    theorem_8_2_concrete_of_poly hDec hPaths
  refine ⟨hq64, hr64, heta64, chosenL_at_2_pow_64, log_at_2_pow_64, hgamma64, hphi64,
    sparsify, params, C_γ, K_s, K_t, hCγ, hKs_eq, ?_⟩
  obtain ⟨hKs, hps, hKt, hpt, hγℓ, hγc, hSpec64⟩ := hSpecAll (2 ^ 64)
  refine ⟨hKs, hps, hKt, hpt, hγℓ, hγc, hSpec64, ?_⟩
  intro C_n r_n hCn hrn
  obtain ⟨C_dyn, hCdyn, h82_64⟩ := hPoly C_n r_n hCn hrn
  refine ⟨C_dyn, hCdyn, ?_⟩
  intro G₀ splitBound Us hVG₀ hGm₀ hnCap hBV hds hSplits
  have h82 := h82_64 (mMax := 2 ^ 64) hVG₀ hGm₀ hnCap hBV hds hSplits
  dsimp only at h82 ⊢
  rwa [chosenL_at_2_pow_64] at h82

end

end

end MinCostFlow.Expander
