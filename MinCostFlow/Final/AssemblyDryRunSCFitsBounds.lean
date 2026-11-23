module

public import MinCostFlow.Final.AssemblyDryRun
public import MinCostFlow.Final.AssemblyDryRunSCStretch
import MinCostFlow.LSF.Lemma54InitWith
import MinCostFlow.LSF.PathRoot
import MinCostFlow.LSF.SafePaths
import MinCostFlow.SparseCore.CompLSF
import MinCostFlow.Final.RuntimeQualityBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Parameter, grid, and per-level stretch bounds for `AssemblyDryRunSCFits`

Provides the helper bounds used to prove `hCoreLenFits` (on fixed-point grid inputs) and
`hLastStretchFits` for the dry run (`Final/AssemblyDryRunSC.lean`):

1. **Format and depth inequalities**:
   * `chosenD_sq_le_integerQualityExponent`: `chosenD (23 / 24) M₀ ^ 2 ≤ integerQualityExponent A M₀`
     for every `1 ≤ M₀`.
   * `chainLen_exponent_le_rangeExponent`: for `1 ≤ m` and `1 ≤ M₀`,
     `chosenD (23 / 24) M₀ * (3 * m.size + 12) ≤ ipmQualityRangeExponent m V (integerQualityExponent A M₀)`.
   * `coreLen_pow_lt_capacity` and `lastStretch_pow_lt_capacity`: comparing the chain-length and
     last-level stretch exponents to `Num.capacity 4 (ipmQualityLimbs m V k) = 2 ^ (4 * L)`.
2. **Exact dyadic-grid preservation and per-level growth for `dryLSFInitUsed`**:
   * `IsDyadicGrid G P ℓ`: every edge length on `G.E` is an integer multiple of `2 ^ (-P)`.
   * `walkLength_safeLen_grid_and_bound`: for any graph `G`, `MGraph.forestPath F u v` has
     `walkLength (safeLen G ℓ)` on the `2 ^ (-P)` grid and bounded by `G.m * B`.
   * `levelStretchBound_mul_grid_and_bound`: multiplying `levelStretchBound` by `ℓ e` stays on
     the `2 ^ (-P)` grid and grows by at most `2 * ((Nat.log 2 G.n + 1) * (Nat.log 2 G.n + 2) + 1) * (2 * G.m + 1)`.
   * `initCompLSFWith_dryLSFInitUsed_wstr_mul`: lifts both the exact grid preservation and the
     per-level factor `2 ^ (3 * m_root.size + 12)` to `initCompLSFWith (dryLSFInitUsed L_in P_fp)`
     at every level `G_i` with `G_i.n ≤ 2 * m_root + 2` and `G_i.m ≤ m_root`.
3. **Quality-derived bounds on `lastCanonConst` and `levelM d`**:
   * `dryWitnessUsed_lastCanonConst_and_levelM_lt`: from `1 / 2 ^ k ≤ alg2KappaOwn`, proves both
     `max 1 lastCanonConst < 2 ^ k` and `levelM cfg.TP cfg.P cfg.P.d + 1 < 2 ^ k`, bounding the
     last-level stretch precision `(1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (m' + 1).size`
     by `100 * F.rangeExponent` for `m' ∈ {I.m, levelM cfg.TP cfg.P cfg.P.d}`.
-/

public section

namespace MinCostFlow.Final.DryRun

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.Chain MinCostFlow.IPM
  MinCostFlow.IPM.Machine MinCostFlow.SparseCore MinCostFlow.SparseCore.Program
  MinCostFlow.Scaling MinCostFlow.LastLevelProgram

/-! ## 1. Fixed-point grid predicate -/

/-- Every edge of `G` has length on the `2 ^ (-P)` dyadic grid. -/
@[expose] def IsDyadicGrid (G : MGraph) (P : ℕ) (ℓ : ℕ → ℝ) : Prop :=
  ∀ e ∈ G.E, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = ℓ e

/-! ## 2. Format, depth, and capacity inequalities -/

/-- The squared chain depth `chosenD (23 / 24) M₀ ^ 2` is at most `integerQualityExponent A M₀`
for every `1 ≤ M₀` and `A : ℕ`. -/
theorem chosenD_sq_le_integerQualityExponent (A : ℕ) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    chosenD (23 / 24) M₀ ^ 2 ≤ integerQualityExponent A M₀ := by
  have hL1 : 1 ≤ Real.log ((M₀ : ℝ) + 2) := by
    have hexp : Real.exp 1 ≤ (M₀ : ℝ) + 2 := by
      have : (1 : ℝ) ≤ (M₀ : ℝ) := by exact_mod_cast hM₀
      linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  have hlog_le_size : Real.log ((M₀ : ℝ) + 2) ≤ ((M₀.size + 1 : ℕ) : ℝ) := by
    have hpow : M₀ + 2 ≤ 2 ^ (M₀.size + 1) := by
      rw [pow_succ]; have := Nat.lt_size_self M₀; omega
    have hcast : (M₀ : ℝ) + 2 ≤ (2 : ℝ) ^ (M₀.size + 1) := by exact_mod_cast hpow
    calc Real.log ((M₀ : ℝ) + 2)
        ≤ Real.log ((2 : ℝ) ^ (M₀.size + 1)) := Real.log_le_log (by positivity) hcast
      _ = ((M₀.size + 1 : ℕ) : ℝ) * Real.log 2 := by rw [Real.log_pow]
      _ ≤ ((M₀.size + 1 : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (Real.log_two_lt_d9.le.trans (by norm_num)) (by positivity)
      _ = ((M₀.size + 1 : ℕ) : ℝ) := mul_one _
  obtain ⟨_, _, hdHi⟩ := chosenD_bounds (β := 23 / 24) (by norm_num) hM₀
  rw [show ((1 : ℝ) - 23 / 24) / 2 = 1 / 48 by norm_num] at hdHi
  set Lnat := M₀.size + 1
  set b := Lnat.size
  set q := (47 * b + 47) / 48
  have hb_pos : 1 ≤ b := Nat.size_pos.mpr (Nat.succ_pos _)
  have hLnat_le : (Lnat : ℝ) ≤ (2 : ℝ) ^ b := by exact_mod_cast (Nat.lt_size_self Lnat).le
  have hceil : 47 * b ≤ 48 * q := by dsimp [q]; omega
  have hlow : (b : ℝ) * (47 / 48 : ℝ) ≤ (q : ℝ) := by
    have hcast : (47 : ℝ) * (b : ℝ) ≤ 48 * (q : ℝ) := by exact_mod_cast hceil
    linarith
  have hLpow : (Lnat : ℝ) ^ (47 / 48 : ℝ) ≤ (2 : ℝ) ^ q := by
    calc (Lnat : ℝ) ^ (47 / 48 : ℝ)
        ≤ ((2 : ℝ) ^ b) ^ (47 / 48 : ℝ) := Real.rpow_le_rpow (by positivity) hLnat_le (by norm_num)
      _ = (2 : ℝ) ^ ((b : ℝ) * (47 / 48 : ℝ)) := (Real.rpow_natCast_mul (by norm_num) b _).symm
      _ ≤ (2 : ℝ) ^ (q : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlow
      _ = (2 : ℝ) ^ q := Real.rpow_natCast 2 q
  have hdsq : ((chosenD (23 / 24) M₀ : ℝ)) ^ 2 ≤ 4 * (2 : ℝ) ^ q := by
    have h1 : ((chosenD (23 / 24) M₀ : ℝ)) ^ 2 ≤
        (2 * Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hdHi 2
    have h2 : (Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) ^ 2 =
        Real.log ((M₀ : ℝ) + 2) ^ (2 / 48 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h3 : Real.log ((M₀ : ℝ) + 2) ^ (2 / 48 : ℝ) ≤
        Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h4 : Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) ≤ (Lnat : ℝ) ^ (47 / 48 : ℝ) :=
      Real.rpow_le_rpow (by linarith) hlog_le_size (by norm_num)
    calc ((chosenD (23 / 24) M₀ : ℝ)) ^ 2
        ≤ (2 * Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) ^ 2 := h1
      _ = 4 * (Real.log ((M₀ : ℝ) + 2) ^ (1 / 48 : ℝ)) ^ 2 := by ring
      _ = 4 * Real.log ((M₀ : ℝ) + 2) ^ (2 / 48 : ℝ) := by rw [h2]
      _ ≤ 4 * Real.log ((M₀ : ℝ) + 2) ^ (47 / 48 : ℝ) := by linarith
      _ ≤ 4 * (Lnat : ℝ) ^ (47 / 48 : ℝ) := by linarith
      _ ≤ 4 * (2 : ℝ) ^ q := by linarith
  have h4le : (4 : ℝ) * (2 : ℝ) ^ q ≤ ((integerQualityExponent A M₀ : ℕ) : ℝ) := by
    unfold integerQualityExponent
    have h128 : 4 ≤ 128 * (A + 1) * b := by
      have hA1 : 1 ≤ A + 1 := Nat.succ_pos A
      have hmul : 1 ≤ (A + 1) * b := Nat.mul_pos hA1 hb_pos
      calc 4 ≤ 128 * 1 := by omega
        _ ≤ 128 * ((A + 1) * b) := Nat.mul_le_mul_left 128 hmul
        _ = 128 * (A + 1) * b := by ring
    have hnat : 4 * 2 ^ q ≤ 128 * (A + 1) * b * 2 ^ q := Nat.mul_le_mul_right _ h128
    exact_mod_cast hnat
  have hreal : (((chosenD (23 / 24) M₀ ^ 2 : ℕ) : ℝ)) ≤ ((integerQualityExponent A M₀ : ℕ) : ℝ) := by
    push_cast; exact hdsq.trans h4le
  exact_mod_cast hreal

/-- The cumulative per-level chain-length exponent `d * (3 * m.size + 12)` fits inside a single
copy of `ipmQualityRangeExponent m V (integerQualityExponent A M₀)`. -/
theorem chainLen_exponent_le_rangeExponent (m V A : ℕ) (hm : 1 ≤ m) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) :
    chosenD (23 / 24) M₀ * (3 * m.size + 12) ≤
      ipmQualityRangeExponent m V (integerQualityExponent A M₀) := by
  set d := chosenD (23 / 24) M₀
  set k := integerQualityExponent A M₀
  have hd2 : d ^ 2 ≤ k := chosenD_sq_le_integerQualityExponent A hM₀
  have hmsz : 1 ≤ m.size := Nat.size_pos.mpr hm
  have hlin : 3 * m.size + 12 ≤ 15 * m.size := by omega
  have hsq : (3 * m.size + 12) ^ 2 ≤ slackRangeExponent m V := by
    unfold slackRangeExponent
    have h1 : (3 * m.size + 12) ^ 2 ≤ (15 * m.size) ^ 2 := Nat.pow_le_pow_left hlin 2
    have h2 : m.size ^ 2 ≤ (m.size + V.size) ^ 2 := Nat.pow_le_pow_left (Nat.le_add_right _ _) 2
    have h3 : (15 * m.size) ^ 2 = 225 * m.size ^ 2 := by ring
    omega
  have ham : d * (3 * m.size + 12) ≤ d ^ 2 + (3 * m.size + 12) ^ 2 := by
    rcases le_total d (3 * m.size + 12) with h | h
    · calc d * (3 * m.size + 12)
          ≤ (3 * m.size + 12) * (3 * m.size + 12) := Nat.mul_le_mul_right _ h
        _ = (3 * m.size + 12) ^ 2 := (sq _).symm
        _ ≤ d ^ 2 + (3 * m.size + 12) ^ 2 := Nat.le_add_left _ _
    · calc d * (3 * m.size + 12)
          ≤ d * d := Nat.mul_le_mul_left _ h
        _ = d ^ 2 := (sq _).symm
        _ ≤ d ^ 2 + (3 * m.size + 12) ^ 2 := Nat.le_add_right _ _
  have hq1 : slackRangeExponent m V ≤ qualitySlackExponent m V k :=
    slackRangeExponent_le_qualitySlackExponent m V k
  have hq2 : k ≤ qualitySlackExponent m V k :=
    qualityExponent_le_qualitySlackExponent m V k
  unfold ipmQualityRangeExponent
  omega

/-- `2 * 2 ^ (P + 2 * E) < Num.capacity 4 L` for the concrete IPM quality format. -/
theorem coreLen_pow_lt_capacity (m V k : ℕ) :
    let E := ipmQualityRangeExponent m V k
    let P := ipmQualityPrecision m V k
    let L := ipmQualityLimbs m V k
    (2 : ℝ) ^ (P + 2 * E + 1) < (Num.capacity 4 L : ℝ) := by
  intro E P L
  have hmar := (ipm_quality_precision_margins m V k).2.2.2.2.1
  have hlt : P + 2 * E + 1 < 4 * L := by omega
  have hnat : 2 ^ (P + 2 * E + 1) < Num.capacity 4 L := by
    rw [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hlt
  exact_mod_cast hnat

/-- For any `stretchP ≤ 100 * E`, `2 ^ (stretchP + 3 * E + m.size + 2) < Num.capacity 4 L`. -/
theorem lastStretch_pow_lt_capacity (m V k stretchP : ℕ)
    (hst : stretchP ≤ 100 * ipmQualityRangeExponent m V k) :
    let E := ipmQualityRangeExponent m V k
    let L := ipmQualityLimbs m V k
    (2 : ℝ) ^ (stretchP + 3 * E + m.size + 2) < (Num.capacity 4 L : ℝ) := by
  intro E L
  have h4L : 116 * E + 16 * m.size + 1000 ≤ 4 * L := by
    dsimp only [L, ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits, E]
    omega
  have hlt : stretchP + 3 * E + m.size + 2 < 4 * L := by omega
  have hnat : 2 ^ (stretchP + 3 * E + m.size + 2) < Num.capacity 4 L := by
    rw [Num.capacity, Num.base, ← pow_mul]
    exact Nat.pow_lt_pow_right (by decide) hlt
  exact_mod_cast hnat

/-! ## 3. Exact grid preservation and per-level growth of `levelStretchBound` and `dryLSFInitUsed` -/

/-- Any `MGraph.forestPath F u v` has `walkLength (safeLen G ℓ)` nonnegative, bounded by `G.m * B`,
and on the `2 ^ (-P)` dyadic grid whenever `ℓ` is on that grid on `G.E`. -/
theorem walkLength_safeLen_grid_and_bound {G F : MGraph} {ℓ : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hℓ : ∀ f ∈ G.E, 0 ≤ ℓ f ∧ ℓ f ≤ B) (u v : ℕ) :
    0 ≤ walkLength (safeLen G ℓ) (F.forestPath u v) ∧
    walkLength (safeLen G ℓ) (F.forestPath u v) ≤ (G.m : ℝ) * B ∧
    ∀ P : ℕ, IsDyadicGrid G P ℓ →
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = walkLength (safeLen G ℓ) (F.forestPath u v) := by
  classical
  have hsafe_nn : ∀ f, 0 ≤ safeLen G ℓ f := fun f => by
    unfold safeLen; split_ifs with hf
    · exact (hℓ f hf).1
    · exact le_rfl
  have hsafe_grid : ∀ P : ℕ, IsDyadicGrid G P ℓ →
      ∀ f, ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = safeLen G ℓ f := fun P hG f => by
    unfold safeLen; split_ifs with hf
    · exact hG f hf
    · exact ⟨0, by simp⟩
  have hnn : 0 ≤ walkLength (safeLen G ℓ) (F.forestPath u v) :=
    Finset.sum_nonneg fun f _ => mul_nonneg (hsafe_nn f) (abs_nonneg _)
  have hsum_grid : ∀ (P : ℕ), IsDyadicGrid G P ℓ → ∀ (S : Finset ℕ),
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = ∑ f ∈ S, safeLen G ℓ f := by
    intro P hG S
    choose qf hqf using hsafe_grid P hG
    refine ⟨∑ f ∈ S, qf f, ?_⟩
    push_cast
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun f _ => hqf f
  refine ⟨hnn, ?_, ?_⟩
  · unfold MGraph.forestPath
    split_ifs with h
    · set p := Classical.choose h
      have hp : F.IsPath u v p := Classical.choose_spec h
      rw [walkLength_eq_sum_of_isPath (safeLen G ℓ) hp]
      have hsub : (walkEdges p).filter (· ∈ G.E) ⊆ G.E := fun x hx => (Finset.mem_filter.mp hx).2
      have hsplit : ∑ f ∈ walkEdges p, safeLen G ℓ f =
          ∑ f ∈ (walkEdges p).filter (· ∈ G.E), ℓ f := by
        rw [← Finset.sum_filter_add_sum_filter_not (walkEdges p) (· ∈ G.E)]
        have hzero : ∑ f ∈ (walkEdges p).filter (fun x => ¬ x ∈ G.E), safeLen G ℓ f = 0 :=
          Finset.sum_eq_zero fun f hf => by
            have hnot : f ∉ G.E := (Finset.mem_filter.mp hf).2
            simp [safeLen, hnot]
        rw [hzero, add_zero]
        exact Finset.sum_congr rfl fun f hf => safeLen_eq_of_mem ℓ (Finset.mem_filter.mp hf).2
      rw [hsplit]
      calc ∑ f ∈ (walkEdges p).filter (· ∈ G.E), ℓ f
          ≤ ∑ f ∈ G.E, ℓ f := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f hf _ => (hℓ f hf).1)
        _ ≤ ∑ _f ∈ G.E, B := Finset.sum_le_sum fun f hf => (hℓ f hf).2
        _ = (G.m : ℝ) * B := by simp [MGraph.m]
    · simp only [walkLength, walkEdges, List.map_nil, List.toFinset_nil, Finset.sum_empty]
      exact mul_nonneg (Nat.cast_nonneg _) hB
  · intro P hG
    unfold MGraph.forestPath
    split_ifs with h
    · set p := Classical.choose h
      have hp : F.IsPath u v p := Classical.choose_spec h
      rw [walkLength_eq_sum_of_isPath (safeLen G ℓ) hp]
      exact hsum_grid P hG (walkEdges p)
    · exact ⟨0, by simp [walkLength, walkEdges]⟩

/-- Multiplying `RF.stretch G (safeLen G ℓ) e` by `ℓ e` stays on the `2 ^ (-P)` dyadic grid and
is bounded by `(2 * G.m + 1) * B`. -/
private theorem rootedForest_stretch_mul_grid_and_bound {G : MGraph} {ℓ : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hℓ : ∀ f ∈ G.E, 0 < ℓ f ∧ ℓ f ≤ B)
    (RF : RootedForest) {e : ℕ} (he : e ∈ G.E) :
    0 ≤ RF.stretch G (safeLen G ℓ) e * ℓ e ∧
    RF.stretch G (safeLen G ℓ) e * ℓ e ≤ ((2 * G.m + 1 : ℕ) : ℝ) * B ∧
    ∀ P : ℕ, IsDyadicGrid G P ℓ →
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = RF.stretch G (safeLen G ℓ) e * ℓ e := by
  have hℓe_pos : 0 < ℓ e := (hℓ e he).1
  have hℓe_le : ℓ e ≤ B := (hℓ e he).2
  have hℓ_nn : ∀ f ∈ G.E, 0 ≤ ℓ f ∧ ℓ f ≤ B := fun f hf => ⟨(hℓ f hf).1.le, (hℓ f hf).2⟩
  have hsafe_e : safeLen G ℓ e = ℓ e := safeLen_eq_of_mem ℓ he
  unfold RootedForest.stretch
  dsimp only
  rw [hsafe_e]
  split_ifs
  · have hEq : (1 + walkLength (safeLen G ℓ) (RF.F.forestPath (G.tail e) (G.head e)) / ℓ e) * ℓ e =
        ℓ e + walkLength (safeLen G ℓ) (RF.F.forestPath (G.tail e) (G.head e)) := by
      field_simp [hℓe_pos.ne']
    rw [hEq]
    obtain ⟨hnn, hle, hgr⟩ := walkLength_safeLen_grid_and_bound (F := RF.F) hB hℓ_nn (G.tail e) (G.head e)
    refine ⟨by linarith, ?_, fun P hG => ?_⟩
    · have h1 : (G.m : ℝ) * B ≤ (2 * (G.m : ℝ)) * B := by nlinarith [Nat.cast_nonneg (α := ℝ) G.m]
      push_cast; nlinarith
    · obtain ⟨q1, hq1⟩ := hG e he
      obtain ⟨q2, hq2⟩ := hgr P hG
      exact ⟨q1 + q2, by simp only [Int.cast_add, add_div, hq1, hq2]⟩
  · have hEq : (1 + (walkLength (safeLen G ℓ) (RF.F.forestPath (G.tail e) (RF.root (G.tail e))) +
          walkLength (safeLen G ℓ) (RF.F.forestPath (G.head e) (RF.root (G.head e)))) / ℓ e) * ℓ e =
        ℓ e + walkLength (safeLen G ℓ) (RF.F.forestPath (G.tail e) (RF.root (G.tail e))) +
          walkLength (safeLen G ℓ) (RF.F.forestPath (G.head e) (RF.root (G.head e))) := by
      field_simp [hℓe_pos.ne']; ring
    rw [hEq]
    obtain ⟨hnn1, hle1, hgr1⟩ :=
      walkLength_safeLen_grid_and_bound (F := RF.F) hB hℓ_nn (G.tail e) (RF.root (G.tail e))
    obtain ⟨hnn2, hle2, hgr2⟩ :=
      walkLength_safeLen_grid_and_bound (F := RF.F) hB hℓ_nn (G.head e) (RF.root (G.head e))
    refine ⟨by linarith, ?_, fun P hG => ?_⟩
    · push_cast; nlinarith
    · obtain ⟨q0, hq0⟩ := hG e he
      obtain ⟨q1, hq1⟩ := hgr1 P hG
      obtain ⟨q2, hq2⟩ := hgr2 P hG
      exact ⟨q0 + q1 + q2, by simp only [Int.cast_add, add_div, hq0, hq1, hq2]⟩

/-- Multiplying `levelStretchBound T₀ r₀ π G (safeLen G ℓ) e` by `ℓ e` stays on the `2 ^ (-P)`
dyadic grid and is bounded by `2 * ((Nat.log 2 G.n + 1) * (Nat.log 2 G.n + 2) + 1) * (2 * G.m + 1) * B`
whenever `T₀.V = G.V`. -/
theorem levelStretchBound_mul_grid_and_bound {G T₀ : MGraph} {r₀ : ℕ} {π : ℕ → ℕ}
    {ℓ : ℕ → ℝ} {B : ℝ} (hTV : T₀.V = G.V) (hB : 0 ≤ B)
    (hℓ : ∀ f ∈ G.E, 0 < ℓ f ∧ ℓ f ≤ B) {e : ℕ} (he : e ∈ G.E) :
    let D := (Nat.log 2 G.n + 1) * (Nat.log 2 G.n + 2)
    levelStretchBound T₀ r₀ π G (safeLen G ℓ) e * ℓ e ≤
      ((2 * (D + 1) * (2 * G.m + 1) : ℕ) : ℝ) * B ∧
    ∀ P : ℕ, IsDyadicGrid G P ℓ →
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P =
        levelStretchBound T₀ r₀ π G (safeLen G ℓ) e * ℓ e := by
  intro D
  unfold levelStretchBound
  have hcard : T₀.V.card = G.n := by rw [hTV]; rfl
  rw [hcard]
  change (2 * ∑ i ∈ Finset.range (D + 1),
      (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e) * ℓ e ≤ _ ∧ _
  have hrew : (2 * ∑ i ∈ Finset.range (D + 1),
      (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e) * ℓ e =
      2 * ∑ i ∈ Finset.range (D + 1),
        ((rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e * ℓ e) := by
    rw [mul_assoc, Finset.sum_mul]
  rw [hrew]
  constructor
  · have hsum : ∑ i ∈ Finset.range (D + 1),
        ((rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e * ℓ e) ≤
        ((D + 1 : ℕ) : ℝ) * (((2 * G.m + 1 : ℕ) : ℝ) * B) := by
      calc ∑ i ∈ Finset.range (D + 1),
            ((rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e * ℓ e)
          ≤ ∑ _i ∈ Finset.range (D + 1), (((2 * G.m + 1 : ℕ) : ℝ) * B) :=
            Finset.sum_le_sum fun i _ =>
              (rootedForest_stretch_mul_grid_and_bound hB hℓ _ he).2.1
        _ = ((D + 1 : ℕ) : ℝ) * (((2 * G.m + 1 : ℕ) : ℝ) * B) := by simp
    push_cast at hsum ⊢
    nlinarith
  · intro P hG
    have hex : ∀ i ∈ Finset.range (D + 1), ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P =
        (rootedForestGivenRoots T₀ r₀ (levelRoots T₀ r₀ i) π).stretch G (safeLen G ℓ) e * ℓ e :=
      fun i _ => (rootedForest_stretch_mul_grid_and_bound hB hℓ _ he).2.2 P hG
    classical
    choose qf hqf using hex
    refine ⟨2 * ∑ i ∈ Finset.range (D + 1), if hi : i ∈ Finset.range (D + 1) then qf i hi else 0, ?_⟩
    push_cast
    rw [mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hi, ↓reduceDIte]
    exact hqf i hi

/-- Per-component `wstr * ℓ` bound and exact dyadic-grid preservation for `dryLSFInitUsed`. -/
theorem dryLSFInitUsed_wstr_mul_grid_and_bound (L_in P_fp : ℕ)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hℓ₀ : ∀ f ∈ G₀.E, 0 < ℓ₀ f ∧ ℓ₀ f ≤ B)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < k) {e : ℕ} (he : e ∈ G₀.E) :
    let S₀ := dryLSFInitUsed L_in P_fp G₀ ℓ₀ k j
    let D := (Nat.log 2 G₀.n + 1) * (Nat.log 2 G₀.n + 2)
    ℓ₀ e ≤ S₀.wstr e * ℓ₀ e ∧
    S₀.wstr e * ℓ₀ e ≤ ((2 * (D + 1) * (2 * G₀.m + 1) : ℕ) : ℝ) * B ∧
    ∀ P : ℕ, IsDyadicGrid G₀ P ℓ₀ →
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = S₀.wstr e * ℓ₀ e := by
  intro S₀ D
  have hApprox := (dryKρ_spec SparseCore.Program.canonicalLSFInit
    SparseCore.Program.canonicalLSFInit_spec).2 L_in P_fp G₀ ℓ₀ k hG₀ hV₀
    (fun f hf => (hℓ₀ f hf).1) hk
  rcases hApprox with ⟨thresh, _, _, v, T_raw, r₀, C_reps, π, W_T,
    _, _, _, _, _, hv_pos, hvalid, _, heq⟩
  have hSeq : S₀ = initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh :=
    heq j hj
  have hsp := initLSFWith_spec hG₀ hV₀ (fun f hf => (hℓ₀ f hf).1) (hv_pos j hj.le)
    (by exact_mod_cast hk) (hvalid j hj)
  rcases hsp with ⟨_, _, _, _, _, _, _, _, _, hT₀_rt, hTV, _, _, _, _, _, _, _, _, _, hwstr_cs, _⟩
  rw [hSeq]
  set raw := levelStretchBound (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).T₀
    (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).r₀
    (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).π
    G₀ (safeLen G₀ ℓ₀) e
  have hℓe_pos : 0 < ℓ₀ e := (hℓ₀ e he).1
  have hℓe_le : ℓ₀ e ≤ B := (hℓ₀ e he).2
  by_cases hth : thresh ≤ raw
  · have hw1 : (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e = 1 :=
      ((hwstr_cs e he).2 hth).1
    rw [hw1, one_mul]
    have hfac1 : (1 : ℝ) ≤ ((2 * (D + 1) * (2 * G₀.m + 1) : ℕ) : ℝ) := by
      exact_mod_cast (by
        have h1 : 1 ≤ D + 1 := Nat.succ_pos _
        have h2 : 1 ≤ 2 * G₀.m + 1 := Nat.succ_pos _
        have h3 : 1 ≤ (D + 1) * (2 * G₀.m + 1) := Nat.mul_pos h1 h2
        calc 1 ≤ 2 * 1 := by omega
          _ ≤ 2 * ((D + 1) * (2 * G₀.m + 1)) := Nat.mul_le_mul_left 2 h3
          _ = 2 * (D + 1) * (2 * G₀.m + 1) := by ring : 1 ≤ 2 * (D + 1) * (2 * G₀.m + 1))
    refine ⟨le_rfl, ?_, fun P hG => hG e he⟩
    calc ℓ₀ e ≤ B := hℓe_le
      _ = 1 * B := (one_mul B).symm
      _ ≤ ((2 * (D + 1) * (2 * G₀.m + 1) : ℕ) : ℝ) * B := mul_le_mul_of_nonneg_right hfac1 hB
  · have hlt : raw < thresh := lt_of_not_ge hth
    have hwr : (initLSFWith G₀ ℓ₀ (v j) (k : ℝ) (T_raw j) (r₀ j) (C_reps j) (π j) (W_T j) thresh).wstr e = raw :=
      (hwstr_cs e he).1 hlt
    rw [hwr]
    have hraw_ge2 : 2 ≤ raw :=
      levelStretchBound_ge_two hT₀_rt _ G₀
        (fun f _ => safeLen_nonneg (fun g hg => (hℓ₀ g hg).1) f)
        (by rw [safeLen_eq_of_mem ℓ₀ he]; exact hℓe_pos)
    obtain ⟨hle, hgr⟩ := levelStretchBound_mul_grid_and_bound hTV hB hℓ₀ he
    refine ⟨?_, hle, hgr⟩
    nlinarith

/-- Per-level `wstrGlobal * ℓ` bound and exact dyadic-grid preservation for
`initCompLSFWith (dryLSFInitUsed L_in P_fp)`, with explicit power-of-two factor
`2 ^ (3 * m_root.size + 12)` whenever `1 ≤ m_root`, `G.n ≤ 2 * m_root + 2`, and `G.m ≤ m_root`. -/
theorem initCompLSFWith_dryLSFInitUsed_wstr_mul (L_in P_fp m_root : ℕ) (hm_root : 1 ≤ m_root)
    {G : MGraph} (hG : G.IsValid) (hGn : G.n ≤ 2 * m_root + 2) (hGm : G.m ≤ m_root)
    {ℓ : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) (hℓ : ∀ f ∈ G.E, 0 < ℓ f ∧ ℓ f ≤ B)
    {k j : ℕ} (hk : 1 ≤ k) (hj : j < k) {e : ℕ} (he : e ∈ G.E) :
    let cs := initCompLSFWith (dryLSFInitUsed L_in P_fp) G ℓ k j
    ℓ e ≤ cs.lsf.wstr e * ℓ e ∧
    cs.lsf.wstr e * ℓ e ≤ (2 : ℝ) ^ (3 * m_root.size + 12) * B ∧
    ∀ P : ℕ, IsDyadicGrid G P ℓ →
      ∃ q : ℤ, (q : ℝ) / (2 : ℝ) ^ P = cs.lsf.wstr e * ℓ e := by
  classical
  intro cs
  have hEx : ∃ C ∈ components G, e ∈ compEdgeSet G C := by
    refine ⟨compOf G (G.tail e), Finset.mem_image.mpr ⟨G.tail e, (hG e he).1, rfl⟩, ?_⟩
    exact Finset.mem_filter.mpr ⟨he, Finset.mem_filter.mpr ⟨(hG e he).1, MGraph.connected_refl G _⟩⟩
  have hwEq : cs.lsf.wstr e =
      (dryLSFInitUsed L_in P_fp (compGraph G hEx.choose) (safeLen G ℓ) k j).wstr e := by
    change (initCompLSFWith (dryLSFInitUsed L_in P_fp) G ℓ k j).wstrGlobal e = _
    unfold initCompLSFWith
    dsimp only
    rw [dite_eq_left hEx]
  set C := hEx.choose
  have hCmem : C ∈ components G := hEx.choose_spec.1
  have heC : e ∈ (compGraph G C).E := hEx.choose_spec.2
  have hGC_val : (compGraph G C).IsValid := compGraph_isValid hG hCmem
  have hGC_ne : (compGraph G C).V.Nonempty := compGraph_nonempty hCmem
  have hGC_subE : (compGraph G C).E ⊆ G.E := Finset.filter_subset _ _
  have hGC_subV : (compGraph G C).V ⊆ G.V := by
    obtain ⟨v, _, hvC⟩ := Finset.mem_image.mp hCmem
    intro x hx
    change x ∈ C at hx
    rw [← hvC] at hx
    exact (Finset.mem_filter.mp hx).1
  have hGC_n : (compGraph G C).n ≤ G.n := Finset.card_le_card hGC_subV
  have hGC_m : (compGraph G C).m ≤ G.m := Finset.card_le_card hGC_subE
  have hℓC : ∀ f ∈ (compGraph G C).E, 0 < safeLen G ℓ f ∧ safeLen G ℓ f ≤ B := fun f hf => by
    have hfG : f ∈ G.E := hGC_subE hf
    rw [safeLen_eq_of_mem ℓ hfG]
    exact hℓ f hfG
  obtain ⟨hlo, hhi, hgr⟩ :=
    dryLSFInitUsed_wstr_mul_grid_and_bound L_in P_fp hGC_val hGC_ne hB hℓC hk hj heC
  have hse : safeLen G ℓ e = ℓ e := safeLen_eq_of_mem ℓ he
  rw [hwEq, ← hse]
  refine ⟨hlo, ?_, fun P hGrid => hgr P (fun f hf => by
    have hfG : f ∈ G.E := hGC_subE hf
    rw [safeLen_eq_of_mem ℓ hfG]
    exact hGrid f hfG)⟩
  -- Bound `2 * (D_C + 1) * (2 * (compGraph G C).m + 1) ≤ 2 ^ (3 * m_root.size + 12)`
  have hfac : 2 * ((Nat.log 2 (compGraph G C).n + 1) * (Nat.log 2 (compGraph G C).n + 2) + 1) *
      (2 * (compGraph G C).m + 1) ≤ 2 ^ (3 * m_root.size + 12) := by
    have hlt : m_root < 2 ^ m_root.size := Nat.lt_size_self m_root
    have hlog_le : Nat.log 2 (compGraph G C).n ≤ (compGraph G C).n := Nat.log_le_self 2 _
    have ha : Nat.log 2 (compGraph G C).n + 2 ≤ 2 ^ (m_root.size + 3) := by
      have h1 : 2 ^ (m_root.size + 3) = 8 * 2 ^ m_root.size := by rw [pow_add]; ring
      omega
    have ha1 : Nat.log 2 (compGraph G C).n + 1 ≤ 2 ^ (m_root.size + 3) := by omega
    have hD1 : (Nat.log 2 (compGraph G C).n + 1) * (Nat.log 2 (compGraph G C).n + 2) + 1 ≤
        2 * (2 ^ (m_root.size + 3) * 2 ^ (m_root.size + 3)) := by
      have hprod := Nat.mul_le_mul ha1 ha
      have hpos : 1 ≤ 2 ^ (m_root.size + 3) * 2 ^ (m_root.size + 3) :=
        Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)
      omega
    have hm1 : 2 * (compGraph G C).m + 1 ≤ 2 ^ (m_root.size + 2) := by
      have h1 : 2 ^ (m_root.size + 2) = 4 * 2 ^ m_root.size := by rw [pow_add]; ring
      omega
    calc 2 * ((Nat.log 2 (compGraph G C).n + 1) * (Nat.log 2 (compGraph G C).n + 2) + 1) *
          (2 * (compGraph G C).m + 1)
        ≤ 2 * (2 * (2 ^ (m_root.size + 3) * 2 ^ (m_root.size + 3))) * 2 ^ (m_root.size + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left 2 hD1) hm1
      _ = 2 ^ (3 * m_root.size + 10) := by
          have : 3 * m_root.size + 10 = 1 + (1 + ((m_root.size + 3) + (m_root.size + 3))) + (m_root.size + 2) := by omega
          rw [this]; simp only [pow_add, pow_one]
      _ ≤ 2 ^ (3 * m_root.size + 12) := Nat.pow_le_pow_right (by decide) (by omega)
  have hfacR : (((2 * ((Nat.log 2 (compGraph G C).n + 1) * (Nat.log 2 (compGraph G C).n + 2) + 1) *
      (2 * (compGraph G C).m + 1) : ℕ) : ℝ)) ≤ (2 : ℝ) ^ (3 * m_root.size + 12) := by
    exact_mod_cast hfac
  exact hhi.trans (mul_le_mul_of_nonneg_right hfacR hB)

/-! ## 4. Quality-derived bounds on `lastCanonConst` and `levelM d` -/

/-- From `1 / 2 ^ k ≤ alg2KappaOwn` (via `dryWitnessUsed.specWith`), both `max 1 lastCanonConst`
and `levelM cfg.TP cfg.P cfg.P.d + 1` lie strictly below `2 ^ k`. -/
theorem dryWitnessUsed_lastCanonConst_and_levelM_lt
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    max 1 lastCanonConst < (2 : ℝ) ^ k ∧
    levelM cfg.TP cfg.P cfg.P.d + 1 < 2 ^ k := by
  intro I threshold A k cfg
  let V := solverPenalty J.m
  let M₀ := max I.m threshold
  let N₀ := 4 * M₀
  let hM₀1 : 1 ≤ M₀ :=
    (by omega : 1 ≤ 2).trans ((concreteEdgeThresholdWithLast_ge_two dryWitnessUsed).trans (le_max_right _ _))
  let α := Num.IPM.alphaPrime I.m V / 8
  let Ψ := ((ipmQualityRangeExponent I.m V k + slackRangeExponent I.m V + 6 : ℕ) : ℝ)
  let ε := (1 / (2 : ℝ) ^ k) * Num.IPM.alphaPrime I.m V / 1024
  obtain ⟨hThresh, hN₀, hPsi, hα, -⟩ :=
    concreteCirculation_bounds_of (le_max_left dryWitnessUsed.M_thresh _)
      (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap
  obtain ⟨⟨hκ_pos, hKappa⟩, _⟩ :=
    dryWitnessUsed.specWith (ipmQualityLimbs I.m V k) (ipmQualityPrecision I.m V k) M₀ N₀ α Ψ ε
      hM₀1 hThresh hN₀ hPsi hα
  have hAge : 15 + 5 * dryWitnessUsed.C_γ ≤ (A : ℝ) := Nat.le_ceil _
  have hk_le_κ : 1 / (2 : ℝ) ^ k ≤
      alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ :=
    concrete_kappa_le_alg2KappaOwn_of A hAge M₀ hKappa
  have hVcfg : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap
  -- Extract `σ_tot + 1 ≤ 1 / alg2KappaOwn ≤ 2 ^ k`
  set σ_tot := alg2SigmaTotOwn cfg.TP cfg.LP cfg.P cfg.N₀
  set σ_mwu_max := alg2SigmaGame cfg.σ_mwu cfg.N₀
  have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hVcfg.hTP.2.2.1 (cfg.P.M₀ ^ 2)
  have hσ_mwu_nn : 0 ≤ σ_mwu_max := le_max_left 0 _
  have hbase_ge1 : 1 ≤ 2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max) := by nlinarith
  have hpow_ge1 : 1 ≤ (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d :=
    one_le_pow₀ hbase_ge1
  have hd_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) := by
    have : (0 : ℝ) ≤ cfg.P.d := Nat.cast_nonneg _
    nlinarith
  have hσ_tot_nn : 0 ≤ σ_tot := by
    unfold σ_tot alg2SigmaTotOwn alg2SigmaTotAt
    exact le_trans zero_le_one ((hVcfg.hLP.1 _).trans (le_max_right _ _))
  have hdenom_ge : σ_tot + 1 ≤ (σ_tot + 1) *
      (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d) := by
    have hprod_ge1 : 1 ≤ ((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
        (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d := by
      nlinarith
    nlinarith
  have hσ_lt_2k : σ_tot + 1 ≤ (2 : ℝ) ^ k := by
    have hκ_eq : alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ =
        1 / ((σ_tot + 1) * (((cfg.P.d : ℝ) + 1) * (2 * (cfg.P.d : ℝ) + 3) *
          (2 * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * (1 + 2 * σ_mwu_max)) ^ cfg.P.d)) := rfl
    have hκ_pos' : 0 < alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ := hκ_pos
    have h2k_pos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hinv : 1 / alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀ ≤ (2 : ℝ) ^ k := by
      rw [div_le_iff₀ hκ_pos']
      have h1 := (div_le_iff₀ h2k_pos).mp hk_le_κ
      linarith
    rw [hκ_eq, one_div_one_div] at hinv
    exact hdenom_ge.trans hinv
  -- Compare `lastLevelParams dryLastConstant` at `n_last := levelM cfg.TP cfg.P cfg.P.d + 1 ≥ 2`
  set n_last := levelM cfg.TP cfg.P cfg.P.d + 1
  have hn_last_ge2 : 2 ≤ n_last := by
    have h1 := Chain.one_le_levelM hVcfg.hTP cfg.P cfg.P.d
    omega
  have hσ_last_le : cfg.LP.σ_last n_last ≤ σ_tot := le_max_right _ _
  have hLP_eq : cfg.LP = lastLevelParams dryLastConstant := rfl
  have hlog_ge1 : 1 ≤ Real.log ((n_last : ℝ) + 2) := by
    have hexp : Real.exp 1 ≤ (n_last : ℝ) + 2 := by
      have : (2 : ℝ) ≤ (n_last : ℝ) := by exact_mod_cast hn_last_ge2
      linarith [Real.exp_one_lt_d9]
    exact (Real.le_log_iff_exp_le (by positivity)).mpr hexp
  have hlog2_ge1 : 1 ≤ (Real.log ((n_last : ℝ) + 2)) ^ 2 := by nlinarith
  have hn2_ge4 : (4 : ℝ) ≤ (n_last : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ (n_last : ℝ) := by exact_mod_cast hn_last_ge2
    nlinarith
  have hC_ge1 : (1 : ℝ) ≤ max 1 dryLastConstant := le_max_left 1 _
  have hσ_last_ge : 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 *
      (Real.log ((n_last : ℝ) + 2)) ^ 2 ≤ σ_tot := by
    have h1 : 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 *
        (Real.log ((n_last : ℝ) + 2)) ^ 2 ≤ cfg.LP.σ_last n_last := by
      rw [hLP_eq]; exact le_max_right _ _
    exact h1.trans hσ_last_le
  constructor
  · have hC_le : max 1 lastCanonConst ≤ max 1 dryLastConstant := by
      unfold dryLastConstant
      have : (1 : ℝ) ≤ max 1 lastCanonConst := le_max_left 1 _
      exact le_trans (by linarith) (le_max_right 1 _)
    have h2C_le : max 1 dryLastConstant ≤ σ_tot := by
      have h1 : max 1 dryLastConstant ≤ 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 := by nlinarith
      have h2 : 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 ≤
          2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 * (Real.log ((n_last : ℝ) + 2)) ^ 2 := by
        nlinarith
      exact (h1.trans h2).trans hσ_last_ge
    linarith
  · have hn_le : (n_last : ℝ) ≤ σ_tot := by
      have hn_le_sq : (n_last : ℝ) ≤ (n_last : ℝ) ^ 2 := by
        have : (2 : ℝ) ≤ (n_last : ℝ) := by exact_mod_cast hn_last_ge2
        nlinarith
      have h1 : (n_last : ℝ) ^ 2 ≤ 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 := by nlinarith
      have h2 : 2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 ≤
          2 * max 1 dryLastConstant * (n_last : ℝ) ^ 2 * (Real.log ((n_last : ℝ) + 2)) ^ 2 := by
        nlinarith
      exact (hn_le_sq.trans (h1.trans h2)).trans hσ_last_ge
    have hreal : ((n_last : ℕ) : ℝ) < (2 : ℝ) ^ k := by linarith
    exact_mod_cast hreal

/-- Both `levelM`-based and `I.m`-based last-level stretch precisions (and their max) lie below
`100 * ipmQualityRangeExponent I.m V k`. -/
theorem dryLastStretchP_le_rangeExponent
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap : ∀ e, 1 ≤ J.capacity e) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let threshold := concreteEdgeThresholdWithLast dryWitnessUsed
    let A := concreteQualityBudgetWithLast dryWitnessUsed
    let k := cappedQualityExponent threshold A I.m
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let E := ipmQualityRangeExponent I.m V k
    (1024 * ⌈max 1 lastCanonConst⌉₊).size + 3 * (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤
      100 * E := by
  intro I V threshold A k cfg E
  obtain ⟨hC_lt, hM_lt⟩ := dryWitnessUsed_lastCanonConst_and_levelM_lt J hJn hJm hCap
  have hceil_le : ⌈max 1 lastCanonConst⌉₊ ≤ 2 ^ k := by
    exact Nat.ceil_le.mpr (by exact_mod_cast hC_lt.le)
  have h1024_lt : 1024 * ⌈max 1 lastCanonConst⌉₊ < 2 ^ (k + 11) := by
    calc 1024 * ⌈max 1 lastCanonConst⌉₊
        ≤ 1024 * 2 ^ k := Nat.mul_le_mul_left 1024 hceil_le
      _ = 2 ^ (k + 10) := by rw [pow_add, mul_comm]; norm_num
      _ < 2 ^ (k + 11) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hsz1 : (1024 * ⌈max 1 lastCanonConst⌉₊).size ≤ k + 11 := Nat.size_le.mpr h1024_lt
  have hszM : (levelM cfg.TP cfg.P cfg.P.d + 1).size ≤ k := Nat.size_le.mpr hM_lt
  have hszI : (I.m + 1).size ≤ I.m.size + 1 := by
    rw [Nat.size_le, pow_succ]
    have h1 := Nat.lt_size_self I.m
    have h2 : 1 ≤ 2 ^ I.m.size := Nat.one_le_two_pow
    omega
  have hszMax : (max I.m (levelM cfg.TP cfg.P cfg.P.d) + 1).size ≤ max (I.m.size + 1) k := by
    rcases le_total I.m (levelM cfg.TP cfg.P cfg.P.d) with h | h
    · rw [max_eq_right h]; exact hszM.trans (le_max_right _ _)
    · rw [max_eq_left h]; exact hszI.trans (le_max_left _ _)
  have hkE : k ≤ E := by
    have hk1 := qualityExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]; omega
  have hImE : I.m.size ≤ E := by
    have h1 : I.m.size ≤ (I.m.size + V.size) ^ 2 :=
      le_trans (Nat.le_add_right _ _) (Nat.le_self_pow (by decide : 2 ≠ 0) _)
    have h2 := slackRangeExponent_le_qualitySlackExponent I.m V k
    dsimp only [E, ipmQualityRangeExponent]
    unfold slackRangeExponent at h2
    omega
  have hE100 : 100 ≤ E := by dsimp only [E, ipmQualityRangeExponent]; omega
  omega

end MinCostFlow.Final.DryRun
