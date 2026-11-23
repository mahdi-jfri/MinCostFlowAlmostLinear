module

public import MinCostFlow.Chain.Lemma6_5
public import MinCostFlow.IPM.MinRatioSpec
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.1 Helpers: IPM Failure Interface and Unconditional Operation Bounds

This module provides:
1. `algorithm2_dsWithFailure`: wraps `algorithm2_ds cfg` as a
   `MinCostFlow.IPM.MinRatioDataStructureWithFailure` and proves exact agreement of
   `eraseFailure` states, directions, increments, flows, `last_e`, and `Detect` sets.
2. `largeBatchEnc_le_linear_log`, `gameShiftBound_powTerm_sum_le`, and
   `theorem_5_1_uncond_complexity`: unconditional (`HiddenStable`-free) runtime (`eq:restatingTimeBoundSR`),
   `T^𝒢` update, shift-bound, `lctUpdateOps`/`lctDetectOps` (`O(log N₀)` amortized LCT charge),
   and `s_i`-eliminated complexity bounds for Algorithm 2.
3. `RebuildFloorHyp`, `rebuildWork_collapse_of_floor`, `alg2CollapsedFactor`, and
   `theorem_5_1_collapsed_of_floor`: global rebuild threshold floor, with a correction of the local versus global
   `Q` (`jtree.tex:848`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section IPMBridge

/-- Wraps `algorithm2_dsWith cfg κ` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailureWith (cfg : Alg2Config) (κ : ℝ) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure where
  State := (algorithm2_dsWith cfg κ).State
  init := (algorithm2_dsWith cfg κ).init
  update := (algorithm2_dsWith cfg κ).update
  query := (algorithm2_dsWith cfg κ).query
  detect := (algorithm2_dsWith cfg κ).detect

/-- Wraps `algorithm2_ds cfg` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailure (cfg : Alg2Config) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure :=
  algorithm2_dsWithFailureWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)

/-- Wraps `algorithm2_dsOwn cfg` as a `MinCostFlow.IPM.MinRatioDataStructureWithFailure`. -/
noncomputable def algorithm2_dsWithFailureOwn (cfg : Alg2Config) :
    MinCostFlow.IPM.MinRatioDataStructureWithFailure :=
  algorithm2_dsWithFailureWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)

lemma algorithm2_eraseFailure_state_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t =
      minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    change (if isUpdate (t + 1) then
        ((algorithm2_dsWithFailureWith cfg κ).update
          (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)
          (D.U (t + 1)) (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1
      else ((algorithm2_dsWithFailureWith cfg κ).detect
        (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)).2) = _
    rw [ih]
    rfl

lemma algorithm2_eraseFailure_state_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailure cfg).eraseFailure D η isUpdate t =
      minRatioFailState (algorithm2_ds cfg) D η isUpdate t :=
  algorithm2_eraseFailure_state_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate t

lemma algorithm2_failureDirection_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    MinCostFlow.IPM.minRatioFailureDirection (algorithm2_dsWithFailureWith cfg κ) D η isUpdate t =
      minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate t := by
  unfold MinCostFlow.IPM.minRatioFailureDirection minRatioFailOptDir
  rw [algorithm2_eraseFailure_state_eq_with]
  rfl

lemma algorithm2_failureDirection_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) :
    MinCostFlow.IPM.minRatioFailureDirection (algorithm2_dsWithFailure cfg) D η isUpdate t =
      minRatioFailOptDir (algorithm2_ds cfg) D η isUpdate t :=
  algorithm2_failureDirection_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate t

lemma algorithm2_eraseFailure_increment_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (s e : ℕ) :
    MinCostFlow.IPM.minRatioIncrement (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate s e =
      minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate s e := by
  cases s with
  | zero => rfl
  | succ s =>
    simp only [MinCostFlow.IPM.minRatioIncrement, minRatioFailIncrement]
    have hdir : MinCostFlow.IPM.minRatioDirection (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate s =
        (minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate s).getD (fun _ => 0) := by
      unfold MinCostFlow.IPM.minRatioDirection
      change ((algorithm2_dsWithFailureWith cfg κ).update
        (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate s)
        (D.U (s + 1)) (D.g (s + 1)) (D.ℓ (s + 1)) (η (s + 1))).2.getD (fun _ => 0) = _
      rw [algorithm2_eraseFailure_state_eq_with]
      rfl
    rw [hdir]
    cases minRatioFailOptDir (algorithm2_dsWith cfg κ) D η isUpdate s with
    | none => simp
    | some Δ => rfl

lemma algorithm2_eraseFailure_increment_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (s e : ℕ) :
    MinCostFlow.IPM.minRatioIncrement (algorithm2_dsWithFailure cfg).eraseFailure D η isUpdate s e =
      minRatioFailIncrement (algorithm2_ds cfg) D η isUpdate s e :=
  algorithm2_eraseFailure_increment_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate s e

lemma algorithm2_eraseFailure_flow_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    MinCostFlow.IPM.minRatioFlow (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t e =
      minRatioFailFlow (algorithm2_dsWith cfg κ) D η isUpdate t e := by
  unfold MinCostFlow.IPM.minRatioFlow minRatioFailFlow
  refine Finset.sum_congr rfl fun s _ => ?_
  exact algorithm2_eraseFailure_increment_eq_with cfg κ D η isUpdate s e

lemma algorithm2_eraseFailure_flow_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    MinCostFlow.IPM.minRatioFlow (algorithm2_dsWithFailure cfg).eraseFailure D η isUpdate t e =
      minRatioFailFlow (algorithm2_ds cfg) D η isUpdate t e :=
  algorithm2_eraseFailure_flow_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate t e

lemma algorithm2_eraseFailure_last_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    MinCostFlow.IPM.minRatioLast (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t e =
      minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e := by
  induction t with
  | zero => rfl
  | succ t ih =>
    unfold MinCostFlow.IPM.minRatioLast minRatioFailLast
    change (if isUpdate (t + 1) = false ∧ e ∈ ((algorithm2_dsWithFailureWith cfg κ).detect
        (MinCostFlow.IPM.minRatioState (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t)).1
      then t + 1
      else MinCostFlow.IPM.minRatioLast (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate t e) = _
    rw [algorithm2_eraseFailure_state_eq_with, ih]
    rfl

lemma algorithm2_eraseFailure_last_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) :
    MinCostFlow.IPM.minRatioLast (algorithm2_dsWithFailure cfg).eraseFailure D η isUpdate t e =
      minRatioFailLast (algorithm2_ds cfg) D η isUpdate t e :=
  algorithm2_eraseFailure_last_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate t e

lemma algorithm2_eraseFailure_detectSet_eq_with (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (ε : ℝ) (t : ℕ) :
    MinCostFlow.IPM.minRatioDetectSet (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate ε t =
      minRatioFailDetectSet (algorithm2_dsWith cfg κ) D η isUpdate ε t := by
  unfold MinCostFlow.IPM.minRatioDetectSet minRatioFailDetectSet
  ext e
  simp only [Finset.mem_filter]
  refine and_congr Iff.rfl ?_
  rw [algorithm2_eraseFailure_last_eq_with]
  have hsum : ∑ s ∈ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) (t + 1),
        |MinCostFlow.IPM.minRatioIncrement (algorithm2_dsWithFailureWith cfg κ).eraseFailure D η isUpdate s e| =
      ∑ s ∈ Finset.Ioc (minRatioFailLast (algorithm2_dsWith cfg κ) D η isUpdate t e) (t + 1),
        |minRatioFailIncrement (algorithm2_dsWith cfg κ) D η isUpdate s e| := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [algorithm2_eraseFailure_increment_eq_with]
  rw [hsum]

lemma algorithm2_eraseFailure_detectSet_eq (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (ε : ℝ) (t : ℕ) :
    MinCostFlow.IPM.minRatioDetectSet (algorithm2_dsWithFailure cfg).eraseFailure D η isUpdate ε t =
      minRatioFailDetectSet (algorithm2_ds cfg) D η isUpdate ε t :=
  algorithm2_eraseFailure_detectSet_eq_with cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    D η isUpdate ε t

end IPMBridge

section UnconditionalBounds

/-- Total number of edge updates across update batches in steps `1 .. T`. -/
def alg2UpdateQueries (D : DynamicInstance) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sum fun s => if isUpdate s then (D.U s).length else 0

/-- Total number of `Update` calls in steps `1 .. T`. -/
def alg2UpdateCount (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  (Finset.range T).sum fun s => if isUpdate (s + 1) then 1 else 0

/-- Total number of edges returned by `Detect` calls in steps `1 .. T` for `algorithm2_dsWith cfg κ`. -/
noncomputable def alg2DetectSizeWith (cfg : Alg2Config) (κ : ℝ) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sum fun s =>
    if isUpdate s = false then
      ((algorithm2_dsWith cfg κ).detect (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card
    else 0

/-- Total number of edges returned by `Detect` calls in steps `1 .. T`. -/
noncomputable def alg2DetectSize (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  alg2DetectSizeWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate T

/-- Total number of edges returned by `Detect` calls in steps `1 .. T` for `algorithm2_dsOwn`. -/
noncomputable def alg2DetectSizeOwn (cfg : Alg2Config) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  alg2DetectSizeWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) D η isUpdate T

/-- Total number of `Detect` calls in steps `1 .. T`. -/
def alg2DetectCount (isUpdate : ℕ → Bool) (T : ℕ) : ℕ :=
  (Finset.Icc 1 T).sum fun s => if isUpdate s = false then 1 else 0

/-- Amortized LCT operation charge at `O(log N₀)` per LCT operation. -/
noncomputable def alg2LctAmortizedCharge (N₀ lctOps : ℕ) : ℝ :=
  (1 + Real.log ((N₀ : ℝ) + 2)) * (lctOps : ℝ)

/-- Unconditional Tree-Chain runtime bound `eq:restatingTimeBoundSR` (`jtree.tex` page 30). -/
noncomputable def alg2RuntimeBoundSR (cfg : Alg2Config) (st : Alg2State cfg) : ℝ :=
  ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
    (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
    (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
    (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1) *
    ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i) +
    st.largeBatchEnc

/-- Unconditional `T^𝒢` edge-update bound in `s_i, r_i`. -/
noncomputable def alg2TreeUpdatesBoundSR (cfg : Alg2Config) (st : Alg2State cfg) : ℝ :=
  (14 * (cfg.P.d : ℝ) + 36) *
    (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1) *
    ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i)

lemma largeBatchEnc_le_linear_log {cfg : Alg2Config} {D : DynamicInstance}
    {isUpdate : ℕ → Bool} {T : ℕ} {enc : ℝ}
    (hEnc : enc ≤ (Finset.Icc 1 T).sum fun s =>
      if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) :
    enc ≤ 40 * (alg2UpdateQueries D isUpdate T : ℝ) *
      Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) := by
  set Q := alg2UpdateQueries D isUpdate T
  have hQ_nn : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  have hM_nn : (0 : ℝ) ≤ (cfg.P.M₀ : ℝ) := Nat.cast_nonneg cfg.P.M₀
  have hsum : (Finset.Icc 1 T).sum (fun s =>
        if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) ≤
      (Finset.Icc 1 T).sum (fun s =>
        40 * ((if isUpdate s then (D.U s).length else 0 : ℕ) : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2)) := by
    refine Finset.sum_le_sum fun s hs => ?_
    by_cases hu : isUpdate s = true
    · simp only [hu, ↓reduceIte]
      unfold largeBatchEncCap
      split_ifs with hle
      · have hlog_nn : 0 ≤ Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) :=
          Real.log_nonneg (by linarith)
        positivity
      · have hUs_gt : (cfg.P.M₀ : ℝ) < ((D.U s).length : ℝ) := by
          exact_mod_cast Nat.lt_of_not_ge hle
        have hUs_le_Q : (D.U s).length ≤ Q := by
          have h1 : (D.U s).length = (if isUpdate s then (D.U s).length else 0) := by simp [hu]
          rw [h1]
          exact Finset.single_le_sum (f := fun j => if isUpdate j then (D.U j).length else 0)
            (fun _ _ => Nat.zero_le _) hs
        have hUs_le_QR : ((D.U s).length : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hUs_le_Q
        have hlog_le : Real.log ((cfg.P.M₀ : ℝ) + ((D.U s).length : ℝ) + 2) ≤
            Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) :=
          Real.log_le_log (by linarith) (by linarith)
        have hcoeff : 20 * ((cfg.P.M₀ : ℝ) + ((D.U s).length : ℝ)) ≤ 40 * ((D.U s).length : ℝ) := by
          linarith
        calc
          20 * ((cfg.P.M₀ : ℝ) + ((D.U s).length : ℝ)) *
              Real.log ((cfg.P.M₀ : ℝ) + ((D.U s).length : ℝ) + 2)
              ≤ (40 * ((D.U s).length : ℝ)) * Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) :=
            mul_le_mul hcoeff hlog_le (Real.log_nonneg (by linarith)) (by positivity)
          _ = 40 * ((D.U s).length : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) := by ring
    · have hf : isUpdate s = false := Bool.eq_false_iff.mpr hu
      simp [hf]
  have hRHS : (Finset.Icc 1 T).sum (fun s =>
        40 * ((if isUpdate s then (D.U s).length else 0 : ℕ) : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2)) =
      40 * (Q : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) := by
    have hpull : ∀ s, 40 * ((if isUpdate s then (D.U s).length else 0 : ℕ) : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) =
        (40 * Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2)) *
          ((if isUpdate s then (D.U s).length else 0 : ℕ) : ℝ) := fun s => by ring
    simp_rw [hpull, ← Finset.mul_sum, ← Nat.cast_sum]
    change 40 * Real.log ((cfg.P.M₀ : ℝ) + (Q : ℝ) + 2) * (Q : ℝ) = _
    ring
  linarith

/-- Eliminates `gameShiftBound` weighted by `powTerm P i` unconditionally via
`k ≤ 2 * M₀^{1/d}` (`P.hk_upper`). -/
lemma gameShiftBound_powTerm_sum_le (P : ChainParams) {Ψ_g : ℝ} (hΨ : 1 ≤ Ψ_g)
    (reb : ℕ → ℕ) :
    ∑ i ∈ Finset.range (P.d + 1), gameShiftBound P Ψ_g reb i * powTerm P i ≤
      ((P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
        ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hM_pos : (0 : ℝ) < (P.M₀ : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have hd_pos : (0 : ℝ) < (P.d : ℝ) := Nat.cast_pos.mpr P.hd
  have h20Ψ1 : (1 : ℝ) ≤ 20 * Ψ_g := by linarith
  have hPowScale : ∀ i' i : ℕ, i' ≤ i → i ≤ P.d →
      (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i') * powTerm P i ≤
        (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * powTerm P i' := by
    intro i' i hi'i hi_d
    have hk_up : (P.k : ℝ) ^ (i - i') ≤ 2 ^ (i - i') *
        ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i') := by
      calc
        (P.k : ℝ) ^ (i - i') ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i') :=
          pow_le_pow_left₀ hk_pos.le P.hk_upper (i - i')
        _ = 2 ^ (i - i') * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i') := mul_pow _ _ _
    have hM_mul : ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i') * powTerm P i = powTerm P i' := by
      unfold powTerm
      rw [← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) (i - i'),
        ← Real.rpow_mul hM_pos.le, ← Real.rpow_add hM_pos]
      congr 1
      rw [Nat.cast_sub hi'i]
      field_simp [hd_pos.ne']
      ring
    have hexp_eq : i + 1 - i' = (i - i') + 1 := by omega
    have h20_le : (10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i') ≤ (20 * Ψ_g) ^ (P.d + 1) := by
      have h1 : (10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i') ≤
          (10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i' + 1) := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)) ?_
        positivity
      calc
        (10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i')
            ≤ (10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i' + 1) := h1
        _ = (20 * Ψ_g) ^ (i - i' + 1) := by rw [← mul_pow]; ring_nf
        _ ≤ (20 * Ψ_g) ^ (P.d + 1) := pow_le_pow_right₀ h20Ψ1 (by omega)
    have hpowTerm_nn : 0 ≤ powTerm P i := le_trans zero_le_one (one_le_powTerm P hi_d)
    have hpowTerm'_nn : 0 ≤ powTerm P i' :=
      le_trans zero_le_one (one_le_powTerm P (le_trans hi'i hi_d))
    calc
      (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i') * powTerm P i
          = (10 * Ψ_g) ^ (i - i' + 1) * (P.k : ℝ) * ((P.k : ℝ) ^ (i - i') * powTerm P i) := by
        rw [hexp_eq, mul_pow, pow_succ]
        ring
      _ ≤ (10 * Ψ_g) ^ (i - i' + 1) * (P.k : ℝ) *
            ((2 ^ (i - i') * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i')) * powTerm P i) := by
        gcongr
      _ = ((10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i')) * (P.k : ℝ) *
            (((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ (i - i') * powTerm P i) := by ring
      _ = ((10 * Ψ_g) ^ (i - i' + 1) * 2 ^ (i - i')) * (P.k : ℝ) * powTerm P i' := by
        rw [hM_mul]
      _ ≤ (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * powTerm P i' := by
        gcongr
  have hSingle : ∀ i ∈ Finset.range (P.d + 1),
      gameShiftBound P Ψ_g reb i * powTerm P i ≤
        ((P.d : ℝ) + 1) * (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
          ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') := by
    intro i hi
    have hi_d : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hinit : (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1) * powTerm P i ≤
        (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * (P.M₀ : ℝ) := by
      simpa [powTerm_zero P] using hPowScale 0 i (Nat.zero_le i) hi_d
    have hreb_part : (∑ i' ∈ Finset.range (i + 1),
          (reb i' : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i')) * powTerm P i ≤
        (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
          ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i' := by
      rw [Finset.sum_mul]
      have hle_sub : ∑ i' ∈ Finset.range (i + 1),
            (reb i' : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i') * powTerm P i ≤
          ∑ i' ∈ Finset.range (i + 1),
            (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * ((reb i' : ℝ) * powTerm P i') := by
        refine Finset.sum_le_sum fun i' hi' => ?_
        have hi'_le : i' ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
        calc
          (reb i' : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i') * powTerm P i
              = (reb i' : ℝ) * ((10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i') * powTerm P i) := by ring
          _ ≤ (reb i' : ℝ) * ((20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * powTerm P i') :=
            mul_le_mul_of_nonneg_left (hPowScale i' i hi'_le hi_d) (Nat.cast_nonneg _)
          _ = (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * ((reb i' : ℝ) * powTerm P i') := by ring
      have hsub_tot : ∑ i' ∈ Finset.range (i + 1),
            (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * ((reb i' : ℝ) * powTerm P i') ≤
          ∑ i' ∈ Finset.range (P.d + 1),
            (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) * ((reb i' : ℝ) * powTerm P i') := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
        intro x hx _
        have hx_le : x ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
        have hpx : 0 ≤ powTerm P x := le_trans zero_le_one (one_le_powTerm P hx_le)
        positivity
      conv_rhs at hsub_tot => rw [← Finset.mul_sum]
      exact le_trans hle_sub hsub_tot
    have hboth : gameShiftBound P Ψ_g reb i * powTerm P i ≤
        (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
          ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') := by
      unfold gameShiftBound
      rw [add_mul]
      linarith
    have hd1 : (1 : ℝ) ≤ (P.d : ℝ) + 1 := by linarith
    have hnn : 0 ≤ (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
        ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') := by
      have hsum_nn : 0 ≤ ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i' :=
        Finset.sum_nonneg fun i' hi' =>
          mul_nonneg (Nat.cast_nonneg _)
            (le_trans zero_le_one (one_le_powTerm P (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi'))))
      positivity
    calc
      gameShiftBound P Ψ_g reb i * powTerm P i
          ≤ 1 * ((20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
              ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i')) := by
        simpa using hboth
      _ ≤ ((P.d : ℝ) + 1) * ((20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
              ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i')) :=
        mul_le_mul_of_nonneg_right hd1 hnn
      _ = _ := by ring
  calc
    ∑ i ∈ Finset.range (P.d + 1), gameShiftBound P Ψ_g reb i * powTerm P i
        ≤ ∑ _i ∈ Finset.range (P.d + 1),
            ((P.d : ℝ) + 1) * (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
              ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') :=
      Finset.sum_le_sum hSingle
    _ = ((P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (P.d + 1) * (P.k : ℝ) *
          ((P.M₀ : ℝ) + ∑ i' ∈ Finset.range (P.d + 1), (reb i' : ℝ) * powTerm P i') := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

lemma sum_shiftCount_le_sum_powTerm (P : ChainParams) (s : ℕ → ℕ) :
    ∑ i ∈ Finset.range (P.d + 1), (s i : ℝ) ≤
      ∑ i ∈ Finset.range (P.d + 1), (s i : ℝ) * powTerm P i := by
  refine Finset.sum_le_sum fun i hi => ?_
  have hi_d : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  calc
    (s i : ℝ) = (s i : ℝ) * 1 := (mul_one _).symm
    _ ≤ (s i : ℝ) * powTerm P i :=
      mul_le_mul_of_nonneg_left (one_le_powTerm P hi_d) (Nat.cast_nonneg _)

/-- Combined non-asymptotic complexity theorem (**Theorem 5.1**, unconditional on hidden stability)
for `algorithm2_dsWith cfg κ` on any valid sequence up to stage `T`. -/
theorem theorem_5_1_uncond_complexity_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
        (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
    let Tfac := (14 * (cfg.P.d : ℝ) + 36) *
        (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1)
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
    (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
    (∀ i : Fin (cfg.P.d + 1),
      (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
    (st.lctUpdateOps : ℝ) ≤ (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
      2 * ((cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) : ℝ) + 3) *
        ((K_upd : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ)) ∧
    (st.lctDetectOps : ℝ) ≤ (Q_det : ℝ) + (K_det : ℝ) ∧
    (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
      Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) +
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
          2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) +
      40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
    (st.chain.totalTreeUpdates : ℝ) ≤
      Tfac * Sfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
  have hUncond := (algorithm2_uncond_preserves_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound).1 T (le_refl T)
  rcases hUncond with ⟨hInv, hBud, _, hEnc, _, _, _, _, _, _, _, hShB, _, hLctU, hLctD⟩
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
  have hRT_raw := totalRuntime_collapse_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hγM₀ hV.hγk hInv hBud
  have hTU_raw := totalTreeUpdates_collapse_with_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P
    hV.hTP hV.hLP hV.hT hV.hγM₀ hV.hγk hInv hBud
  have hPrefix_nn : 0 ≤ ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) := by
    have := hV.hTP.2.2.2.2.2.2.2.2.2
    have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    positivity
  have hRT : (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st := by
    unfold alg2RuntimeBoundSR
    exact hRT_raw
  have hceil_le : (Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 2 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3 := by
    have hγnn : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := le_trans zero_le_one (hV.hTP.2.2.1 (cfg.P.M₀ ^ 2))
    linarith [Nat.ceil_lt_add_one hγnn]
  have hLctU : (st.lctUpdateOps : ℝ) ≤ (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) *
        ((alg2UpdateCount isUpdate T : ℝ) +
          ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ)) := by
    have hcast : (st.lctUpdateOps : ℝ) ≤ (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
        2 * ((Nat.ceil (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) : ℝ) + 2) *
          ((alg2UpdateCount isUpdate T : ℝ) +
            ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ)) := by
      exact_mod_cast hLctU
    have hsum_nn : 0 ≤ (alg2UpdateCount isUpdate T : ℝ) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) := by positivity
    nlinarith
  have hLctD : (st.lctDetectOps : ℝ) ≤
      (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ) := by
    have hsum_split : (Finset.Icc 1 T).sum (fun s =>
          if isUpdate s = false then
            ((algorithm2_dsWith cfg κ).detect
              (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate (s - 1))).1.card + 1
          else 0) =
        alg2DetectSizeWith cfg κ D η isUpdate T + alg2DetectCount isUpdate T := by
      unfold alg2DetectSizeWith alg2DetectCount
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      split_ifs <;> omega
    rw [hsum_split] at hLctD
    exact_mod_cast hLctD
  have hEnc_bound := largeBatchEnc_le_linear_log (cfg := cfg) (D := D) (isUpdate := isUpdate) hEnc
  have hShiftSum_le : ∑ i ∈ Finset.range (cfg.P.d + 1),
        (st.chain.shiftCount i : ℝ) * powTerm cfg.P i ≤
      ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * alg2PsiGame cfg.Ψ cfg.P.M₀) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) *
        ((cfg.P.M₀ : ℝ) + ∑ i' ∈ Finset.range (cfg.P.d + 1),
          (st.chain.rebuildCount i' : ℝ) * powTerm cfg.P i') := by
    have h1 : ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i ≤
        ∑ i ∈ Finset.range (cfg.P.d + 1),
          gameShiftBound cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) st.chain.rebuildCount i *
            powTerm cfg.P i := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hi_lt := Finset.mem_range.mp hi
      have hpow_nn : 0 ≤ powTerm cfg.P i :=
        le_trans zero_le_one (one_le_powTerm cfg.P (Nat.lt_succ_iff.mp hi_lt))
      exact mul_le_mul_of_nonneg_right (hShB ⟨i, hi_lt⟩) hpow_nn
    exact le_trans h1 (gameShiftBound_powTerm_sum_le cfg.P (alg2PsiGame_ge_one _ _) _)
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
  set RebTot := (cfg.P.M₀ : ℝ) +
    ∑ i' ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i' : ℝ) * powTerm cfg.P i'
  have hRebTot_nn : 0 ≤ RebTot := by
    have hs : 0 ≤ ∑ i' ∈ Finset.range (cfg.P.d + 1),
        (st.chain.rebuildCount i' : ℝ) * powTerm cfg.P i' :=
      Finset.sum_nonneg fun i hi => mul_nonneg (Nat.cast_nonneg _)
        (le_trans zero_le_one (one_le_powTerm cfg.P (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))))
    have := Nat.cast_nonneg (α := ℝ) cfg.P.M₀
    linarith
  have hSR_collapse : (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i ≤
      Sfac * RebTot := by
    have hsplit : ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i =
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i +
          ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.cast_add, add_mul]
    rw [show (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i =
        (∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i) +
          RebTot by rw [hsplit]; simp only [RebTot]; ring]
    calc
      (∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i) + RebTot
          ≤ (((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ)) * RebTot +
              1 * RebTot := by linarith [hShiftSum_le]
      _ = Sfac * RebTot := by simp only [Sfac]; ring
  set Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
      (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
  set Tfac := (14 * (cfg.P.d : ℝ) + 36) *
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1)
  have hCfac_nn : 0 ≤ Cfac := by
    have := one_le_logFactor cfg.P cfg.N₀
    exact mul_nonneg hPrefix_nn (pow_nonneg (by linarith) _)
  have hTfac_nn : 0 ≤ Tfac := by
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    positivity
  have hlogN_nn : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have h2 : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀]
    linarith [Real.log_nonneg h2]
  have hSh_le_Reb : ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) ≤
      Sfac * RebTot := by
    have h1 := sum_shiftCount_le_sum_powTerm cfg.P st.chain.shiftCount
    have h2 : Sfac * RebTot - RebTot =
        ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) * RebTot := by
      simp only [Sfac]; ring
    have hdiff_nn : 0 ≤ ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) * RebTot := by
      have := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
      positivity
    linarith [h1, hShiftSum_le, hRebTot_nn, h2, hdiff_nn]
  refine ⟨hRT, hTU_raw, hShB, hLctU, hLctD, hEnc_bound, ?_, ?_⟩
  · have hLctTotal : alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
        (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
          ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
            2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (alg2UpdateCount isUpdate T : ℝ) +
            (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) +
        2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (Sfac * RebTot) := by
      unfold alg2LctAmortizedCharge
      rw [Nat.cast_add]
      have hsumOps : (st.lctUpdateOps : ℝ) + (st.lctDetectOps : ℝ) ≤
          ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
            2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (alg2UpdateCount isUpdate T : ℝ) +
            (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) +
          2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (Sfac * RebTot) := by
        have hγnn : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3 := by
          linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
        nlinarith [hLctU, hLctD, hSh_le_Reb]
      have hmul := mul_le_mul_of_nonneg_left hsumOps hlogN_nn
      linarith
    have hRT_coll : (st.chain.totalRuntime : ℝ) ≤ Cfac * (Sfac * RebTot) +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) := by
      unfold alg2RuntimeBoundSR at hRT
      have h1 : Cfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i) ≤
          Cfac * (Sfac * RebTot) :=
        mul_le_mul_of_nonneg_left hSR_collapse hCfac_nn
      linarith [hRT, hEnc_bound, h1]
    linarith
  · calc
      (st.chain.totalTreeUpdates : ℝ) ≤ Tfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((st.chain.shiftCount i + st.chain.rebuildCount i : ℕ) : ℝ) * powTerm cfg.P i) := hTU_raw
      _ ≤ Tfac * (Sfac * RebTot) := mul_le_mul_of_nonneg_left hSR_collapse hTfac_nn
      _ = Tfac * Sfac * RebTot := by ring

/-- Combined non-asymptotic complexity theorem (**Theorem 5.1**, unconditional on hidden stability)
for `algorithm2_ds` on any valid sequence up to stage `T`. -/
theorem theorem_5_1_uncond_complexity {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
        (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
    let Tfac := (14 * (cfg.P.d : ℝ) + 36) *
        (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1)
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
    let Q_upd := alg2UpdateQueries D isUpdate T
    let K_upd := alg2UpdateCount isUpdate T
    let Q_det := alg2DetectSize cfg D η isUpdate T
    let K_det := alg2DetectCount isUpdate T
    (st.chain.totalRuntime : ℝ) ≤ alg2RuntimeBoundSR cfg st ∧
    (st.chain.totalTreeUpdates : ℝ) ≤ alg2TreeUpdatesBoundSR cfg st ∧
    (∀ i : Fin (cfg.P.d + 1),
      (st.chain.shiftCount i.val : ℝ) ≤ gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i.val) ∧
    (st.lctUpdateOps : ℝ) ≤ (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
      2 * ((cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) : ℝ) + 3) *
        ((K_upd : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ)) ∧
    (st.lctDetectOps : ℝ) ≤ (Q_det : ℝ) + (K_det : ℝ) ∧
    (st.largeBatchEnc : ℝ) ≤ 40 * (Q_upd : ℝ) *
      Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) +
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
          2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) +
      40 * (Q_upd : ℝ) * Real.log ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2) ∧
    (st.chain.totalTreeUpdates : ℝ) ≤
      Tfac * Sfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) :=
  theorem_5_1_uncond_complexity_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hmBound hnBound

end UnconditionalBounds

section RebuildFloorCollapse

/-- Global rebuild threshold floor, with a correction of the local versus global `Q`
(`jtree.tex:848`, page 30):
when `selfReb i` counts rebuilds initiated at level `i` (`reb i ≤ ∑_{i' ≤ i} selfReb i'`), and
each self-rebuild at `i < P.d` retires updates above the threshold floor
`M₀ / (k^{i+1} * log²(M₀ + N₀ + 2))` from level-`i` update traffic `≤ γ_r(M₀²)^i * Q_upd`
(plus at most `1` boundary/global step), `∑ r_i * powTerm P i` collapses cleanly. -/
def RebuildFloorHyp (TP : SparseCoreParams) (P : ChainParams) (N₀ Q_upd : ℕ)
    (reb selfReb : ℕ → ℕ) : Prop :=
  (∀ i ≤ P.d, reb i ≤ ∑ i' ∈ Finset.range (i + 1), selfReb i') ∧
  (selfReb P.d = 0) ∧
  (∀ i < P.d,
    (selfReb i : ℝ) * ((P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * (logFactor P N₀) ^ 2)) ≤
      16 * (TP.γ_r (P.M₀ ^ 2)) ^ i * (Q_upd : ℝ) +
        (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i + 1) * (logFactor P N₀) ^ 2))

lemma rebuildWork_collapse_of_floor {TP : SparseCoreParams} {P : ChainParams}
    (hTP : TP.Valid) {N₀ Q_upd : ℕ} {reb selfReb : ℕ → ℕ}
    (hFl : RebuildFloorHyp TP P N₀ Q_upd reb selfReb) :
    ∑ i ∈ Finset.range (P.d + 1), (reb i : ℝ) * powTerm P i ≤
      16 * ((P.d : ℝ) + 1) ^ 2 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
        (Q_upd : ℝ) + ((P.d : ℝ) + 1) ^ 2 * (P.M₀ : ℝ) := by
  have hM1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hM_pos : (0 : ℝ) < (P.M₀ : ℝ) := lt_of_lt_of_le zero_lt_one hM1
  have hk_pos : (0 : ℝ) < (P.k : ℝ) := Nat.cast_pos.mpr P.hk
  have hL1 : (1 : ℝ) ≤ logFactor P N₀ := one_le_logFactor P N₀
  have hγr1 : (1 : ℝ) ≤ TP.γ_r (P.M₀ ^ 2) := hTP.2.2.2.2.2.2.1 (P.M₀ ^ 2)
  have hSelfTerm : ∀ i' ∈ Finset.range P.d,
      (selfReb i' : ℝ) * powTerm P i' ≤
        16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 * (Q_upd : ℝ) + (P.M₀ : ℝ) := by
    intro i' hi'
    have hi'_lt : i' < P.d := Finset.mem_range.mp hi'
    have hi'_le : i' ≤ P.d := hi'_lt.le
    set θ := (P.M₀ : ℝ) / ((P.k : ℝ) ^ (i' + 1) * (logFactor P N₀) ^ 2)
    have hθ_pos : 0 < θ := by positivity
    have hfl := hFl.2.2 i' hi'_lt
    have hpow_div : powTerm P i' / θ ≤ 2 ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 := by
      have hhk : (P.k : ℝ) ^ i' ≤ 2 ^ i' * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i' := by
        calc
          (P.k : ℝ) ^ i' ≤ (2 * (P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i' :=
            pow_le_pow_left₀ hk_pos.le P.hk_upper i'
          _ = 2 ^ i' * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i' := mul_pow _ _ _
      have hm_eq : powTerm P i' * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i' = (P.M₀ : ℝ) := by
        unfold powTerm
        have hd_pos : (0 : ℝ) < P.d := Nat.cast_pos.mpr P.hd
        rw [← Real.rpow_natCast ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) i',
          ← Real.rpow_mul hM_pos.le, ← Real.rpow_add hM_pos]
        have hexp : (1 - (i' : ℝ) / (P.d : ℝ)) + (1 / (P.d : ℝ) * (i' : ℝ)) = 1 := by
          field_simp [hd_pos.ne']; ring
        rw [hexp, Real.rpow_one]
      have hmul_pow : powTerm P i' * (P.k : ℝ) ^ i' ≤ 2 ^ P.d * (P.M₀ : ℝ) := by
        have hpow_nn : 0 ≤ powTerm P i' := le_trans zero_le_one (one_le_powTerm P hi'_le)
        calc
          powTerm P i' * (P.k : ℝ) ^ i'
              ≤ powTerm P i' * (2 ^ i' * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i') :=
            mul_le_mul_of_nonneg_left hhk hpow_nn
          _ = 2 ^ i' * (powTerm P i' * ((P.M₀ : ℝ) ^ (1 / (P.d : ℝ))) ^ i') := by ring
          _ = 2 ^ i' * (P.M₀ : ℝ) := by rw [hm_eq]
          _ ≤ 2 ^ P.d * (P.M₀ : ℝ) := by gcongr; norm_num
      have h_eq : powTerm P i' / θ =
          (powTerm P i' * (P.k : ℝ) ^ i' / (P.M₀ : ℝ)) * (P.k : ℝ) * (logFactor P N₀) ^ 2 := by
        simp only [θ, pow_succ]
        field_simp [hM_pos.ne', hk_pos.ne', (by positivity : (logFactor P N₀) ≠ 0)]
      rw [h_eq]
      calc
        (powTerm P i' * (P.k : ℝ) ^ i' / (P.M₀ : ℝ)) * (P.k : ℝ) * (logFactor P N₀) ^ 2
            ≤ (2 ^ P.d * (P.M₀ : ℝ) / (P.M₀ : ℝ)) * (P.k : ℝ) * (logFactor P N₀) ^ 2 := by
          gcongr
        _ = 2 ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 := by
          field_simp [hM_pos.ne']
    have hself_le : (selfReb i' : ℝ) ≤ 16 * (TP.γ_r (P.M₀ ^ 2)) ^ i' * (Q_upd : ℝ) / θ + 1 := by
      have hdiv := div_le_div_of_nonneg_right hfl hθ_pos.le
      rw [mul_div_cancel_right₀ _ hθ_pos.ne', add_div, div_self hθ_pos.ne'] at hdiv
      exact hdiv
    have hpow_nn : 0 ≤ powTerm P i' := le_trans zero_le_one (one_le_powTerm P hi'_le)
    have hpow_le_M : powTerm P i' ≤ (P.M₀ : ℝ) := by
      simpa [powTerm_zero P] using powTerm_antitone P (Nat.zero_le i')
    have hγi : (TP.γ_r (P.M₀ ^ 2)) ^ i' ≤ (TP.γ_r (P.M₀ ^ 2)) ^ P.d := pow_le_pow_right₀ hγr1 hi'_le
    calc
      (selfReb i' : ℝ) * powTerm P i'
          ≤ (16 * (TP.γ_r (P.M₀ ^ 2)) ^ i' * (Q_upd : ℝ) / θ + 1) * powTerm P i' :=
        mul_le_mul_of_nonneg_right hself_le hpow_nn
      _ = 16 * (TP.γ_r (P.M₀ ^ 2)) ^ i' * (Q_upd : ℝ) * (powTerm P i' / θ) + powTerm P i' := by ring
      _ ≤ 16 * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (Q_upd : ℝ) * (2 ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2) +
            (P.M₀ : ℝ) := by
        have h1 : 16 * (TP.γ_r (P.M₀ ^ 2)) ^ i' * (Q_upd : ℝ) * (powTerm P i' / θ) ≤
            16 * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (Q_upd : ℝ) * (2 ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2) := by
          gcongr
        linarith
      _ = _ := by ring
  have hSelfSum : ∑ i' ∈ Finset.range P.d, (selfReb i' : ℝ) * powTerm P i' ≤
      (P.d : ℝ) * (16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
        (Q_upd : ℝ) + (P.M₀ : ℝ)) := by
    calc
      ∑ i' ∈ Finset.range P.d, (selfReb i' : ℝ) * powTerm P i'
          ≤ ∑ _i' ∈ Finset.range P.d,
              (16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 * (Q_upd : ℝ) +
                (P.M₀ : ℝ)) := Finset.sum_le_sum hSelfTerm
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTerm_i : ∀ i ∈ Finset.range (P.d + 1),
      (reb i : ℝ) * powTerm P i ≤
        ((P.d : ℝ) + 1) * (16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
          (Q_upd : ℝ) + (P.M₀ : ℝ)) := by
    intro i hi
    have hi_le : i ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hpow_nn : 0 ≤ powTerm P i := le_trans zero_le_one (one_le_powTerm P hi_le)
    have h1 : (reb i : ℝ) ≤ ∑ i' ∈ Finset.range (i + 1), (selfReb i' : ℝ) := by
      exact_mod_cast hFl.1 i hi_le
    have hreb_pow : (reb i : ℝ) * powTerm P i ≤
        ∑ i' ∈ Finset.range P.d, (selfReb i' : ℝ) * powTerm P i' := by
      calc
        (reb i : ℝ) * powTerm P i
            ≤ (∑ i' ∈ Finset.range (i + 1), (selfReb i' : ℝ)) * powTerm P i :=
          mul_le_mul_of_nonneg_right h1 hpow_nn
        _ = ∑ i' ∈ Finset.range (i + 1), (selfReb i' : ℝ) * powTerm P i := by rw [Finset.sum_mul]
        _ ≤ ∑ i' ∈ Finset.range (i + 1), (selfReb i' : ℝ) * powTerm P i' := by
          refine Finset.sum_le_sum fun i' hi' => ?_
          have hi'_le : i' ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')
          exact mul_le_mul_of_nonneg_left (powTerm_antitone P hi'_le) (Nat.cast_nonneg _)
        _ ≤ ∑ i' ∈ Finset.range (P.d + 1), (selfReb i' : ℝ) * powTerm P i' := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) ?_
          intro x hx _
          have hx_le : x ≤ P.d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
          exact mul_nonneg (Nat.cast_nonneg _) (le_trans zero_le_one (one_le_powTerm P hx_le))
        _ = ∑ i' ∈ Finset.range P.d, (selfReb i' : ℝ) * powTerm P i' := by
          rw [Finset.sum_range_succ, hFl.2.1, Nat.cast_zero, zero_mul, add_zero]
    have hterm_nn : 0 ≤ 16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
        (Q_upd : ℝ) + (P.M₀ : ℝ) := by positivity
    have hd_le : (P.d : ℝ) ≤ (P.d : ℝ) + 1 := by linarith
    exact le_trans hreb_pow (le_trans hSelfSum (mul_le_mul_of_nonneg_right hd_le hterm_nn))
  calc
    ∑ i ∈ Finset.range (P.d + 1), (reb i : ℝ) * powTerm P i
        ≤ ∑ _i ∈ Finset.range (P.d + 1),
            ((P.d : ℝ) + 1) * (16 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
              (Q_upd : ℝ) + (P.M₀ : ℝ)) := Finset.sum_le_sum hTerm_i
    _ = 16 * ((P.d : ℝ) + 1) ^ 2 * 2 ^ P.d * (TP.γ_r (P.M₀ ^ 2)) ^ P.d * (P.k : ℝ) * (logFactor P N₀) ^ 2 *
          (Q_upd : ℝ) + ((P.d : ℝ) + 1) ^ 2 * (P.M₀ : ℝ) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      ring

/-- Combined amortized overhead factor in the global-threshold-floor bound (`eq:restatingTimeBoundSR`
after eliminating `s_i` and `r_i`). -/
noncomputable def alg2CollapsedFactor (cfg : Alg2Config) : ℝ :=
  let Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
      (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
  let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
  let Rfac := 16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
      (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2 + ((cfg.P.d : ℝ) + 1) ^ 2 + 1
  (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac * Rfac +
    (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1)

private lemma alg2_collapse_algebra {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    (reb : ℕ → ℕ) (Q_upd K_upd Q_det K_det : ℕ) (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ Q_upd reb selfReb) :
    let Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
        (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
        (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
        (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
    (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (reb i : ℝ) * powTerm cfg.P i) +
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
          2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) ≤
      alg2CollapsedFactor cfg *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
  set Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
      (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
  set Rfac := 16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
      (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2 + ((cfg.P.d : ℝ) + 1) ^ 2 + 1
  have hReb := rebuildWork_collapse_of_floor hV.hTP hFl
  have hRebTot : (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      (reb i : ℝ) * powTerm cfg.P i ≤ Rfac * ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ)) := by
    have hM_nn : (0 : ℝ) ≤ (cfg.P.M₀ : ℝ) := Nat.cast_nonneg _
    have hQ_nn : (0 : ℝ) ≤ (Q_upd : ℝ) := Nat.cast_nonneg _
    set A := 16 * ((cfg.P.d : ℝ) + 1) ^ 2 * 2 ^ cfg.P.d * (cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ cfg.P.d *
        (cfg.P.k : ℝ) * (logFactor cfg.P cfg.N₀) ^ 2
    set D := ((cfg.P.d : ℝ) + 1) ^ 2 + 1
    have hA_nn : 0 ≤ A := by
      have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2); have := one_le_logFactor cfg.P cfg.N₀; positivity
    have hD_nn : 0 ≤ D := by positivity
    have hR_eq : Rfac = A + D := by simp only [Rfac, A, D]; ring
    calc
      (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (reb i : ℝ) * powTerm cfg.P i
          ≤ (cfg.P.M₀ : ℝ) + (A * (Q_upd : ℝ) + ((cfg.P.d : ℝ) + 1) ^ 2 * (cfg.P.M₀ : ℝ)) := by
        linarith only [hReb]
      _ = A * (Q_upd : ℝ) + D * (cfg.P.M₀ : ℝ) := by simp only [D]; ring
      _ ≤ Rfac * (Q_upd : ℝ) + Rfac * (cfg.P.M₀ : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_right (by rw [hR_eq]; linarith only [hD_nn]) hQ_nn)
          (mul_le_mul_of_nonneg_right (by rw [hR_eq]; linarith only [hA_nn]) hM_nn)
      _ = Rfac * ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ)) := by ring
  have hPref_nn : 0 ≤ (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac := by
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2); have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    have := one_le_logFactor cfg.P cfg.N₀; have := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    positivity
  have hMQ_le : (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) ≤
      (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) K_upd; have := Nat.cast_nonneg (α := ℝ) Q_det
    have := Nat.cast_nonneg (α := ℝ) K_det; linarith
  have hRfac_nn : 0 ≤ Rfac := by
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2); have := one_le_logFactor cfg.P cfg.N₀; positivity
  have hPart1 : (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac *
      ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (reb i : ℝ) * powTerm cfg.P i) ≤
      ((Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac * Rfac) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) :=
    le_trans (mul_le_mul_of_nonneg_left hRebTot hPref_nn)
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hMQ_le (mul_nonneg hPref_nn hRfac_nn))
  have hPart2 : (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
      ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
        2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) ≤
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
    have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
      have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2); linarith
    have h2γ_nn : 0 ≤ 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) := by linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
    have h2γ1 : 1 ≤ 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1 := by linarith only [h2γ_nn]
    have h2γK : 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) ≤
        (2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1) * (K_upd : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only) (Nat.cast_nonneg _)
    have h1 : (cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
        2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ) ≤
        (2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1) *
          ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
      have hM_le := mul_le_mul_of_nonneg_right h2γ1 (Nat.cast_nonneg (α := ℝ) cfg.P.M₀)
      have hQ_le := mul_le_mul_of_nonneg_right h2γ1 (Nat.cast_nonneg (α := ℝ) Q_upd)
      have hQd_le := mul_le_mul_of_nonneg_right h2γ1 (Nat.cast_nonneg (α := ℝ) Q_det)
      have hKd_le := mul_le_mul_of_nonneg_right h2γ1 (Nat.cast_nonneg (α := ℝ) K_det)
      linarith only [h2γK, hM_le, hQ_le, hQd_le, hKd_le]
    calc
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
          ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
            2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ))
          ≤ (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * ((2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) + 1) *
              ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 hln
      _ = _ := by ring
  unfold alg2CollapsedFactor; dsimp only; linarith only [hPart1, hPart2]

/-- Under `RebuildFloorHyp`, total runtime + LCT charge collapses cleanly to
`alg2CollapsedFactor cfg * (M₀ + Q_upd + K_upd + Q_det + K_det)` plus the large-batch encoding
term `40 * Q_upd * log(M₀ + Q_upd + 2)` (which is `0` when all batches satisfy `|U| ≤ M₀`). -/
theorem theorem_5_1_collapsed_of_floor_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount selfReb) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) := by
  have hU := theorem_5_1_uncond_complexity_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound
  dsimp only at hU
  rcases hU with ⟨_, _, _, _, _, _, hTot, _⟩
  have hAlg := alg2_collapse_algebra hV
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount
    (alg2UpdateQueries D isUpdate T) (alg2UpdateCount isUpdate T)
    (alg2DetectSizeWith cfg κ D η isUpdate T) (alg2DetectCount isUpdate T) selfReb hFl
  dsimp only at hAlg
  linarith only [hTot, hAlg]

theorem theorem_5_1_collapsed_of_floor {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.rebuildCount selfReb) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSize cfg D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot +
        40 * (alg2UpdateQueries D isUpdate T : ℝ) *
          Real.log ((cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) + 2) :=
  theorem_5_1_collapsed_of_floor_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hmBound hnBound selfReb hFl

/-- Unconditional `Detect` LCT amortized charge bound (`jtree.tex` lines 20–21):
`(1 + log(N₀ + 2)) * lctDetectOps ≤ (1 + log(N₀ + 2)) * (Q_det + K_det)`, holding with zero
rebuild-floor or hidden-stability hypotheses. -/
theorem alg2Detect_work_le_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) := by
  have hU := theorem_5_1_uncond_complexity_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound
  dsimp only at hU
  have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  exact mul_le_mul_of_nonneg_left hU.2.2.2.2.1 hln

theorem alg2Detect_work_le {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((alg2DetectSize cfg D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) :=
  alg2Detect_work_le_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hmBound hnBound

/-- When every update batch has size `≤ cfg.P.M₀`, no large-batch overflow accumulates:
`st.largeBatchEnc = 0`. -/
theorem largeBatchEnc_eq_zero_of_le_M₀_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) :
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc = 0 := by
  have hUI := (algorithm2_uncond_preserves_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound).1 T (le_refl T)
  have h0 : 0 ≤ (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc := hUI.2.2.1
  have hLe : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc ≤
      (Finset.Icc 1 T).sum (fun s => if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) :=
    hUI.2.2.2.1
  have hSum0 : (Finset.Icc 1 T).sum (fun s => if isUpdate s then largeBatchEncCap cfg.P (D.U s) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    rcases Finset.mem_Icc.mp hs with ⟨hs1, hsT⟩
    by_cases hu : isUpdate s = true
    · simp only [hu, ↓reduceIte, largeBatchEncCap, hSmallBatch s hs1 hsT hu]
    · simp [hu]
  linarith

theorem largeBatchEnc_eq_zero_of_le_M₀ {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) :
    (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).largeBatchEnc = 0 :=
  largeBatchEnc_eq_zero_of_le_M₀_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV
    hHist hmBound hnBound hSmallBatch

/-- Under `RebuildFloorHyp` AND the small-batch assumption `(D.U t).length ≤ cfg.P.M₀`,
total runtime + LCT charge is bounded purely by `alg2CollapsedFactor cfg * Q_tot` with zero
`Q_upd log(M₀ + Q_upd)` overflow term. -/
theorem theorem_5_1_collapsed_of_floor_smallBatch_with {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀)
    (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount selfReb) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot := by
  have hU := theorem_5_1_uncond_complexity_with (cfg := cfg) (η := η) κ hV hHist hmBound hnBound
  dsimp only at hU
  rcases hU with ⟨hRun, _, hShB, hLctU, hLctD, _, _, _⟩
  have hZero : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc = 0 :=
    largeBatchEnc_eq_zero_of_le_M₀_with κ hV hHist hmBound hnBound hSmallBatch
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
  set Q_upd := alg2UpdateQueries D isUpdate T
  set K_upd := alg2UpdateCount isUpdate T
  set Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
  set K_det := alg2DetectCount isUpdate T
  set Cfac := ((cfg.P.d : ℝ) + 1) * (8 * cfg.TP.c_T + 81 * cfg.LP.c_last + 430) *
      (cfg.P.M₀ : ℝ) ^ (1 / (cfg.P.d : ℝ)) *
      (cfg.TP.γ_r (cfg.P.M₀ ^ 2) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2)) ^ (3 * cfg.P.d + 2)) *
      (2 * logFactor cfg.P cfg.N₀) ^ (max cfg.TP.p_T cfg.LP.p_last + 1)
  set Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  set Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
  have hPowNN : ∀ i, 0 ≤ powTerm cfg.P i := fun i =>
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hShPow : ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i ≤
      (Sfac - 1) * ((cfg.P.M₀ : ℝ) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
    have hSum : ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i ≤
        ∑ i ∈ Finset.range (cfg.P.d + 1),
          gameShiftBound cfg.P Ψ_g st.chain.rebuildCount i * powTerm cfg.P i := by
      refine Finset.sum_le_sum fun i hi => ?_
      exact mul_le_mul_of_nonneg_right (hShB ⟨i, Finset.mem_range.mp hi⟩) (hPowNN i)
    have hG := gameShiftBound_powTerm_sum_le cfg.P (alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀) st.chain.rebuildCount
    refine le_trans hSum ?_
    simpa only [Sfac, add_sub_cancel_right] using hG
  have hShSum : ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) ≤
      Sfac * ((cfg.P.M₀ : ℝ) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
    have h1 := sum_shiftCount_le_sum_powTerm cfg.P st.chain.shiftCount
    have hM_nn : (0 : ℝ) ≤ (cfg.P.M₀ : ℝ) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i :=
      add_nonneg (Nat.cast_nonneg _)
        (Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hPowNN i))
    linarith [le_trans h1 hShPow]
  have hSR : (cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
      ((st.chain.shiftCount i : ℝ) + (st.chain.rebuildCount i : ℝ)) * powTerm cfg.P i ≤
      Sfac * ((cfg.P.M₀ : ℝ) +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
    have hSplit : ∑ i ∈ Finset.range (cfg.P.d + 1),
        ((st.chain.shiftCount i : ℝ) + (st.chain.rebuildCount i : ℝ)) * powTerm cfg.P i =
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.shiftCount i : ℝ) * powTerm cfg.P i +
        ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    linarith [hShPow, hSplit]
  have hCfac_nn : 0 ≤ Cfac := by
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2); have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    have := one_le_logFactor cfg.P cfg.N₀; positivity
  have hRunZero : (st.chain.totalRuntime : ℝ) ≤
      Cfac * Sfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
    have hR0 : (st.chain.totalRuntime : ℝ) ≤
        Cfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((st.chain.shiftCount i : ℝ) + (st.chain.rebuildCount i : ℝ)) * powTerm cfg.P i) := by
      simpa only [alg2RuntimeBoundSR, Cfac, hZero, add_zero, one_div, Nat.cast_add] using hRun
    rw [mul_assoc]; exact le_trans hR0 (mul_le_mul_of_nonneg_left hSR hCfac_nn)
  have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2); linarith
  have hγnn : 0 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3 := by linarith [hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)]
  have h2γSh := mul_le_mul_of_nonneg_left hShSum (by linarith only [hγnn] : 0 ≤ 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3))
  have hOps : ((st.lctUpdateOps + st.lctDetectOps : ℕ) : ℝ) ≤
      2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) +
      ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
    push_cast; linarith only [hLctU, hLctD, h2γSh]
  have hLctCharge : alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) +
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + 2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
    change (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * ((st.lctUpdateOps + st.lctDetectOps : ℕ) : ℝ) ≤ _
    linarith [mul_le_mul_of_nonneg_left hOps hln]
  have hAlg := alg2_collapse_algebra hV st.chain.rebuildCount Q_upd K_upd Q_det K_det selfReb hFl
  dsimp only [Cfac, Ψ_g, Sfac, st, Q_upd, K_upd, Q_det, K_det] at hAlg
  linarith only [hRunZero, hLctCharge, hAlg]

theorem theorem_5_1_collapsed_of_floor_smallBatch {cfg : Alg2Config} (hV : cfg.ValidNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀)
    (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ (alg2UpdateQueries D isUpdate T)
      (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).chain.rebuildCount selfReb) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Q_tot := (cfg.P.M₀ : ℝ) + (alg2UpdateQueries D isUpdate T : ℝ) +
      (alg2UpdateCount isUpdate T : ℝ) + (alg2DetectSize cfg D η isUpdate T : ℝ) +
      (alg2DetectCount isUpdate T : ℝ)
    (st.chain.totalRuntime : ℝ) + alg2LctAmortizedCharge cfg.N₀ (st.lctUpdateOps + st.lctDetectOps) ≤
      alg2CollapsedFactor cfg * Q_tot :=
  theorem_5_1_collapsed_of_floor_smallBatch_with (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    hV hHist hmBound hnBound hSmallBatch selfReb hFl

end RebuildFloorCollapse

end MinCostFlow.Chain
