module

public import MinCostFlow.Chain.Ordered.Theorem5_1Deps
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Theorem 5.1 Helpers (Ordered): IPM Failure Interface and Unconditional Operation Bounds

Ordered-chain counterpart of `MinCostFlow/Chain/Theorem5_1Helpers.lean`, using `lemma511TimeFactor`
(with `M₀^{2/d}`) and the ordered Algorithm 2 procedures in `MinCostFlow/Chain/Ordered/Algorithm2.lean`
together with `UpdateProofs`, `CollapseBounds`, and `Algorithm2Uncond`:
1. Agreement lemmas between `algorithm2_dsWithFailureWith.eraseFailure` and `algorithm2_dsWith`.
2. `theorem_5_1_uncond_complexity{_with}`: unconditional (`HiddenStable`-free) runtime,
   `T^𝒢` update, shift-bound, `lctUpdateOps`/`lctDetectOps`, and `s_i`-eliminated complexity bounds.
3. `theorem_5_1_collapsed_of_floor{_with}`, `alg2Detect_work_le{_with}`,
   `largeBatchEnc_eq_zero_of_le_M₀{_with}`, and `theorem_5_1_collapsed_of_floor_smallBatch{_with}`.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow.Bundle

section IPMBridge

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

/-- Combined non-asymptotic complexity theorem (**Theorem 5.1**, unconditional on hidden stability)
for ordered `algorithm2_dsWith cfg κ` on any valid edge-only sequence up to stage `T`. -/
theorem theorem_5_1_uncond_complexity_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    let Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
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
  have hUncond := (algorithm2_uncond_preserves_with
    (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound).1 T (le_refl T)
  rcases hUncond with ⟨hInv, hBud, _, hEnc, _, _, _, _, _, _, _, hShB, _, hLctU, hLctD⟩
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
  have hRT_raw := totalRuntime_collapse_with_noHidden
    cfg.T cfg.L cfg.TP cfg.LP cfg.P hV.hTP hV.hLP hV.hγM₀ hV.hγk hInv hBud
  have hTU_raw := totalTreeUpdates_collapse_with_noHidden
    cfg.T cfg.L cfg.TP cfg.LP cfg.P hV.hTP hV.hLP hV.hγM₀ hV.hγk hInv hBud
  have hCfac_nn : 0 ≤ lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀ := by
    unfold lemma511TimeFactor
    have := hV.hTP.2.2.2.2.2.2.2.2.2
    have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2)
    have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    have := one_le_logFactor cfg.P cfg.N₀
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
  set Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
  set Tfac := (14 * (cfg.P.d : ℝ) + 36) *
      (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) * cfg.TP.γ_r (cfg.P.M₀ ^ 2)) ^ (2 * cfg.P.d + 1)
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
for ordered `algorithm2_ds` on any valid edge-only sequence up to stage `T`. -/
theorem theorem_5_1_uncond_complexity
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    let Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
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
  theorem_5_1_uncond_complexity_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound

end UnconditionalBounds

section RebuildFloorCollapse

private lemma alg2_collapse_algebra {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    (reb : ℕ → ℕ) (Q_upd K_upd Q_det K_det : ℕ) (selfReb : ℕ → ℕ)
    (hFl : RebuildFloorHyp cfg.TP cfg.P cfg.N₀ Q_upd reb selfReb) :
    let Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
    let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
    let Sfac := ((cfg.P.d : ℝ) + 1) ^ 2 * (20 * Ψ_g) ^ (cfg.P.d + 1) * (cfg.P.k : ℝ) + 1
    (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac *
        ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1), (reb i : ℝ) * powTerm cfg.P i) +
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) +
          2 * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3) * (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) ≤
      alg2CollapsedFactor cfg *
        ((cfg.P.M₀ : ℝ) + (Q_upd : ℝ) + (K_upd : ℝ) + (Q_det : ℝ) + (K_det : ℝ)) := by
  set Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
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
  have hCfac_nn : 0 ≤ Cfac := by
    unfold Cfac lemma511TimeFactor
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2); have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    have := one_le_logFactor cfg.P cfg.N₀
    positivity
  have hPref_nn : 0 ≤ (Cfac + 2 * (1 + Real.log ((cfg.N₀ : ℝ) + 2)) * (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) + 3)) * Sfac := by
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2); have := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀
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
theorem theorem_5_1_collapsed_of_floor_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
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
  have hU := theorem_5_1_uncond_complexity_with
    (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound
  dsimp only at hU
  rcases hU with ⟨_, _, _, _, _, _, hTot, _⟩
  have hAlg := alg2_collapse_algebra hV
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).chain.rebuildCount
    (alg2UpdateQueries D isUpdate T) (alg2UpdateCount isUpdate T)
    (alg2DetectSizeWith cfg κ D η isUpdate T) (alg2DetectCount isUpdate T) selfReb hFl
  dsimp only at hAlg
  linarith only [hTot, hAlg]

theorem theorem_5_1_collapsed_of_floor
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
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
  theorem_5_1_collapsed_of_floor_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound selfReb hFl

/-- Unconditional `Detect` LCT amortized charge bound (`jtree.tex` lines 20–21):
`(1 + log(N₀ + 2)) * lctDetectOps ≤ (1 + log(N₀ + 2)) * (Q_det + K_det)`, holding with zero
rebuild-floor or hidden-stability hypotheses. -/
theorem alg2Detect_work_le_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
    alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) := by
  have hUncond := (algorithm2_uncond_preserves_with
    (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound).1 T (le_refl T)
  rcases hUncond with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hLctD⟩
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
  have hLctD' : ((minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).lctDetectOps : ℝ) ≤
      (alg2DetectSizeWith cfg κ D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ) := by
    exact_mod_cast hLctD
  have hln : 0 ≤ 1 + Real.log ((cfg.N₀ : ℝ) + 2) := by
    have := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) cfg.N₀] : (1 : ℝ) ≤ (cfg.N₀ : ℝ) + 2)
    linarith
  exact mul_le_mul_of_nonneg_left hLctD' hln

theorem alg2Detect_work_le
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀) :
    let st := minRatioFailState (algorithm2_ds cfg) D η isUpdate T
    alg2LctAmortizedCharge cfg.N₀ st.lctDetectOps ≤
      (1 + Real.log ((cfg.N₀ : ℝ) + 2)) *
        ((alg2DetectSize cfg D η isUpdate T : ℝ) + (alg2DetectCount isUpdate T : ℝ)) :=
  alg2Detect_work_le_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound

/-- When every update batch has size `≤ cfg.P.M₀`, no large-batch overflow accumulates:
`st.largeBatchEnc = 0`. -/
theorem largeBatchEnc_eq_zero_of_le_M₀_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) :
    (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc = 0 := by
  have hUI := (algorithm2_uncond_preserves_with
    (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound).1 T (le_refl T)
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

theorem largeBatchEnc_eq_zero_of_le_M₀
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
    (hmBound : ∀ t ≤ T, (D.G t).m ≤ cfg.P.M₀)
    (hnBound : ∀ t ≤ T, (D.G t).n ≤ cfg.N₀)
    (hSmallBatch : ∀ t, 1 ≤ t → t ≤ T → isUpdate t = true → (D.U t).length ≤ cfg.P.M₀) :
    (minRatioFailState (algorithm2_ds cfg) D η isUpdate T).largeBatchEnc = 0 :=
  largeBatchEnc_eq_zero_of_le_M₀_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀) hV hHist hEdge hLen hmBound hnBound hSmallBatch

/-- Under `RebuildFloorHyp` AND the small-batch assumption `(D.U t).length ≤ cfg.P.M₀`,
total runtime + LCT charge is bounded purely by `alg2CollapsedFactor cfg * Q_tot` with zero
`Q_upd log(M₀ + Q_upd)` overflow term. -/
theorem theorem_5_1_collapsed_of_floor_smallBatch_with
    {cfg : Alg2Config} (κ : ℝ) (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
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
  have hU := theorem_5_1_uncond_complexity_with
    (cfg := cfg) (η := η) κ hV hHist hEdge hLen hmBound hnBound
  dsimp only at hU
  rcases hU with ⟨hRun, _, hShB, hLctU, hLctD, _, _, _⟩
  have hZero : (minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T).largeBatchEnc = 0 :=
    largeBatchEnc_eq_zero_of_le_M₀_with κ hV hHist hEdge hLen hmBound hnBound hSmallBatch
  set st := minRatioFailState (algorithm2_dsWith cfg κ) D η isUpdate T
  set Q_upd := alg2UpdateQueries D isUpdate T
  set K_upd := alg2UpdateCount isUpdate T
  set Q_det := alg2DetectSizeWith cfg κ D η isUpdate T
  set K_det := alg2DetectCount isUpdate T
  set Cfac := lemma511TimeFactor cfg.TP cfg.LP cfg.P cfg.N₀
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
    unfold Cfac lemma511TimeFactor
    have := hV.hTP.2.2.2.2.2.2.2.2.2; have := hV.hLP.2.2.2.2
    have := hV.hTP.2.2.1 (cfg.P.M₀ ^ 2); have := hV.hTP.2.2.2.2.2.2.1 (cfg.P.M₀ ^ 2)
    have := one_le_logFactor cfg.P cfg.N₀; positivity
  have hRunZero : (st.chain.totalRuntime : ℝ) ≤
      Cfac * Sfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
        (st.chain.rebuildCount i : ℝ) * powTerm cfg.P i) := by
    have hR0 : (st.chain.totalRuntime : ℝ) ≤
        Cfac * ((cfg.P.M₀ : ℝ) + ∑ i ∈ Finset.range (cfg.P.d + 1),
          ((st.chain.shiftCount i : ℝ) + (st.chain.rebuildCount i : ℝ)) * powTerm cfg.P i) := by
      simpa only [alg2RuntimeBoundSR, Cfac, hZero, add_zero, Nat.cast_add] using hRun
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

theorem theorem_5_1_collapsed_of_floor_smallBatch
    {cfg : Alg2Config} (hV : cfg.ValidOrdNoHidden)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hEdge : HistoryEdgeOnly D T)
    (hLen : HistoryLengthsInRange D T cfg.Ψ)
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
  theorem_5_1_collapsed_of_floor_smallBatch_with
    (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    hV hHist hEdge hLen hmBound hnBound hSmallBatch selfReb hFl

end RebuildFloorCollapse

end MinCostFlow.Chain.Ordered
