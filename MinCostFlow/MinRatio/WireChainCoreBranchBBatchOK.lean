module

public import MinCostFlow.MinRatio.WireChainCoreBranchBSizesKFBL
public import MinCostFlow.MinRatio.WireChainSpecs
public import MinCostFlow.Chain.Ordered.ShiftLoopLevels
import MinCostFlow.Chain.Ordered.BudgetHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Validity of the batches along the Branch B update loop (`WireChainCoreBranchBBatchOK`)

`wireBranchBFrontLoopKFBL_runs` (`MinRatio/WireChainCoreBranchBFrontLoopKFBL.lean`) takes one model
premise: every batch `branchBStepBatch … j` that the plain-step loop passes to level `j < d` meets
`BranchBStepBatchOK cfg model.chain j`, meaning:
1. `(model.chain.G j).IsValid`;
2. `(model.chain.G j).BatchIsValid (branchBStepBatch … j)`;
3. `(model.chain.G j).m ≤ levelM cfg.TP cfg.P j`.

This file proves all three parts from the model hypotheses available in Branch B:
* `branchBStepBatch_isValid`: part 2 holds for every level `j ≥ idx`, by induction on `rem` from
  `UpdateLoopModelInv` (`MinRatio/WireChainSpecs.lean`), whose recursion matches `branchBStepNext`
  and `branchBStepBatch` and leaves `st.G k` unchanged for `k > idx`.
* `chainInv_level_m_le_levelM_of_tpValid`: part 3 holds for every level `j < cfg.P.d` from
  `cfg.TP.Valid`, `Chain.Ordered.ShiftLoopChainInv`, and `ShiftLoopLevelFacts` (splitting on
  whether `cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k`, and deriving `cfg.P.k ≤ cfg.P.M₀` from
  `ChainParams.hk_upper` whenever `2 ≤ cfg.P.d` and `2 ≤ cfg.P.M₀`).
* `branchBStepBatch_ok_of_mLe`: combines parts 1 and 2 from `UpdateCoreModelInv` and
  `UpdateCoreModelInvKFBL` with any proof of part 3.
* `branchBStepBatch_ok`: proves the exact premise of `wireBranchBFrontLoopKFBL_runs` from
  `cfg.TP.Valid`, `ShiftLoopChainInv`, `UpdateCoreModelInv`, and `UpdateCoreModelInvKFBL`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM Chain Chain.Ordered DynSpanner.Program SparseCore.Program Bundle IPM.Machine

/-- Every batch `branchBStepBatch … j` for `idx ≤ j` is valid for the old graph `ch.G j`,
provided `UpdateLoopModelInv` holds from `(rem, idx, st, curG, curU, curEnc)` and `st.G` agrees
with `ch.G` from `idx` onward. Levels at or after the first threshold overflow (or past
`idx + rem`) receive the empty batch, which is valid for every graph. -/
theorem branchBStepBatch_isValid {w L P wordExp stretchPrec : ℕ} {cfg : Alg2Config}
    {vcOf ecOf : ℕ → ℕ} {origLen : ℕ → ℕ → ℝ} {ℓ' g' : ℕ → ℝ} {ch : ChainState cfg.T cfg.P} :
    ∀ (rem idx : ℕ) (st : ChainState cfg.T cfg.P) (curG : MGraph) (curU : List Update)
      (curEnc : ℕ) (oldOrd : ℕ → List End),
      UpdateLoopModelInv w L P wordExp stretchPrec vcOf ecOf origLen ℓ' g' rem idx st curG curU
        curEnc oldOrd →
      (∀ k, idx ≤ k → st.G k = ch.G k) →
      ∀ j, idx ≤ j →
        (ch.G j).BatchIsValid (branchBStepBatch cfg ℓ' g' rem idx st curG curU curEnc j) := by
  intro rem
  induction rem with
  | zero =>
    intro idx st curG curU curEnc oldOrd _ _ j _
    simp [branchBStepBatch, MGraph.BatchIsValid]
  | succ rem ih =>
    intro idx st curG curU curEnc oldOrd hLoop hGEq j hj
    obtain ⟨_, hBatch, _, _, _, hTail⟩ := hLoop
    by_cases hTh : intRebuildThreshold cfg.P st.N₀ idx < st.updCount idx + curU.length
    · simp only [branchBStepBatch, ite_eq_left hTh]
      trivial
    · by_cases hjeq : j = idx
      · subst hjeq
        simp only [branchBStepBatch, ite_eq_right hTh, ↓reduceIte]
        rw [← hGEq j le_rfl]
        exact hBatch
      · rw [ite_eq_right hTh] at hTail
        obtain ⟨_, _, _, _, _, _, hLoopNext⟩ := hTail
        simp only [branchBStepBatch, ite_eq_right hTh, ite_eq_right hjeq]
        refine ih (idx + 1) _ _ _ 0 _ hLoopNext (fun k hk => ?_) j (by omega)
        change (if k = idx then curG else st.G k) = ch.G k
        rw [ite_eq_right (by omega : k ≠ idx)]
        exact hGEq k (by omega)

/-- When `2 ≤ P.d` and `2 ≤ P.M₀`, the upper bound `P.k ≤ 2 · M₀^(1/d)` in `ChainParams` implies
`P.k ≤ P.M₀`. -/
private lemma chainParams_k_le_M₀ {P : ChainParams} (hd : 2 ≤ P.d) (hM₀ : 2 ≤ P.M₀) :
    P.k ≤ P.M₀ := by
  have hM0_nn : (0 : ℝ) ≤ (P.M₀ : ℝ) := Nat.cast_nonneg _
  have hM0_ge1 : (1 : ℝ) ≤ (P.M₀ : ℝ) := by exact_mod_cast P.hM₀
  have hexp : (1 : ℝ) / (P.d : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hd)
  have hrpow : (P.M₀ : ℝ) ^ ((1 : ℝ) / (P.d : ℝ)) ≤ (P.M₀ : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hM0_ge1 hexp
  have hk_le : (P.k : ℝ) ≤ 2 * (P.M₀ : ℝ) ^ ((1 : ℝ) / 2) :=
    P.hk_upper.trans (by linarith)
  have hsq_r : (P.k : ℝ) ^ 2 ≤ (2 * (P.M₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hk_le 2
  have hrhs : (2 * (P.M₀ : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 4 * (P.M₀ : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast ((P.M₀ : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul hM0_nn]
    norm_num
  have hsq_nat : P.k ^ 2 ≤ 4 * P.M₀ := by
    have hle : ((P.k ^ 2 : ℕ) : ℝ) ≤ ((4 * P.M₀ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hle
  by_cases hM4 : 4 ≤ P.M₀
  · have hle : P.k * P.k ≤ P.M₀ * P.M₀ := by
      have hsq' : P.k * P.k ≤ 4 * P.M₀ := by simpa [sq] using hsq_nat
      exact hsq'.trans (Nat.mul_le_mul_right P.M₀ hM4)
    nlinarith
  · have hcase : P.M₀ = 2 ∨ P.M₀ = 3 := by omega
    rcases hcase with h2 | h3
    · rw [h2] at hsq_nat ⊢
      nlinarith
    · rw [h3] at hsq_nat ⊢
      nlinarith

/-- Under `cfg.TP.Valid`, `ShiftLoopChainInv cfg ch`, and `ShiftLoopLevelFacts cfg ch`, every
level graph `ch.G j` (`j < cfg.P.d`) has at most `levelM cfg.TP cfg.P j` edges. No separate
`γ_ℓ ≤ k` or `γ_ℓ ≤ M₀` assumption is required: if `γ_ℓ > k` then `levelM ≥ M₀ ≥ (ch.G j).m`,
while if `γ_ℓ ≤ k` then either `d = 1`, `M₀ = 1`, or `P.k ≤ P.M₀` gives `γ_ℓ ≤ M₀` and
`Chain.Ordered.level_bounds_aux_noHidden` applies. -/
theorem chainInv_level_m_le_levelM_of_tpValid {cfg : Alg2Config} {ch : ChainState cfg.T cfg.P}
    (hTP : cfg.TP.Valid) (hShift : Chain.Ordered.ShiftLoopChainInv cfg ch)
    (hFacts : ShiftLoopLevelFacts cfg ch) :
    ∀ j < cfg.P.d, (ch.G j).m ≤ levelM cfg.TP cfg.P j := by
  intro j hj
  by_cases hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ (cfg.P.k : ℝ)
  · by_cases hd1 : cfg.P.d = 1
    · have hj0 : j = 0 := by omega
      subst hj0
      exact le_trans hShift.1.hG0m (M₀_le_levelM_zero hTP cfg.P)
    · by_cases hM1 : cfg.P.M₀ = 1
      · have hle1 : (ch.G j).m ≤ 1 := by
          have h1 := hFacts.2.2.2 j (Nat.le_of_lt hj)
          have h2 := hShift.1.hG0m
          omega
        exact hle1.trans (one_le_levelM hTP cfg.P j)
      · have hk_le_M0 : cfg.P.k ≤ cfg.P.M₀ :=
          chainParams_k_le_M₀ (by have := cfg.P.hd; omega) (by have := cfg.P.hM₀; omega)
        have hγM₀ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ (cfg.P.M₀ : ℝ) :=
          hγk.trans (by exact_mod_cast hk_le_M0)
        have hLvl := Chain.Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
          hTP hγM₀ hγk hShift.1 j (Nat.le_of_lt hj)
        exact_mod_cast hLvl.2.2.1
  · have hγ1 : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) := hTP.2.2.1 (cfg.P.M₀ ^ 2)
    have hk_pos : (0 : ℝ) < (cfg.P.k : ℝ) := Nat.cast_pos.mpr cfg.P.hk
    have hrat : 1 ≤ cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ) :=
      (one_le_div hk_pos).mpr (le_of_lt (lt_of_not_ge hγk))
    have hpow : 1 ≤ (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ j := one_le_pow₀ hrat
    have hM0_nn : (0 : ℝ) ≤ (cfg.P.M₀ : ℝ) := Nat.cast_nonneg _
    have hM0_le_r : (cfg.P.M₀ : ℝ) ≤ (levelM cfg.TP cfg.P j : ℝ) := by
      calc (cfg.P.M₀ : ℝ)
          = (cfg.P.M₀ : ℝ) * 1 * 1 := by ring
        _ ≤ (cfg.P.M₀ : ℝ) * cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) *
              (cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) / (cfg.P.k : ℝ)) ^ j :=
            mul_le_mul (mul_le_mul_of_nonneg_left hγ1 hM0_nn) hpow zero_le_one
              (mul_nonneg hM0_nn (le_trans zero_le_one hγ1))
        _ ≤ (levelM cfg.TP cfg.P j : ℝ) := rpow_le_levelM cfg.TP cfg.P j
    have hM0_le : cfg.P.M₀ ≤ levelM cfg.TP cfg.P j := by exact_mod_cast hM0_le_r
    exact ((hFacts.2.2.2 j (Nat.le_of_lt hj)).trans hShift.1.hG0m).trans hM0_le

/-- The `BranchBStepBatchOK` premise of `wireBranchBFrontLoopKFBL_runs`, given `UpdateCoreModelInv`,
`UpdateCoreModelInvKFBL`, and the level edge-count bound `(model.chain.G j).m ≤ levelM j` for
every `j < cfg.P.d`. -/
theorem branchBStepBatch_ok_of_mLe
    {w L P m epsExp wordExp stretchPrec g l : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec)
    (hMLe : ∀ j < cfg.P.d, (model.chain.G j).m ≤ levelM cfg.TP cfg.P j) :
    let d := cfg.P.d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let g' := fun e' => gVec (tr.2.2.1 e')
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    ∀ j < d, BranchBStepBatchOK cfg model.chain j
      (branchBStepBatch cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int) j) := by
  intro d tr U_int G0 gVec lVec ℓ' g' st0 j hj
  obtain ⟨_, _, _, _, _, _, _, _, ⟨_, vcOf, ecOf, _, _, hLoop⟩, _⟩ := hModelInv
  have hValid : (model.chain.G j).IsValid := (hModelInvKFBL.2.2.1 j (Nat.le_of_lt hj)).1
  have hBatch : (model.chain.G j).BatchIsValid
      (branchBStepBatch cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int) j) :=
    branchBStepBatch_isValid d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int)
      (st0.levelOrd 0) hLoop (fun _ _ => rfl) j (Nat.zero_le j)
  exact ⟨hValid, hBatch, hMLe j hj⟩

/-- **The validity premise of `wireBranchBFrontLoopKFBL_runs`.**
Every batch `branchBStepBatch … j` entering level `j < cfg.P.d` along the plain-step loop of
Branch B satisfies `BranchBStepBatchOK cfg model.chain j`, from `cfg.TP.Valid`,
`ShiftLoopChainInv cfg model.chain`, `UpdateCoreModelInv`, and `UpdateCoreModelInvKFBL`. -/
theorem branchBStepBatch_ok
    {w L P m epsExp wordExp stretchPrec g l : ℕ} {cfg : Alg2Config}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {mem0 : ℕ → ℕ} {model : Alg2State cfg}
    {tok : SolverToken cfg L Rcore} {U : List Update} {B : ℤ}
    (hTP : cfg.TP.Valid)
    (hShift : Chain.Ordered.ShiftLoopChainInv cfg model.chain)
    (hModelInv : UpdateCoreModelInv w L P m epsExp wordExp stretchPrec model tok U mem0 g l B)
    (hModelInvKFBL :
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
      UpdateCoreModelInvKFBL model U gVec lVec) :
    let d := cfg.P.d
    let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
    let U_int := tr.2.2.2.2
    let G0 := model.chain.G 0
    let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 L P m) model.extg
    let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 L P m) model.extℓ
    let ℓ' := fun e' => lVec (tr.2.2.1 e')
    let g' := fun e' => gVec (tr.2.2.1 e')
    let st0 : ChainState cfg.T cfg.P :=
      { model.chain with
        recUpdates := fun j =>
          if j = 0 then model.chain.recUpdates 0 + U_int.length else model.chain.recUpdates j }
    ∀ j < d, BranchBStepBatchOK cfg model.chain j
      (branchBStepBatch cfg ℓ' g' d 0 st0 (G0.applyBatch U_int) U_int (G0.batchEnc U_int) j) :=
  branchBStepBatch_ok_of_mLe hModelInv hModelInvKFBL
    (chainInv_level_m_le_levelM_of_tpValid hTP hShift hModelInvKFBL.1)

end MinCostFlow.MinRatio
