module

public import MinCostFlow.Chain.BundleRestartSCur
public import MinCostFlow.Chain.SparseCoreOrdSpec
import MinCostFlow.SparseCore.BundleStepBounds
import MinCostFlow.SparseCore.BundleOutOrder
import MinCostFlow.SparseCore.BundleMetrics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Post-Restart Output Order, LSF/MWU Guarantees, and Restart Obligations

Publicly re-exports `BundleRestartSCur` (`runOrdAfterRestarts_S_cur_inv`,
`epochBundleSeq_step_spec`) and proves:
- `epochBundleSeq_orderedUpTo`: `OrderedUpTo` on branch `j`'s `coreInstanceOrdFrom` from any last
  restart `s₀` through `t`;
- `sparseCoreBundleRestartTool_lsf_eq_bundleTool`, `sparseCoreBundleRestartTool_lsf_guarantees_at`,
  and `sparseCoreBundleRestartTool_toolMWUOrdRestart`;
- `sparseCoreBundleRestartTool_embedsSurvivingOrdRestart` (`ToolEmbedsSurvivingOrdRestart`);
- `sparseCoreBundleRestartTool_toolNoReinsertOrdRestart` (`ToolNoReinsertOrdRestart`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.LSF
open MinCostFlow.Bundle

/-! ## 1. Post-restart output order (`OrderedUpTo`) -/

/-- Post-restart output order (`OrderedUpTo`) on branch `j`'s `coreInstanceOrdFrom` from any
last restart `s₀` through `t` (`∀ r, s₀ < r → r ≤ t → j ∉ restarts r`), for both nonempty and
empty `(D.G 0).V` (no `hThresh` required). -/
theorem epochBundleSeq_orderedUpTo
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_b : SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hSp : SparsifySpec M P_b (sparsify M))
    (hG₀ : (D.G 0).IsValid) (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e)
    (hD : D.IsValid τ) (hOrd : OrderedUpTo D τ 2 ord)
    (s₀ t j : ℕ) (hInit : IsValidLSFInitFor lsfInit C_lsst k j) (hst : s₀ ≤ t) (htτ : t ≤ τ)
    (hNoRest : ∀ r, s₀ < r → r ≤ t → j ∉ restarts r) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
      (fun δ => T.rot (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j) := by
  intro T
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hNoRest_lt : ∀ r, s₀ < r → r < t → j ∉ restarts r := fun r h1 h2 => hNoRest r h1 h2.le
    have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
      k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit
    have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL P_b sparsify
      k M N τ hk D ord restarts hM hN hSp hG₀ hV₀ hℓ₀ hD hOrd j hInit
    have hSt_step := (epochBundleSeq_steps lsfInit C_lsst L sparsify
      k M N D ord restarts hV₀ s₀ t j hst hNoRest_lt).2
    have hEp := epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j hst
    set bt := epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ t j
    have hbt_eq : ∀ δ ≤ t - s₀,
        bt δ = (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j := by
      intro δ hδ
      by_cases hlt : δ < t - s₀
      · exact hEp.1 δ hlt
      · have hδeq : δ = t - s₀ := by omega
        subst hδeq
        rw [show s₀ + (t - s₀) = t by omega]
        refine hEp.2.1 ?_
        by_cases hst_lt : s₀ < t
        · exact Or.inl (hNoRest t hst_lt le_rfl)
        · exact Or.inr (by omega)
    let D_shift : DynamicInstance :=
      { G := fun δ => D.G (s₀ + δ)
        U := fun δ => D.U (s₀ + δ)
        g := fun δ => D.g (s₀ + δ)
        ℓ := fun δ => D.ℓ (s₀ + δ) }
    have hD_shift : D_shift.IsValid (t - s₀) := by
      intro δ hδ1 hδ2
      have h1 := hD (s₀ + δ) (by omega) (by omega)
      have hsub : s₀ + δ - 1 = s₀ + (δ - 1) := by omega
      simpa only [D_shift, hsub] using h1
    have hOrd_shift : OrderedUpTo D_shift (t - s₀) 2 (fun δ => ord (s₀ + δ)) := by
      obtain ⟨ρ, hρord, hρstep⟩ := hOrd
      refine ⟨fun δ => ρ (s₀ + δ), fun δ hδ => hρord (s₀ + δ) (by omega), fun δ hδ => ?_⟩
      obtain ⟨hG, hrb⟩ := hρstep (s₀ + δ) (by omega)
      exact ⟨hG, hrb⟩
    have hne_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true := fun s =>
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
        (decide_eq_true hV₀)
    have hord_post : ∀ s, (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s := fun s =>
      ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
    have hrot_eq : ∀ δ ≤ t - s₀,
        T.rot (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j =
          (bt δ).outOrder (ord (s₀ + δ)) := by
      intro δ hδ
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_rot_eq, hne_post (s₀ + δ), ite_eq_left rfl, hord_post (s₀ + δ),
        ← hbt_eq δ hδ]
    have hMain := bundleSeq_orderedUpTo sparsify
      D_shift (t - s₀) (fun δ => ord (s₀ + δ)) hD_shift hOrd_shift bt
      (T.coreInstanceOrdFrom k M N D ord restarts s₀ j)
      (fun δ hδ => by
        dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T]
        rw [sparseCoreBundleRestartTool_S_eq, hne_post (s₀ + δ), ite_eq_left rfl, ← hbt_eq δ hδ])
      (fun δ hδ => by
        dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T]
        exact (hSt_step δ hδ).2)
      (fun δ hδ => (hSt_step δ hδ).1)
      (fun δ hδ => by
        have hbf : BundleBaseFieldsEq ((T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)).trees j)
            ((T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1.trees j) :=
          (foldl_bundleRestart_props lsfInit C_lsst L sparsify
            (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).1 (restarts (s₀ + δ))).2.2.2.2.1 j
        have hB := hBun (s₀ + δ) (by omega)
        rw [hbt_eq δ hδ]
        exact ⟨hbf.cs.symm ▸ hB.2.2.2.2.2.2.2.1, by rw [hbf.cs]; exact hB.2.2.2.2.2.2.2.2.1⟩)
      (fun δ hδ => by rw [hbt_eq δ hδ]; exact (hSc (s₀ + δ) (by omega)).2.1)
      (fun δ hδ => by rw [hbt_eq δ hδ]; exact (hSc (s₀ + δ) (by omega)).2.2.1)
      (fun δ hδ => by rw [hbt_eq δ hδ]; exact (hSc (s₀ + δ) (by omega)).2.2.2.2)
    obtain ⟨ρOut, hOutOrd, hOutStep⟩ := hMain
    exact ⟨ρOut, fun δ hδ => (hOutOrd δ hδ).trans (hrot_eq δ hδ).symm, hOutStep⟩
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit C_lsst L sparsify k M N D ord restarts hV₀
    have hG_eq : ∀ δ, (T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G δ = emptyGraph := fun δ => by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T]
      rw [sparseCoreBundleRestartTool_S_eq, (hrunE (s₀ + δ)).2.1]; rfl
    have hU_eq : ∀ δ, (T.coreInstanceOrdFrom k M N D ord restarts s₀ j).U δ = [] := fun δ => by
      dsimp only [SparseCoreRestartTool.coreInstanceOrdFrom, T]
      rw [(hrunE (s₀ + δ)).2.2]
    have hRot_eq : ∀ δ, T.rot (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j =
        fun _ => [] := fun δ => by
      dsimp only [T]
      rw [sparseCoreBundleRestartTool_rot_eq, (hrunE (s₀ + δ)).2.1]; rfl
    let ρEmpty : Rotation emptyGraph :=
      ⟨fun _ => [], fun _ => List.nodup_nil, fun _ _ => by simp [emptyGraph]⟩
    refine ⟨fun δ => (hG_eq δ).symm ▸ ρEmpty,
      fun δ _ => by dsimp only; rw [rotation_cast_order, hRot_eq δ], fun δ _ => ?_⟩
    have hStepG : (T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G (δ + 1) =
        ((T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G δ).applyBatch
          ((T.coreInstanceOrdFrom k M N D ord restarts s₀ j).U (δ + 1)) := by
      rw [hG_eq (δ + 1), hG_eq δ, hU_eq (δ + 1)]; rfl
    refine ⟨hStepG, ?_⟩
    have aux : ∀ (W : List Update) (hW : W = [])
        (hS : (T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G (δ + 1) =
          ((T.coreInstanceOrdFrom k M N D ord restarts s₀ j).G δ).applyBatch W),
        RotationBatch 2 W ((hG_eq δ).symm ▸ ρEmpty) (hS ▸ (hG_eq (δ + 1)).symm ▸ ρEmpty) := by
      intro W hW hS; subst hW
      exact RotationBatch.nil fun _ => by rw [rotation_cast_order, rotation_cast_order, rotation_cast_order]
    exact aux _ (hU_eq (δ + 1)) hStepG

/-! ## 2. LSF/MWU guarantees and restart obligations -/

/-- The LSF exported by `sparseCoreBundleRestartToolWith` along `runOrdAfterRestarts` agrees
unconditionally with `sparseCoreBundleToolWith` along `runOrdAt`. -/
theorem sparseCoreBundleRestartTool_lsf_eq_bundleTool
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ) (t j : ℕ) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).lsfs
        ((sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).runOrdAfterRestarts k M N D ord
          restarts t) j =
      (sparseCoreBundleToolWith lsfInit L sparsify).lsfs
        ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1 j := by
  set T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hne1 : (T.runOrdAfterRestarts k M N D ord restarts t).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts t).2.1.trans
        (decide_eq_true hV₀)
    have hB := sparseCoreBundleToolWith_runOrdAt lsfInit L sparsify k M N D ord hV₀ t
    have hp := (runOrdAfterRestarts_base_proj lsfInit C_lsst L sparsify k M N D ord restarts hV₀ j t).2.cs
    dsimp only [T] at hne1 ⊢
    rw [sparseCoreBundleRestartTool_lsfs_of_nonempty hne1]
    change _ = if ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.isNonempty =
        true then _ else _
    rw [hB.1, ite_eq_left rfl, hp, hB.2.2.2.1 j]
  · have h1 := (runOrdAfterRestarts_empty_case lsfInit C_lsst L sparsify k M N D ord restarts hV₀ t).2.1
    have h2 : ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.isNonempty =
        false := by
      have := (runOrdAfterRestarts_empty_case lsfInit C_lsst L sparsify k M N D ord (fun _ => [])
        hV₀ t).2.1
      rw [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] at this
      exact this
    dsimp only [T] at h1 ⊢
    rw [sparseCoreBundleRestartTool_lsfs_of_empty h1]
    change _ = if ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.isNonempty =
        true then _ else _
    rw [h2]; rfl

/-- Per-branch LSF guarantees (`Holds`, connected root count, decremental forest, `wstr`
immutability/reset) for `sparseCoreBundleRestartToolWith` along `runOrdAfterRestarts`. -/
theorem sparseCoreBundleRestartToolWith_lsf_guarantees_branch
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ →
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1)) := by
  intro T post m₀ n₀
  have hBase := sparseCoreBundleToolWith_lsf_guarantees_branch lsfInit C_lsst L sparsify
    k M N τ hk D ord hG₀ hD hℓ hLen hInit
  have heq := fun t => sparseCoreBundleRestartTool_lsf_eq_bundleTool lsfInit C_lsst L sparsify
    k M N D ord restarts t j
  exact ⟨fun t ht => by rw [heq t]; exact hBase.1 t ht,
    fun t ht1 htτ => by rw [heq t, heq (t - 1)]; exact hBase.2 t ht1 htτ⟩

/-- All LSF guarantees (Holds, connected root count, decremental forest, `wstr` immutability/reset,
and exact Lemma 5.5 MWU average stretch bound) for `sparseCoreBundleRestartTool` along
`runOrdAfterRestarts`. -/
theorem sparseCoreBundleRestartTool_lsf_guarantees_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance)
    (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ) :
    let T := sparseCoreBundleRestartTool oracle C_lsst L sparsify
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1)) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (post t) j).wstr e) / (k : ℝ) ≤
        (26 * mwuK0 C_lsst + 128) *
          (Real.log ((D.G 0).n + 2 : ℝ)) ^ 6 * (Real.log ((D.G 0).m + 2 : ℝ))) := by
  intro T post m₀ n₀
  have hBase := sparseCoreBundleTool_lsf_guarantees_at oracle C_lsst L sparsify hLSST
    k M N τ hk D ord hG₀ hD hℓ hLen
  have heq := fun t j => sparseCoreBundleRestartTool_lsf_eq_bundleTool
    (initLSFOnline oracle C_lsst) C_lsst L sparsify k M N D ord restarts t j
  refine ⟨fun t ht j hj => by rw [show T.lsfs (post t) j = _ from heq t j]; exact hBase.1 t ht j hj,
    fun t ht1 htτ j hj => by
      rw [show T.lsfs (post t) j = _ from heq t j, show T.lsfs (post (t - 1)) j = _ from heq (t - 1) j]
      exact hBase.2.1 t ht1 htτ j hj,
    fun t ht e he => ?_⟩
  have hsum : (∑ j ∈ Finset.range k, (T.lsfs (post t) j).wstr e) =
      ∑ j ∈ Finset.range k, ((sparseCoreBundleTool oracle C_lsst L sparsify).lsfs
        ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1 j).wstr e :=
    Finset.sum_congr rfl fun j _ => by rw [show T.lsfs (post t) j = _ from heq t j]; rfl
  rw [hsum]; exact hBase.2.2 t ht e he

/-- **Unconditional** `ToolEmbedsSurvivingOrdRestart` for `sparseCoreBundleRestartToolWith`. -/
theorem sparseCoreBundleRestartToolWith_embedsSurvivingOrdRestart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).ToolEmbedsSurvivingOrdRestart := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh t ht j hj e he
  rw [sparseCoreBundleRestartTool_S_eq] at he
  split_ifs at he with hne
  · rw [sparseCoreBundleRestartTool_emb_eq, ite_eq_left hne]
    dsimp only [BundleTreeState.emb]
    rw [ite_eq_left he]
  · simp [emptyGraph] at he

/-- **Unconditional** `ToolEmbedsSurvivingOrdRestart` for `sparseCoreBundleRestartTool`. -/
theorem sparseCoreBundleRestartTool_embedsSurvivingOrdRestart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).ToolEmbedsSurvivingOrdRestart :=
  sparseCoreBundleRestartToolWith_embedsSurvivingOrdRestart (initLSFOnline oracle C_lsst) C_lsst L
    sparsify

private lemma applyBatch_V_subset (G : MGraph) (U : List Update) :
    G.V ⊆ (G.applyBatch U).V := by
  induction U generalizing G with
  | nil => exact Finset.Subset.rfl
  | cons u rest ih =>
    refine Finset.Subset.trans ?_ (ih (G.applyUpdate u))
    cases u with
    | insert _ _ _ => exact Finset.Subset.rfl
    | delete _ => exact Finset.Subset.rfl
    | split _ _ _ _ => exact Finset.subset_insert _ _

private lemma dynInstance_n_mono {D : DynamicInstance} {τ : ℕ} (hD : D.IsValid τ) :
    ∀ t ≤ τ, (D.G 0).n ≤ (D.G t).n := by
  intro t
  induction t with
  | zero => intro _; exact le_rfl
  | succ s ih =>
    intro hs1
    have hstep := hD (s + 1) (Nat.succ_pos s) hs1
    simp only [Nat.add_sub_cancel] at hstep
    exact le_trans (ih (Nat.le_of_succ_le hs1))
      (hstep.2.symm ▸ Finset.card_le_card (applyBatch_V_subset (D.G s) (D.U (s + 1))))

/-- `ToolMWUOrdRestart` bound for `sparseCoreBundleRestartToolWith` under `IsApproxMWUInit` and
polynomial edge density `(D.G 0).m + 2 ≤ ((D.G 0).n + 2)^μ`. -/
theorem sparseCoreBundleRestartToolWith_toolMWUOrdRestart
    (lsfInit : LSFInit) (C_lsst α K_σ K_ρ : ℝ) (L μ : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hKρ : 1 ≤ K_ρ)
    (hApprox : IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ)
    {k M N τ : ℕ} {D : DynamicInstance} (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let K := 3 * K_ρ * K₀
    let σ_mwu := fun n => (μ : ℝ) * K * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) /
          (k : ℝ) ≤ σ_mwu (D.G t).n := by
  intro T K₀ K σ_mwu t ht e he
  have hbase := sparseCoreBundleToolWith_mwu_bound_at lsfInit C_lsst α K_σ K_ρ L sparsify
    hKρ hApprox k M N τ hk D ord hG₀ hD hℓ t ht e he
  have hsum : (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) =
      ∑ j ∈ Finset.range k, ((sparseCoreBundleToolWith lsfInit L sparsify).lsfs
        ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1 j).wstr e :=
    Finset.sum_congr rfl fun j _ => by
      rw [sparseCoreBundleRestartTool_lsf_eq_bundleTool lsfInit C_lsst L sparsify]
  rw [hsum]
  have hK0_nn : 0 ≤ K := by
    have h2240 : (0 : ℝ) ≤ K₀ :=
      le_trans (by norm_num) (le_trans (le_max_right _ (2240 : ℝ)) (le_max_right K_σ _))
    dsimp only [K]; positivity
  have hlog0_nn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
    linarith [half_lt_log_add_two (D.G 0).n]
  have hlogt_ge : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log (((D.G t).n : ℝ) + 2) :=
    Real.log_le_log (by positivity)
      (by linarith [show ((D.G 0).n : ℝ) ≤ ((D.G t).n : ℝ) from by exact_mod_cast dynInstance_n_mono hD t ht])
  have hlogm_le : Real.log (((D.G 0).m : ℝ) + 2) ≤ (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := by
    calc Real.log (((D.G 0).m : ℝ) + 2)
        ≤ Real.log ((((D.G 0).n : ℝ) + 2) ^ μ) := Real.log_le_log (by positivity) hM_poly
      _ = (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := Real.log_pow _ μ
  calc (∑ j ∈ Finset.range k, ((sparseCoreBundleToolWith lsfInit L sparsify).lsfs
          ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1 j).wstr e) /
        (k : ℝ)
      ≤ K * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
          Real.log (((D.G 0).m : ℝ) + 2) := hbase
    _ ≤ K * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
          ((μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogm_le (mul_nonneg hK0_nn (pow_nonneg hlog0_nn 6))
    _ = (μ : ℝ) * K * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 7 := by ring
    _ ≤ (μ : ℝ) * K * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0_nn hlogt_ge 7)
          (mul_nonneg (Nat.cast_nonneg μ) hK0_nn)

/-- `ToolMWUOrdRestart` bound for `sparseCoreBundleRestartTool` under `hLSST` and polynomial edge
density `(D.G 0).m + 2 ≤ ((D.G 0).n + 2)^μ`. -/
theorem sparseCoreBundleRestartTool_toolMWUOrdRestart (C_lsst : ℝ) (L μ : ℕ)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    {k M N τ : ℕ} {D : DynamicInstance} (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    (hM_poly : ((D.G 0).m : ℝ) + 2 ≤ (((D.G 0).n : ℝ) + 2) ^ μ) :
    let T := sparseCoreBundleRestartTool oracle C_lsst L sparsify
    let σ_mwu := fun n => (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log ((n : ℝ) + 2)) ^ 7
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) /
          (k : ℝ) ≤ σ_mwu (D.G t).n := by
  intro T σ_mwu t ht e he
  have hbase := (sparseCoreBundleRestartTool_lsf_guarantees_at oracle C_lsst L sparsify hLSST
    k M N τ hk D ord restarts hG₀ hD hℓ hLen).2.2 t ht e he
  have hK0_nn : 0 ≤ 26 * mwuK0 C_lsst + 128 := by
    have := mwuK0_pos C_lsst; linarith
  have hlog0_nn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
    linarith [half_lt_log_add_two (D.G 0).n]
  have hlogt_ge : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log (((D.G t).n : ℝ) + 2) :=
    Real.log_le_log (by positivity)
      (by linarith [show ((D.G 0).n : ℝ) ≤ ((D.G t).n : ℝ) from by exact_mod_cast dynInstance_n_mono hD t ht])
  have hlogm_le : Real.log (((D.G 0).m : ℝ) + 2) ≤ (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := by
    calc Real.log (((D.G 0).m : ℝ) + 2)
        ≤ Real.log ((((D.G 0).n : ℝ) + 2) ^ μ) := Real.log_le_log (by positivity) hM_poly
      _ = (μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2) := Real.log_pow _ μ
  calc (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) /
        (k : ℝ)
      ≤ (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
          Real.log (((D.G 0).m : ℝ) + 2) := hbase
    _ ≤ (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 *
          ((μ : ℝ) * Real.log (((D.G 0).n : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hlogm_le (mul_nonneg hK0_nn (pow_nonneg hlog0_nn 6))
    _ = (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 7 := by ring
    _ ≤ (μ : ℝ) * (26 * mwuK0 C_lsst + 128) * (Real.log (((D.G t).n : ℝ) + 2)) ^ 7 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0_nn hlogt_ge 7)
          (mul_nonneg (Nat.cast_nonneg μ) hK0_nn)

private lemma mem_applyBatch_E_of_no_inserts' {G : MGraph} {U : List Update} {e : ℕ}
    (he : e ∈ (G.applyBatch U).E) (hni : ∀ u ∈ U, ¬ u.Inserts e) : e ∈ G.E := by
  induction U generalizing G with
  | nil => exact he
  | cons u rest ih =>
    have h1 := ih he (fun u' hu' => hni u' (List.mem_cons_of_mem u hu'))
    have hu_ni := hni u List.mem_cons_self
    cases u with
    | delete _ => exact Finset.mem_of_mem_erase h1
    | split _ _ _ _ => exact h1
    | insert _ _ _ =>
      rcases Finset.mem_insert.mp h1 with rfl | heG
      · exact False.elim (hu_ni rfl)
      · exact heG

private lemma mem_foldl_updateInserted_iff' {ins : Finset ℕ} {G : MGraph}
    {U : List Update} {e : ℕ} (he_end : e ∈ (G.applyBatch U).E) :
    ((e ∈ G.E ∧ e ∈ ins) ∨ (∃ u ∈ U, u.Inserts e)) →
    e ∈ U.foldl updateInserted ins := by
  intro h
  induction U generalizing G ins with
  | nil => rcases h with ⟨_, hins⟩ | ⟨_, hmem, _⟩; exact hins; simp at hmem
  | cons u rest ih =>
    dsimp only [MGraph.applyBatch] at he_end
    dsimp only [List.foldl_cons]
    by_cases hr : ∃ u' ∈ rest, u'.Inserts e
    · exact ih he_end (Or.inr hr)
    · have he1 : e ∈ (G.applyUpdate u).E :=
        mem_applyBatch_E_of_no_inserts' he_end (fun u' hu' hI => hr ⟨u', hu', hI⟩)
      have h_prev : e ∈ G.E ∧ e ∈ ins ∨ u.Inserts e := by
        rcases h with h0 | ⟨u', hu', hIu'⟩
        · exact Or.inl h0
        · rcases List.mem_cons.mp hu' with rfl | hmem
          · exact Or.inr hIu'
          · exact False.elim (hr ⟨u', hmem, hIu'⟩)
      refine ih he_end (Or.inl ⟨he1, ?_⟩)
      cases u with
      | split _ _ _ _ =>
        rcases h_prev with ⟨_, hins⟩ | hI; exact hins; simp only [Update.Inserts] at hI
      | delete e₀ =>
        rcases h_prev with ⟨_, hins⟩ | hI
        · rw [MGraph.applyUpdate] at he1
          exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp he1).1, hins⟩
        · simp only [Update.Inserts] at hI
      | insert e₀ _ _ =>
        rcases h_prev with ⟨_, hins⟩ | hI
        · exact Finset.mem_insert_of_mem hins
        · simp only [Update.Inserts] at hI; subst hI; exact Finset.mem_insert_self _ _

/-- **Unconditional** `ToolNoReinsertOrdRestart` for `sparseCoreBundleRestartToolWith` under
`IsValidLSFInitFor`, `1 ≤ L`, and `∀ m, SparsifySpec m (P_fn m) (sparsify m)`. -/
theorem sparseCoreBundleRestartToolWith_toolNoReinsertOrdRestart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hInit : ∀ k, 0 < k → ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify).ToolNoReinsertOrdRestart := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD _ hWeak hOrd hM hN hrest _ t ht1 htτ j hj
    e hePrev heCur hNoIns u hu hIu
  by_cases hV₀ : (D.G 0).V.Nonempty
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
    simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hePrev
    have hℓ₀ : ∀ x ∈ (D.G 0).E, 0 < D.ℓ 0 x :=
      fun x hx => ((hWeak 0 (Nat.zero_le τ)).2.2.2 x hx).2.2.1
    set T := sparseCoreBundleRestartToolWith lsfInit C_lsst L sparsify
    have hne_s : (T.runOrdAfterRestarts k M N D ord restarts s).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.1.trans
        (decide_eq_true hV₀)
    have hne_s1 : (T.runOrdAfterRestarts k M N D ord restarts (s + 1)).isNonempty = true :=
      (runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts (s + 1)).2.1.trans
        (decide_eq_true hV₀)
    have hord_s : (T.runOrdAfterRestarts k M N D ord restarts s).ord = ord s :=
      ((runOrdAfterRestarts_isNonempty lsfInit C_lsst L sparsify k M N D ord restarts s).2.2.2.2 hV₀).2
    set stPrev := (T.runOrdAfterRestarts k M N D ord restarts s).trees j
    set stPre := (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1.trees j
    set stPost := (T.runOrdAfterRestarts k M N D ord restarts (s + 1)).trees j
    have hePrev' : e ∈ stPrev.S_cur.E := by
      dsimp only [T] at hePrev hne_s
      rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left hne_s] at hePrev; exact hePrev
    have heCur' : e ∈ stPost.S_cur.E := by
      dsimp only [T] at heCur hne_s1
      rw [sparseCoreBundleRestartTool_S_eq, ite_eq_left hne_s1] at heCur; exact heCur
    have hNoIns' : ∀ u' ∈ (stepBundleTree sparsify stPrev (D.U (s + 1)) (ord s) (ord (s + 1))).U_S,
        ¬ u'.Inserts e := by
      intro u' hu'
      apply hNoIns u'
      rw [T.runOrdAfterUpdate_succ]
      dsimp only [T] at hne_s hord_s ⊢
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_s, hord_s]
      exact hu'
    have hInit_j := hInit k hk j hj
    have hSc := runOrdAfterRestarts_S_cur_inv lsfInit C_lsst L hL (P_fn M) sparsify
      k M N τ hk D ord restarts hM hN (hSp M) hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
    have hSc_s := (hSc s (Nat.le_of_lt htτ)).2
    have hSc_s1_pre := (hSc (s + 1) htτ).1
    have hSc_s1 := (hSc (s + 1) htτ).2
    have hBun := runOrdAfterRestarts_bun_inv lsfInit C_lsst L sparsify
      k M N τ hk D ord restarts hG₀ hV₀ hℓ₀ hD hOrd j hInit_j
    have hBs := hBun s (Nat.le_of_lt htτ)
    have hBs1 := hBun (s + 1) htτ
    have hbf_s : BundleBaseFieldsEq stPrev ((T.runOrdAfterUpdate k M N D ord restarts s).1.trees j) :=
      (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts s).1 (restarts s)).2.2.2.2.1 j
    have hbf_s1 : BundleBaseFieldsEq stPost stPre :=
      (foldl_bundleRestart_props lsfInit C_lsst L sparsify
        (T.runOrdAfterUpdate k M N D ord restarts (s + 1)).1 (restarts (s + 1))).2.2.2.2.1 j
    have hDt := hD (s + 1) (Nat.succ_pos s) htτ
    simp only [Nat.add_sub_cancel] at hDt
    have hBU : stPrev.cs.G.BatchIsValid (D.U (s + 1)) := by
      rw [hbf_s.cs, hBs.2.2.2.2.2.2.2.2.1]; exact hDt.1
    have hstPre_eq : stPre = (stepBundleTree sparsify stPrev (D.U (s + 1)) (ord s) (ord (s + 1))).state := by
      dsimp only [stPre]; rw [T.runOrdAfterUpdate_succ]; dsimp only [T] at hne_s hord_s ⊢
      rw [sparseCoreBundleRestartTool_updateOrd_of_nonempty hne_s, hord_s]
    have heG_s1 : e ∈ stPost.cs.G.E := (Finset.mem_sdiff.mp (hSc_s1.2.2.2.2.1 heCur')).1
    by_cases hePre : e ∈ stPre.S_cur.E
    · have hUS_eq := stepBundleTree_U_S_eq sparsify stPrev (D.U (s + 1)) (ord s) (ord (s + 1))
      rw [hUS_eq] at hNoIns'
      exact (buildUSOrd_noReinsert hBU hSc_s.2.2.2 _ hePrev' (hstPre_eq ▸ hePre) hNoIns').2 u hu hIu
    · rw [hSc_s1.2.2.1] at heCur'
      rcases Finset.mem_union.mp heCur' with he12 | heX
      · rcases Finset.mem_union.mp he12 with heD | heEx
        · rw [Finset.mem_biUnion] at heD; rcases heD with ⟨C, hCA, heB⟩
          rw [Finset.mem_biUnion] at heB; rcases heB with ⟨b, _, heb⟩
          have hC : C ∈ components (D.G 0) :=
            hBs1.2.2.2.2.2.2.2.2.2.1.2 (hbf_s1.activeComps ▸ hCA)
          set s₀ := bundleLastRestart restarts j (s + 1)
          have hs₀ := bundleLastRestart_spec restarts j (s + 1)
          have hDyn := epochBundleSeq_dyn_spec lsfInit C_lsst L hL (P_fn M) sparsify
            k M N τ hk D ord restarts hM hN (hSp M) hG₀ hV₀ hℓ₀ hD hOrd s₀ (s + 1) j hInit_j
            hs₀.1 htτ hs₀.2.1 (fun r hr1 hr2 => hs₀.2.2 r hr1 hr2.le) C hC b
          have hd_post := hDyn.2.2.2.2.2.2.2.2.2.1 (s + 1 - s₀) le_rfl
          have hst_ep : epochBundleSeq lsfInit C_lsst L sparsify k M N D ord restarts s₀ (s + 1) j
              (s + 1 - s₀) = stPost := by
            refine (epochBundleSeq_eq_post lsfInit C_lsst L sparsify k M N D ord restarts s₀ (s + 1) j
              hs₀.1).2.1 ?_
            by_cases hlt : s₀ < s + 1
            · exact Or.inl (hs₀.2.2 (s + 1) hlt le_rfl)
            · exact Or.inr (by omega)
          rw [hst_ep] at hd_post
          have heG_cb : e ∈ (stPost.dyn (C, b)).G.E := hd_post.2.2.2.1.2.1 heb
          have heBun : e ∈ (stPre.bun (C, b)).edges := by
            rw [hd_post.2.1.2.1] at heG_cb
            have hEqE : (stPost.bun (C, b)).edges = (stPre.bun (C, b)).edges :=
              ((hBs1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1
            exact hEqE ▸ heG_cb
          have hcs_step : stPost.cs = compLSFBatch stPrev.cs (D.U (s + 1)) := by
            rw [hbf_s1.cs, hbf_s.cs, hBs1.2.2.2.2.2.2.1, hBs.2.2.2.2.2.2.1,
              dynBatches_succ, List.flatten_append, compLSFBatch_append,
              List.flatten_cons, List.flatten_nil, List.append_nil]
          have he_insG : e ∈ stPre.cs.insertedGlobal := by
            rw [← hbf_s1.cs, hcs_step, compLSFBatch_insertedGlobal]
            refine mem_foldl_updateInserted_iff' (G := stPrev.cs.G) ?_ (Or.inr ⟨u, hu, hIu⟩)
            rw [← compLSFBatch_G, ← hcs_step]; exact heG_s1
          exact Finset.disjoint_left.mp
            ((hBs1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.2.1 heBun he_insG
        · refine False.elim (hePre ?_)
          rw [hSc_s1_pre.2.2.1, Finset.mem_union, Finset.mem_union]
          left; right
          rw [Finset.mem_biUnion] at heEx ⊢
          rcases heEx with ⟨C, hCA, heExC⟩
          have hC : C ∈ components (D.G 0) :=
            hBs1.2.2.2.2.2.2.2.2.2.1.2 (hbf_s1.activeComps ▸ hCA)
          refine ⟨C, hbf_s1.activeComps ▸ hCA, ?_⟩
          unfold BundleTreeState.extraEdges at heExC ⊢
          rw [hbf_s1.cs, hbf_s1.activeBuckets] at heExC
          have hbi : (stPre.activeBuckets C).biUnion (fun b => (stPost.bun (C, b)).edges) =
              (stPre.activeBuckets C).biUnion (fun b => (stPre.bun (C, b)).edges) :=
            Finset.biUnion_congr rfl fun b _ => ((hBs1.2.2.2.2.2.2.2.2.2.2.2 C hC).2 b).2.2.2.1
          rwa [hbi] at heExC
      · refine False.elim (hePre ?_)
        rw [hSc_s1_pre.2.2.1, Finset.mem_union, Finset.mem_union]
        right; rwa [← hbf_s1.cs]
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit C_lsst L sparsify k M N D ord restarts hV₀
      (t - 1)
    rw [sparseCoreBundleRestartTool_S_eq, hrunE.2.1] at hePrev
    simp [emptyGraph] at hePrev

/-- **Unconditional** `ToolNoReinsertOrdRestart` for `sparseCoreBundleRestartTool` under `hLSST`,
`1 ≤ L`, and `∀ m, SparsifySpec m (P_fn m) (sparsify m)`. -/
theorem sparseCoreBundleRestartTool_toolNoReinsertOrdRestart
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).ToolNoReinsertOrdRestart :=
  sparseCoreBundleRestartToolWith_toolNoReinsertOrdRestart (initLSFOnline oracle C_lsst) C_lsst L hL
    P_fn sparsify (fun k _ j _ => initLSFOnline_isValidLSFInitFor hLSST k j) hSp

end MinCostFlow.Chain

end
