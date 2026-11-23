module

public import MinCostFlow.SparseCore.BundleTool
public import MinCostFlow.SparseCore.SparseCoreMetrics
import MinCostFlow.SparseCore.SparseCoreRunBounds
import MinCostFlow.SparseCore.CompLSFMWUWith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# LSF/MWU metrics and core-state agreement for `sparseCoreBundleTool`

At every stage `t`, the component-wise LSF state of `bundleRunSeq` equals that of `treeRunSeq`
(`bundleRunSeq_cs_eq`, `bundleRunSeq_cs_eq_treeRunSeq`), because both evolve by `compLSFBatch`
from `initCompLSF`. This carries the LSF and MWU guarantees of `SparseCoreMetrics.lean`
(`sparseCore_lsf_guarantees_at`) directly to `sparseCoreBundleTool` along `runOrdAt`
(`sparseCoreBundleTool_lsf_guarantees_at`), together with the initial large-component root bound
and cross-edge/inserted-edge cardinality bounds used by `BundleSpannerMetrics.lean`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow.LSF
open MinCostFlow.Chain
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

@[expose] public section

/-! ## 1. Agreement of `cs` between `bundleRunSeq` and `treeRunSeq` -/

theorem bundleRunSeqWith_cs_eq
    (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ∀ t : ℕ, (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs =
      compLSFBatch (initCompLSFWith lsfInit (D.G 0) (D.ℓ 0) k j) (dynBatches D t).flatten := by
  intro t
  induction t with
  | zero => rfl
  | succ s ih =>
    rw [bundleRunSeqWith_cs, ih, compLSFBatch_dynBatches_succ]

/-- The component-wise LSF state of `bundleRunSeq` at stage `t` is the batch evolution of
`initCompLSF` on the first `t` input batches. -/
theorem bundleRunSeq_cs_eq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) :
    ∀ t : ℕ, (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs =
      compLSFBatch (initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j) (dynBatches D t).flatten :=
  bundleRunSeqWith_cs_eq (initLSFOnline oracle C_lsst) L sparsify k M N D ord j

/-- At every stage `t`, `bundleRunSeq` and `treeRunSeq` maintain identical component-wise LSF
states. -/
theorem bundleRunSeq_cs_eq_treeRunSeq
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (t : ℕ) :
    (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs =
      (treeRunSeq oracle C_lsst L sparsify k M N D j t).1.cs := by
  rw [bundleRunSeq_cs_eq, treeRunSeq_cs_eq]

lemma bundleRunSeqWith_crossEdges_le
    (lsfInit : LSFInit) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (t : ℕ) :
    (bundleRunSeqWith lsfInit L sparsify k M N D ord j t).1.cs.crossEdges.card ≤
      ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
  induction t with
  | zero =>
    have h0 : (bundleRunSeqWith lsfInit L sparsify k M N D ord j 0).1.cs.crossEdges = ∅ := rfl
    rw [h0, Finset.card_empty]
    simp
  | succ s ih =>
    set st_s := (bundleRunSeqWith lsfInit L sparsify k M N D ord j s).1
    have hcs1 : (bundleRunSeqWith lsfInit L sparsify k M N D ord j (s + 1)).1.cs =
        compLSFBatch st_s.cs (D.U (s + 1)) := rfl
    have hsub : (compLSFBatch st_s.cs (D.U (s + 1))).crossEdges ⊆
        st_s.cs.crossEdges ∪ ((compLSFBatch st_s.cs (D.U (s + 1))).crossEdges \ st_s.cs.crossEdges) :=
      fun e he => by
        by_cases h : e ∈ st_s.cs.crossEdges
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, h⟩)
    have h1 := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have h2 := compLSF_crossEdges_sdiff_cur (D.U (s + 1)) st_s.cs
    have hIcc : Finset.Icc 1 (s + 1) = insert (s + 1) (Finset.Icc 1 s) := by
      ext x; simp [Finset.mem_Icc]; omega
    rw [hIcc, Finset.sum_insert (by simp), hcs1]
    omega

lemma bundleRunSeq_crossEdges_le
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (j : ℕ) (t : ℕ) :
    (bundleRunSeq oracle C_lsst L sparsify k M N D ord j t).1.cs.crossEdges.card ≤
      ∑ s ∈ Finset.Icc 1 t, (D.U s).length :=
  bundleRunSeqWith_crossEdges_le (initLSFOnline oracle C_lsst) L sparsify k M N D ord j t

/-! ## 2. LSF and MWU guarantees for `sparseCoreBundleTool` -/

/-- The LSF exported by `sparseCoreBundleTool` along `runOrdAt` agrees at every stage and branch
with the LSF exported by `sparseCoreTool` along `runAt`. -/
theorem sparseCoreBundleTool_lsf_eq_sparseCoreTool
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (t j : ℕ) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).lsfs
        ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1 j =
      (sparseCoreTool oracle C_lsst L sparsify).lsfs
        ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1 j := by
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hB := sparseCoreBundleTool_runOrdAt oracle C_lsst L sparsify k M N D ord hV₀ t
    have hT := sparseCoreTool_runAt_eq_treeRunSeq oracle C_lsst L sparsify k M N D hV₀ t
    set stB := ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1
    set stT := ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1
    change (if stB.isNonempty then (stB.trees j).cs.lsf else emptyLSF) =
      (if stT.isNonempty then (stT.trees j).cs.lsf else emptyLSF)
    rw [hB.1, hT.1]
    simp only [↓reduceIte]
    rw [hB.2.2.2.1 j, hT.2.2.1 j, bundleRunSeq_cs_eq_treeRunSeq]
  · have hBf : ∀ s,
        ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord s).1.isNonempty = false := by
      intro s
      induction s with
      | zero =>
        simp [SparseCoreTool.runOrdAt, sparseCoreBundleTool, sparseCoreBundleToolWith,
          initBundleCoreWith, initBundleCoreWithParams, hV₀]
      | succ s ih =>
        set stS := ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord s).1
        change (updateBundleCore sparsify stS (D.U (s + 1)) (ord (s + 1))).1.isNonempty = false
        simp [updateBundleCore, ih]
    have hTf : ∀ s,
        ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1.isNonempty = false := by
      intro s
      induction s with
      | zero =>
        simp [SparseCoreTool.runAt, sparseCoreTool, sparseCoreToolWith, hV₀]
      | succ s ih =>
        set stS := ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D s).1
        change (if stS.isNonempty = true then _ else (stS, fun _ => [])).1.isNonempty = false
        rw [ih]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact ih
    set stB := ((sparseCoreBundleTool oracle C_lsst L sparsify).runOrdAt k M N D ord t).1
    set stT := ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1
    change (if stB.isNonempty then (stB.trees j).cs.lsf else emptyLSF) =
      (if stT.isNonempty then (stT.trees j).cs.lsf else emptyLSF)
    rw [hBf t, hTf t]
    rfl

/-- Per-branch LSF guarantees (`Holds`, connected root count, decremental forest, `wstr`
immutability/reset) for `sparseCoreBundleToolWith` along `runOrdAt` under `IsValidLSFInitFor`. -/
theorem sparseCoreBundleToolWith_lsf_guarantees_branch
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ)
    {j : ℕ} (hInit : IsValidLSFInitFor lsfInit C_lsst k j) :
    let T := sparseCoreBundleToolWith lsfInit L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ →
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1)) := by
  classical
  intro T st m₀ n₀
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreBundleToolWith_runOrdAt lsfInit L sparsify k M N D ord hV₀
    let cs₀ := initCompLSFWith lsfInit (D.G 0) (D.ℓ 0) k j
    let cs := fun t => compLSFBatch cs₀ (dynBatches D t).flatten
    have hL_eq : ∀ t, T.lsfs (st t) j = (cs t).lsf := fun t => by
      have h1 := (hrun t).1
      have h3 := (hrun t).2.2.2.1 j
      change (if ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
          then (((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.trees j).cs.lsf
          else emptyLSF) = _
      rw [h1, ite_eq_left rfl, h3, bundleRunSeqWith_cs_eq]
    have hBat : ∀ t ≤ τ, (D.G 0).BatchIsValid (dynBatches D t).flatten ∧
        (D.G 0).applyBatch (dynBatches D t).flatten = D.G t := by
      intro t ht
      have hba := applyBatch_dynBatches hD t ht
      exact ⟨(batchIsValid_flatten (D.G 0) (dynBatches D t)).mpr hba.2,
        (applyBatch_flatten (D.G 0) (dynBatches D t)).trans hba.1⟩
    have hI₀ : CompLSFInv C_lsst (D.ℓ 0) cs₀ := compLSFInv_initWith hInit hG₀ hV₀ hℓ₀ hk
    have hI_t : ∀ t ≤ τ, CompLSFInv C_lsst (D.ℓ 0) (cs t) :=
      fun t ht => compLSFBatch_inv hI₀ (hBat t ht).1
    have hG_t : ∀ t ≤ τ, (cs t).G = D.G t := fun t ht => by
      dsimp only [cs, cs₀]; rw [compLSFBatch_G]; exact (hBat t ht).2
    have hIns_t : ∀ t, (cs t).insertedGlobal = batchesInserted (dynBatches D t) := fun t => by
      dsimp only [cs, cs₀]; rw [compLSFBatch_insertedGlobal]
      exact foldl_updateInserted_flatten (dynBatches D t) ∅
    refine ⟨fun t ht => ?_, fun t ht1 htτ => ?_⟩
    · have hIt := hI_t t ht
      have hGt := hG_t t ht
      have hℓt : ∀ e ∈ (cs t).G.E, 0 < D.ℓ t e := by rw [hGt]; exact hℓ t ht
      have hℓo : ∀ e ∈ (cs t).G₀.E, e ∈ (cs t).G.E → e ∉ (cs t).insertedGlobal →
          D.ℓ t e = D.ℓ 0 e := fun e _ he hni => by
        rw [hGt] at he; rw [hIns_t t] at hni
        exact length_eq_init_of_not_batchesInserted hD hLen t ht e he hni
      have hH := hIt.to_Holds hℓt hℓo
      have hcs₀_n : (cs t).G₀.n = n₀ := by dsimp only [cs, cs₀]; rw [compLSFBatch_G₀]; rfl
      have hcs_k : (cs t).k = k := by dsimp only [cs, cs₀]; rw [compLSFBatch_k]; rfl
      rw [hL_eq t]
      refine ⟨?_, ?_⟩
      · rw [hGt, hcs₀_n, hcs_k] at hH
        refine lsfHolds_mono_stretch hH ?_
        have hK_eq : mwuK0 C_lsst = 6272 * max 1 C_lsst := rfl
        rw [← hK_eq]
        have hlog1 : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
        have hlog_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log ((D.G t).n + 2 : ℝ) :=
          Real.log_le_log (by positivity) (by
            have hn_mono : n₀ ≤ (D.G t).n := dyn_G_n_mono hD (Nat.zero_le t) ht
            linarith [show (n₀ : ℝ) ≤ (D.G t).n from by exact_mod_cast hn_mono])
        have hK₀ := (mwuK0_pos C_lsst).le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog1 hlog_le 6) (by positivity)
      · intro hConn
        have hRc := compLSF_connected_R_card_le_with hInit hG₀ hV₀ hConn hℓ₀ hk (hBat t ht).1
        dsimp only at hRc
        change ((cs t).RF.R.card : ℝ) ≤ 1 + 4 * ((D.G 0).m : ℝ) / (k : ℝ) +
          112 * ((dynBatches D t).flatten.length : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 2 at hRc
        have hfl_len : (dynBatches D t).flatten.length =
            ∑ s ∈ Finset.Icc 1 t, (D.U s).length := by
          rw [← totalUpdates_dynBatches D t, MinCostFlow.LSF.totalUpdates, List.length_flatten]
        rw [hfl_len, mul_div_assoc] at hRc
        have hlog_pos : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) :=
          (half_lt_log_add_two n₀).le.trans' (by norm_num)
        have hm₀_nn : (0 : ℝ) ≤ (m₀ : ℝ) / (k : ℝ) := by positivity
        have hsum_nn : (0 : ℝ) ≤
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 := by positivity
        change ((cs t).RF.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1)
        dsimp only [m₀, n₀]
        linarith
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      simp only [Nat.add_sub_cancel]
      have hs_le : s ≤ τ := Nat.le_of_lt htτ
      have hBV_U : (cs s).G.BatchIsValid (D.U (s + 1)) := by
        rw [hG_t s hs_le]; exact (hD (s + 1) (Nat.succ_pos s) htτ).1
      have hstep : cs (s + 1) = compLSFBatch (cs s) (D.U (s + 1)) := by
        dsimp only [cs]; exact compLSFBatch_dynBatches_succ D cs₀ s
      have hsp := compLSFBatch_step_props (D.U (s + 1)) (hI_t s hs_le) hBV_U
      refine ⟨?_, ?_, ?_⟩
      · rw [hL_eq (s + 1), hL_eq s, hstep]; exact hsp.2.2.2.1
      · intro e _ _ hni
        rw [hL_eq (s + 1), hL_eq s, hstep]
        exact compLSFBatch_wstr_of_not_inserts (cs s) (D.U (s + 1)) hni
      · intro e het ⟨u, hu, hins⟩
        rw [hL_eq (s + 1)]
        have hs := hD (s + 1) (Nat.succ_pos s) htτ
        simp only [Nat.add_sub_cancel] at hs
        have het' : e ∈ ((D.G s).applyBatch (D.U (s + 1))).E := hs.2 ▸ het
        have heins : e ∈ (cs (s + 1)).insertedGlobal := by
          rw [hstep, compLSFBatch_insertedGlobal]
          exact mem_foldl_updateInserted_of_mem_applyBatch_inserts het' hu hins
        exact ((hI_t (s + 1) htτ).hIns_wstr_R e heins).1
  · have hVempty : ∀ t ≤ τ, ¬ (D.G t).V.Nonempty ∧ (D.G t).IsValid := by
      intro t ht
      induction t with
      | zero => exact ⟨hV₀, hG₀⟩
      | succ s ih =>
        obtain ⟨hnV, hGs⟩ := ih (Nat.le_of_succ_le ht)
        have hVs : (D.G s).V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnV
        have hEs : (D.G s).E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
          Finset.notMem_empty _ (hVs ▸ (hGs e he).1)
        have hs := hD (s + 1) (Nat.succ_pos s) ht
        simp only [Nat.add_sub_cancel] at hs
        have hUs_nil : D.U (s + 1) = [] := by
          cases hU : D.U (s + 1) with
          | nil => rfl
          | cons u rest =>
            exfalso
            have hu : (D.G s).UpdateIsValid u := (hU ▸ hs.1).1
            cases u with
            | insert _ u1 _ => exact Finset.notMem_empty u1 (hVs ▸ hu.2.1)
            | delete e => exact Finset.notMem_empty e (hEs ▸ hu)
            | split v _ _ _ => exact Finset.notMem_empty v (hVs ▸ hu.1)
        have hGeq : D.G (s + 1) = D.G s := by rw [hs.2, hUs_nil]; rfl
        rw [hGeq]; exact ⟨hnV, hGs⟩
    have hL_empty : ∀ t, T.lsfs (st t) j = emptyLSF := fun t => by
      have hfalse : (st t).isNonempty = false := by
        induction t with
        | zero => simp [st, SparseCoreTool.runOrdAt, T, sparseCoreBundleToolWith,
            initBundleCoreWith, initBundleCoreWithParams, hV₀]
        | succ s ih =>
          change (updateBundleCore sparsify (st s) (D.U (s + 1)) (ord (s + 1))).1.isNonempty = false
          simp [updateBundleCore, ih]
      change (if (st t).isNonempty = true then ((st t).trees j).cs.lsf else emptyLSF) = emptyLSF
      simp [hfalse]
    refine ⟨fun t ht => ?_, fun t _ htτ => ?_⟩
    · obtain ⟨hnV, hGt⟩ := hVempty t ht
      rw [hL_empty t]
      refine ⟨emptyLSF_holds hnV hGt _ _, fun _ => ?_⟩
      simp only [emptyLSF, emptyGraph, Finset.card_empty, Nat.cast_zero]
      have : (0 : ℝ) ≤ Real.log ((n₀ : ℝ) + 2) := (half_lt_log_add_two n₀).le.trans' (by norm_num)
      positivity
    · obtain ⟨hnV, hGt⟩ := hVempty t htτ
      have hEt : (D.G t).E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun e he =>
        hnV ⟨(D.G t).tail e, (hGt e he).1⟩
      rw [hL_empty t, hL_empty (t - 1)]
      exact ⟨Finset.Subset.rfl, fun e he => absurd he (hEt ▸ Finset.notMem_empty e),
        fun e he => absurd he (hEt ▸ Finset.notMem_empty e)⟩

/-- MWU average-stretch bound for `sparseCoreBundleToolWith` along `runOrdAt` under
`IsApproxMWUInit` (paper Lemma 5.5, page 18). -/
theorem sparseCoreBundleToolWith_mwu_bound_at
    (lsfInit : LSFInit) (C_lsst α K_σ K_ρ : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hKρ : 1 ≤ K_ρ)
    (hApprox : IsApproxMWUInit lsfInit C_lsst α K_σ K_ρ)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) :
    let T := sparseCoreBundleToolWith lsfInit L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let K₀ := max K_σ (max (112 * (1 + α) * max 1 C_lsst) 2240)
    let K := 3 * K_ρ * K₀
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤
        K * (Real.log ((D.G 0).n + 2 : ℝ)) ^ 6 * Real.log ((D.G 0).m + 2 : ℝ) := by
  intro T st K₀ K t ht e he
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hrun := sparseCoreBundleToolWith_runOrdAt lsfInit L sparsify k M N D ord hV₀
    have hba := applyBatch_dynBatches hD t ht
    have hBV : (D.G 0).BatchIsValid (dynBatches D t).flatten :=
      (batchIsValid_flatten (D.G 0) (dynBatches D t)).mpr hba.2
    have hApp : (D.G 0).applyBatch (dynBatches D t).flatten = D.G t :=
      (applyBatch_flatten (D.G 0) (dynBatches D t)).trans hba.1
    have hmwu := compLSF_mwu_bound_with lsfInit C_lsst α K_σ K_ρ hKρ hApprox
      (D.G 0) hG₀ hV₀ (D.ℓ 0) hℓ₀ k hk (dynBatches D t).flatten hBV e (hApp.symm ▸ he)
    have hsum_eq : (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) =
        ∑ j ∈ Finset.range k, ((1 : ℝ) / (k : ℝ)) *
          (compLSFBatch (initCompLSFWith lsfInit (D.G 0) (D.ℓ 0) k j) (dynBatches D t).flatten).wstrGlobal e := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h1 := (hrun t).1
      have h3 := (hrun t).2.2.2.1 j
      have hL : T.lsfs (st t) j =
          (compLSFBatch (initCompLSFWith lsfInit (D.G 0) (D.ℓ 0) k j) (dynBatches D t).flatten).lsf := by
        change (if ((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.isNonempty = true
            then (((sparseCoreBundleToolWith lsfInit L sparsify).runOrdAt k M N D ord t).1.trees j).cs.lsf
            else emptyLSF) = _
        rw [h1, ite_eq_left rfl, h3, bundleRunSeqWith_cs_eq]
      rw [hL, div_eq_mul_inv, one_div, mul_comm]
      rfl
    rw [hsum_eq]
    exact hmwu
  · exfalso
    have hGt_em : (D.G t).E = ∅ := by
      have hVempty : ∀ s ≤ τ, ¬ (D.G s).V.Nonempty ∧ (D.G s).IsValid := by
        intro s hs
        induction s with
        | zero => exact ⟨hV₀, hG₀⟩
        | succ m ih =>
          obtain ⟨hnV, hGm⟩ := ih (Nat.le_of_succ_le hs)
          have hVm : (D.G m).V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnV
          have hEm : (D.G m).E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun f hf =>
            Finset.notMem_empty _ (hVm ▸ (hGm f hf).1)
          have hm := hD (m + 1) (Nat.succ_pos m) hs
          simp only [Nat.add_sub_cancel] at hm
          have hUm : D.U (m + 1) = [] := by
            cases hU : D.U (m + 1) with
            | nil => rfl
            | cons u _ =>
              exfalso
              have hu : (D.G m).UpdateIsValid u := (hU ▸ hm.1).1
              cases u with
              | insert _ u1 _ => exact Finset.notMem_empty u1 (hVm ▸ hu.2.1)
              | delete f => exact Finset.notMem_empty f (hEm ▸ hu)
              | split v _ _ _ => exact Finset.notMem_empty v (hVm ▸ hu.1)
          have hGeq : D.G (m + 1) = D.G m := by rw [hm.2, hUm]; rfl
          rw [hGeq]; exact ⟨hnV, hGm⟩
      obtain ⟨hnV, hGt⟩ := hVempty t ht
      exact Finset.eq_empty_iff_forall_notMem.mpr fun f hf => hnV ⟨(D.G t).tail f, (hGt f hf).1⟩
    exact Finset.notMem_empty e (hGt_em ▸ he)

/-- LSF `Holds`, connected-graph root count, decremental forest, `wstr` immutability, and exact
Lemma 5.5 MWU average stretch bound for `sparseCoreBundleTool` along `runOrdAt`
(paper Lemma 5.4, page 17, and Lemma 5.5, page 18). -/
theorem sparseCoreBundleTool_lsf_guarantees_at
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (ord : ℕ → ℕ → List End)
    (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) (hLen : LengthsStable D τ) :
    let T := sparseCoreBundleTool oracle C_lsst L sparsify
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t)
        (mwuK0 C_lsst * (k : ℝ) * (Real.log ((D.G t).n + 2 : ℝ)) ^ 6) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          112 * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1)) ∧
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) / (k : ℝ) ≤
        (26 * mwuK0 C_lsst + 128) *
          (Real.log ((D.G 0).n + 2 : ℝ)) ^ 6 * (Real.log ((D.G 0).m + 2 : ℝ))) := by
  intro T st m₀ n₀
  have hOld := sparseCore_lsf_guarantees_at oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hD hℓ hLen
  have heq : ∀ t j, T.lsfs (st t) j =
      (sparseCoreTool oracle C_lsst L sparsify).lsfs
        ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1 j :=
    fun t j => sparseCoreBundleTool_lsf_eq_sparseCoreTool oracle C_lsst L sparsify k M N D ord t j
  refine ⟨fun t ht j hj => ?_, fun t ht1 htτ j hj => ?_, fun t ht e he => ?_⟩
  · rw [heq t j]; exact hOld.1 t ht j hj
  · rw [heq t j, heq (t - 1) j]; exact hOld.2.1 t ht1 htτ j hj
  · have hsum : (∑ j ∈ Finset.range k, (T.lsfs (st t) j).wstr e) =
        ∑ j ∈ Finset.range k, ((sparseCoreTool oracle C_lsst L sparsify).lsfs
          ((sparseCoreTool oracle C_lsst L sparsify).runAt k M N D t).1 j).wstr e :=
      Finset.sum_congr rfl fun j _ => by rw [heq t j]
    rw [hsum]
    exact hOld.2.2 t ht e he

/-! ## 3. Initial large-component root bound and inserted-edge cardinality -/

/-- For a large component `C ∈ largeComps k G₀` (`4 * m_C ≥ k`), the initial LSF produced by any
valid `lsfInit` has at most `8 * m_C / k` roots (paper Lemma 5.4, page 17). -/
lemma initLSF_large_R_card_le_with {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (hk : 1 ≤ k) {C : Finset ℕ} (hC : C ∈ largeComps k G₀) :
    let G_C := compGraph G₀ C
    let S₀ := lsfInit G_C ℓ₀ k j
    (S₀.R.card : ℝ) ≤ 8 * (G_C.m : ℝ) / (k : ℝ) := by
  intro G_C S₀
  have hC_mem : C ∈ components G₀ := largeComps_sub hC
  have hGC_val := compGraph_isValid hG₀ hC_mem
  have hGC_ne := compGraph_nonempty hC_mem
  have hGC_conn := compGraph_connected hG₀ hC_mem
  have hℓC : ∀ e ∈ G_C.E, 0 < ℓ₀ e := fun e he => hℓ₀ e (Finset.filter_subset _ _ he)
  have hm_ge : k ≤ 4 * G_C.m := (Finset.mem_filter.mp hC).2.2
  have h1_le : (1 : ℝ) ≤ 4 * ((G_C.m : ℝ) / (k : ℝ)) := by
    have hm_r : (k : ℝ) ≤ 4 * (G_C.m : ℝ) := by exact_mod_cast hm_ge
    have := (one_le_div (by positivity : (0 : ℝ) < k)).mpr hm_r
    linarith [show 4 * ((G_C.m : ℝ) / (k : ℝ)) = 4 * (G_C.m : ℝ) / (k : ℝ) from by ring]
  have hR := (hInit G_C ℓ₀ hGC_val hGC_ne hℓC hk).2.2.2.2.2.2.2.1
  rw [ite_eq_left hGC_conn] at hR
  have hEqR : 4 * (G_C.E.card : ℝ) / (k : ℝ) = 4 * ((G_C.m : ℝ) / (k : ℝ)) := by
    change 4 * (G_C.m : ℝ) / (k : ℝ) = _; ring
  change (S₀.R.card : ℝ) ≤ 1 + 4 * (G_C.E.card : ℝ) / (k : ℝ) at hR
  rw [hEqR] at hR
  have h8 : 8 * ((G_C.m : ℝ) / (k : ℝ)) = 8 * (G_C.m : ℝ) / (k : ℝ) := by ring
  linarith

/-- For a large component `C ∈ largeComps k G₀` (`4 * m_C ≥ k`), the initial LSF has at most
`8 * m_C / k` roots (paper Lemma 5.4, page 17). -/
lemma initLSF_large_R_card_le {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) {C : Finset ℕ} (hC : C ∈ largeComps k G₀) (j : ℕ) :
    let G_C := compGraph G₀ C
    let S₀ := initLSFOnline oracle C_lsst G_C ℓ₀ k j
    (S₀.R.card : ℝ) ≤ 8 * (G_C.m : ℝ) / (k : ℝ) :=
  initLSF_large_R_card_le_with (initLSFOnline_isValidLSFInitFor hLSST k j) hG₀ hℓ₀ hk hC

lemma foldl_updateInserted_card_le (U : List Update) (S : Finset ℕ) :
    (U.foldl updateInserted S).card ≤ S.card + U.length := by
  induction U generalizing S with
  | nil => simp
  | cons u rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have h1 : (updateInserted S u).card ≤ S.card + 1 := by
      cases u with
      | insert e _ _ => exact Finset.card_insert_le e S
      | delete e => exact le_trans (Finset.card_erase_le) (Nat.le_succ _)
      | split _ _ _ _ => exact Nat.le_succ _
    have h2 := ih (updateInserted S u)
    omega

lemma compLSFBatch_insertedGlobal_card_le (cs₀ : CompLSFState) (hIns₀ : cs₀.insertedGlobal = ∅)
    (U : List Update) :
    (compLSFBatch cs₀ U).insertedGlobal.card ≤ U.length := by
  rw [compLSFBatch_insertedGlobal, hIns₀]
  simpa using foldl_updateInserted_card_le U ∅

end

end MinCostFlow.SparseCore
