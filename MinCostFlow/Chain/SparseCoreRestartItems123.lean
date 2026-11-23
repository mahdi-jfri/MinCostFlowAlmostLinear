module

public import MinCostFlow.Chain.SparseCoreRestart
public import MinCostFlow.Chain.SparseCoreRestartInv
import MinCostFlow.Chain.SparseCoreRestartEpoch
public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.SparseCoreCostEnv
import MinCostFlow.SparseCore.Lemma517
import MinCostFlow.SparseCore.SparseCoreBounds
import MinCostFlow.SparseCore.SparseCoreCost
import MinCostFlow.SparseCore.SparseCoreRecourse
import MinCostFlow.SparseCore.SparseCoreMetrics
import MinCostFlow.SparseCore.SparseCoreRunBounds
import MinCostFlow.SparseCore.SparseCoreSpannerMetrics
import MinCostFlow.SparseCore.SparseCoreStability
import MinCostFlow.DynSpanner.Complexity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Items 1–3 (non-cost) of `IsSpecRestart` for `sparseCoreRestartTool`

Proves `sparseCoreRestart_spec_item1_noComp`, `sparseCoreRestart_spec_item2_noComp`, and
`sparseCoreRestart_spec_item3_noComp` (the non-cost part of item 3) on nonempty initial graphs,
using the update budget at `(M, N)` directly (no `hThresh₀`).
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- Helper: at any step `t ≤ τ`, the LSF of branch `j` in `runAfterRestarts k M N` coincides with
the LSF of `sparseCoreTool.run k D t`. -/
lemma sRT_lsfs_eq_run (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (k M N τ : ℕ) (hk : 1 ≤ k) (D : DynamicInstance) (restarts : ℕ → List ℕ)
    (hG₀ : (D.G 0).IsValid) (hV₀ : (D.G 0).V.Nonempty)
    (hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) (hD : D.IsValid τ) :
    let T := sparseCoreRestartTool oracle C_lsst L sparsify
    ∀ t ≤ τ, ∀ j,
      T.lsfs (T.runAfterRestarts k M N D restarts t) j =
        (sparseCoreTool oracle C_lsst L sparsify).lsfs
          ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1 j := by
  intro T t ht j
  have hne : (T.runAfterRestarts k M N D restarts t).isNonempty = true :=
    (runAfterRestarts_isNonempty oracle C_lsst L sparsify k M N D restarts t).2.1.trans
      (decide_eq_true hV₀)
  have hrun := sparseCoreTool_run_eq_treeRunSeq oracle C_lsst L sparsify k D hV₀
  have hp := (runAfterRestarts_base_proj oracle C_lsst L sparsify k M N D restarts hV₀ j t).2.cs
  have hcs1 := ((treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k M N τ hk D hG₀ hV₀ hℓ₀ hD j).1 t ht).2.2.2.2.2.2.2.1
  have hcs2 := ((treeRunSeq_tilde_core_inv oracle C_lsst L sparsify hLSST
    k (D.G 0).m (D.G 0).n τ hk D hG₀ hV₀ hℓ₀ hD j).1 t ht).2.2.2.2.2.2.2.1
  have hne0 : ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = true :=
    (hrun t).1
  dsimp only [T] at hne ⊢
  rw [sRT_lsfs_of_nonempty hne j, hp, hcs1, ← hcs2, ← (hrun t).2.2.1 j]
  change _ = (if ((sparseCoreTool oracle C_lsst L sparsify).run k D t).1.isNonempty = true then
    _ else _)
  simp only [hne0, ↓reduceIte]

/-- Item 1 of `IsSpecRestart` for `sparseCoreRestartTool` on a nonempty initial graph: the LSF
bounds and the sparsified core graph property at every stage. -/
theorem sparseCoreRestart_spec_item1_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let post := fun t => T.runAfterRestarts k M N D restarts t
    ∀ t ≤ τ, ∀ j < k,
        (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
        IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
          (T.S (post t) j) (T.emb (post t) j) ∧
        ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
          ((T.lsfs (post t) j).F.R.card : ℝ) ≤
            P.c_R * ((M : ℝ) / (k : ℝ) +
              (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
                (Real.log ((N : ℝ) + 2)) ^ 2 + 1)) := by
  intro T P post
  have hValP := sparseCoreParams_valid E
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  set m₀ := (D.G 0).m
  set n₀ := (D.G 0).n
  have hm₀M : (m₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hn₀N : (n₀ : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hLSF := sparseCore_lsf_guarantees oracle E.C_lsst E.L sparsify hHyps.hLSST
    k τ hk D hG₀ hD hℓ hLen
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hLSF_eq := sRT_lsfs_eq_run oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D restarts hG₀ hV₀ hℓ₀ hD
  have hSc := runAfterRestarts_S_cur_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD
  intro t ht j hj
  have hlsf_tj := hLSF.1 t ht j hj
  rw [← hLSF_eq t ht j] at hlsf_tj
  have hholds := holds_mono_sigma hlsf_tj.1 (le_max_right (1 : ℝ) _)
  set s₀ := lastRestart restarts j t
  have hs₀ := lastRestart_spec restarts j t
  have hInv := epochTreeSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hThresh s₀ t j hj hs₀.1 ht hs₀.2.1
    (fun r hr1 hr2 => hs₀.2.2 r hr1 (Nat.le_of_lt hr2))
  have hep_post : epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j (t - s₀) =
      (post t).trees j := by
    refine (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ t j hs₀.1).2.1 ?_
    by_cases hlt : s₀ < t
    · exact Or.inl (hs₀.2.2 t hlt le_rfl)
    · exact Or.inr (by omega)
  have hSt_t := (epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ t j hs₀.1 (fun r hr1 hr2 => hs₀.2.2 r hr1 (Nat.le_of_lt hr2))).1
      (t - s₀) le_rfl
  rw [hep_post, show s₀ + (t - s₀) = t by omega] at hSt_t
  have hStg_t := hInv.2.2.1 (t - s₀) le_rfl
  have hSc_t := (hSc j t ht).2
  rw [hep_post] at hStg_t
  obtain ⟨hBaseT, _, _⟩ := treeRunSeq_tilde_core_inv oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D hG₀ hV₀ hℓ₀ hD j
  have hOB : ((post t).trees j).origBucket =
      fun e => bucketOf (coreLen (initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j).lsf
        (safeLen (D.G 0) (D.ℓ 0)) e) :=
    hSt_t.origBucket.trans (hBaseT t ht).2.2.2.2.1
  have hSp_core := treeCoreState_isSparsifiedCoreGraph oracle E.C_lsst E.L E.hL (E.P_fn M)
    sparsify hHyps.hLSST k M N τ hk1 D hG₀ hV₀ hD hℓ hLen hM hN hThresh hHyps.hSp j hj t ht
    ((post t).trees j) hOB hSt_t.cs hSt_t.ts hSt_t.activeComps
    hSc_t.2.1 hSc_t.2.2.1 hSc_t.2.2.2
    (fun C hC b =>
      let cb := hStg_t.2.2 C hC b
      ⟨cb.1, cb.2.1,
        cb.2.2.1.trans (origBucket_filter_safe_eq oracle E.C_lsst hk1 hG₀ hV₀ hℓ₀ hC hHyps.hLSST
          (hSt_t.ts.symm ▸ ((hBaseT t ht).2.2.2.2.2.2.2.2.2.2.2.2 C hC).2.2.1) hOB b),
        cb.2.2.2.1⟩)
    (fun C hC b =>
      let cb := hStg_t.2.2 C hC b
      ⟨cb.2.2.2.2.1, cb.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.1,
        cb.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.1, cb.2.2.2.2.2.2.2.2.2.2⟩)
  dsimp only at hSp_core
  have hL_pt : T.lsfs (post t) j = ((post t).trees j).cs.lsf := by
    dsimp only [T]; exact sRT_lsfs_of_nonempty (hne t) j
  have hS_pt : T.S (post t) j = ((post t).trees j).S_cur := by
    dsimp only [T]; exact sRT_S_of_nonempty (hne t) j
  have hEmb_pt : T.emb (post t) j = ((post t).trees j).emb := by
    dsimp only [T]; exact sRT_emb_of_nonempty (hne t) j
  rw [← hL_pt, ← hS_pt, ← hEmb_pt] at hSp_core
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlen : ((T.emb (post t) j).length (coreGraph (D.G t) (T.lsfs (post t) j)) : ℝ) ≤
      P.γ_ℓ M :=
    le_trans hSp_core.2.2.2.1 (le_max_left _ _)
  have hcong : (T.emb (post t) j).econg (coreGraph (D.G t) (T.lsfs (post t) j))
      (T.S (post t) j) (fun _ => 1) (fun _ => 1) ≤ (k : ℝ) * P.γ_c M := by
    set cs₀ := initCompLSF oracle E.C_lsst (D.G 0) (D.ℓ 0) k j
    have hdeg_le : (((components (D.G 0)).sup fun C =>
        (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) ≤ (E.d_fn M : ℝ) := by
      exact_mod_cast hHyps.hDeg_bound.2 j hj
    have hce_nn := coreE82Cong_nonneg E.L (E.P_fn M)
    have h1 : 1 + coreE82Cong E.L (E.P_fn M) *
        (((components (D.G 0)).sup fun C =>
          (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) ≤ P.γ_c M := by
      dsimp only [P, sparseCoreParams]
      nlinarith
    have hγc_ge1 : 1 ≤ P.γ_c M := hValP.2.2.2.2.1 M
    calc _ ≤ 1 + coreE82Cong E.L (E.P_fn M) *
          (((components (D.G 0)).sup fun C =>
            (initTildeState (cs₀.compSt C)).C.maxDeg : ℕ) : ℝ) := hSp_core.2.2.2.2.1
      _ ≤ P.γ_c M := h1
      _ = 1 * P.γ_c M := (one_mul _).symm
      _ ≤ (k : ℝ) * P.γ_c M := by nlinarith
  have hcard : ((T.S (post t) j).E.card : ℝ) ≤ (M : ℝ) * P.γ_ℓ M / (k : ℝ) := by
    have hC_sp := hSp_core.2.2.2.2.2.2 (E.B_fn M) (hHyps.hB_bound j hj)
    have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    have hdeg_le : ((D.G 0).maxDeg : ℝ) ≤ (E.d_fn M : ℝ) := by
      exact_mod_cast hHyps.hDeg_bound.1
    have hKs_nn := (E.P_fn M).hK_s
    have hγ_nn : 0 ≤ (E.P_fn M).γ_ℓ := by linarith [(E.P_fn M).hγ_ℓ]
    have hlam_nn := coreLambdaS_pos (E.P_fn M) M
    have hB_nn : (0 : ℝ) ≤ (E.B_fn M : ℝ) := Nat.cast_nonneg _
    have hcoef :
        (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
              (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤ P.γ_ℓ M := by
      have h11 : (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
          coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
            (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) ≤
          11 * (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
              (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) := by
        have : (0 : ℝ) ≤ ((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
            coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
              (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115 := by positivity
        linarith
      refine le_trans h11 (le_trans ?_ (le_max_right _ _))
      gcongr
    have hmul : (((E.L : ℝ) + 1) * (E.P_fn M).K_s * (E.P_fn M).γ_ℓ *
        coreLambdaS (E.P_fn M) M * (E.B_fn M : ℝ) *
          (2 * ((D.G 0).maxDeg : ℝ) + 190) + 115) * (M : ℝ) ≤
        P.γ_ℓ M * (M : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg _)
    exact le_trans hC_sp (div_le_div_of_nonneg_right hmul (le_of_lt hk_pos) |>.trans_eq (by ring))
  have hR_le : (∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
      ((T.lsfs (post t) j).F.R.card : ℝ) ≤ P.c_R * ((M : ℝ) / (k : ℝ) +
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          (Real.log ((N : ℝ) + 2)) ^ 2 + 1) := by
    intro hConn
    have hbase := hlsf_tj.2 hConn
    have h1 : (m₀ : ℝ) / (k : ℝ) ≤ (M : ℝ) / (k : ℝ) :=
      div_le_div_of_nonneg_right hm₀M (by positivity)
    have hlogn : 0 ≤ Real.log ((n₀ : ℝ) + 2) := Real.log_nonneg (by linarith)
    have hlogn_le : Real.log ((n₀ : ℝ) + 2) ≤ Real.log ((N : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have hsq_le : Real.log ((n₀ : ℝ) + 2) ^ 2 ≤ Real.log ((N : ℝ) + 2) ^ 2 :=
      pow_le_pow_left₀ hlogn hlogn_le 2
    have h2 : (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          Real.log ((n₀ : ℝ) + 2) ^ 2 ≤
        (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
          Real.log ((N : ℝ) + 2) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq_le (Nat.cast_nonneg _)
    have hcR : (0 : ℝ) ≤ P.c_R := hValP.2.2.2.2.2.2.2.2.1
    refine le_trans hbase (mul_le_mul_of_nonneg_left ?_ hcR)
    linarith
  exact ⟨hholds, ⟨hSp_core.1, hSp_core.2.1, hSp_core.2.2.1, hlen, hcong, hcard⟩, hR_le⟩

/-- Item 2 of `IsSpecRestart` for `sparseCoreRestartTool` on a nonempty initial graph: the forest
only shrinks, stretches change only on inserted edges, and each spanner batch is valid. -/
theorem sparseCoreRestart_spec_item2_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (_hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D)
    (hV₀ : (D.G 0).V.Nonempty) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
    let post := fun t => T.runAfterRestarts k M N D restarts t
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
        (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
        (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
          (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
        (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
        (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
        T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j) := by
  intro T pre U_S post
  have hk1 : 1 ≤ k := hk
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := hℓ 0 (Nat.zero_le τ)
  have hLSF := sparseCore_lsf_guarantees oracle E.C_lsst E.L sparsify hHyps.hLSST
    k τ hk D hG₀ hD hℓ hLen
  have hne : ∀ s, (post s).isNonempty = true := fun s =>
    (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts s).2.1.trans
      (decide_eq_true hV₀)
  have hLSF_eq := sRT_lsfs_eq_run oracle E.C_lsst E.L sparsify hHyps.hLSST
    k M N τ hk1 D restarts hG₀ hV₀ hℓ₀ hD
  intro t ht1 htτ j hj
  have hlsf_step := hLSF.2.1 t ht1 htτ j hj
  rw [← hLSF_eq t htτ j, ← hLSF_eq (t - 1) (by omega) j] at hlsf_step
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hlsf_step ⊢
  set s₀ := lastRestart restarts j s
  have hs₀ := lastRestart_spec restarts j s
  have hNoR : ∀ r, s₀ < r → r < s + 1 → j ∉ restarts r :=
    fun r hr1 hr2 => hs₀.2.2 r hr1 (by omega)
  have hInv := epochTreeSeq_inv oracle E.C_lsst E.L E.hL (E.P_fn M) sparsify hHyps.hLSST
    k M N τ hk1 D restarts hM hN hHyps.hSp hG₀ hV₀ hℓ₀ hD hThresh s₀ (s + 1) j hj
    (by omega) htτ hs₀.2.1 hNoR
  have hStep := (epochTreeSeq_steps oracle E.C_lsst E.L sparsify
    k M N D restarts hV₀ s₀ (s + 1) j (by omega) hNoR).2 (s - s₀) (by omega)
  have hStp := hInv.2.2.2.1 (s - s₀) (by omega)
  have hprev : epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ (s + 1) j (s - s₀) =
      (post s).trees j := by
    have h1 := (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ (s + 1) j (by omega)).1
      (s - s₀) (by omega)
    rw [show s₀ + (s - s₀) = s by omega] at h1
    exact h1
  have hcur : epochTreeSeq oracle E.C_lsst E.L sparsify k M N D restarts s₀ (s + 1) j (s - s₀ + 1) =
      (pre (s + 1)).trees j := by
    have h2 := (epochTreeSeq_eq_post oracle E.C_lsst E.L sparsify k M N D restarts s₀ (s + 1) j (by omega)).2.2
      (by omega)
    rw [show s + 1 - s₀ = s - s₀ + 1 by omega] at h2
    exact h2
  have hUS : U_S (s + 1) j =
      (stepTreeCoreAux sparsify ((post s).trees j) (D.U (s + 1))).U_S := by
    have := hStep.2
    rw [show s₀ + (s - s₀) + 1 = s + 1 by omega, hprev] at this
    exact this
  have hBV : T.S (post s) j |>.BatchIsValid (U_S (s + 1) j) := by
    dsimp only [T, post] at hne ⊢
    rw [sRT_S_of_nonempty (hne s) j, hUS, ← hprev]
    rw [show s₀ + (s - s₀) + 1 = s + 1 by omega] at hStp
    exact hStp.1
  have hApp : T.S (pre (s + 1)) j = (T.S (post s) j).applyBatch (U_S (s + 1) j) := by
    have hne_pre : (pre (s + 1)).isNonempty = true :=
      (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts (s + 1)).1.trans
        (decide_eq_true hV₀)
    dsimp only [T, pre, post] at hne hne_pre ⊢
    rw [sRT_S_of_nonempty hne_pre j, sRT_S_of_nonempty (hne s) j, hUS, ← hcur, ← hprev]
    rw [show s₀ + (s - s₀) + 1 = s + 1 by omega] at hStp
    exact hStp.2.1
  exact ⟨hlsf_step.1, hlsf_step.2.1, hlsf_step.2.2, hBV, hApp⟩

/-- The non-cost part of item 3 of `IsSpecRestart` for `sparseCoreRestartTool`: a restart of branch
`j'` keeps all forests and all other branches. -/
theorem sparseCoreRestart_spec_item3_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
        let st' := p.foldl T.restart (pre r)
        (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
        (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
        T.cost st' ≤ T.cost (T.restart st' j') := by
  intro T pre r _ p j' _ st'
  exact ⟨fun b _ => sparseCoreRestartTool_restart_lsfs oracle E.C_lsst E.L sparsify st' j' b,
    fun b _ hbj => (sparseCoreRestartTool_restart_other oracle E.C_lsst E.L sparsify st' hbj).2,
    sparseCoreRestartTool_cost_le_restart oracle E.C_lsst E.L sparsify st' j'⟩

end MinCostFlow.Chain

end
