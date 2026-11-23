module

public import MinCostFlow.Chain.BundleRestartCostBranch
public import MinCostFlow.SparseCore.BundleExamples
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Full `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden` for `sparseCoreBundleRestartTool`

Proves item 7 (total cumulative cost) of `SparseCoreRestartTool.IsSpecOrdRestart` for
`sparseCoreBundleRestartTool` (`bundleRestart_totalCost_le`), by summing
`bundleBranch_cost_restart_le` across all `k` branches. Combining with items 1–6
(`bundleRestart_spec_noTotalCost`) gives the complete specification (`bundleRestart_spec`,
`sparseCoreBundleRestartTool_isSpecOrdRestart`, `sparseCoreBundleRestartTool_isSpecOrdRestartNoHidden`,
and the unconditional `*_of_B_ge_m` corollaries) under `BundleCoreHypsAt`, with no input degree
bound and no `hComp_bound` (paper Lemma 5.17, pages 23–24).

Also provides concrete non-vacuity witnesses (`ex_bundleRestart_isSpecOrdRestart` and
`ex_bundleRestart_inst`) exercising a nontrivial restart schedule on `(exBundleDyn, exBundleOrd)`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner
open MinCostFlow.Bundle

private lemma list_sum_count_eq_length' (xs : List ℕ) (k : ℕ) (h : ∀ j ∈ xs, j < k) :
    ∑ j ∈ Finset.range k, xs.count j = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx : x < k := h x List.mem_cons_self
    have hxs : ∀ j ∈ xs, j < k := fun j hj => h j (List.mem_cons_of_mem x hj)
    have hsplit : ∑ j ∈ Finset.range k, (x :: xs).count j =
        ∑ j ∈ Finset.range k, (xs.count j + if j = x then 1 else 0) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjx : j = x
      · subst hjx; simp [List.count_cons_self]
      · simp [List.count_cons_of_ne (Ne.symm hjx), hjx]
    rw [hsplit, Finset.sum_add_distrib, ih hxs]
    simp [Finset.mem_range.mpr hx]

/-- Item 7 of `SparseCoreRestartTool.IsSpecOrdRestart` for `sparseCoreBundleRestartToolWith`
(without any input degree bound or `hComp_bound`): the cumulative cost after step `τ` is at most
`c_T * (M + 1) * (k + R) * (k + 1) * γ_r(M) * log^{p_T}(M + N + 2)`. -/
theorem bundleRestartWith_totalCost_le (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    (T.cost (T.runOrdAfterRestarts k M N D ord restarts τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro T P
  have hValP := bundleCoreParams_valid E
  have hγrM : 1 ≤ P.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hcT_nn : 0 ≤ P.c_T := hValP.2.2.2.2.2.2.2.2.2
  have hlogMN_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
  set G_M := P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + 1) * P.γ_r M *
    (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T with hG_Mdef
  have hG_M_nn : 0 ≤ G_M :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hcT_nn (by positivity)) (by positivity)) (by linarith))
      (pow_nonneg hlogMN_nn _)
  set S := ((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) with hSdef
  have hgoal_eq : P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + (S : ℝ)) * ((k : ℝ) + 1) * P.γ_r M *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T = ((k : ℝ) + (S : ℝ)) * G_M := by
    rw [hG_Mdef]; ring
  rw [hgoal_eq]
  have hkS_nn : 0 ≤ (k : ℝ) + (S : ℝ) := by positivity
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
      ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
    have hne := (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts τ).2.1.trans
      (decide_eq_true hV₀)
    have hk_post :=
      (runOrdAfterRestarts_isNonempty lsfInit E.C_lsst E.L sparsify k M N D ord restarts τ).2.2.2.1
    have hcost : T.cost (T.runOrdAfterRestarts k M N D ord restarts τ) =
        ∑ j ∈ Finset.range k, ((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost := by
      change (if (T.runOrdAfterRestarts k M N D ord restarts τ).isNonempty = true then
        ∑ j ∈ Finset.range (T.runOrdAfterRestarts k M N D ord restarts τ).k,
          ((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost else 0) = _
      dsimp only [T]
      simp only [hne, ↓reduceIte, hk_post]
    rw [hcost, Nat.cast_sum]
    have hS_eq : (S : ℝ) = ∑ j ∈ Finset.range k,
        ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
      rw [Finset.sum_comm, hSdef, Nat.cast_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [← list_sum_count_eq_length' (restarts r) k (hrest r hr_le), Nat.cast_sum]
    have hbranch : ∀ j ∈ Finset.range k,
        ((((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost : ℕ) : ℝ) ≤
          (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M := fun j hj =>
      bundleBranch_cost_restart_le E lsfInit sparsify k M N τ D ord restarts hk hG₀ hV₀ hℓ₀ hD hOrd
        hM hN hThresh hHyps j (Finset.mem_range.mp hj)
    calc ∑ j ∈ Finset.range k,
            ((((T.runOrdAfterRestarts k M N D ord restarts τ).trees j).cost : ℕ) : ℝ)
        ≤ ∑ j ∈ Finset.range k,
            (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M :=
          Finset.sum_le_sum hbranch
      _ = ((k : ℝ) + (S : ℝ)) * G_M := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, hS_eq]
          simp
  · have hrunE := runOrdAfterRestarts_empty_case lsfInit E.C_lsst E.L sparsify k M N D ord restarts hV₀
    have hcost0 : T.cost (T.runOrdAfterRestarts k M N D ord restarts τ) = 0 := by
      have hhem : (T.runOrdAfterRestarts k M N D ord restarts τ).isNonempty = false := (hrunE τ).2.1
      change (if (T.runOrdAfterRestarts k M N D ord restarts τ).isNonempty = true then _ else 0) = 0
      rw [hhem]; rfl
    rw [hcost0, Nat.cast_zero]
    exact mul_nonneg hkS_nn hG_M_nn

/-- Item 7 of `SparseCoreRestartTool.IsSpecOrdRestart` for `sparseCoreBundleRestartTool` (without
any input degree bound or `hComp_bound`): the cumulative cost after step `τ` is at most
`c_T * (M + 1) * (k + R) * (k + 1) * γ_r(M) * log^{p_T}(M + N + 2)`. -/
theorem bundleRestart_totalCost_le (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    (T.cost (T.runOrdAfterRestarts k M N D ord restarts τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T :=
  bundleRestartWith_totalCost_le E (initLSFOnline oracle E.C_lsst) sparsify k τ M N D ord restarts
    Ψ c w hk hG₀ hD hWeak hOrd hM hN hrest hThresh hHyps.toWith

/-- Full `SparseCoreRestartTool.IsSpecOrdRestart` (all seven items) for
`sparseCoreBundleRestartToolWith` on one instance under `BundleCoreHypsAtWith`. -/
theorem bundleRestartWith_spec (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    let T := sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (post t) j) (T.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
      (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (T.coreCOrdFrom k M N D ord restarts c s₀ j)
          (T.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j)) ∧
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  intro T P pre U_S post
  have h := bundleRestart_spec_noTotalCost E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hHyps
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2,
    bundleRestartWith_totalCost_le E lsfInit sparsify k τ M N D ord restarts Ψ c w hk hG₀ hD hWeak hOrd
      hM hN hrest hThresh hHyps⟩

/-- Full `SparseCoreRestartTool.IsSpecOrdRestart` (all seven items) for
`sparseCoreBundleRestartTool` on one instance under `BundleCoreHypsAt` (paper Lemma 5.17, pages
23–24). -/
theorem bundleRestart_spec (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hOrd : OrderedUpTo D τ 2 ord)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : BundleCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify
    let P := bundleCoreParams E
    let pre := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).1
    let U_S := fun t => (T.runOrdAfterUpdate k M N D ord restarts t).2
    let post := fun t => T.runOrdAfterRestarts k M N D ord restarts t
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (post t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (post t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (post t) j) (T.emb (post t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (post t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (post t) j).F.F.E ⊆ (T.lsfs (post (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (post t) j).wstr e = (T.lsfs (post (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (post t) j).wstr e = 1) ∧
      (T.S (post (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (pre t) j = (T.S (post (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (pre r)
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r < t → j ∉ restarts r) →
      (((Finset.Icc (s₀ + 1) t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc (s₀ + 1) t).sum fun s => (T.S (post (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc (s₀ + 1) t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      ∃ Ψ' : ℝ,
        WeakHiddenStable (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) Ψ'
          (T.coreCOrdFrom k M N D ord restarts c s₀ j)
          (T.coreWOrdFrom k M N D ord restarts w s₀ j)) ∧
    (∀ s₀ t, s₀ ≤ t → t ≤ τ → ∀ j < k,
      (s₀ = 0 ∨ j ∈ restarts s₀) →
      (∀ r, s₀ < r → r ≤ t → j ∉ restarts r) →
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j)) ∧
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :=
  bundleRestartWith_spec E (initLSFOnline oracle E.C_lsst) sparsify k τ M N D ord restarts
    Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hHyps.toWith

/-- **`SparseCoreRestartTool.IsSpecOrdRestart` for `sparseCoreBundleRestartToolWith`** with
`bundleCoreParams E`, under a per-instance `BundleCoreHypsAtWith` provider. -/
theorem sparseCoreBundleRestartToolWith_isSpecOrdRestart (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    (sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify).IsSpecOrdRestart
      (bundleCoreParams E) := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh
  exact bundleRestartWith_spec E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH

/-- **`SparseCoreRestartTool.IsSpecOrdRestartNoHidden` for `sparseCoreBundleRestartToolWith`** with
`bundleCoreParams E`, derived from `sparseCoreBundleRestartToolWith_isSpecOrdRestart`. -/
theorem sparseCoreBundleRestartToolWith_isSpecOrdRestartNoHidden (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    (sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify).IsSpecOrdRestartNoHidden
      (bundleCoreParams E) :=
  (sparseCoreBundleRestartToolWith_isSpecOrdRestart E lsfInit sparsify hHyps).toNoHidden

/-- **General `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden` for
`sparseCoreBundleRestartToolWith`** from any approximate MWU LSF initializer (`IsApproxMWUInit`). -/
theorem toolWith_isSpecOrdRestart
    (E : SparseCoreEnv) (α K_σ K_ρ : ℝ) (_hα : 1 ≤ α) (_hKρ : 1 ≤ K_ρ) :
    ∃ TP : SparseCoreParams, TP.Valid ∧
      ∀ (lsfInit : LSFInit)
        (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut),
        IsApproxMWUInit lsfInit E.C_lsst α K_σ K_ρ →
        (∀ m, DynSpanner.SparsifySpec m (E.P_fn m) (sparsify m)) → (∀ m, m ≤ E.B_fn m) →
        (sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify).IsSpecOrdRestart TP ∧
        (sparseCoreBundleRestartToolWith lsfInit E.C_lsst E.L sparsify).IsSpecOrdRestartNoHidden TP := by
  let E' : SparseCoreEnv := { E with C_lsst := max E.C_lsst (K_σ / 6272) }
  refine ⟨bundleCoreParams E', bundleCoreParams_valid E', fun lsfInit sparsify hApprox hSp hBm => ?_⟩
  have hSpec : (sparseCoreBundleRestartToolWith lsfInit E'.C_lsst E'.L sparsify).IsSpecOrdRestart
      (bundleCoreParams E') :=
    sparseCoreBundleRestartToolWith_isSpecOrdRestart E' lsfInit sparsify
      (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
        bundleCoreHypsAtWith_of_B_ge_m (fun j hj => hApprox.toValidLSFInitFor hj)
          (hSp M) (le_trans hM (hBm M)))
  exact ⟨hSpec, hSpec.toNoHidden⟩

/-- **`SparseCoreRestartTool.IsSpecOrdRestart` for `sparseCoreBundleRestartTool`** with
`bundleCoreParams E`, under a per-instance `BundleCoreHypsAt` provider (no input degree bound and
no `hComp_bound`; paper Lemma 5.17, pages 23–24). -/
theorem sparseCoreBundleRestartTool_isSpecOrdRestart (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify).IsSpecOrdRestart
      (bundleCoreParams E) := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh
  exact bundleRestart_spec E oracle sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH

/-- **`SparseCoreRestartTool.IsSpecOrdRestartNoHidden` for `sparseCoreBundleRestartTool`** with
`bundleCoreParams E`, derived from `sparseCoreBundleRestartTool_isSpecOrdRestart`. -/
theorem sparseCoreBundleRestartTool_isSpecOrdRestartNoHidden (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      BundleCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify).IsSpecOrdRestartNoHidden
      (bundleCoreParams E) :=
  (sparseCoreBundleRestartTool_isSpecOrdRestart E oracle sparsify hHyps).toNoHidden

/-- Unconditional `IsSpecOrdRestart` when `∀ m, m ≤ E.B_fn m` and `sparsify` satisfies
`SparsifySpec` at every `m`. -/
theorem sparseCoreBundleRestartTool_isSpecOrdRestart_of_B_ge_m (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : ∀ m, SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    (sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify).IsSpecOrdRestart
      (bundleCoreParams E) :=
  sparseCoreBundleRestartTool_isSpecOrdRestart E oracle sparsify
    (fun _ _ M _ _ _ _ _ _ _ _ _ hM _ _ =>
      bundleCoreHypsAt_of_B_ge_m hLSST (hSp M) (le_trans hM (hBm M)))

/-- Unconditional `IsSpecOrdRestartNoHidden` when `∀ m, m ≤ E.B_fn m` and `sparsify` satisfies
`SparsifySpec` at every `m`. -/
theorem sparseCoreBundleRestartTool_isSpecOrdRestartNoHidden_of_B_ge_m (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hLSST : HasLSSTSpec oracle E.C_lsst)
    (hSp : ∀ m, SparsifySpec m (E.P_fn m) (sparsify m))
    (hBm : ∀ m, m ≤ E.B_fn m) :
    (sparseCoreBundleRestartTool oracle E.C_lsst E.L sparsify).IsSpecOrdRestartNoHidden
      (bundleCoreParams E) :=
  (sparseCoreBundleRestartTool_isSpecOrdRestart_of_B_ge_m E oracle sparsify hLSST hSp hBm).toNoHidden

/-! ## Concrete Non-Vacuity Witnesses -/

/-- **Non-vacuity of `IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden`** for
`sparseCoreBundleRestartTool` with `bundleCoreParams (exBundleEnv C_lsst)`. -/
theorem ex_bundleRestart_isSpecOrdRestart :
    ∃ oracle C_lsst, HasLSSTSpec oracle C_lsst ∧
      let E := exBundleEnv C_lsst
      let T := sparseCoreBundleRestartTool oracle E.C_lsst E.L (fun _ => idSparsify)
      let P := bundleCoreParams E
      P.Valid ∧ T.IsSpecOrdRestart P ∧ T.IsSpecOrdRestartNoHidden P := by
  obtain ⟨oracle, C_lsst, hLSST⟩ := theorem_2_2
  have hSpec := sparseCoreBundleRestartTool_isSpecOrdRestart_of_B_ge_m
    (exBundleEnv C_lsst) oracle (fun _ => idSparsify) hLSST idSparsify_spec (fun m => Nat.le_succ m)
  exact ⟨oracle, C_lsst, hLSST, bundleCoreParams_valid _, hSpec, hSpec.toNoHidden⟩

/-- Nontrivial restart schedule for `exBundleDyn`: restarts branch `0` at step `1` (after the edge
insertion and before the edge deletion and vertex split). -/
def exBundleRestarts : ℕ → List ℕ := fun t => if t = 1 then [0] else []

/-- **Concrete instantiation of `bundleRestart_spec`** on `(exBundleDyn, exBundleOrd)` with the
nontrivial restart schedule `exBundleRestarts`. -/
theorem ex_bundleRestart_inst :
    ∃ oracle C_lsst, HasLSSTSpec oracle C_lsst ∧
      let E := exBundleEnv C_lsst
      let T := sparseCoreBundleRestartTool oracle E.C_lsst E.L (fun _ => idSparsify)
      let P := bundleCoreParams E
      let post := fun t => T.runOrdAfterRestarts 1 exBundleG₀.m exBundleG₀.n exBundleDyn exBundleOrd
        exBundleRestarts t
      (∀ t ≤ 3,
        IsSparsifiedCoreGraphAt (exBundleDyn.G t) (T.lsfs (post t) 0) (exBundleDyn.ℓ t)
          ((1 : ℕ) : ℝ) (P.γ_ℓ exBundleG₀.m) (P.γ_c exBundleG₀.m) exBundleG₀.m
          (T.S (post t) 0) (T.emb (post t) 0)) ∧
      OrderedUpTo (T.coreInstanceOrdFrom 1 exBundleG₀.m exBundleG₀.n exBundleDyn exBundleOrd
          exBundleRestarts 1 0) (3 - 1) 2 (fun δ => T.rot (post (1 + δ)) 0) ∧
      ((T.cost (post 3) : ℝ) ≤
        P.c_T * ((exBundleG₀.m : ℝ) + 1) * (((1 : ℕ) : ℝ) + (1 : ℝ)) * (((1 : ℕ) : ℝ) + 1) *
          P.γ_r exBundleG₀.m * (Real.log ((exBundleG₀.m : ℝ) + (exBundleG₀.n : ℝ) + 2)) ^ P.p_T) := by
  obtain ⟨oracle, C_lsst, hLSST⟩ := theorem_2_2
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero exBundleDyn_len_pos
  have hrest : ∀ r ≤ 3, ∀ j ∈ exBundleRestarts r, j < 1 := by
    intro r _ j hj
    dsimp only [exBundleRestarts] at hj
    split_ifs at hj
    · simp only [List.mem_singleton] at hj; omega
    · cases hj
  have hSpec := bundleRestart_spec (exBundleEnv C_lsst) oracle (fun _ => idSparsify)
    1 3 exBundleG₀.m exBundleG₀.n exBundleDyn exBundleOrd exBundleRestarts Ψ _ _
    Nat.one_pos exBundleG₀_valid exBundleDyn_valid exBundleDyn_lengthsStable hWeak
    exBundleDyn_orderedUpTo le_rfl le_rfl hrest exBundleDyn_thresh
    (exBundleDyn_hypsAt oracle C_lsst hLSST)
  refine ⟨oracle, C_lsst, hLSST, fun t ht => (hSpec.1 t ht 0 Nat.one_pos).2.1, ?_, ?_⟩
  · exact hSpec.2.2.2.2.2.1 1 3 (by omega) le_rfl 0 Nat.one_pos
      (Or.inr (by simp [exBundleRestarts]))
      (fun r hr1 _ => by
        dsimp only [exBundleRestarts]
        split_ifs with hr
        · omega
        · simp)
  · have hsumR : ((Finset.range (3 + 1)).sum fun s => (exBundleRestarts s).length) = 1 := by
      simp [exBundleRestarts, Finset.sum_range_succ]
    have hcost := hSpec.2.2.2.2.2.2
    simpa only [hsumR, Nat.cast_one] using hcost

end MinCostFlow.Chain

end
