module

public import MinCostFlow.Chain.SparseCoreRestartBranchCost
import MinCostFlow.Chain.SparseCoreRestartAux
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# `IsSpecRestart` for `sparseCoreRestartTool`

This file proves item 6 of `SparseCoreRestartTool.IsSpecRestart`, the bound on the total cost of
a run with restarts (`sparseCoreRestart_totalCost_le_noComp`), by summing
`branch_cost_restart_le_noComp` over the branches. With items 1 to 5
(`sparseCoreRestart_spec_noTotalCost_noComp`) it gives the full specification
(`sparseCoreRestart_spec_noComp` and `sparseCoreRestartTool_isSpecRestart_noComp`), using the
update budget at `(M, N)` directly — with NO `hThresh₀` assumption.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.LSF
open MinCostFlow.SparseCore
open MinCostFlow.DynSpanner

/-- Item 6 of `SparseCoreRestartTool.IsSpecRestart` for `sparseCoreRestartTool` (without
`hComp_bound` or `hThresh₀`): the total cost after step `τ` is at most
`c_T (M + 1) (k + R) γ_r(M) log^{p_T}(M + N + 2)`. -/
theorem sparseCoreRestart_totalCost_le_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    (T.cost (T.runAfterRestarts k M N D restarts τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T := by
  intro T P
  have hValP := sparseCoreParams_valid E
  have hγrM : 1 ≤ P.γ_r M := hValP.2.2.2.2.2.2.1 M
  have hcT_nn : 0 ≤ P.c_T := hValP.2.2.2.2.2.2.2.2.2
  have hlogMN_nn : 0 ≤ Real.log ((M : ℝ) + (N : ℝ) + 2) :=
    Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) M, Nat.cast_nonneg (α := ℝ) N])
  set G_M := P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T
    with hG_Mdef
  have hG_M_nn : 0 ≤ G_M :=
    mul_nonneg (mul_nonneg (mul_nonneg hcT_nn (by positivity)) (by linarith))
      (pow_nonneg hlogMN_nn _)
  set S := ((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) with hSdef
  have hgoal_eq : P.c_T * ((M : ℝ) + 1) * ((k : ℝ) + (S : ℝ)) * P.γ_r M *
      (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T = ((k : ℝ) + (S : ℝ)) * G_M := by
    rw [hG_Mdef]; ring
  rw [hgoal_eq]
  have hkS_nn : 0 ≤ (k : ℝ) + (S : ℝ) := by positivity
  by_cases hV₀ : (D.G 0).V.Nonempty
  · have hℓ₀ : ∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e := fun e he =>
      ((hWeak 0 (Nat.zero_le τ)).2.2.2 e he).2.2.1
    have hne := (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts τ).2.1.trans
      (decide_eq_true hV₀)
    have hk_post := (runAfterRestarts_isNonempty oracle E.C_lsst E.L sparsify k M N D restarts τ).2.2.2
    have hcost : T.cost (T.runAfterRestarts k M N D restarts τ) =
        ∑ j ∈ Finset.range k, ((T.runAfterRestarts k M N D restarts τ).trees j).cost := by
      change (if (T.runAfterRestarts k M N D restarts τ).isNonempty = true then
        ∑ j ∈ Finset.range (T.runAfterRestarts k M N D restarts τ).k,
          ((T.runAfterRestarts k M N D restarts τ).trees j).cost else 0) = _
      dsimp only [T]
      simp only [hne, ↓reduceIte, hk_post]
    rw [hcost, Nat.cast_sum]
    have hS_eq : (S : ℝ) = ∑ j ∈ Finset.range k,
        ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ) := by
      rw [Finset.sum_comm, hSdef, Nat.cast_sum]
      refine Finset.sum_congr rfl fun r hr => ?_
      have hr_le : r ≤ τ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      rw [list_sum_count_eq_length (restarts r) k (hrest r hr_le), Nat.cast_sum]
    have hbranch : ∀ j ∈ Finset.range k,
        ((((T.runAfterRestarts k M N D restarts τ).trees j).cost : ℕ) : ℝ) ≤
          (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M := fun j hj =>
      branch_cost_restart_le_noComp E oracle sparsify k M N τ D restarts hk hG₀ hV₀ hℓ₀ hD hM hN
        hThresh hHyps j (Finset.mem_range.mp hj)
    calc ∑ j ∈ Finset.range k, ((((T.runAfterRestarts k M N D restarts τ).trees j).cost : ℕ) : ℝ)
        ≤ ∑ j ∈ Finset.range k, (1 + ∑ r ∈ Finset.range (τ + 1), ((restarts r).count j : ℝ)) * G_M :=
          Finset.sum_le_sum hbranch
      _ = ((k : ℝ) + (S : ℝ)) * G_M := by
          rw [← Finset.sum_mul, Finset.sum_add_distrib, hS_eq]
          simp
  · have hrunE := runAfterRestarts_empty_case oracle E.C_lsst E.L sparsify k M N D restarts hV₀
    have hcost0 : T.cost (T.runAfterRestarts k M N D restarts τ) = 0 :=
      sRT_cost_of_empty (hrunE τ).2.1
    rw [hcost0, Nat.cast_zero]
    exact mul_nonneg hkS_nn hG_M_nn

/-- `SparseCoreRestartTool.IsSpecRestart` for `sparseCoreRestartTool` on one instance, with all
six items, without `hComp_bound` or `hThresh₀`. -/
theorem sparseCoreRestart_spec_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (hk : 0 < k) (hG₀ : (D.G 0).IsValid) (hD : D.IsValid τ)
    (hLen : LengthsStable D τ) (hWeak : WeakHiddenStable D τ Ψ c w)
    (hM : (D.G 0).m ≤ M) (hN : (D.G 0).n ≤ N)
    (hrest : ∀ r ≤ τ, ∀ j ∈ restarts r, j < k)
    (hThresh : (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N)
    (hHyps : SparseCoreCoreHypsAt E oracle sparsify k M D) :
    let T := sparseCoreRestartTool oracle E.C_lsst E.L sparsify
    let P := sparseCoreParams E
    let pre := fun t => (T.runAfterUpdate k M N D restarts t).1
    let U_S := fun t => (T.runAfterUpdate k M N D restarts t).2
    let post := fun t => T.runAfterRestarts k M N D restarts t
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
      (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
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
        WeakHiddenStable (T.coreInstanceFrom k M N D restarts s₀ j) (t - s₀) Ψ'
          (T.coreCFrom k M N D restarts c s₀ j) (T.coreWFrom k M N D restarts w s₀ j)) ∧
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) := by
  intro T P pre U_S post
  have h := sparseCoreRestart_spec_noTotalCost_noComp E oracle sparsify k τ M N D restarts Ψ c w
    hk hG₀ hD hLen hWeak hM hN hrest hThresh hHyps
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2,
    sparseCoreRestart_totalCost_le_noComp E oracle sparsify k τ M N D restarts Ψ c w hk hG₀ hD hWeak
      hM hN hrest hThresh hHyps⟩

/-- `SparseCoreRestartTool.IsSpecRestart` for `sparseCoreRestartTool`, without `hComp_bound` or
`hThresh₀`. -/
theorem sparseCoreRestartTool_isSpecRestart_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      SparseCoreCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreRestartTool oracle E.C_lsst E.L sparsify).IsSpecRestart (sparseCoreParams E) := by
  intro k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D hk hG₀ hD hLen hℓ hM hN hThresh
  exact sparseCoreRestart_spec_noComp E oracle sparsify k τ M N D restarts Ψ c w
    hk hG₀ hD hLen hWeak hM hN hrest hThresh hH

end MinCostFlow.Chain

end
