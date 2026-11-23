module

public import MinCostFlow.Chain.SparseCoreRestartFull
public import MinCostFlow.Chain.LevelInvariants
public import MinCostFlow.Chain.ConcreteDefs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Restricted `IsSpecRestartOn` Specification and Field Bridge (`MinCostFlow/Chain/RestartSpecOn`)

After Item A moves the edge-count clause of `IsSpecRestart` to `IsSparsifiedCoreGraphAt ... M`
(Lemma 5.17 / Definition 5.15, pages 19 and 23) and Item D passes `(M, N)` directly to
`SparseCoreTool.init` (so `initTreeCore` computes `splitB` and `sparsify M` from `(M, N)` instead
of `(G₀.m, G₀.n)`), the concrete `sparseCoreRestartTool` meets `IsSpecRestart` on every instance
satisfying:
1. `k = P.k`, `M ≤ M₀ ^ 2`, `N ≤ N₀` (so `SparsifySpec M (params (M₀ ^ 2)) sparsify` holds by
   monotonicity from `SparsifySpec (M₀ ^ 2)`),
2. the initial-length range bound discharging `hB_bound` at `concreteBCap` and
   `concreteBucketCapacity true` via `initCompLSF_bucket_bound`, and
3. the explicit root-degree cap hypothesis `hDeg_bound` (kept explicit here rather than hidden
   inside the instance predicate).

No local `hThresh₀` hypothesis is needed anywhere. This file defines
`SparseCoreRestartTool.IsSpecRestartOn` and `SparseCoreRestartTool.IsSpecRestartNoHiddenOn`,
defines the `hThresh₀`-free chain-instance predicate `concreteChainToolPred`, discharges `hLSST`,
`hComp_bound`, `hSp`, and `hB_bound` from `sparseCoreRestartTool_isSpecRestart_noComp` and
`initCompLSF_bucket_bound`, proves that every level `i < P.d` under `ChainInv` and level-0 length
bounds satisfies the entire `concreteChainToolPred`, and proves the field bridge theorems matching
`DyadicWithVConcretePrograms.restartSpec` (`Final/ForestConcretePrograms.lean`) and
`ConcreteDataStructurePrograms.restartSpec` (`Final/ConcretePrograms.lean`) with `IsSpecRestart`
replaced by `IsSpecRestartOn _ (concreteChainToolPred ...)`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner

section RestrictedSpec

/-- Restartable `SparseCoreTool` specification (Lemma 5.17, page 23) restricted to instances
`(k, τ, M, N, D)` satisfying `Pred k τ M N D`. -/
def SparseCoreRestartTool.IsSpecRestartOn (T : SparseCoreRestartTool) (P : SparseCoreParams)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    Pred k τ M N D →
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
    (∀ r ≤ τ, ∀ p j', p ++ [j'] <+: restarts r →
      let st' := List.foldl T.restart (pre r) p
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
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

/-- No-hidden variant of `IsSpecRestartOn`, dropping `WeakHiddenStable` (item 5). -/
def SparseCoreRestartTool.IsSpecRestartNoHiddenOn (T : SparseCoreRestartTool) (P : SparseCoreParams)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    Pred k τ M N D →
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
    (∀ r ≤ τ, ∀ p j', p ++ [j'] <+: restarts r →
      let st' := List.foldl T.restart (pre r) p
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
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

lemma SparseCoreRestartTool.IsSpecRestart.toOn {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (h : T.IsSpecRestart P) (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) :
    T.IsSpecRestartOn P Pred :=
  fun k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh _ =>
    h k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh

lemma SparseCoreRestartTool.IsSpecRestartOn.toNoHiddenOn {T : SparseCoreRestartTool}
    {P : SparseCoreParams} {Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop}
    (h : T.IsSpecRestartOn P Pred) : T.IsSpecRestartNoHiddenOn P Pred := by
  intro k τ M N D restarts hk hG₀ hD hLen hℓ hM hN hrest hThresh hPred
  obtain ⟨Ψ, hWeak⟩ := exists_weakHiddenStable_zero hℓ
  have hFull := h k τ M N D restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG₀ hD hLen hWeak.2 hM hN hrest hThresh hPred
  exact ⟨hFull.1, hFull.2.1, hFull.2.2.1, hFull.2.2.2.1, hFull.2.2.2.2.2⟩

/-- `IsSpecRestartOn` for `sparseCoreRestartTool` without `hComp_bound` or `hThresh₀`, proved
directly from `sparseCoreRestart_spec_noComp`. -/
theorem sparseCoreRestartTool_isSpecRestartOn_noComp (E : SparseCoreEnv)
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop)
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      Pred k τ M N D →
      SparseCoreCoreHypsAt E oracle sparsify k M D) :
    (sparseCoreRestartTool oracle E.C_lsst E.L sparsify).IsSpecRestartOn
      (sparseCoreParams E) Pred := by
  intro k τ M N D restarts Ψ c w hk hG₀ hD hLen hWeak hM hN hrest hThresh hPred
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D hk hG₀ hD hLen hℓ hM hN hThresh hPred
  exact sparseCoreRestart_spec_noComp E oracle sparsify k τ M N D restarts Ψ c w
    hk hG₀ hD hLen hWeak hM hN hrest hThresh hH

end RestrictedSpec

section ChainPredicate

/-- Chain-instance predicate restricting `IsSpecRestart` to instances that `sparseCoreRestartTool`
handles without `hComp_bound` or `hThresh₀`:
1. `k = (concreteChainParams M₀ hM₀1).k`, `M ≤ M₀ ^ 2`, `N ≤ N₀` (every chain level `i < P.d`
   uses `k = P.k`, `M = levelM TP P i ≤ M₀ ^ 2`, and `N = N₀`),
2. initial edge lengths lie in `[exp (-max 0 Ψ), exp (max 0 Ψ + (P.d - 1 : ℕ) * log σ_cap)]`
   (satisfied at every level `i < P.d` under `ChainInv` and level-0 length bounds
   `exp (-max 0 Ψ) ≤ st.ℓ e ≤ exp (max 0 Ψ)`, automatically discharging `hB_bound` at both
   `concreteBCap` and `concreteBucketCapacity true`).

Root degree cap `hDeg_bound` is kept as an explicit hypothesis of the bridge theorems below. -/
def concreteChainToolPred (C_lsst : ℝ) (M₀ N₀ : ℕ) (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    (k _τ M N : ℕ) (D : DynamicInstance) : Prop :=
  let P := concreteChainParams M₀ hM₀1
  let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  k = P.k ∧
  M ≤ M₀ ^ 2 ∧
  N ≤ N₀ ∧
  (∀ e ∈ (D.G 0).E,
    Real.exp (-max 0 Ψ) ≤ D.ℓ 0 e ∧
    D.ℓ 0 e ≤ Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap))

/-- `concreteChainToolPred` discharges `hB_bound` at `concreteBCap C_lsst Ψ M₀ N₀ hM₀1` directly
via `initCompLSF_bucket_bound`. -/
lemma concreteChainToolPred_hB_bound
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    (M₀ N₀ : ℕ) (hM₀1 : 1 ≤ M₀) (Ψ : ℝ)
    {k τ M N : ℕ} {D : DynamicInstance}
    (hG₀ : (D.G 0).IsValid) (hN : (D.G 0).n ≤ N)
    (hPred : concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D) :
    ∀ j < k,
      let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
      ∀ C ∈ components (D.G 0),
        ((initTildeState (cs₀.compSt C)).C.E.image
          fun e => bucketOf (coreLen cs₀.lsf (D.ℓ 0) e)).card ≤
          concreteBCap C_lsst Ψ M₀ N₀ hM₀1 := by
  rcases hPred with ⟨hk_eq, _, hN_le, hℓ_bd⟩
  let P := concreteChainParams M₀ hM₀1
  let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
  have hσ_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hΨ_nn : 0 ≤ max 0 Ψ := le_max_left _ _
  have hB_nn : 0 ≤ max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap := by positivity
  have hG₀n_le : (D.G 0).n ≤ N₀ := le_trans hN hN_le
  have hσ_mwu : mwuK0 C_lsst * (k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤ σ_cap := by
    rw [hk_eq]
    have hn_r : ((D.G 0).n : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hG₀n_le
    have hlog_le : Real.log (((D.G 0).n : ℝ) + 2) ≤ Real.log ((N₀ : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hlog_nn : 0 ≤ Real.log (((D.G 0).n : ℝ) + 2) := by
      linarith [half_lt_log_add_two (D.G 0).n]
    have hK_nn : 0 ≤ mwuK0 C_lsst := (mwuK0_pos C_lsst).le
    have h1 : mwuK0 C_lsst * (P.k : ℝ) * (Real.log (((D.G 0).n : ℝ) + 2)) ^ 6 ≤
        mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6 := by gcongr
    exact le_trans h1 (le_trans (le_max_right _ _) (le_max_right _ _))
  intro j hj cs₀ C hC
  have hk1 : 1 ≤ k := hk_eq ▸ P.hk
  have hbd := initCompLSF_bucket_bound oracle hLSST hk1 hG₀ hΨ_nn hB_nn hσ_ge2 hσ_mwu hℓ_bd j hj C hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd_cast : ((P.d - 1 : ℕ) : ℝ) + 1 = (P.d : ℝ) := by
    have hd1 : 1 ≤ P.d := P.hd
    rw [Nat.cast_sub hd1, Nat.cast_one]
    ring
  have hnum_eq :
      (max 0 Ψ + (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) + Real.log σ_cap) / Real.log 2 =
      (2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap) / Real.log 2 := by
    congr 1
    calc
      max 0 Ψ + (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) + Real.log σ_cap
          = 2 * max 0 Ψ + (((P.d - 1 : ℕ) : ℝ) + 1) * Real.log σ_cap := by ring
      _ = 2 * max 0 Ψ + (P.d : ℝ) * Real.log σ_cap := by rw [hd_cast]
  unfold concreteBCap
  simpa only [P, σ_cap, hnum_eq] using hbd

/-- Under `ChainInv` and level-0 length bounds `exp (-max 0 Ψ) ≤ st.ℓ e ≤ exp (max 0 Ψ)`,
every level `i < P.d` satisfies the non-`hThresh₀` clauses of `concreteChainToolPred` (`k = P.k`,
`levelM ≤ M₀ ^ 2`, `N₀ ≤ N₀`, and the initial-length range bound discharging `hB_bound`). -/
theorem chainInv_satisfies_concreteChainToolPred_noThresh
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams}
    {C_lsst : ℝ} {M₀ N₀ : ℕ} {hM₀1 : 1 ≤ M₀} {Ψ : ℝ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ M₀)
    (hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (concreteChainParams M₀ hM₀1).k)
    {st : ChainState T (concreteChainParams M₀ hM₀1)}
    (hInv : ChainInv T L TP LP (concreteChainParams M₀ hM₀1) N₀ st)
    (hℓ0 : ∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) :
    let P := concreteChainParams M₀ hM₀1
    let σ_cap := max (2 : ℝ) (max 1 (mwuK0 C_lsst * (P.k : ℝ) * (Real.log ((N₀ : ℝ) + 2)) ^ 6))
    ∀ i < P.d,
      P.k = P.k ∧
      levelM TP P i ≤ M₀ ^ 2 ∧
      N₀ ≤ N₀ ∧
      (∀ e ∈ (st.G i).E,
        Real.exp (-max 0 Ψ) ≤ st.toTreeChain.chainLen st.ℓ i e ∧
        st.toTreeChain.chainLen st.ℓ i e ≤
          Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap)) := by
  intro P σ_cap i hi
  have hM₀_eq : P.M₀ = M₀ := rfl
  have hγM₀' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.M₀ := by simpa only [hM₀_eq] using hγM₀
  have hγk' : TP.γ_ℓ (P.M₀ ^ 2) ≤ P.k := by simpa only [hM₀_eq] using hγk
  refine ⟨rfl, by simpa only [hM₀_eq] using levelM_le_sq hTP hγM₀' hγk' i, le_rfl, ?_⟩
  have hlen := chainInv_length_bounds hTP hT hγM₀' hγk' hInv hℓ0 i (Nat.le_of_lt hi)
  have hσ_eq' : max (2 : ℝ) (TP.σ P.k N₀) = σ_cap := by simp only [σ_cap, hσ_eq]
  have hσ_ge2 : (2 : ℝ) ≤ σ_cap := le_max_left _ _
  have hσ_pos : 0 < σ_cap := by linarith
  have hlogσ_nn : 0 ≤ Real.log σ_cap := Real.log_nonneg (by linarith)
  have hi_le_nat : i ≤ P.d - 1 := Nat.le_sub_one_of_lt hi
  have hi_le : (i : ℝ) ≤ ((P.d - 1 : ℕ) : ℝ) := by exact_mod_cast hi_le_nat
  intro e he
  have hle := hlen e he
  rw [hσ_eq'] at hle
  refine ⟨hle.1, ?_⟩
  calc
    st.toTreeChain.chainLen st.ℓ i e ≤ Real.exp (max 0 Ψ) * σ_cap ^ i := hle.2
    _ = Real.exp (max 0 Ψ) * Real.exp ((i : ℝ) * Real.log σ_cap) := by
      conv_lhs => rw [← Real.exp_log hσ_pos, ← Real.exp_nat_mul]
    _ = Real.exp (max 0 Ψ + (i : ℝ) * Real.log σ_cap) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (max 0 Ψ + ((P.d - 1 : ℕ) : ℝ) * Real.log σ_cap) :=
      Real.exp_le_exp.mpr (add_le_add le_rfl (mul_le_mul_of_nonneg_right hi_le hlogσ_nn))

/-- Under `ChainInv` and level-0 length bounds `exp (-max 0 Ψ) ≤ st.ℓ e ≤ exp (max 0 Ψ)`,
every level `i < P.d` satisfies the **entire** `concreteChainToolPred` (with no `hThresh₀`
remaining) for any dynamic instance `D` initialized at `(st.G i, st.toTreeChain.chainLen st.ℓ i)`. -/
theorem chainInv_satisfies_concreteChainToolPred
    {T : SparseCoreRestartTool} {L : LastLevelTool}
    {TP : SparseCoreParams} {LP : LastLevelParams}
    {C_lsst : ℝ} {M₀ N₀ : ℕ} {hM₀1 : 1 ≤ M₀} {Ψ : ℝ}
    (hTP : TP.Valid) (hT : T.IsSpecRestartNoHidden TP)
    (hσ_eq : ∀ k n, TP.σ k n = max 1 (mwuK0 C_lsst * (k : ℝ) * (Real.log ((n : ℝ) + 2)) ^ 6))
    (hγM₀ : TP.γ_ℓ (M₀ ^ 2) ≤ M₀)
    (hγk : TP.γ_ℓ (M₀ ^ 2) ≤ (concreteChainParams M₀ hM₀1).k)
    {st : ChainState T (concreteChainParams M₀ hM₀1)}
    (hInv : ChainInv T L TP LP (concreteChainParams M₀ hM₀1) N₀ st)
    (hℓ0 : ∀ e ∈ (st.G 0).E, Real.exp (-max 0 Ψ) ≤ st.ℓ e ∧ st.ℓ e ≤ Real.exp (max 0 Ψ)) :
    let P := concreteChainParams M₀ hM₀1
    ∀ i < P.d, ∀ (τ : ℕ) (D : DynamicInstance),
      D.G 0 = st.G i → D.ℓ 0 = st.toTreeChain.chainLen st.ℓ i →
      concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ P.k τ (levelM TP P i) N₀ D := by
  intro P i hi τ D hG0 hℓi
  have h := chainInv_satisfies_concreteChainToolPred_noThresh hTP hT hσ_eq hγM₀ hγk hInv hℓ0 i hi
  refine ⟨h.1, h.2.1, h.2.2.1, fun e he => ?_⟩
  rw [hG0] at he
  rw [hℓi]
  exact h.2.2.2 e he

end ChainPredicate

section FieldBridge

/-- Generic field bridge for `concreteAlg2CfgWithLast` with any bucket cap `cap ≥ concreteBCap`
(covering both `concreteBucketCapacity true` in `Final/ForestConcretePrograms.lean:306` and
`concreteBCap` in `Final/ConcretePrograms.lean:79`). Discharges `hLSST`, `hComp_bound`, `hSp`,
and `hB_bound`, keeping only `hDeg_bound` explicit. -/
theorem concreteRestartSpecOn_withLast_of_cap
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (cap : ∀ (M₀ : ℕ), ℕ → ℝ → 1 ≤ M₀ → ℕ)
    (hCap : ∀ (M₀ N₀ : ℕ) (Ψ : ℝ) (hM₀1 : 1 ≤ M₀),
      concreteBCap C_lsst Ψ M₀ N₀ hM₀1 ≤ cap M₀ N₀ Ψ hM₀1)
    (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀)
    (hDeg_bound :
      ∀ (k τ M N : ℕ) (D : DynamicInstance),
        0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
        (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
        (D.G 0).m ≤ M → (D.G 0).n ≤ N →
        (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
          SparseCoreTool.updateThreshold k M N →
        concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D →
        (D.G 0).maxDeg ≤ D_cap ∧
        ∀ j < k,
          let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
          (components (D.G 0)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤ D_cap) :
    let B_cap := cap M₀ N₀ Ψ hM₀1
    let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool lastConstant sparsify
      params hp_s hp_t M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
    cfg.T.IsSpecRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro B_cap cfg
  let E := concreteEnv C_lsst params hp_s hp_t M₀ B_cap D_cap
  change (sparseCoreRestartTool oracle E.C_lsst E.L (fun _ => sparsify)).IsSpecRestartOn
    (sparseCoreParams E) (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ)
  refine sparseCoreRestartTool_isSpecRestartOn_noComp E oracle (fun _ => sparsify)
    (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) ?_
  intro k τ M N D hk hG₀ hD hLen hℓ hM hN hThresh hPred
  have hM_sq : M ≤ M₀ ^ 2 := hPred.2.1
  have hB := concreteChainToolPred_hB_bound oracle hLSST M₀ N₀ hM₀1 Ψ hG₀ hN hPred
  have hDeg := hDeg_bound k τ M N D hk hG₀ hD hLen hℓ hM hN hThresh hPred
  exact
    { hLSST := hLSST
      hSp := sparsifySpec_mono_mMax hM_sq (hSp (M₀ ^ 2))
      hB_bound := fun j hj C hC =>
        le_trans (hB j hj C hC) (le_trans (hCap M₀ N₀ Ψ hM₀1) (le_max_right 1 B_cap))
      hDeg_bound := hDeg }

/-- Exact specialization for `DyadicWithVConcretePrograms.restartSpec`
(`Final/ForestConcretePrograms.lean:295–309`), using `B_cap := concreteBucketCapacity true` and
`D_cap := degCap M₀`, with `IsSpecRestart` replaced by `IsSpecRestartOn _ (concreteChainToolPred ...)`
and only `hDeg_bound` kept explicit. -/
theorem concreteRestartSpecOn_forest
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (lastTool : LastLevelTool) (lastConstant : ℝ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (degCap : ℕ → ℕ)
    (M_thresh degConstant : ℝ)
    (hDeg_bound :
      ∀ (M₀ N₀ : ℕ) (α Ψ _ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
        (degCap M₀ : ℝ) ≤ Real.exp (degConstant * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        ∀ (k τ M N : ℕ) (D : DynamicInstance),
          0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
          (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
          (D.G 0).m ≤ M → (D.G 0).n ≤ N →
          (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
            SparseCoreTool.updateThreshold k M N →
          concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D →
          (D.G 0).maxDeg ≤ degCap M₀ ∧
          ∀ j < k,
            let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
            (components (D.G 0)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤
              degCap M₀) :
    ∀ (M₀ N₀ : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
      M_thresh ≤ M₀ →
      1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
      (degCap M₀ : ℝ) ≤ Real.exp (degConstant * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      0 < α →
      let B_cap := concreteBucketCapacity true C_lsst Ψ M₀ N₀ hM₀1
      let cfg := concreteAlg2CfgWithLast oracle C_lsst lastTool lastConstant sparsify
        params hp_s hp_t M₀ N₀ B_cap (degCap M₀) hM₀1 α Ψ ε
      cfg.T.IsSpecRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hD_cap hΨ hα
  exact concreteRestartSpecOn_withLast_of_cap oracle C_lsst hLSST lastTool lastConstant
    sparsify params hp_s hp_t hSp
    (fun m n ψ hm => concreteBucketCapacity true C_lsst ψ m n hm)
    (fun m n ψ hm => concreteBCap_le_bucketCap_ceil C_lsst ψ m n hm)
    M₀ N₀ (degCap M₀) α Ψ ε hM₀1
    (hDeg_bound M₀ N₀ α Ψ ε hM₀1 hM₀ hN₀ hD_cap hΨ hα)

/-- Exact specialization for `ConcreteDataStructurePrograms.restartSpec`
(`Final/ConcretePrograms.lean:69–82`), using `B_cap := concreteBCap` and `concreteAlg2Cfg`, with
`IsSpecRestart` replaced by `IsSpecRestartOn _ (concreteChainToolPred ...)` and only `hDeg_bound`
kept explicit. -/
theorem concreteRestartSpecOn_programs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams)
    (hp_s : ∀ m, (params m).p_s ≤ 1) (hp_t : ∀ m, (params m).p_t ≤ 1)
    (hSp : ∀ mMax, SparsifySpec mMax (params mMax) sparsify)
    (M_thresh degConstant : ℝ)
    (hDeg_bound :
      ∀ (M₀ N₀ D_cap : ℕ) (α Ψ _ε : ℝ) (hM₀1 : 1 ≤ M₀),
        M_thresh ≤ M₀ →
        1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
        (D_cap : ℝ) ≤ Real.exp (degConstant * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
          Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
        0 < α →
        ∀ (k τ M N : ℕ) (D : DynamicInstance),
          0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
          (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
          (D.G 0).m ≤ M → (D.G 0).n ≤ N →
          (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
            SparseCoreTool.updateThreshold k M N →
          concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ k τ M N D →
          (D.G 0).maxDeg ≤ D_cap ∧
          ∀ j < k,
            let cs₀ := initCompLSF oracle C_lsst (D.G 0) (D.ℓ 0) k j
            (components (D.G 0)).sup (fun C => (initTildeState (cs₀.compSt C)).C.maxDeg) ≤ D_cap) :
    ∀ (M₀ N₀ D_cap : ℕ) (α Ψ ε : ℝ) (hM₀1 : 1 ≤ M₀),
      M_thresh ≤ M₀ →
      1 + Real.log ((N₀ : ℝ) + 2) ≤ 4 * Real.log ((M₀ : ℝ) + 2) →
      (D_cap : ℝ) ≤ Real.exp (degConstant * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      alg2PsiGame Ψ M₀ ≤ Real.exp (1 * Real.log ((M₀ : ℝ) + 2) ^ (23 / 24 : ℝ) *
        Real.log (Real.log ((M₀ : ℝ) + 2) + 2)) →
      0 < α →
      let B_cap := concreteBCap C_lsst Ψ M₀ N₀ hM₀1
      let cfg := concreteAlg2Cfg oracle C_lsst sparsify params hp_s hp_t
        M₀ N₀ B_cap D_cap hM₀1 α Ψ ε
      cfg.T.IsSpecRestartOn cfg.TP (concreteChainToolPred C_lsst M₀ N₀ hM₀1 Ψ) := by
  intro M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hD_cap hΨ hα
  exact concreteRestartSpecOn_withLast_of_cap oracle C_lsst hLSST
    (lastLevelTool oracle C_lsst) C_lsst sparsify params hp_s hp_t hSp
    (fun m n ψ hm => concreteBCap C_lsst ψ m n hm)
    (fun _ _ _ _ => le_rfl)
    M₀ N₀ D_cap α Ψ ε hM₀1
    (hDeg_bound M₀ N₀ D_cap α Ψ ε hM₀1 hM₀ hN₀ hD_cap hΨ hα)

end FieldBridge

end MinCostFlow.Chain
