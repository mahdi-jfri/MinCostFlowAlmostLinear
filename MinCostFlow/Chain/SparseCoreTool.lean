module

public import MinCostFlow.Chain.CoreGraph
public import MinCostFlow.Bundle.Cyclic
import MinCostFlow.Chain.WalkFlow
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Per-level dynamic sparsified core graph specification (`SparseCoreTool`, Lemma 5.17)

This file formalizes the interface and specification of the per-level data structure
`𝒜^{(SparseCore)}` from **Lemma 5.17** (page 23) as a tool parameter for Algorithm 1, together
with the static level-`d` LSF/MWU builder `LastLevelTool` (Definition 5.8, page 19–20).

Faithfulness notes:
* `SparseCoreTool.IsSpec` captures strictly what Lemma 5.17 states (together with the guarantees of
  Lemma 5.4 that Lemma 5.17 explicitly incorporates: `LSF.Holds`, decremental `F`, `wstr`
  immutability / `wstr = 1` on inserted edges, and connected-graph root count), plus a corrected
  Item 2 (`WeakHiddenStable`: items 1, 2, 4, and 5 of Definition 4.4 with updated log bound `Ψ'`),
  because Definition 4.4 item 3 (`⟨g, c⟩ / ‖w‖₁ ≤ -α`) does not hold in `𝒮(G, F_j)` (see
  `lemma_5_17_item2_counterexample`).
* Additional properties needed by `Algorithm 1` / `Lemma 5.11` that Lemma 5.17 omits to state
  explicitly are kept separate from `SparseCoreTool.IsSpec` as named predicates:
  `ToolMWU` (Lemma 5.5 average stretch bound), `ToolEmbedsSurviving` (`EmbedsSurviving`), and
  `ToolNoReinsert` (update batches do not delete and re-insert an existing edge ID in one batch).
* The tool carries orders of ends: `initOrd` and `updateOrd`
  take the order at each input vertex, `rot` returns it for each output graph. The defaults
  ignore the orders (runs with orders: `Chain/SparseCoreToolOrd.lean`).
-/

@[expose] public section

namespace MinCostFlow.Chain

section DynamicHelpers

/-- Edge lengths do not change across a batch unless the edge is inserted in that batch. -/
def LengthsStable (D : DynamicInstance) (τ : ℕ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ τ → ∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E →
    (∀ u ∈ D.U t, ¬ u.Inserts e) → D.ℓ t e = D.ℓ (t - 1) e

/-- A batch `U` on `G` does not insert any edge ID that was already in `G.E` (in particular, it
never deletes and re-inserts the same edge ID within one batch). -/
def NoBatchReinsert (G : MGraph) (U : List Update) : Prop :=
  ∀ e ∈ G.E, ∀ u ∈ U, ¬ u.Inserts e

/-- Weakened hidden stability at stage `t` (Definition 4.4 items 1, 2, 4, 5, omitting item 3):
`(c t)` is a circulation, `(c t, w t)` is a valid pair, `w` satisfies factor-`2` stability on
non-inserted edges, and entries of `w, ℓ` are positive with log-magnitude at most `Ψ`.

Lemma 5.17's proof (pages 23–24) establishes items 1, 2, 4, and 5 for `𝒮(G, F_j)` (with a larger
log bound `Ψ'`), whereas item 3 (`⟨g, c⟩ / ‖w‖₁ ≤ -α`) fails for `𝒮(G, F_j)`. -/
def WeakHiddenStableAt (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (t : ℕ) : Prop :=
  (D.G t).IsCirculation (c t) ∧
  IsValidPair (D.G t) (D.ℓ t) (c t) (w t) ∧
  (∀ e ∈ (D.G t).E, ∀ t' ≤ t, D.NotInsertedBetween e t' t → w t e ≤ 2 * w t' e) ∧
  (∀ e ∈ (D.G t).E, 0 < w t e ∧ |Real.log (w t e)| ≤ Ψ ∧ 0 < D.ℓ t e ∧ |Real.log (D.ℓ t e)| ≤ Ψ)

/-- Weakened hidden stability up to stage `T`. -/
def WeakHiddenStable (D : DynamicInstance) (T : ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) : Prop :=
  ∀ t ≤ T, WeakHiddenStableAt D Ψ c w t

lemma weakHiddenStableAt_of_hiddenStableAt {D : DynamicInstance} {α Ψ : ℝ}
    {c w : ℕ → ℕ → ℝ} {t : ℕ} (h : D.HiddenStableAt α Ψ c w t) :
    WeakHiddenStableAt D Ψ c w t :=
  ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2⟩

lemma weakHiddenStable_of_hiddenStable {D : DynamicInstance} {T : ℕ} {α Ψ : ℝ} :
    D.HiddenStable T α Ψ → ∃ c w : ℕ → ℕ → ℝ, WeakHiddenStable D T Ψ c w := by
  rintro ⟨c, w, h⟩
  exact ⟨c, w, fun t ht => weakHiddenStableAt_of_hiddenStableAt (h t ht)⟩

lemma exists_weakHiddenStable_zero {D : DynamicInstance} {τ : ℕ}
    (hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) :
    ∃ Ψ : ℝ, 0 ≤ Ψ ∧ WeakHiddenStable D τ Ψ (fun _ _ => 0) (fun _ _ => 1) := by
  refine ⟨∑ t ∈ Finset.range (τ + 1), ∑ e ∈ (D.G t).E, |Real.log (D.ℓ t e)|, ?_, ?_⟩
  · exact Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun e _ => abs_nonneg _
  · intro t ht
    refine ⟨fun v _ => by simp [MGraph.demand], ⟨fun v _ => by simp [MGraph.demand], fun e _ => by norm_num⟩,
      fun e _ t' _ _ => by norm_num, fun e he => ?_⟩
    have hnonneg : 0 ≤ ∑ t ∈ Finset.range (τ + 1), ∑ e ∈ (D.G t).E, |Real.log (D.ℓ t e)| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨by norm_num, by simpa using hnonneg, hℓ t ht e he, ?_⟩
    have ht_mem : t ∈ Finset.range (τ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le ht)
    have hinner : |Real.log (D.ℓ t e)| ≤ ∑ e' ∈ (D.G t).E, |Real.log (D.ℓ t e')| :=
      Finset.single_le_sum (f := fun e' => |Real.log (D.ℓ t e')|) (fun _ _ => abs_nonneg _) he
    have houter : (∑ e' ∈ (D.G t).E, |Real.log (D.ℓ t e')|) ≤
        ∑ t' ∈ Finset.range (τ + 1), ∑ e' ∈ (D.G t').E, |Real.log (D.ℓ t' e')| :=
      Finset.single_le_sum (f := fun t' => ∑ e' ∈ (D.G t').E, |Real.log (D.ℓ t' e')|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) ht_mem
    exact le_trans hinner houter

end DynamicHelpers

section SparseCoreSpec

/-- Asymptotic parameter functions and constants for `SparseCoreTool` (Lemma 5.17, page 23). -/
structure SparseCoreParams where
  /-- LSF stretch bound `σ(k, n)` (for `O(k log^6 n)` in Lemma 5.4). -/
  σ : ℕ → ℕ → ℝ
  /-- Spanner length bound `γ_ℓ(m)` (`exp(O(log^{8/9} m log log m))`). -/
  γ_ℓ : ℕ → ℝ
  /-- Spanner congestion bound `γ_c(m)` (`exp(O(log^{8/9} m log log m))`). -/
  γ_c : ℕ → ℝ
  /-- Spanner recourse bound `γ_r(m)` (`exp(O(log^{8/9} m log log m))`). -/
  γ_r : ℕ → ℝ
  /-- Root-count constant in Lemma 5.4 item 1. -/
  c_R : ℝ
  /-- Total runtime constant in Lemma 5.17 (`Õ(m k γ_r)`). -/
  c_T : ℝ
  /-- Polylog exponent `p_T` in Lemma 5.17's `Õ(m k γ_r)` bound. -/
  p_T : ℕ

/-- Parameter sanity conditions: positivity (`≥ 1`) and monotonicity in graph sizes. -/
def SparseCoreParams.Valid (P : SparseCoreParams) : Prop :=
  (∀ k n, 1 ≤ k → 1 ≤ P.σ k n) ∧
  (∀ k₁ k₂ n₁ n₂, k₁ ≤ k₂ → n₁ ≤ n₂ → P.σ k₁ n₁ ≤ P.σ k₂ n₂) ∧
  (∀ m, 1 ≤ P.γ_ℓ m) ∧
  (∀ m₁ m₂, m₁ ≤ m₂ → P.γ_ℓ m₁ ≤ P.γ_ℓ m₂) ∧
  (∀ m, 1 ≤ P.γ_c m) ∧
  (∀ m₁ m₂, m₁ ≤ m₂ → P.γ_c m₁ ≤ P.γ_c m₂) ∧
  (∀ m, 1 ≤ P.γ_r m) ∧
  (∀ m₁ m₂, m₁ ≤ m₂ → P.γ_r m₁ ≤ P.γ_r m₂) ∧
  0 ≤ P.c_R ∧
  0 ≤ P.c_T

/-- Abstract interface of the per-level dynamic sparsified core graph algorithm `𝒜^{(SparseCore)}`
(Lemma 5.17, page 23): data and operations only; correctness and complexity are in `IsSpec`. -/
structure SparseCoreTool where
  /-- Internal state of `𝒜^{(SparseCore)}`. -/
  State : Type
  /-- Initialize `𝒜^{(SparseCore)}` on `(k, M, N, G, ℓ, g)` with size upper bounds `(M, N)`. -/
  init : (k M N : ℕ) → MGraph → (ℕ → ℝ) → (ℕ → ℝ) → State
  /-- Apply an update batch `U` with new lengths `ℓ` and gradients `g`, returning the updated
  state and for each `j < k` the update batch `U_{\mathcal{S}, j}` for `𝒮(G, F_j)`. -/
  update : State → List Update → (ℕ → ℝ) → (ℕ → ℝ) → State × (ℕ → List Update)
  /-- The `k` maintained LSFs `(T_j, F_j, wstr_j)` for `j < k`. -/
  lsfs : State → ℕ → LSF
  /-- The `k` maintained sparsified core graphs `𝒮(G, F_j)` for `j < k`. -/
  S : State → ℕ → MGraph
  /-- The `k` maintained embeddings `Π_{𝒞(G, F_j) → 𝒮(G, F_j)}` for `j < k`. -/
  emb : State → ℕ → Embedding
  /-- Cumulative running-time cost of `init` and all `update` calls on this instance. -/
  cost : State → ℕ
  /-- Initialize on `(k, M, N, G, ℓ, g)` with the order `ord v` of the ends at each vertex `v` of
  `G`. The default ignores the order. -/
  initOrd : (k M N : ℕ) → MGraph → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → List Bundle.End) → State :=
    fun k M N G ℓ g _ => init k M N G ℓ g
  /-- Apply an update batch with new lengths and gradients, given the order of the ends at each
  vertex of the input graph after the batch. The default ignores the order. -/
  updateOrd : State → List Update → (ℕ → ℝ) → (ℕ → ℝ) → (ℕ → List Bundle.End) →
      State × (ℕ → List Update) :=
    fun st U ℓ g _ => update st U ℓ g
  /-- The order of the ends at each vertex of the output graph `S st j` of branch `j`: the forest
  tours restricted to the output edges. The default is the
  empty order. -/
  rot : State → ℕ → ℕ → List Bundle.End := fun _ _ _ => []

namespace SparseCoreTool

/-- Sequential execution of `SparseCoreTool` on a `DynamicInstance` at parameter `k` and size
upper bounds `(M, N)`. -/
def runAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance) :
    ℕ → T.State × (ℕ → List Update)
  | 0 => (T.init k M N (D.G 0) (D.ℓ 0) (D.g 0), fun _ => [])
  | t + 1 =>
    let prev := T.runAt k M N D t
    T.update prev.1 (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1))

/-- Sequential execution of `SparseCoreTool` initialized at the initial graph's own sizes
`((D.G 0).m, (D.G 0).n)`. -/
abbrev run (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance) :
    ℕ → T.State × (ℕ → List Update) :=
  T.runAt k (D.G 0).m (D.G 0).n D

/-- The induced `DynamicInstance` on `𝒮(G^{(t)}, F_j^{(t)})` for branch `j` at size bounds `(M, N)`. -/
noncomputable def coreInstanceAt (T : SparseCoreTool) (k M N : ℕ)
    (D : DynamicInstance) (j : ℕ) : DynamicInstance where
  G := fun t => T.S (T.runAt k M N D t).1 j
  U := fun t => (T.runAt k M N D t).2 j
  g := fun t => coreGrad (D.G t) (T.lsfs (T.runAt k M N D t).1 j) (D.g t)
  ℓ := fun t => coreLen (T.lsfs (T.runAt k M N D t).1 j) (D.ℓ t)

/-- The induced `DynamicInstance` on `𝒮(G^{(t)}, F_j^{(t)})` initialized at `((D.G 0).m, (D.G 0).n)`. -/
noncomputable abbrev coreInstance (T : SparseCoreTool) (k : ℕ)
    (D : DynamicInstance) (j : ℕ) : DynamicInstance :=
  T.coreInstanceAt k (D.G 0).m (D.G 0).n D j

/-- Hidden circulation `c^{(t), 𝒮(G^{(t)}, F_j^{(t)})}` on branch `j` at size bounds `(M, N)` (Definition 5.15). -/
noncomputable def coreCAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (c : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  let st := (T.runAt k M N D t).1
  let L := T.lsfs st j
  passSparseCoreC (coreGraph (D.G t) L) (T.emb st j) (passCoreC (c t))

/-- Hidden circulation `c^{(t), 𝒮(G^{(t)}, F_j^{(t)})}` on branch `j` (Definition 5.15). -/
noncomputable abbrev coreC (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (c : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  T.coreCAt k (D.G 0).m (D.G 0).n D c j t

/-- Hidden upper bound `w^{(t), 𝒮(G^{(t)}, F_j^{(t)})}` on branch `j` at size bounds `(M, N)` (Definition 5.15). -/
noncomputable def coreWAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (w : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  let st := (T.runAt k M N D t).1
  let L := T.lsfs st j
  passSparseCoreW (coreGraph (D.G t) L) (T.emb st j) (passCoreW L (w t))

/-- Hidden upper bound `w^{(t), 𝒮(G^{(t)}, F_j^{(t)})}` on branch `j` (Definition 5.15). -/
noncomputable abbrev coreW (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (w : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  T.coreWAt k (D.G 0).m (D.G 0).n D w j t

/-- The update-count threshold `m / (k log²(n + 2))` of Lemma 5.17 (page 23). -/
noncomputable def updateThreshold (k m₀ n₀ : ℕ) : ℝ :=
  (m₀ : ℝ) / ((k : ℝ) * (Real.log ((n₀ : ℝ) + 2)) ^ 2)

/-- Specification of **Lemma 5.17** (page 23): for every `k > 0`, every valid dynamic instance `D`
of length `τ` with `LengthsStable`, `WeakHiddenStable`, and total updates at most
`updateThreshold k (D.G 0).m (D.G 0).n`:
* at all `t ≤ τ` and `j < k`, `(lsfs j)` satisfies `LSF.Holds` (with decremental `F_j`, immutable
  `wstr` on surviving edges, `wstr = 1` on inserted edges, and Lemma 5.4 item 1 root count on
  connected graphs), and `(S j, emb j)` is a `(γ_ℓ, γ_c)`-sparsified core graph;
* for `1 ≤ t ≤ τ`, `U_{\mathcal{S}, j}^{(t)}` is a valid batch producing `S^{(t)}` from `S^{(t-1)}`;
* item 1 (Low Recourse) bounds `∑ |U_{\mathcal{S}, j}|` and `∑ Enc(U_{\mathcal{S}, j})`;
* item 2 (`WeakHiddenStable`) holds for `coreInstance k D j` with `(coreC, coreW)`;
* total running time `T.cost (st τ)` is bounded by `c_T * (m₀ + 1) * k * γ_r(m₀) * log^{p_T}(m₀ + n₀ + 2)`. -/
def IsSpec (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    let st := fun t => (T.run k D t).1
    let U_S := fun t => (T.run k D t).2
    let m₀ := (D.G 0).m
    let n₀ := (D.G 0).n
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ m₀) (P.γ_c m₀) m₀
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((m₀ : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((n₀ : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r m₀ * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r m₀ * ((m₀ : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ,
      WeakHiddenStable (T.coreInstance k D j) τ Ψ' (T.coreC k D c j) (T.coreW k D w j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T)

/-- **Lemma 5.17 with explicit size upper bounds `(M, N)`** (`jtree.tex`, page 23):
identical to `IsSpec`, except `m₀ = (D.G 0).m` and `n₀ = (D.G 0).n` are replaced by quantified
upper bounds `M ≥ (D.G 0).m` and `N ≥ (D.G 0).n` in the update budget `updateThreshold k M N`
and in all size, root-count, encoding, cost, and `γ_ℓ, γ_c, γ_r` parameter bounds. -/
def IsSpecUpTo (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k M N →
    let st := fun t => (T.runAt k M N D t).1
    let U_S := fun t => (T.runAt k M N D t).2
    (∀ t ≤ τ, ∀ j < k,
      (T.lsfs (st t) j).Holds (D.G t) (D.ℓ t) (P.σ k (D.G t).n) ∧
      IsSparsifiedCoreGraphAt (D.G t) (T.lsfs (st t) j) (D.ℓ t) (k : ℝ) (P.γ_ℓ M) (P.γ_c M) M
        (T.S (st t) j) (T.emb (st t) j) ∧
      ((∀ u ∈ (D.G 0).V, ∀ v ∈ (D.G 0).V, (D.G 0).Connected u v) →
        ((T.lsfs (st t) j).F.R.card : ℝ) ≤
          P.c_R * ((M : ℝ) / (k : ℝ) +
            (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) *
              (Real.log ((N : ℝ) + 2)) ^ 2 + 1))) ∧
    (∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      (T.lsfs (st t) j).F.F.E ⊆ (T.lsfs (st (t - 1)) j).F.F.E ∧
      (∀ e ∈ (D.G t).E, e ∈ (D.G (t - 1)).E → (∀ u ∈ D.U t, ¬ u.Inserts e) →
        (T.lsfs (st t) j).wstr e = (T.lsfs (st (t - 1)) j).wstr e) ∧
      (∀ e ∈ (D.G t).E, (∃ u ∈ D.U t, u.Inserts e) → (T.lsfs (st t) j).wstr e = 1) ∧
      (T.S (st (t - 1)) j).BatchIsValid (U_S t j) ∧
      T.S (st t) j = (T.S (st (t - 1)) j).applyBatch (U_S t j)) ∧
    (∀ t ≤ τ, ∀ j < k,
      (((Finset.Icc 1 t).sum fun s => (U_S s j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) ∧
      (((Finset.Icc 1 t).sum fun s => (T.S (st (s - 1)) j).batchEnc (U_S s j) : ℕ) : ℝ) ≤
        P.γ_r M * ((M : ℝ) / (k : ℝ) +
          (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ))) ∧
    (∀ j < k, ∃ Ψ' : ℝ,
      WeakHiddenStable (T.coreInstanceAt k M N D j) τ Ψ' (T.coreCAt k M N D c j) (T.coreWAt k M N D w j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

/-- `IsSpecUpTo` implies `IsSpec` by taking `M = (D.G 0).m` and `N = (D.G 0).n`. -/
lemma IsSpecUpTo.toIsSpec {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecUpTo P) : T.IsSpec P :=
  fun k τ D Ψ c w hk hG0 hD hLen hWeak hThresh =>
    hT k τ (D.G 0).m (D.G 0).n D Ψ c w hk hG0 hD hLen hWeak le_rfl le_rfl hThresh

/-- Extra property needed by Definition 5.8 (`TreeChain.Holds`) that Lemma 5.17 omits to state:
at all stages `t ≤ τ`, the `k` LSFs satisfy the MWU average-stretch bound `σ_mwu` (Lemma 5.5). -/
def ToolMWU (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.run k D t).1 j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n

/-- Extra property needed by Lemma 7.15 / Lemma A.2 that Definition 5.7 and Lemma 5.17 omit:
surviving edges in `𝒮(G, F_j)` embed as themselves (`emb e = [(e, true)]`). -/
def ToolEmbedsSurviving (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.run k D t).1 j).E,
      T.emb (T.run k D t).1 j e = [(e, true)]

/-- Extra property needed to propagate insertion absence along surviving edges through
levels `i ≥ 1`: if an edge `e` survives in `T.S _ j` across step `t` without being inserted in
`U_{\mathcal{S}, j}^{(t)}`, then it was not inserted in `D.U t` either.
Under `D_total` re-insertion in Lemma 5.17, any surviving edge deleted and re-inserted by `D.U t`
is explicitly re-inserted into `S` by `U_{\mathcal{S}, j}^{(t)}`. -/
def ToolNoReinsert (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.run k D (t - 1)).1 j).E,
        e ∈ (T.S (T.run k D t).1 j).E →
        (∀ u ∈ (T.run k D t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

/-- Legacy strict `NoBatchReinsert` propagation property (without `D_total` re-insertion). -/
def ToolNoReinsertStrict (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.run k D (t - 1)).1 j) ((T.run k D t).2 j)

/-- `ToolMWU` with explicit size upper bounds `(M, N)` and budget `updateThreshold k M N`. -/
def ToolMWUUpTo (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runAt k M N D t).1 j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n

lemma ToolMWUUpTo.toToolMWU {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWUUpTo σ_mwu) : T.ToolMWU σ_mwu :=
  fun k τ D Ψ c w hk hG0 hD hLen hWeak hThresh =>
    hMWU k τ (D.G 0).m (D.G 0).n D Ψ c w hk hG0 hD hLen hWeak le_rfl le_rfl hThresh

/-- `ToolEmbedsSurviving` with explicit size upper bounds `(M, N)`. -/
def ToolEmbedsSurvivingUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runAt k M N D t).1 j).E,
      T.emb (T.runAt k M N D t).1 j e = [(e, true)]

lemma ToolEmbedsSurvivingUpTo.toToolEmbedsSurviving {T : SparseCoreTool}
    (hEmb : T.ToolEmbedsSurvivingUpTo) : T.ToolEmbedsSurviving :=
  fun k τ D Ψ c w hk hG0 hD hLen hWeak hThresh =>
    hEmb k τ (D.G 0).m (D.G 0).n D Ψ c w hk hG0 hD hLen hWeak le_rfl le_rfl hThresh

/-- `ToolNoReinsert` with explicit size upper bounds `(M, N)`. -/
def ToolNoReinsertUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runAt k M N D (t - 1)).1 j).E,
        e ∈ (T.S (T.runAt k M N D t).1 j).E →
        (∀ u ∈ (T.runAt k M N D t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertUpTo.toToolNoReinsert {T : SparseCoreTool}
    (hNoReins : T.ToolNoReinsertUpTo) : T.ToolNoReinsert :=
  fun k τ D Ψ c w hk hG0 hD hLen hWeak hThresh =>
    hNoReins k τ (D.G 0).m (D.G 0).n D Ψ c w hk hG0 hD hLen hWeak le_rfl le_rfl hThresh

/-- `ToolNoReinsertStrict` with explicit size upper bounds `(M, N)`. -/
def ToolNoReinsertStrictUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.runAt k M N D (t - 1)).1 j) ((T.runAt k M N D t).2 j)

lemma ToolNoReinsertStrictUpTo.toToolNoReinsertStrict {T : SparseCoreTool}
    (hNoReins : T.ToolNoReinsertStrictUpTo) : T.ToolNoReinsertStrict :=
  fun k τ D Ψ c w hk hG0 hD hLen hWeak hThresh =>
    hNoReins k τ (D.G 0).m (D.G 0).n D Ψ c w hk hG0 hD hLen hWeak le_rfl le_rfl hThresh

/-- Switched-branch recourse bound (`jtree.tex` page 30, line 852): along any active branch
schedule `b : ℕ → ℕ` (`b s < k`), cumulative forwarded updates `∑_{s=1}^t |U_{S, b s}^{(s)}|`
are at most `P.γ_r M * ∑_{s=1}^t |D.U s|`. Lemma 5.17 (`IsSpecUpTo`) states only the fixed-`j`
special case `b _ = j`. -/
def ToolSwitchedRecourse (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ s, b s < k) →
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 (b s)).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)

/-- Existing `IsSpec` item 1 (`j < k`) yields switched-branch recourse with a factor of `k`. -/
lemma isSpecUpTo_switched_recourse_mul_k {T : SparseCoreTool} {P : SparseCoreParams}
    {k τ M N : ℕ} {D : DynamicInstance} (b : ℕ → ℕ)
    (hb : ∀ s, b s < k) (hSum : ∀ j < k, ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) :
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 (b s)).length : ℕ) : ℝ) ≤
        (k : ℝ) * P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
  intro t ht
  have h1 : (Finset.Icc 1 t).sum (fun s => ((T.runAt k M N D s).2 (b s)).length) ≤
      (Finset.range k).sum (fun j => (Finset.Icc 1 t).sum (fun s => ((T.runAt k M N D s).2 j).length)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun s _ => ?_
    exact Finset.single_le_sum (f := fun j => ((T.runAt k M N D s).2 j).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (hb s))
  have h1r : (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 (b s)).length : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.range k,
        (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 j).length : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2r : ∑ j ∈ Finset.range k,
        (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 j).length : ℕ) : ℝ) ≤
      ∑ _j ∈ Finset.range k,
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) :=
    Finset.sum_le_sum fun j hj => hSum j (Finset.mem_range.mp hj) t ht
  have h2r' : ∑ _j ∈ Finset.range k,
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) =
      (k : ℝ) * P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  exact le_trans h1r (h2r.trans_eq h2r')

end SparseCoreTool

/-- Extension of `SparseCoreTool` adding `restart : State → ℕ → State`, which restarts only
branch `j`'s dynamic spanner (`Theorem 8.2`) onto the current core graph `C(G, F_j)` inside
`Shift(i)`. This restart is our repair of the rebuild count of Theorem 5.1 (see the README,
"Where the proof departs from the paper"). -/
structure SparseCoreRestartTool extends SparseCoreTool where
  /-- Restart the dynamic spanner on branch `j` onto the current core graph `C(G, F_j)`. -/
  restart : State → ℕ → State

namespace SparseCoreRestartTool

/-- State and emitted spanner update batches right after step `t` (`init` at `t = 0`, `update`
at `t + 1`), before applying `restarts t`, initialized at size upper bounds `(M, N)`. -/
def runAfterUpdate (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) : ℕ → T.State × (ℕ → List Update)
  | 0 => (T.init k M N (D.G 0) (D.ℓ 0) (D.g 0), fun _ => [])
  | t + 1 =>
    let stPrev := (restarts t).foldl T.restart (T.runAfterUpdate k M N D restarts t).1
    T.update stPrev (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1))

/-- State after applying all branch restarts in `restarts t` following step `t`. -/
def runAfterRestarts (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (t : ℕ) : T.State :=
  (restarts t).foldl T.restart (T.runAfterUpdate k M N D restarts t).1

lemma runAfterUpdate_succ (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (t : ℕ) :
    T.runAfterUpdate k M N D restarts (t + 1) =
      T.update (T.runAfterRestarts k M N D restarts t) (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1)) := rfl

lemma runAfterUpdate_empty_eq_runAt (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance) :
    ∀ t, T.runAfterUpdate k M N D (fun _ => []) t = T.toSparseCoreTool.runAt k M N D t
  | 0 => rfl
  | t + 1 => by
    simp only [runAfterUpdate, List.foldl_nil, SparseCoreTool.runAt,
      runAfterUpdate_empty_eq_runAt T k M N D t]

lemma runAfterRestarts_empty_eq_runAt (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (t : ℕ) :
    T.runAfterRestarts k M N D (fun _ => []) t = (T.toSparseCoreTool.runAt k M N D t).1 := by
  simp only [runAfterRestarts, List.foldl_nil, runAfterUpdate_empty_eq_runAt]

lemma runAfterUpdate_congr_lt (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {restarts₁ restarts₂ : ℕ → List ℕ} (t : ℕ)
    (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s)
    (hrest : ∀ s < t, restarts₁ s = restarts₂ s) :
    T.runAfterUpdate k M N D₁ restarts₁ t = T.runAfterUpdate k M N D₂ restarts₂ t := by
  induction t with
  | zero => simp [runAfterUpdate, hG0, hℓ0, hg0]
  | succ m ih =>
    have ih' := ih (fun s hs1 hsm => hstep s hs1 (Nat.le_succ_of_le hsm))
      (fun s hsm => hrest s (Nat.lt_succ_of_lt hsm))
    have hm := hstep (m + 1) (Nat.succ_pos m) (le_refl _)
    have hr := hrest m (Nat.lt_succ_self m)
    simp only [runAfterUpdate, ih', hr, hm.1, hm.2.1, hm.2.2]

lemma runAfterRestarts_congr_le (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {restarts₁ restarts₂ : ℕ → List ℕ} (t : ℕ)
    (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s)
    (hrest : ∀ s ≤ t, restarts₁ s = restarts₂ s) :
    T.runAfterRestarts k M N D₁ restarts₁ t = T.runAfterRestarts k M N D₂ restarts₂ t := by
  unfold runAfterRestarts
  rw [T.runAfterUpdate_congr_lt k M N t hG0 hℓ0 hg0 hstep (fun s hs => hrest s (Nat.le_of_lt hs)),
    hrest t (le_refl t)]

/-- Suffix `DynamicInstance` on branch `j` starting at stage `s₀` (right after `restarts s₀`)
under a run with restarts initialized at size bounds `(M, N)`. -/
noncomputable def coreInstanceFrom (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (restarts : ℕ → List ℕ) (s₀ j : ℕ) : DynamicInstance where
  G := fun δ => T.S (T.runAfterRestarts k M N D restarts (s₀ + δ)) j
  U := fun δ => (T.runAfterUpdate k M N D restarts (s₀ + δ)).2 j
  g := fun δ => coreGrad (D.G (s₀ + δ)) (T.lsfs (T.runAfterRestarts k M N D restarts (s₀ + δ)) j)
    (D.g (s₀ + δ))
  ℓ := fun δ => coreLen (T.lsfs (T.runAfterRestarts k M N D restarts (s₀ + δ)) j) (D.ℓ (s₀ + δ))

/-- Hidden circulation `c` lifted to `coreInstanceFrom` for branch `j` from stage `s₀`. -/
noncomputable def coreCFrom (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (c : ℕ → ℕ → ℝ) (s₀ j δ : ℕ) : ℕ → ℝ :=
  let st := T.runAfterRestarts k M N D restarts (s₀ + δ)
  let L := T.lsfs st j
  passSparseCoreC (coreGraph (D.G (s₀ + δ)) L) (T.emb st j) (passCoreC (c (s₀ + δ)))

/-- Hidden width `w` lifted to `coreInstanceFrom` for branch `j` from stage `s₀`. -/
noncomputable def coreWFrom (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (restarts : ℕ → List ℕ) (w : ℕ → ℕ → ℝ) (s₀ j δ : ℕ) : ℕ → ℝ :=
  let st := T.runAfterRestarts k M N D restarts (s₀ + δ)
  let L := T.lsfs st j
  passSparseCoreW (coreGraph (D.G (s₀ + δ)) L) (T.emb st j) (passCoreW L (w (s₀ + δ)))

/-- Run-with-restarts specification of Lemma 5.17 (`IsSpecUpTo`) plus the five guarantees of
restarting a single branch's Theorem 8.2 dynamic spanner:
1. Sparsified core graph (`LSF.Holds`, `IsSparsifiedCoreGraph`, connected root count) at every `t`
   (in particular right after a restart);
2. Decremental `F`, `wstr` immutability/reset, and `applyBatch` step from `post (t - 1)` to `pre t`;
3. Each restart in `restarts r` leaves all `lsfs` and all other branches `b ≠ j'` unchanged and
   pays at most a single Theorem 8.2 restart initialization cost;
4. Windowed recourse and encoding (with Theorem 8.2's `M / k` initialization term) from any branch
   `j`'s last restart `s₀` up to `t`;
5. `WeakHiddenStable` on branch `j`'s `coreInstanceFrom` from `s₀` through `t` (`∀ r ∈ (s₀, t], j ∉ restarts r`),
   plus cumulative runtime cost across `init`, updates, and restarts. -/
def IsSpecRestart (T : SparseCoreRestartTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
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
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

/-- `IsSpecRestart` implies `SparseCoreTool.IsSpecUpTo` on the underlying `SparseCoreTool`
by taking empty restart schedules `restarts _ = []`. -/
lemma IsSpecRestart.toIsSpecUpTo {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (hT : T.IsSpecRestart P) : T.toSparseCoreTool.IsSpecUpTo P := by
  intro k τ M N D Ψ c w hk hG0 hD hLen hWeak hM hN hThresh
  have hR := hT k τ M N D (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hM hN
    (fun _ _ _ h => by cases h) hThresh
  dsimp only at hR
  have hpre : ∀ t, (T.runAfterUpdate k M N D (fun _ => []) t) = T.toSparseCoreTool.runAt k M N D t :=
    T.runAfterUpdate_empty_eq_runAt k M N D
  have hpost : ∀ t, T.runAfterRestarts k M N D (fun _ => []) t = (T.toSparseCoreTool.runAt k M N D t).1 :=
    T.runAfterRestarts_empty_eq_runAt k M N D
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht j hj
    simpa only [hpost t] using hR.1 t ht j hj
  · intro t ht1 ht j hj
    simpa only [hpost t, hpost (t - 1), hpre t] using hR.2.1 t ht1 ht j hj
  · intro t ht j hj
    have h4 := hR.2.2.2.1 0 t (Nat.zero_le t) ht j hj (Or.inl rfl) (fun _ _ _ h => by cases h)
    simpa only [Nat.zero_add, hpre, hpost] using h4
  · intro j hj
    have h5 := hR.2.2.2.2.1 0 τ (Nat.zero_le τ) (le_refl τ) j hj (Or.inl rfl)
      (fun _ _ _ h => by cases h)
    have hI : T.coreInstanceFrom k M N D (fun _ => []) 0 j = T.toSparseCoreTool.coreInstanceAt k M N D j := by
      simp only [coreInstanceFrom, SparseCoreTool.coreInstanceAt, Nat.zero_add, hpre, hpost]
    have hC : T.coreCFrom k M N D (fun _ => []) c 0 j = T.toSparseCoreTool.coreCAt k M N D c j := by
      funext δ e
      simp only [coreCFrom, SparseCoreTool.coreCAt, Nat.zero_add, hpost]
    have hW : T.coreWFrom k M N D (fun _ => []) w 0 j = T.toSparseCoreTool.coreWAt k M N D w j := by
      funext δ e
      simp only [coreWFrom, SparseCoreTool.coreWAt, Nat.zero_add, hpost]
    rw [Nat.sub_zero, hI, hC, hW] at h5
    exact h5
  · simpa only [hpost τ, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, add_zero]
      using hR.2.2.2.2.2

/-- MWU average-stretch bound along a run with restarts (`ToolMWUUpTo` generalization). -/
def ToolMWURestart (T : SparseCoreRestartTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runAfterRestarts k M N D restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

lemma ToolMWURestart.toToolMWUUpTo {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWURestart σ_mwu) : T.toSparseCoreTool.ToolMWUUpTo σ_mwu := by
  intro k τ M N D Ψ c w hk hG0 hD hLen hWeak hM hN hThresh t ht e he
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using
    hMWU k τ M N D (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hM hN
      (fun _ _ _ h => by cases h) hThresh t ht e he

/-- Surviving-edge self-embedding property along a run with restarts (`ToolEmbedsSurvivingUpTo` generalization). -/
def ToolEmbedsSurvivingRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runAfterRestarts k M N D restarts t) j).E,
      T.emb (T.runAfterRestarts k M N D restarts t) j e = [(e, true)]

lemma ToolEmbedsSurvivingRestart.toToolEmbedsSurvivingUpTo {T : SparseCoreRestartTool}
    (hEmb : T.ToolEmbedsSurvivingRestart) : T.toSparseCoreTool.ToolEmbedsSurvivingUpTo := by
  intro k τ M N D Ψ c w hk hG0 hD hLen hWeak hM hN hThresh t ht j hj e he
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using
    hEmb k τ M N D (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hM hN
      (fun _ _ _ h => by cases h) hThresh t ht j hj e
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using he)

/-- Surviving-edge non-insertion propagation along a run with restarts
(`ToolNoReinsertUpTo` generalization). -/
def ToolNoReinsertRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runAfterRestarts k M N D restarts (t - 1)) j).E,
        e ∈ (T.S (T.runAfterRestarts k M N D restarts t) j).E →
        (∀ u ∈ (T.runAfterUpdate k M N D restarts t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertRestart.toToolNoReinsertUpTo {T : SparseCoreRestartTool}
    (hNoReins : T.ToolNoReinsertRestart) : T.toSparseCoreTool.ToolNoReinsertUpTo := by
  intro k τ M N D Ψ c w hk hG0 hD hLen hWeak hM hN hThresh t ht1 ht j hj e hePrev heCur hNoU
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D (t - 1),
    T.runAfterRestarts_empty_eq_runAt k M N D t, T.runAfterUpdate_empty_eq_runAt k M N D t] using
    hNoReins k τ M N D (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hM hN
      (fun _ _ _ h => by cases h) hThresh t ht1 ht j hj e
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D (t - 1)] using hePrev)
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using heCur)
      (by simpa only [T.runAfterUpdate_empty_eq_runAt k M N D t] using hNoU)

/-- Strict no-reinsertion propagation along a run with restarts. -/
def ToolNoReinsertStrictRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.runAfterRestarts k M N D restarts (t - 1)) j)
        ((T.runAfterUpdate k M N D restarts t).2 j)

lemma ToolNoReinsertStrictRestart.toToolNoReinsertStrictUpTo {T : SparseCoreRestartTool}
    (hNoReins : T.ToolNoReinsertStrictRestart) : T.toSparseCoreTool.ToolNoReinsertStrictUpTo := by
  intro k τ M N D Ψ c w hk hG0 hD hLen hWeak hM hN hThresh hNR t ht1 ht j hj
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D (t - 1), T.runAfterUpdate_empty_eq_runAt k M N D t] using
    hNoReins k τ M N D (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hM hN
      (fun _ _ _ h => by cases h) hThresh hNR t ht1 ht j hj

end SparseCoreRestartTool

end SparseCoreSpec

section LastLevelSpec

/-- Parameters for the static level-`d` LSF/MWU builder (Definition 5.8, pages 19–20). -/
structure LastLevelParams where
  /-- Worst-case stretch bound `σ_last(n)` for `LSF.Holds` at level `d`. -/
  σ_last : ℕ → ℝ
  /-- MWU average-stretch bound `σ_mwu_last(n)` at level `d`. -/
  σ_mwu : ℕ → ℝ
  /-- Runtime constant `c_last` for `Õ(|E(G_d)|^2)`. -/
  c_last : ℝ
  /-- Polylog exponent `p_last` for `Õ(|E(G_d)|^2)`. -/
  p_last : ℕ

/-- Parameter sanity conditions for `LastLevelParams`. -/
def LastLevelParams.Valid (P : LastLevelParams) : Prop :=
  (∀ n, 1 ≤ P.σ_last n) ∧
  (∀ n₁ n₂, n₁ ≤ n₂ → P.σ_last n₁ ≤ P.σ_last n₂) ∧
  (∀ n, 1 ≤ P.σ_mwu n) ∧
  (∀ n₁ n₂, n₁ ≤ n₂ → P.σ_mwu n₁ ≤ P.σ_mwu n₂) ∧
  0 ≤ P.c_last

/-- Static level-`d` MWU LSF builder `(lastK, lastLSFs)` on `G_d` (Definition 5.8, lines 219–220,
rebuilt when `G_d` changes as noted on page 26). -/
structure LastLevelTool where
  /-- Build `(lastK, lastLSFs)` for graph `G_d` with lengths `ℓ_d`. -/
  build : MGraph → (ℕ → ℝ) → ℕ × (ℕ → LSF)
  /-- Running-time cost on `G_d`. -/
  cost : MGraph → ℕ

/-- Specification of `LastLevelTool`: for every valid `G_d` with positive edge lengths, `build`
returns `lastK > 0` and `lastLSFs` satisfying `LSF.Holds`, the MWU bound `σ_mwu`, and
component-spanning `LastLevelSpans` for every `j < lastK`, in time `Õ((G_d.m + 1)^2)`. -/
def LastLevelTool.IsSpec (L : LastLevelTool) (P : LastLevelParams) : Prop :=
  ∀ (G_d : MGraph) (ℓ_d : ℕ → ℝ),
    G_d.IsValid →
    (∀ e ∈ G_d.E, 0 < ℓ_d e) →
    let res := L.build G_d ℓ_d
    0 < res.1 ∧
    (∀ j < res.1, (res.2 j).Holds G_d ℓ_d (P.σ_last G_d.n)) ∧
    (∀ e ∈ G_d.E,
      (∑ j ∈ Finset.range res.1, (res.2 j).wstr e) / (res.1 : ℝ) ≤ P.σ_mwu G_d.n) ∧
    (∀ j < res.1, ∀ u ∈ G_d.V, ∀ v ∈ G_d.V,
      G_d.Connected u v → (res.2 j).F.F.Connected u v) ∧
    ((L.cost G_d : ℝ) ≤
      P.c_last * ((G_d.m : ℝ) + 1) ^ 2 *
        (Real.log ((G_d.m : ℝ) + (G_d.n : ℝ) + 2)) ^ P.p_last)

end LastLevelSpec

end MinCostFlow.Chain
