module

public import MinCostFlow.Chain.SparseCoreToolOrd
public import MinCostFlow.Bundle.Ordered
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Ordered specifications of `SparseCoreTool`

This file defines the ordered versions of the `SparseCoreTool` specifications
(`Chain/SparseCoreTool.lean` and `Chain/SparseCoreNoHidden.lean`) for the tour-bundle repair
(paper Lemma 5.17, page 23):

* `IsSpecOrdUpTo` and `IsSpecOrd`, together with their hidden-stability-free counterparts
  `IsSpecOrdNoHiddenUpTo` and `IsSpecOrdNoHidden`: they assume `OrderedUpTo D τ 2 ord`, export
  `OrderedUpTo (coreInstanceOrdAt ...) τ 2 (fun t => T.rot (st t) j)` for every branch `j < k`,
  and bound the runtime cost by `c_T (M + 1) k (k + 1) γ_r(M) log^{p_T}(M + N + 2)` (where the
  extra factor `k + 1` comes from bundle degree `≤ k` in Theorem 8.2 while `γ_r` stays free of `k`
  and of degrees).
* Ordered side predicates (`ToolMWUOrd*`, `ToolEmbedsSurvivingOrd*`, `ToolNoReinsertOrd*`,
  `ToolNoReinsertStrictOrd*`, `ToolSwitchedRecourseOrd*`) and conversions between them.

The restartable versions (`SparseCoreRestartTool.IsSpecOrdRestart`, `IsSpecOrdRestartNoHidden`,
and `Tool*OrdRestart*`) are in `Chain/SparseCoreOrdSpec.lean`, which publicly re-exports this file.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.Bundle

namespace SparseCoreTool

/-- Ordered specification of **Lemma 5.17** with size upper bounds `(M, N)` (paper page 23): assumes
`OrderedUpTo D τ 2 ord`, exports `OrderedUpTo` on each branch's output graph with `rot`, and bounds
total runtime with the bundle-degree factor `k + 1`. -/
def IsSpecOrdUpTo (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let U_S := fun t => (T.runOrdAt k M N D ord t).2
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
    (∀ j < k, ∃ Ψ' : ℝ, WeakHiddenStable (T.coreInstanceOrdAt k M N D ord j) τ Ψ'
      (T.coreCOrdAt k M N D ord c j) (T.coreWOrdAt k M N D ord w j)) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

/-- Ordered specification of **Lemma 5.17** at the initial graph's own sizes
`((D.G 0).m, (D.G 0).n)`. -/
def IsSpecOrd (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    let st := fun t => (T.runOrd k D ord t).1
    let U_S := fun t => (T.runOrd k D ord t).2
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
    (∀ j < k, ∃ Ψ' : ℝ, WeakHiddenStable (T.coreInstanceOrd k D ord j) τ Ψ'
      (T.coreCOrd k D ord c j) (T.coreWOrd k D ord w j)) ∧
    (∀ j < k, OrderedUpTo (T.coreInstanceOrd k D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T)

/-- `IsSpecOrdUpTo` implies `IsSpecOrd` by taking `M = (D.G 0).m` and `N = (D.G 0).n`. -/
lemma IsSpecOrdUpTo.toIsSpecOrd {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrdUpTo P) : T.IsSpecOrd P :=
  fun k τ D ord Ψ c w hk hG0 hD hLen hWeak hOrd hTh =>
    hT k τ (D.G 0).m (D.G 0).n D ord Ψ c w hk hG0 hD hLen hWeak hOrd le_rfl le_rfl hTh

/-- Hidden-stability-free version of `IsSpecOrdUpTo`: replaces `WeakHiddenStable D` with
positivity of edge lengths and drops `WeakHiddenStable` on `coreInstanceOrdAt`, keeping the
output-order and runtime clauses. -/
def IsSpecOrdNoHiddenUpTo (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    let st := fun t => (T.runOrdAt k M N D ord t).1
    let U_S := fun t => (T.runOrdAt k M N D ord t).2
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
    (∀ j < k, OrderedUpTo (T.coreInstanceOrdAt k M N D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

lemma IsSpecOrdUpTo.toNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrdUpTo P) : T.IsSpecOrdNoHiddenUpTo P := by
  intro k τ M N D ord hk hG0 hD hLen hℓPos hOrd hM hN hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  have h := hT k τ M N D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hOrd hM hN hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Hidden-stability-free version of `IsSpecOrd`. -/
def IsSpecOrdNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    let st := fun t => (T.runOrd k D ord t).1
    let U_S := fun t => (T.runOrd k D ord t).2
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
    (∀ j < k, OrderedUpTo (T.coreInstanceOrd k D ord j) τ 2 (fun t => T.rot (st t) j)) ∧
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * ((k : ℝ) + 1) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T)

lemma IsSpecOrdNoHiddenUpTo.toIsSpecOrdNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrdNoHiddenUpTo P) : T.IsSpecOrdNoHidden P :=
  fun k τ D ord hk hG0 hD hLen hℓPos hOrd hTh =>
    hT k τ (D.G 0).m (D.G 0).n D ord hk hG0 hD hLen hℓPos hOrd le_rfl le_rfl hTh

lemma IsSpecOrd.toNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrd P) : T.IsSpecOrdNoHidden P := by
  intro k τ D ord hk hG0 hD hLen hℓPos hOrd hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  have h := hT k τ D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hOrd hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-- Ordered MWU average-stretch bound with size upper bounds `(M, N)` (Lemma 5.5). -/
def ToolMWUOrdUpTo (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAt k M N D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

/-- Ordered MWU average-stretch bound at `((D.G 0).m, (D.G 0).n)`. -/
def ToolMWUOrd (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrd k D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

/-- Hidden-stability-free version of `ToolMWUOrdUpTo`. -/
def ToolMWUOrdNoHiddenUpTo (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrdAt k M N D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

/-- Hidden-stability-free version of `ToolMWUOrd`. -/
def ToolMWUOrdNoHidden (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runOrd k D ord t).1 j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

lemma ToolMWUOrdUpTo.toToolMWUOrd {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdUpTo σ_mwu) : T.ToolMWUOrd σ_mwu :=
  fun k τ D ord Ψ c w hk hG0 hD hLen hW hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord Ψ c w hk hG0 hD hLen hW hOrd le_rfl le_rfl hTh

lemma ToolMWUOrdUpTo.toNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdUpTo σ_mwu) : T.ToolMWUOrdNoHiddenUpTo σ_mwu := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hM hN hTh

lemma ToolMWUOrdNoHiddenUpTo.toToolMWUOrdNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdNoHiddenUpTo σ_mwu) : T.ToolMWUOrdNoHidden σ_mwu :=
  fun k τ D ord hk hG0 hD hLen hℓ hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord hk hG0 hD hLen hℓ hOrd le_rfl le_rfl hTh

lemma ToolMWUOrd.toNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrd σ_mwu) : T.ToolMWUOrdNoHidden σ_mwu := by
  intro k τ D ord hk hG0 hD hLen hℓ hOrd hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hTh

/-- Ordered surviving-edge self-embedding property with size upper bounds `(M, N)`. -/
def ToolEmbedsSurvivingOrdUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E,
      T.emb (T.runOrdAt k M N D ord t).1 j e = [(e, true)]

/-- Ordered surviving-edge self-embedding property at `((D.G 0).m, (D.G 0).n)`. -/
def ToolEmbedsSurvivingOrd (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrd k D ord t).1 j).E,
      T.emb (T.runOrd k D ord t).1 j e = [(e, true)]

/-- Hidden-stability-free version of `ToolEmbedsSurvivingOrdUpTo`. -/
def ToolEmbedsSurvivingOrdNoHiddenUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E,
      T.emb (T.runOrdAt k M N D ord t).1 j e = [(e, true)]

/-- Hidden-stability-free version of `ToolEmbedsSurvivingOrd`. -/
def ToolEmbedsSurvivingOrdNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrd k D ord t).1 j).E,
      T.emb (T.runOrd k D ord t).1 j e = [(e, true)]

lemma ToolEmbedsSurvivingOrdUpTo.toToolEmbedsSurvivingOrd {T : SparseCoreTool}
    (h : T.ToolEmbedsSurvivingOrdUpTo) : T.ToolEmbedsSurvivingOrd :=
  fun k τ D ord Ψ c w hk hG0 hD hLen hW hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord Ψ c w hk hG0 hD hLen hW hOrd le_rfl le_rfl hTh

lemma ToolEmbedsSurvivingOrdUpTo.toNoHidden {T : SparseCoreTool}
    (h : T.ToolEmbedsSurvivingOrdUpTo) : T.ToolEmbedsSurvivingOrdNoHiddenUpTo := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hM hN hTh

lemma ToolEmbedsSurvivingOrdNoHiddenUpTo.toToolEmbedsSurvivingOrdNoHidden {T : SparseCoreTool}
    (h : T.ToolEmbedsSurvivingOrdNoHiddenUpTo) : T.ToolEmbedsSurvivingOrdNoHidden :=
  fun k τ D ord hk hG0 hD hLen hℓ hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord hk hG0 hD hLen hℓ hOrd le_rfl le_rfl hTh

lemma ToolEmbedsSurvivingOrd.toNoHidden {T : SparseCoreTool}
    (h : T.ToolEmbedsSurvivingOrd) : T.ToolEmbedsSurvivingOrdNoHidden := by
  intro k τ D ord hk hG0 hD hLen hℓ hOrd hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hTh

/-- Ordered surviving-edge non-insertion propagation with size upper bounds `(M, N)`. -/
def ToolNoReinsertOrdUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrdAt k M N D ord (t - 1)).1 j).E,
        e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E →
        (∀ u ∈ (T.runOrdAt k M N D ord t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

/-- Ordered surviving-edge non-insertion propagation at `((D.G 0).m, (D.G 0).n)`. -/
def ToolNoReinsertOrd (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrd k D ord (t - 1)).1 j).E,
        e ∈ (T.S (T.runOrd k D ord t).1 j).E →
        (∀ u ∈ (T.runOrd k D ord t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

/-- Hidden-stability-free version of `ToolNoReinsertOrdUpTo`. -/
def ToolNoReinsertOrdNoHiddenUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrdAt k M N D ord (t - 1)).1 j).E,
        e ∈ (T.S (T.runOrdAt k M N D ord t).1 j).E →
        (∀ u ∈ (T.runOrdAt k M N D ord t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

/-- Hidden-stability-free version of `ToolNoReinsertOrd`. -/
def ToolNoReinsertOrdNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrd k D ord (t - 1)).1 j).E,
        e ∈ (T.S (T.runOrd k D ord t).1 j).E →
        (∀ u ∈ (T.runOrd k D ord t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertOrdUpTo.toToolNoReinsertOrd {T : SparseCoreTool}
    (h : T.ToolNoReinsertOrdUpTo) : T.ToolNoReinsertOrd :=
  fun k τ D ord Ψ c w hk hG0 hD hLen hW hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord Ψ c w hk hG0 hD hLen hW hOrd le_rfl le_rfl hTh

lemma ToolNoReinsertOrdUpTo.toNoHidden {T : SparseCoreTool}
    (h : T.ToolNoReinsertOrdUpTo) : T.ToolNoReinsertOrdNoHiddenUpTo := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hM hN hTh

lemma ToolNoReinsertOrdNoHiddenUpTo.toToolNoReinsertOrdNoHidden {T : SparseCoreTool}
    (h : T.ToolNoReinsertOrdNoHiddenUpTo) : T.ToolNoReinsertOrdNoHidden :=
  fun k τ D ord hk hG0 hD hLen hℓ hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord hk hG0 hD hLen hℓ hOrd le_rfl le_rfl hTh

lemma ToolNoReinsertOrd.toNoHidden {T : SparseCoreTool}
    (h : T.ToolNoReinsertOrd) : T.ToolNoReinsertOrdNoHidden := by
  intro k τ D ord hk hG0 hD hLen hℓ hOrd hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ D ord Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd hTh

/-- Ordered strict `NoBatchReinsert` propagation with size upper bounds `(M, N)`. -/
def ToolNoReinsertStrictOrdUpTo (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.runOrdAt k M N D ord (t - 1)).1 j)
        ((T.runOrdAt k M N D ord t).2 j)

/-- Ordered strict `NoBatchReinsert` propagation at `((D.G 0).m, (D.G 0).n)`. -/
def ToolNoReinsertStrictOrd (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.runOrd k D ord (t - 1)).1 j) ((T.runOrd k D ord t).2 j)

lemma ToolNoReinsertStrictOrdUpTo.toToolNoReinsertStrictOrd {T : SparseCoreTool}
    (h : T.ToolNoReinsertStrictOrdUpTo) : T.ToolNoReinsertStrictOrd :=
  fun k τ D ord Ψ c w hk hG0 hD hLen hW hOrd hTh =>
    h k τ (D.G 0).m (D.G 0).n D ord Ψ c w hk hG0 hD hLen hW hOrd le_rfl le_rfl hTh

/-- Ordered switched-branch recourse bound (`jtree.tex` page 30, line 852). -/
def ToolSwitchedRecourseOrd (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (Ψ : ℝ) (c w : ℕ → ℕ → ℝ)
    (b : ℕ → ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ s, b s < k) →
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)

/-- Hidden-stability-free version of `ToolSwitchedRecourseOrd`. -/
def ToolSwitchedRecourseOrdNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (b : ℕ → ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ s, b s < k) →
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)

lemma ToolSwitchedRecourseOrd.toNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (h : T.ToolSwitchedRecourseOrd P) : T.ToolSwitchedRecourseOrdNoHidden P := by
  intro k τ M N D ord b hk hG0 hD hLen hℓ hOrd hM hN hTh hb
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord Ψ (fun _ _ => 0) (fun _ _ => 1) b hk hG0 hD hLen hW hOrd hM hN hTh hb

/-- Fixed-branch ordered recourse (`j < k`) yields switched-branch recourse with a factor of `k`. -/
lemma isSpecOrdUpTo_switched_recourse_mul_k {T : SparseCoreTool} {P : SparseCoreParams}
    {k τ M N : ℕ} {D : DynamicInstance} {ord : ℕ → ℕ → List End} (b : ℕ → ℕ)
    (hb : ∀ s, b s < k) (hSum : ∀ j < k, ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 j).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)) :
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length : ℕ) : ℝ) ≤
        (k : ℝ) * P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
  intro t ht
  have h1 : (Finset.Icc 1 t).sum (fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length) ≤
      (Finset.range k).sum (fun j =>
        (Finset.Icc 1 t).sum (fun s => ((T.runOrdAt k M N D ord s).2 j).length)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun s _ => ?_
    exact Finset.single_le_sum (f := fun j => ((T.runOrdAt k M N D ord s).2 j).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (hb s))
  have h1r : (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 (b s)).length : ℕ) : ℝ) ≤
      ∑ j ∈ Finset.range k,
        (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 j).length : ℕ) : ℝ) := by
    exact_mod_cast h1
  have h2r : ∑ j ∈ Finset.range k,
        (((Finset.Icc 1 t).sum fun s => ((T.runOrdAt k M N D ord s).2 j).length : ℕ) : ℝ) ≤
      ∑ _j ∈ Finset.range k,
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) :=
    Finset.sum_le_sum fun j hj => hSum j (Finset.mem_range.mp hj) t ht
  have h2r' : ∑ _j ∈ Finset.range k,
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) =
      (k : ℝ) * P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ) := by
    simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  exact le_trans h1r (h2r.trans_eq h2r')

end SparseCoreTool

end MinCostFlow.Chain
