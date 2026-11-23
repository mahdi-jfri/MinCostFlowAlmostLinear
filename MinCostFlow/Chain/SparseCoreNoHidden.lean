module

public import MinCostFlow.Chain.SparseCoreTool

/-!
# Hidden-stability-free specification for `SparseCoreTool`

This file isolates the hidden-stability-free portion `SparseCoreTool.IsSpecNoHidden` of
`SparseCoreTool.IsSpec` (all clauses of `SparseCoreTool.IsSpec` except item 2
`WeakHiddenStable (coreInstance ...)`, and with the `WeakHiddenStable D` hypothesis replaced by
positivity of edge lengths `0 < D.ℓ t e`), together with matching no-hidden versions of
`ToolMWU`, `ToolEmbedsSurviving`, and `ToolNoReinsert` and bridge lemmas showing each follows
from its hidden-stable counterpart via `exists_weakHiddenStable_zero`.

Algorithm 1's maintenance proofs (`Algorithm1Proofs`, `Algorithm1UpdateProofs`, `Lemma5_11`) and
Algorithm 2 (`Theorem 5.1`, pages 25–30) require only `IsSpecNoHidden` unconditionally on all
inputs, reserving item 2 (`WeakHiddenStable`) strictly for the hidden-stable quality analysis
(`Lemma 6.5`).
-/

@[expose] public section

namespace MinCostFlow.Chain

namespace SparseCoreTool

/-- All clauses of `SparseCoreTool.IsSpec` (Lemma 5.17, page 23) except item 2 (`WeakHiddenStable`
for `coreInstance`), with `WeakHiddenStable D` weakened to `∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e`. -/
def IsSpecNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
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
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((m₀ : ℝ) + 1) * (k : ℝ) * P.γ_r m₀ *
        (Real.log ((m₀ : ℝ) + (n₀ : ℝ) + 2)) ^ P.p_T)

lemma IsSpec.toIsSpecNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpec P) : T.IsSpecNoHidden P := by
  intro k τ D hk hG0 hD hLen hℓPos hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  have h := hT k τ D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Hidden-stability-free version of `ToolMWU` (Lemma 5.5 average stretch bound). -/
def ToolMWUNoHidden (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.run k D t).1 j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n

lemma ToolMWU.toNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWU σ_mwu) : T.ToolMWUNoHidden σ_mwu := by
  intro k τ D hk hG0 hD hLen hℓPos hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hMWU k τ D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hTh

/-- Hidden-stability-free version of `ToolEmbedsSurviving`. -/
def ToolEmbedsSurvivingNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.run k D t).1 j).E,
      T.emb (T.run k D t).1 j e = [(e, true)]

lemma ToolEmbedsSurviving.toNoHidden {T : SparseCoreTool}
    (hEmb : T.ToolEmbedsSurviving) : T.ToolEmbedsSurvivingNoHidden := by
  intro k τ D hk hG0 hD hLen hℓPos hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hEmb k τ D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hTh

/-- Hidden-stability-free version of `ToolNoReinsert`. -/
def ToolNoReinsertNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      updateThreshold k (D.G 0).m (D.G 0).n →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.run k D (t - 1)).1 j).E,
        e ∈ (T.S (T.run k D t).1 j).E →
        (∀ u ∈ (T.run k D t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsert.toNoHidden {T : SparseCoreTool}
    (hNoReins : T.ToolNoReinsert) : T.ToolNoReinsertNoHidden := by
  intro k τ D hk hG0 hD hLen hℓPos hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hNoReins k τ D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hTh

/-- Hidden-stability-free version of `SparseCoreTool.IsSpecUpTo` (Lemma 5.17 with upper bounds
`(M, N)`, page 23). -/
def IsSpecUpToNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
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
    ((T.cost (st τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) * (k : ℝ) * P.γ_r M *
        (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

lemma IsSpecUpTo.toNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecUpTo P) : T.IsSpecUpToNoHidden P := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  have h := hT k τ M N D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

lemma IsSpecUpToNoHidden.toIsSpecNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hT : T.IsSpecUpToNoHidden P) : T.IsSpecNoHidden P :=
  fun k τ D hk hG0 hD hLen hℓPos hTh =>
    hT k τ (D.G 0).m (D.G 0).n D hk hG0 hD hLen hℓPos le_rfl le_rfl hTh

/-- Hidden-stability-free version of `ToolMWUUpTo`. -/
def ToolMWUUpToNoHidden (T : SparseCoreTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runAt k M N D t).1 j).wstr e) / (k : ℝ) ≤ σ_mwu (D.G t).n

lemma ToolMWUUpTo.toNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWUUpTo σ_mwu) : T.ToolMWUUpToNoHidden σ_mwu := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hMWU k τ M N D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hTh

lemma ToolMWUUpToNoHidden.toToolMWUNoHidden {T : SparseCoreTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWUUpToNoHidden σ_mwu) : T.ToolMWUNoHidden σ_mwu :=
  fun k τ D hk hG0 hD hLen hℓPos hTh =>
    hMWU k τ (D.G 0).m (D.G 0).n D hk hG0 hD hLen hℓPos le_rfl le_rfl hTh

/-- Hidden-stability-free version of `ToolEmbedsSurvivingUpTo`. -/
def ToolEmbedsSurvivingUpToNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runAt k M N D t).1 j).E,
      T.emb (T.runAt k M N D t).1 j e = [(e, true)]

lemma ToolEmbedsSurvivingUpTo.toNoHidden {T : SparseCoreTool}
    (hEmb : T.ToolEmbedsSurvivingUpTo) : T.ToolEmbedsSurvivingUpToNoHidden := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hEmb k τ M N D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hTh

lemma ToolEmbedsSurvivingUpToNoHidden.toToolEmbedsSurvivingNoHidden {T : SparseCoreTool}
    (hEmb : T.ToolEmbedsSurvivingUpToNoHidden) : T.ToolEmbedsSurvivingNoHidden :=
  fun k τ D hk hG0 hD hLen hℓPos hTh =>
    hEmb k τ (D.G 0).m (D.G 0).n D hk hG0 hD hLen hℓPos le_rfl le_rfl hTh

/-- Hidden-stability-free version of `ToolNoReinsertUpTo`. -/
def ToolNoReinsertUpToNoHidden (T : SparseCoreTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runAt k M N D (t - 1)).1 j).E,
        e ∈ (T.S (T.runAt k M N D t).1 j).E →
        (∀ u ∈ (T.runAt k M N D t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertUpTo.toNoHidden {T : SparseCoreTool}
    (hNoReins : T.ToolNoReinsertUpTo) : T.ToolNoReinsertUpToNoHidden := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hNoReins k τ M N D Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hTh

lemma ToolNoReinsertUpToNoHidden.toToolNoReinsertNoHidden {T : SparseCoreTool}
    (hNoReins : T.ToolNoReinsertUpToNoHidden) : T.ToolNoReinsertNoHidden :=
  fun k τ D hk hG0 hD hLen hℓPos hTh =>
    hNoReins k τ (D.G 0).m (D.G 0).n D hk hG0 hD hLen hℓPos le_rfl le_rfl hTh

/-- Hidden-stability-free version of `ToolSwitchedRecourse`. -/
def ToolSwitchedRecourseNoHidden (T : SparseCoreTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (b : ℕ → ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤ updateThreshold k M N →
    (∀ s, b s < k) →
    ∀ t ≤ τ,
      (((Finset.Icc 1 t).sum fun s => ((T.runAt k M N D s).2 (b s)).length : ℕ) : ℝ) ≤
        P.γ_r M * (((Finset.Icc 1 t).sum fun s => (D.U s).length : ℕ) : ℝ)

lemma ToolSwitchedRecourse.toNoHidden {T : SparseCoreTool} {P : SparseCoreParams}
    (hSw : T.ToolSwitchedRecourse P) : T.ToolSwitchedRecourseNoHidden P := by
  intro k τ M N D b hk hG0 hD hLen hℓPos hM hN hTh hb
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hSw k τ M N D Ψ (fun _ _ => 0) (fun _ _ => 1) b hk hG0 hD hLen hWeak hM hN hTh hb

end SparseCoreTool

namespace SparseCoreRestartTool

/-- Hidden-stability-free version of `SparseCoreRestartTool.IsSpecRestart`: omits `WeakHiddenStable` item 5 while keeping all structural, windowed recourse,
branch-invariance, restart-cost, and cumulative runtime guarantees. -/
def IsSpecRestartNoHidden (T : SparseCoreRestartTool) (P : SparseCoreParams) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
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
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

lemma IsSpecRestart.toNoHidden {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (hT : T.IsSpecRestart P) : T.IsSpecRestartNoHidden P := by
  intro k τ M N D restarts hk hG0 hD hLen hℓPos hM hN hRest hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  have h := hT k τ M N D restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hRest hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩

lemma IsSpecRestartNoHidden.toIsSpecUpToNoHidden {T : SparseCoreRestartTool}
    {P : SparseCoreParams} (hT : T.IsSpecRestartNoHidden P) :
    T.toSparseCoreTool.IsSpecUpToNoHidden P := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh
  have h := hT k τ M N D (fun _ => []) hk hG0 hD hLen hℓPos hM hN (fun _ _ _ h => by cases h) hTh
  have hpre : ∀ t, (T.runAfterUpdate k M N D (fun _ => []) t) = T.toSparseCoreTool.runAt k M N D t :=
    T.runAfterUpdate_empty_eq_runAt k M N D
  have hpost : ∀ t, T.runAfterRestarts k M N D (fun _ => []) t = (T.toSparseCoreTool.runAt k M N D t).1 :=
    T.runAfterRestarts_empty_eq_runAt k M N D
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht j hj; simpa only [hpost t] using h.1 t ht j hj
  · intro t ht1 ht j hj; simpa only [hpost t, hpost (t - 1), hpre t] using h.2.1 t ht1 ht j hj
  · intro t ht j hj
    have h4 := h.2.2.2.1 0 t (Nat.zero_le t) ht j hj (Or.inl rfl) (fun _ _ _ h => by cases h)
    simpa only [Nat.zero_add, hpre, hpost] using h4
  · simpa only [hpost τ, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, add_zero]
      using h.2.2.2.2

/-- Adding `[]` at step `t` leaves the `foldl` unchanged; restarting `j'` leaves `lsfs` unchanged
for all `b < k` and `S, emb` unchanged for all `b < k` with `b ≠ j'`. -/
lemma lsfs_runAfterRestarts_eq {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {k τ M N : ℕ} {D : DynamicInstance} {restarts : ℕ → List ℕ}
    (hBranch : ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (T.runAfterUpdate k M N D restarts r).1
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :
    ∀ t ≤ τ, ∀ b < k,
      T.lsfs (T.runAfterRestarts k M N D restarts t) b = T.lsfs (T.runAfterUpdate k M N D restarts t).1 b := by
  intro t ht b hb
  unfold runAfterRestarts
  suffices h : ∀ (l : List ℕ), l <+: restarts t →
      T.lsfs (l.foldl T.restart (T.runAfterUpdate k M N D restarts t).1) b =
        T.lsfs (T.runAfterUpdate k M N D restarts t).1 b from
    h (restarts t) (List.prefix_refl _)
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton xs x ih =>
    intro hpref
    have hxs : xs <+: restarts t := List.IsPrefix.trans ⟨[x], rfl⟩ hpref
    have hstep := (hBranch t ht xs x hpref).1 b hb
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hstep, ih hxs]

lemma S_emb_runAfterRestarts_eq_of_not_mem {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {k τ M N : ℕ} {D : DynamicInstance} {restarts : ℕ → List ℕ}
    (hBranch : ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (T.runAfterUpdate k M N D restarts r).1
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' → T.S (T.restart st' j') b = T.S st' b ∧ T.emb (T.restart st' j') b = T.emb st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :
    ∀ t ≤ τ, ∀ b < k, b ∉ restarts t →
      T.S (T.runAfterRestarts k M N D restarts t) b = T.S (T.runAfterUpdate k M N D restarts t).1 b ∧
      T.emb (T.runAfterRestarts k M N D restarts t) b = T.emb (T.runAfterUpdate k M N D restarts t).1 b := by
  intro t ht b hb hnot
  unfold runAfterRestarts
  suffices h : ∀ (l : List ℕ), l <+: restarts t → b ∉ l →
      T.S (l.foldl T.restart (T.runAfterUpdate k M N D restarts t).1) b =
          T.S (T.runAfterUpdate k M N D restarts t).1 b ∧
      T.emb (l.foldl T.restart (T.runAfterUpdate k M N D restarts t).1) b =
          T.emb (T.runAfterUpdate k M N D restarts t).1 b from
    h (restarts t) (List.prefix_refl _) hnot
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; exact ⟨rfl, rfl⟩
  | append_singleton xs x ih =>
    intro hpref hnl
    have hxs : xs <+: restarts t := List.IsPrefix.trans ⟨[x], rfl⟩ hpref
    have hne : b ≠ x := fun h => hnl (by simp [h])
    have hnb : b ∉ xs := fun h => hnl (List.mem_append_left [x] h)
    have hstep := (hBranch t ht xs x hpref).2.1 b hb hne
    have hprev := ih hxs hnb
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨hstep.1.trans hprev.1, hstep.2.trans hprev.2⟩

/-- Hidden-stability-free version of `ToolMWURestart`. -/
def ToolMWURestartNoHidden (T : SparseCoreRestartTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k, (T.lsfs (T.runAfterRestarts k M N D restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

lemma ToolMWURestart.toNoHidden {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWURestart σ_mwu) : T.ToolMWURestartNoHidden σ_mwu := by
  intro k τ M N D restarts hk hG0 hD hLen hℓPos hM hN hRest hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hMWU k τ M N D restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hRest hTh

lemma ToolMWURestartNoHidden.toToolMWUUpToNoHidden {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (hMWU : T.ToolMWURestartNoHidden σ_mwu) : T.toSparseCoreTool.ToolMWUUpToNoHidden σ_mwu := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh t ht e he
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using
    hMWU k τ M N D (fun _ => []) hk hG0 hD hLen hℓPos hM hN
      (fun _ _ _ h => by cases h) hTh t ht e he

/-- Hidden-stability-free version of `ToolEmbedsSurvivingRestart`. -/
def ToolEmbedsSurvivingRestartNoHidden (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runAfterRestarts k M N D restarts t) j).E,
      T.emb (T.runAfterRestarts k M N D restarts t) j e = [(e, true)]

lemma ToolEmbedsSurvivingRestart.toNoHidden {T : SparseCoreRestartTool}
    (hEmb : T.ToolEmbedsSurvivingRestart) : T.ToolEmbedsSurvivingRestartNoHidden := by
  intro k τ M N D restarts hk hG0 hD hLen hℓPos hM hN hRest hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hEmb k τ M N D restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hRest hTh

lemma ToolEmbedsSurvivingRestartNoHidden.toToolEmbedsSurvivingUpToNoHidden
    {T : SparseCoreRestartTool} (hEmb : T.ToolEmbedsSurvivingRestartNoHidden) :
    T.toSparseCoreTool.ToolEmbedsSurvivingUpToNoHidden := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh t ht j hj e he
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using
    hEmb k τ M N D (fun _ => []) hk hG0 hD hLen hℓPos hM hN
      (fun _ _ _ h => by cases h) hTh t ht j hj e
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using he)

/-- Hidden-stability-free version of `ToolNoReinsertRestart`. -/
def ToolNoReinsertRestartNoHidden (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runAfterRestarts k M N D restarts (t - 1)) j).E,
        e ∈ (T.S (T.runAfterRestarts k M N D restarts t) j).E →
        (∀ u ∈ (T.runAfterUpdate k M N D restarts t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertRestart.toNoHidden {T : SparseCoreRestartTool}
    (hNoReins : T.ToolNoReinsertRestart) : T.ToolNoReinsertRestartNoHidden := by
  intro k τ M N D restarts hk hG0 hD hLen hℓPos hM hN hRest hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓPos
  exact hNoReins k τ M N D restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hM hN hRest hTh

lemma ToolNoReinsertRestartNoHidden.toToolNoReinsertUpToNoHidden
    {T : SparseCoreRestartTool} (hNoReins : T.ToolNoReinsertRestartNoHidden) :
    T.toSparseCoreTool.ToolNoReinsertUpToNoHidden := by
  intro k τ M N D hk hG0 hD hLen hℓPos hM hN hTh t ht1 ht j hj e hePrev heCur hNoU
  simpa only [T.runAfterRestarts_empty_eq_runAt k M N D (t - 1),
    T.runAfterRestarts_empty_eq_runAt k M N D t, T.runAfterUpdate_empty_eq_runAt k M N D t] using
    hNoReins k τ M N D (fun _ => []) hk hG0 hD hLen hℓPos hM hN
      (fun _ _ _ h => by cases h) hTh t ht1 ht j hj e
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D (t - 1)] using hePrev)
      (by simpa only [T.runAfterRestarts_empty_eq_runAt k M N D t] using heCur)
      (by simpa only [T.runAfterUpdate_empty_eq_runAt k M N D t] using hNoU)

end SparseCoreRestartTool

end MinCostFlow.Chain
