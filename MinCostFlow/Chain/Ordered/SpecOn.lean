module

public import MinCostFlow.Chain.SparseCoreOrdSpec
public import MinCostFlow.Chain.RestartSpecOn

/-!
# Ordered restart specifications restricted to a predicate

`IsSpecOrdRestartOn T P Pred` and `IsSpecOrdRestartNoHiddenOn T P Pred` are
`SparseCoreRestartTool.IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden`
(`Chain/SparseCoreOrdSpec.lean`), asked only for the inputs `(k, τ, M, N, D)` that satisfy
`Pred`, as `IsSpecRestartOn` does for the unordered specification (`Chain/RestartSpecOn.lean`).
The concrete tool meets them with `Pred := concreteChainToolPred`, and the chain supplies
`concreteChainToolPred` at every level (`chainInv_satisfies_concreteChainToolPred`).

The chain uses the restricted specification one level history at a time. `ToolOKAt T P k M N G ℓ`
says that the tool meets `IsSpecOrdRestart` on every input history with parameters `(k, M, N)`
that starts at the graph `G` with lengths `ℓ`. A level records this fact when it is built
(`LevelHistory.hOK`), and every later use of the specification at that level is on a history with
the same start. `toolOKAt_of_on` gives it from `IsSpecOrdRestartOn` for a predicate that only looks
at the start. The average stretch bound is asked only for edge bounds `M ≤ Mmax`
(`ToolMWUOrdRestartNoHiddenLe`), since the chain calls the tool only with `M ≤ M₀²`.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.Bundle

namespace SparseCoreRestartTool

/-- `IsSpecOrdRestart` for the inputs that satisfy `Pred`. -/
def IsSpecOrdRestartOn (T : SparseCoreRestartTool) (P : SparseCoreParams)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    Pred k τ M N D →
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
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)

/-- `IsSpecOrdRestartNoHidden` for the inputs that satisfy `Pred`. -/
def IsSpecOrdRestartNoHiddenOn (T : SparseCoreRestartTool) (P : SparseCoreParams)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
    0 < k →
    (D.G 0).IsValid →
    D.IsValid τ →
    LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) →
    OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M →
    (D.G 0).n ≤ N →
    (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    Pred k τ M N D →
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
      OrderedUpTo (T.coreInstanceOrdFrom k M N D ord restarts s₀ j) (t - s₀) 2
        (fun δ => T.rot (post (s₀ + δ)) j)) ∧
    ((T.cost (post τ) : ℝ) ≤
      P.c_T * ((M : ℝ) + 1) *
        ((k : ℝ) + (((Finset.range (τ + 1)).sum fun s => (restarts s).length : ℕ) : ℝ)) *
        ((k : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T)


lemma IsSpecOrdRestart.toOn {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (h : T.IsSpecOrdRestart P) (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) :
    T.IsSpecOrdRestartOn P Pred :=
  fun k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh _ =>
    h k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh

lemma IsSpecOrdRestartNoHidden.toOn {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (h : T.IsSpecOrdRestartNoHidden P) (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop) :
    T.IsSpecOrdRestartNoHiddenOn P Pred :=
  fun k τ M N D ord restarts hk hG₀ hD hLen hℓ hOrd hM hN hrest hThresh _ =>
    h k τ M N D ord restarts hk hG₀ hD hLen hℓ hOrd hM hN hrest hThresh

lemma IsSpecOrdRestartOn.toNoHiddenOn {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop}
    (h : T.IsSpecOrdRestartOn P Pred) : T.IsSpecOrdRestartNoHiddenOn P Pred := by
  intro k τ M N D ord restarts hk hG₀ hD hLen hℓ hOrd hM hN hrest hThresh hPred
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓ
  have h' := h k τ M N D ord restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG₀ hD hLen hWeak hOrd
    hM hN hrest hThresh hPred
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2.2.1, h'.2.2.2.2.2.2⟩

/-- The inputs `(k', τ, M', N', D)` with `(k', M', N') = (k, M, N)` whose history starts at the
graph `G` with lengths `ℓ`. -/
def StartsAt (k M N : ℕ) (G : MGraph) (ℓ : ℕ → ℝ) :
    ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop :=
  fun k' _ M' N' D => k' = k ∧ M' = M ∧ N' = N ∧ D.G 0 = G ∧ D.ℓ 0 = ℓ

/-- The tool meets `IsSpecOrdRestart` on every input history with parameters `(k, M, N)` that
starts at the graph `G` with lengths `ℓ`. -/
def ToolOKAt (T : SparseCoreRestartTool) (P : SparseCoreParams) (k M N : ℕ) (G : MGraph)
    (ℓ : ℕ → ℝ) : Prop :=
  T.IsSpecOrdRestartOn P (StartsAt k M N G ℓ)

lemma ToolOKAt.noHidden {T : SparseCoreRestartTool} {P : SparseCoreParams} {k M N : ℕ}
    {G : MGraph} {ℓ : ℕ → ℝ} (h : T.ToolOKAt P k M N G ℓ) :
    T.IsSpecOrdRestartNoHiddenOn P (StartsAt k M N G ℓ) :=
  IsSpecOrdRestartOn.toNoHiddenOn h

/-- `IsSpecOrdRestartOn` for a predicate that holds on every history with the given start gives
`ToolOKAt` at that start. -/
lemma toolOKAt_of_on {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop} (h : T.IsSpecOrdRestartOn P Pred)
    {k M N : ℕ} {G : MGraph} {ℓ : ℕ → ℝ}
    (hPred : ∀ (τ : ℕ) (D : DynamicInstance), D.G 0 = G → D.ℓ 0 = ℓ → Pred k τ M N D) :
    T.ToolOKAt P k M N G ℓ := by
  intro k' τ M' N' D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hStart
  obtain ⟨rfl, rfl, rfl, hG, hℓ⟩ := hStart
  exact h k' τ M' N' D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh
    (hPred τ D hG hℓ)

/-- `ToolMWUOrdRestartNoHidden` for the edge bounds `M ≤ Mmax`. -/
def ToolMWUOrdRestartNoHiddenLe (T : SparseCoreRestartTool) (σ_mwu : ℕ → ℝ) (Mmax : ℕ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
    M ≤ Mmax →
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k,
        (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

lemma ToolMWUOrdRestartNoHidden.toLe {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdRestartNoHidden σ_mwu) (Mmax : ℕ) : T.ToolMWUOrdRestartNoHiddenLe σ_mwu Mmax :=
  fun k τ M N D ord restarts _ => h k τ M N D ord restarts

end SparseCoreRestartTool

end MinCostFlow.Chain
