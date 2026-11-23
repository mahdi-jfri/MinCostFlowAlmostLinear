module

public import MinCostFlow.Chain.SparseCoreOrdToolSpec

/-!
# Ordered specifications of `SparseCoreTool` and `SparseCoreRestartTool`

This file publicly re-exports `Chain/SparseCoreOrdToolSpec.lean` (`SparseCoreTool.IsSpecOrdUpTo`,
`IsSpecOrd`, `IsSpecOrdNoHiddenUpTo`, `IsSpecOrdNoHidden`, and their `Tool*Ord*` side predicates)
and defines the ordered run-with-restarts specifications for `SparseCoreRestartTool`
(paper Lemma 5.17, page 23):

* `SparseCoreRestartTool.IsSpecOrdRestart` and `IsSpecOrdRestartNoHidden`: assume
  `OrderedUpTo D τ 2 ord`, preserve `lsfs` on all branches and `S`, `emb`, `rot` on non-restarted
  branches during each restart, charge each single restart as before
  (`c_T (M + 1) γ_r(M) log^{p_T}`), export `OrderedUpTo` on each branch from its last restart `s₀`
  through `t`, and bound cumulative runtime with `(k + R) (k + 1)`.
* Restart branch-invariance lemmas (`lsfs_runOrdAfterRestarts_eq`,
  `S_emb_rot_runOrdAfterRestarts_eq_of_not_mem`), ordered restart side predicates
  (`ToolMWUOrdRestart*`, `ToolEmbedsSurvivingOrdRestart*`, `ToolNoReinsertOrdRestart*`,
  `ToolNoReinsertStrictOrdRestart`), and conversions to the non-restart and no-hidden forms.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.Bundle

namespace SparseCoreRestartTool

/-- Ordered run-with-restarts specification of **Lemma 5.17** (paper page 23):
1. Sparsified core graph (`LSF.Holds`, `IsSparsifiedCoreGraphAt`, connected root count) at every `t`;
2. Decremental `F`, `wstr` immutability/reset, and `applyBatch` step from `post (t - 1)` to `pre t`;
3. Each restart in `restarts r` leaves all `lsfs` and all other branches' `S`, `emb`, and `rot`
   unchanged, and pays at most a single restart initialization cost `c_T (M + 1) γ_r(M) log^{p_T}`;
4. Windowed recourse and encoding from any branch `j`'s last restart `s₀` up to `t`;
5. `WeakHiddenStable` on branch `j`'s `coreInstanceOrdFrom` from `s₀` through `t`;
6. `OrderedUpTo` on branch `j`'s `coreInstanceOrdFrom` with `rot` from `s₀` through `t`;
7. Cumulative runtime cost bounded with `(k + R) (k + 1)`. -/
def IsSpecOrdRestart (T : SparseCoreRestartTool) (P : SparseCoreParams) : Prop :=
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

/-- `IsSpecOrdRestart` implies `SparseCoreTool.IsSpecOrdUpTo` on the underlying `SparseCoreTool`
by taking empty restart schedules `restarts _ = []`. -/
lemma IsSpecOrdRestart.toIsSpecOrdUpTo {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrdRestart P) : T.toSparseCoreTool.IsSpecOrdUpTo P := by
  intro k τ M N D ord Ψ c w hk hG0 hD hLen hWeak hOrd hM hN hTh
  have hR := hT k τ M N D ord (fun _ => []) Ψ c w hk hG0 hD hLen hWeak hOrd hM hN
    (fun _ _ _ h => by cases h) hTh
  dsimp only at hR
  have hpre : ∀ t, T.runOrdAfterUpdate k M N D ord (fun _ => []) t =
      T.toSparseCoreTool.runOrdAt k M N D ord t :=
    T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord
  have hpost : ∀ t, T.runOrdAfterRestarts k M N D ord (fun _ => []) t =
      (T.toSparseCoreTool.runOrdAt k M N D ord t).1 :=
    T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
    simpa only [Nat.sub_zero, coreInstanceOrdFrom_empty_zero, coreCOrdFrom_empty_zero,
      coreWOrdFrom_empty_zero] using h5
  · intro j hj
    have h6 := hR.2.2.2.2.2.1 0 τ (Nat.zero_le τ) (le_refl τ) j hj (Or.inl rfl)
      (fun _ _ _ h => by cases h)
    simpa only [Nat.sub_zero, Nat.zero_add, coreInstanceOrdFrom_empty_zero, hpost] using h6
  · simpa only [hpost τ, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, add_zero]
      using hR.2.2.2.2.2.2

/-- Hidden-stability-free version of `IsSpecOrdRestart`: omits `WeakHiddenStable` item 5 while
keeping all structural, branch-invariance, windowed recourse, output-order, restart-cost, and
cumulative runtime guarantees. -/
def IsSpecOrdRestartNoHidden (T : SparseCoreRestartTool) (P : SparseCoreParams) : Prop :=
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

lemma IsSpecOrdRestart.toNoHidden {T : SparseCoreRestartTool} {P : SparseCoreParams}
    (hT : T.IsSpecOrdRestart P) : T.IsSpecOrdRestartNoHidden P := by
  intro k τ M N D ord restarts hk hG0 hD hLen hℓ hOrd hM hN hRest hTh
  obtain ⟨Ψ, _, hWeak⟩ := exists_weakHiddenStable_zero hℓ
  have h := hT k τ M N D ord restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hWeak hOrd
    hM hN hRest hTh
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

lemma IsSpecOrdRestartNoHidden.toIsSpecOrdNoHiddenUpTo {T : SparseCoreRestartTool}
    {P : SparseCoreParams} (hT : T.IsSpecOrdRestartNoHidden P) :
    T.toSparseCoreTool.IsSpecOrdNoHiddenUpTo P := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh
  have h := hT k τ M N D ord (fun _ => []) hk hG0 hD hLen hℓ hOrd hM hN
    (fun _ _ _ h => by cases h) hTh
  have hpre : ∀ t, T.runOrdAfterUpdate k M N D ord (fun _ => []) t =
      T.toSparseCoreTool.runOrdAt k M N D ord t :=
    T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord
  have hpost : ∀ t, T.runOrdAfterRestarts k M N D ord (fun _ => []) t =
      (T.toSparseCoreTool.runOrdAt k M N D ord t).1 :=
    T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht j hj; simpa only [hpost t] using h.1 t ht j hj
  · intro t ht1 ht j hj; simpa only [hpost t, hpost (t - 1), hpre t] using h.2.1 t ht1 ht j hj
  · intro t ht j hj
    have h4 := h.2.2.2.1 0 t (Nat.zero_le t) ht j hj (Or.inl rfl) (fun _ _ _ h => by cases h)
    simpa only [Nat.zero_add, hpre, hpost] using h4
  · intro j hj
    have h6 := h.2.2.2.2.1 0 τ (Nat.zero_le τ) (le_refl τ) j hj (Or.inl rfl)
      (fun _ _ _ h => by cases h)
    simpa only [Nat.sub_zero, Nat.zero_add, coreInstanceOrdFrom_empty_zero, hpost] using h6
  · simpa only [hpost τ, List.length_nil, Finset.sum_const_zero, Nat.cast_zero, add_zero]
      using h.2.2.2.2.2

/-- Restarting any branch leaves `lsfs` unchanged for all branches `b < k`. -/
lemma lsfs_runOrdAfterRestarts_eq {T : SparseCoreRestartTool} {P : SparseCoreParams}
    {k τ M N : ℕ} {D : DynamicInstance} {ord : ℕ → ℕ → List End} {restarts : ℕ → List ℕ}
    (hBranch : ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts r).1
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :
    ∀ t ≤ τ, ∀ b < k,
      T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) b =
        T.lsfs (T.runOrdAfterUpdate k M N D ord restarts t).1 b := by
  intro t ht b hb
  unfold runOrdAfterRestarts
  suffices h : ∀ (l : List ℕ), l <+: restarts t →
      T.lsfs (l.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1) b =
        T.lsfs (T.runOrdAfterUpdate k M N D ord restarts t).1 b from
    h (restarts t) (List.prefix_refl _)
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton xs x ih =>
    intro hpref
    have hxs : xs <+: restarts t := List.IsPrefix.trans ⟨[x], rfl⟩ hpref
    have hstep := (hBranch t ht xs x hpref).1 b hb
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, hstep, ih hxs]

/-- For a branch `b ∉ restarts t`, restarting leaves `S`, `emb`, and `rot` unchanged. -/
lemma S_emb_rot_runOrdAfterRestarts_eq_of_not_mem {T : SparseCoreRestartTool}
    {P : SparseCoreParams} {k τ M N : ℕ} {D : DynamicInstance} {ord : ℕ → ℕ → List End}
    {restarts : ℕ → List ℕ}
    (hBranch : ∀ r ≤ τ, ∀ (p : List ℕ) (j' : ℕ), p ++ [j'] <+: restarts r →
      let st' := p.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts r).1
      (∀ b < k, T.lsfs (T.restart st' j') b = T.lsfs st' b) ∧
      (∀ b < k, b ≠ j' →
        T.S (T.restart st' j') b = T.S st' b ∧
        T.emb (T.restart st' j') b = T.emb st' b ∧
        T.rot (T.restart st' j') b = T.rot st' b) ∧
      T.cost st' ≤ T.cost (T.restart st' j') ∧
      (T.cost (T.restart st' j') : ℝ) ≤ (T.cost st' : ℝ) +
        P.c_T * ((M : ℝ) + 1) * P.γ_r M * (Real.log ((M : ℝ) + (N : ℝ) + 2)) ^ P.p_T) :
    ∀ t ≤ τ, ∀ b < k, b ∉ restarts t →
      T.S (T.runOrdAfterRestarts k M N D ord restarts t) b =
          T.S (T.runOrdAfterUpdate k M N D ord restarts t).1 b ∧
      T.emb (T.runOrdAfterRestarts k M N D ord restarts t) b =
          T.emb (T.runOrdAfterUpdate k M N D ord restarts t).1 b ∧
      T.rot (T.runOrdAfterRestarts k M N D ord restarts t) b =
          T.rot (T.runOrdAfterUpdate k M N D ord restarts t).1 b := by
  intro t ht b hb hnot
  unfold runOrdAfterRestarts
  suffices h : ∀ (l : List ℕ), l <+: restarts t → b ∉ l →
      T.S (l.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1) b =
          T.S (T.runOrdAfterUpdate k M N D ord restarts t).1 b ∧
      T.emb (l.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1) b =
          T.emb (T.runOrdAfterUpdate k M N D ord restarts t).1 b ∧
      T.rot (l.foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1) b =
          T.rot (T.runOrdAfterUpdate k M N D ord restarts t).1 b from
    h (restarts t) (List.prefix_refl _) hnot
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _ _; exact ⟨rfl, rfl, rfl⟩
  | append_singleton xs x ih =>
    intro hpref hnl
    have hxs : xs <+: restarts t := List.IsPrefix.trans ⟨[x], rfl⟩ hpref
    have hne : b ≠ x := fun h => hnl (by simp [h])
    have hnb : b ∉ xs := fun h => hnl (List.mem_append_left [x] h)
    have hstep := (hBranch t ht xs x hpref).2.1 b hb hne
    have hprev := ih hxs hnb
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact ⟨hstep.1.trans hprev.1, hstep.2.1.trans hprev.2.1, hstep.2.2.trans hprev.2.2⟩

/-- Ordered MWU average-stretch bound along a run with restarts. -/
def ToolMWUOrdRestart (T : SparseCoreRestartTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k,
        (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

/-- Hidden-stability-free version of `ToolMWUOrdRestart`. -/
def ToolMWUOrdRestartNoHidden (T : SparseCoreRestartTool) (σ_mwu : ℕ → ℝ) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ e ∈ (D.G t).E,
      (∑ j ∈ Finset.range k,
        (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts t) j).wstr e) / (k : ℝ) ≤
        σ_mwu (D.G t).n

lemma ToolMWUOrdRestart.toToolMWUOrdUpTo {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdRestart σ_mwu) : T.toSparseCoreTool.ToolMWUOrdUpTo σ_mwu := by
  intro k τ M N D ord Ψ c w hk hG0 hD hLen hW hOrd hM hN hTh t ht e he
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) Ψ c w hk hG0 hD hLen hW hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht e he

lemma ToolMWUOrdRestart.toNoHidden {T : SparseCoreRestartTool} {σ_mwu : ℕ → ℝ}
    (h : T.ToolMWUOrdRestart σ_mwu) : T.ToolMWUOrdRestartNoHidden σ_mwu := by
  intro k τ M N D ord restarts hk hG0 hD hLen hℓ hOrd hM hN hRest hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd
    hM hN hRest hTh

lemma ToolMWUOrdRestartNoHidden.toToolMWUOrdNoHiddenUpTo {T : SparseCoreRestartTool}
    {σ_mwu : ℕ → ℝ} (h : T.ToolMWUOrdRestartNoHidden σ_mwu) :
    T.toSparseCoreTool.ToolMWUOrdNoHiddenUpTo σ_mwu := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh t ht e he
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) hk hG0 hD hLen hℓ hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht e he

/-- Ordered surviving-edge self-embedding property along a run with restarts. -/
def ToolEmbedsSurvivingOrdRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts t) j).E,
      T.emb (T.runOrdAfterRestarts k M N D ord restarts t) j e = [(e, true)]

/-- Hidden-stability-free version of `ToolEmbedsSurvivingOrdRestart`. -/
def ToolEmbedsSurvivingOrdRestartNoHidden (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t ≤ τ, ∀ j < k, ∀ e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts t) j).E,
      T.emb (T.runOrdAfterRestarts k M N D ord restarts t) j e = [(e, true)]

lemma ToolEmbedsSurvivingOrdRestart.toToolEmbedsSurvivingOrdUpTo {T : SparseCoreRestartTool}
    (h : T.ToolEmbedsSurvivingOrdRestart) : T.toSparseCoreTool.ToolEmbedsSurvivingOrdUpTo := by
  intro k τ M N D ord Ψ c w hk hG0 hD hLen hW hOrd hM hN hTh t ht j hj e he
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) Ψ c w hk hG0 hD hLen hW hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht j hj e
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using he)

lemma ToolEmbedsSurvivingOrdRestart.toNoHidden {T : SparseCoreRestartTool}
    (h : T.ToolEmbedsSurvivingOrdRestart) : T.ToolEmbedsSurvivingOrdRestartNoHidden := by
  intro k τ M N D ord restarts hk hG0 hD hLen hℓ hOrd hM hN hRest hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd
    hM hN hRest hTh

lemma ToolEmbedsSurvivingOrdRestartNoHidden.toToolEmbedsSurvivingOrdNoHiddenUpTo
    {T : SparseCoreRestartTool} (h : T.ToolEmbedsSurvivingOrdRestartNoHidden) :
    T.toSparseCoreTool.ToolEmbedsSurvivingOrdNoHiddenUpTo := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh t ht j hj e he
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) hk hG0 hD hLen hℓ hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht j hj e
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using he)

/-- Ordered surviving-edge non-insertion propagation along a run with restarts. -/
def ToolNoReinsertOrdRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts (t - 1)) j).E,
        e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts t) j).E →
        (∀ u ∈ (T.runOrdAfterUpdate k M N D ord restarts t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

/-- Hidden-stability-free version of `ToolNoReinsertOrdRestart`. -/
def ToolNoReinsertOrdRestartNoHidden (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
    (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
    (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      ∀ e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts (t - 1)) j).E,
        e ∈ (T.S (T.runOrdAfterRestarts k M N D ord restarts t) j).E →
        (∀ u ∈ (T.runOrdAfterUpdate k M N D ord restarts t).2 j, ¬ u.Inserts e) →
        ∀ u ∈ D.U t, ¬ u.Inserts e

lemma ToolNoReinsertOrdRestart.toToolNoReinsertOrdUpTo {T : SparseCoreRestartTool}
    (h : T.ToolNoReinsertOrdRestart) : T.toSparseCoreTool.ToolNoReinsertOrdUpTo := by
  intro k τ M N D ord Ψ c w hk hG0 hD hLen hW hOrd hM hN hTh t ht1 ht j hj e heP heC hNoU
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord (t - 1),
    T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t,
    T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) Ψ c w hk hG0 hD hLen hW hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht1 ht j hj e
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord (t - 1)] using heP)
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using heC)
      (by simpa only [T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord t] using hNoU)

lemma ToolNoReinsertOrdRestart.toNoHidden {T : SparseCoreRestartTool}
    (h : T.ToolNoReinsertOrdRestart) : T.ToolNoReinsertOrdRestartNoHidden := by
  intro k τ M N D ord restarts hk hG0 hD hLen hℓ hOrd hM hN hRest hTh
  obtain ⟨Ψ, _, hW⟩ := exists_weakHiddenStable_zero hℓ
  exact h k τ M N D ord restarts Ψ (fun _ _ => 0) (fun _ _ => 1) hk hG0 hD hLen hW hOrd
    hM hN hRest hTh

lemma ToolNoReinsertOrdRestartNoHidden.toToolNoReinsertOrdNoHiddenUpTo
    {T : SparseCoreRestartTool} (h : T.ToolNoReinsertOrdRestartNoHidden) :
    T.toSparseCoreTool.ToolNoReinsertOrdNoHiddenUpTo := by
  intro k τ M N D ord hk hG0 hD hLen hℓ hOrd hM hN hTh t ht1 ht j hj e heP heC hNoU
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord (t - 1),
    T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t,
    T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) hk hG0 hD hLen hℓ hOrd hM hN
      (fun _ _ _ h => by cases h) hTh t ht1 ht j hj e
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord (t - 1)] using heP)
      (by simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord t] using heC)
      (by simpa only [T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord t] using hNoU)

/-- Ordered strict `NoBatchReinsert` propagation along a run with restarts. -/
def ToolNoReinsertStrictOrdRestart (T : SparseCoreRestartTool) : Prop :=
  ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End) (restarts : ℕ → List ℕ)
    (Ψ : ℝ) (c w : ℕ → ℕ → ℝ),
    0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ → WeakHiddenStable D τ Ψ c w →
    OrderedUpTo D τ 2 ord → (D.G 0).m ≤ M → (D.G 0).n ≤ N → (∀ r ≤ τ, ∀ j ∈ restarts r, j < k) →
    (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
      SparseCoreTool.updateThreshold k M N →
    (∀ t, 1 ≤ t → t ≤ τ → NoBatchReinsert (D.G (t - 1)) (D.U t)) →
    ∀ t, 1 ≤ t → t ≤ τ → ∀ j < k,
      NoBatchReinsert (T.S (T.runOrdAfterRestarts k M N D ord restarts (t - 1)) j)
        ((T.runOrdAfterUpdate k M N D ord restarts t).2 j)

lemma ToolNoReinsertStrictOrdRestart.toToolNoReinsertStrictOrdUpTo {T : SparseCoreRestartTool}
    (h : T.ToolNoReinsertStrictOrdRestart) : T.toSparseCoreTool.ToolNoReinsertStrictOrdUpTo := by
  intro k τ M N D ord Ψ c w hk hG0 hD hLen hW hOrd hM hN hTh hNR t ht1 ht j hj
  simpa only [T.runOrdAfterRestarts_empty_eq_runOrdAt k M N D ord (t - 1),
    T.runOrdAfterUpdate_empty_eq_runOrdAt k M N D ord t] using
    h k τ M N D ord (fun _ => []) Ψ c w hk hG0 hD hLen hW hOrd hM hN
      (fun _ _ _ h => by cases h) hTh hNR t ht1 ht j hj

end SparseCoreRestartTool

end MinCostFlow.Chain
