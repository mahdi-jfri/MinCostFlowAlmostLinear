module

public import MinCostFlow.Chain.SparseCoreTool

/-!
# Runs of the sparse core tool with orders of ends

`SparseCoreTool` carries orders of ends: `initOrd` and
`updateOrd` take the order of the ends at each vertex of the input graph, and `rot` returns the
order at each vertex of each output graph. This file defines the runs that pass a sequence of
orders `ord t`, one for each stage `t`, with and without restarts. A restart keeps the order the
state stores, so it takes none.

`coreInstanceOrdAt`, `coreCOrdAt` and `coreWOrdAt` are the instance and the hidden pair that
the run with orders passes to the next level, as `coreInstanceAt`, `coreCAt` and `coreWAt` are
for the run without orders. `coreInstanceOrdFrom`, `coreCOrdFrom` and `coreWOrdFrom` are the
suffix versions starting at stage `s₀` under a run with orders and restarts.

A tool that keeps the default `initOrd` and `updateOrd` ignores the orders (`OrderFree`). Its
runs with orders are its runs without them (`runOrdAt_eq_runAt`, `runOrdAfterUpdate_eq`).
-/

@[expose] public section

namespace MinCostFlow.Chain

namespace SparseCoreTool

/-- The tool ignores the orders: `initOrd` and `updateOrd` agree with `init` and `update`. This
holds for every tool that keeps the default `initOrd` and `updateOrd`. -/
def OrderFree (T : SparseCoreTool) : Prop :=
  (∀ k M N G ℓ g ord, T.initOrd k M N G ℓ g ord = T.init k M N G ℓ g) ∧
  ∀ st U ℓ g ord, T.updateOrd st U ℓ g ord = T.update st U ℓ g

/-- Sequential execution of `SparseCoreTool` with orders: `ord t` is the order of ends at each
vertex of `D.G t`, passed to `initOrd` at `t = 0` and to `updateOrd` after the batch at `t + 1`. -/
def runOrdAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) : ℕ → T.State × (ℕ → List Update)
  | 0 => (T.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0), fun _ => [])
  | t + 1 =>
    let prev := T.runOrdAt k M N D ord t
    T.updateOrd prev.1 (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1)) (ord (t + 1))

/-- For a tool that ignores the orders, the run with orders is the run without them. -/
theorem runOrdAt_eq_runAt {T : SparseCoreTool} (hT : T.OrderFree) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) :
    ∀ t, T.runOrdAt k M N D ord t = T.runAt k M N D t
  | 0 => by simp only [runOrdAt, runAt, hT.1]
  | t + 1 => by simp only [runOrdAt, runAt, hT.2, runOrdAt_eq_runAt hT k M N D ord t]

/-- Sequential execution of `SparseCoreTool` with orders initialized at the initial graph's own
sizes `((D.G 0).m, (D.G 0).n)`. -/
abbrev runOrd (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) : ℕ → T.State × (ℕ → List Update) :=
  T.runOrdAt k (D.G 0).m (D.G 0).n D ord

lemma runOrdAt_congr (T : SparseCoreTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List Bundle.End} (t : ℕ)
    (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s)
    (hord : ∀ s ≤ t, ord₁ s = ord₂ s) :
    T.runOrdAt k M N D₁ ord₁ t = T.runOrdAt k M N D₂ ord₂ t := by
  induction t with
  | zero => simp [runOrdAt, hG0, hℓ0, hg0, hord 0 (le_refl 0)]
  | succ m ih =>
    have ih' := ih (fun s hs1 hsm => hstep s hs1 (Nat.le_succ_of_le hsm))
      (fun s hsm => hord s (Nat.le_succ_of_le hsm))
    have hm := hstep (m + 1) (Nat.succ_pos m) (le_refl _)
    have ho := hord (m + 1) (le_refl _)
    simp only [runOrdAt, ih', hm.1, hm.2.1, hm.2.2, ho]

/-- The induced dynamic instance on the output graph of branch `j` in the run with orders. -/
noncomputable def coreInstanceOrdAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (j : ℕ) : DynamicInstance where
  G := fun t => T.S (T.runOrdAt k M N D ord t).1 j
  U := fun t => (T.runOrdAt k M N D ord t).2 j
  g := fun t => coreGrad (D.G t) (T.lsfs (T.runOrdAt k M N D ord t).1 j) (D.g t)
  ℓ := fun t => coreLen (T.lsfs (T.runOrdAt k M N D ord t).1 j) (D.ℓ t)

/-- The induced dynamic instance on branch `j` initialized at `((D.G 0).m, (D.G 0).n)`. -/
noncomputable abbrev coreInstanceOrd (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (j : ℕ) : DynamicInstance :=
  T.coreInstanceOrdAt k (D.G 0).m (D.G 0).n D ord j

/-- The hidden circulation passed to branch `j` in the run with orders (Definition 5.15). -/
noncomputable def coreCOrdAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (c : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  let st := (T.runOrdAt k M N D ord t).1
  passSparseCoreC (coreGraph (D.G t) (T.lsfs st j)) (T.emb st j) (passCoreC (c t))

/-- The hidden circulation passed to branch `j` initialized at `((D.G 0).m, (D.G 0).n)`. -/
noncomputable abbrev coreCOrd (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (c : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  T.coreCOrdAt k (D.G 0).m (D.G 0).n D ord c j t

/-- The hidden width passed to branch `j` in the run with orders (Definition 5.15). -/
noncomputable def coreWOrdAt (T : SparseCoreTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (w : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  let st := (T.runOrdAt k M N D ord t).1
  passSparseCoreW (coreGraph (D.G t) (T.lsfs st j)) (T.emb st j) (passCoreW (T.lsfs st j) (w t))

/-- The hidden width passed to branch `j` initialized at `((D.G 0).m, (D.G 0).n)`. -/
noncomputable abbrev coreWOrd (T : SparseCoreTool) (k : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (w : ℕ → ℕ → ℝ) (j t : ℕ) : ℕ → ℝ :=
  T.coreWOrdAt k (D.G 0).m (D.G 0).n D ord w j t

theorem coreInstanceOrdAt_eq_coreInstanceAt {T : SparseCoreTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (j : ℕ) :
    T.coreInstanceOrdAt k M N D ord j = T.coreInstanceAt k M N D j := by
  simp only [coreInstanceOrdAt, coreInstanceAt, runOrdAt_eq_runAt hT]

theorem coreCOrdAt_eq_coreCAt {T : SparseCoreTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (c : ℕ → ℕ → ℝ) (j : ℕ) :
    T.coreCOrdAt k M N D ord c j = T.coreCAt k M N D c j := by
  funext t e
  simp only [coreCOrdAt, coreCAt, runOrdAt_eq_runAt hT]

theorem coreWOrdAt_eq_coreWAt {T : SparseCoreTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (w : ℕ → ℕ → ℝ) (j : ℕ) :
    T.coreWOrdAt k M N D ord w j = T.coreWAt k M N D w j := by
  funext t e
  simp only [coreWOrdAt, coreWAt, runOrdAt_eq_runAt hT]

end SparseCoreTool

namespace SparseCoreRestartTool

/-- `runAfterUpdate` with orders: `ord t` is the order of ends at each vertex of `D.G t`. A
restart keeps the stored order, so it takes none. -/
def runOrdAfterUpdate (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) : ℕ → T.State × (ℕ → List Update)
  | 0 => (T.initOrd k M N (D.G 0) (D.ℓ 0) (D.g 0) (ord 0), fun _ => [])
  | t + 1 =>
    let stPrev := (restarts t).foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1
    T.updateOrd stPrev (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1)) (ord (t + 1))

/-- `runAfterRestarts` with orders. -/
def runOrdAfterRestarts (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) (t : ℕ) : T.State :=
  (restarts t).foldl T.restart (T.runOrdAfterUpdate k M N D ord restarts t).1

lemma runOrdAfterUpdate_succ (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) (t : ℕ) :
    T.runOrdAfterUpdate k M N D ord restarts (t + 1) =
      T.updateOrd (T.runOrdAfterRestarts k M N D ord restarts t)
        (D.U (t + 1)) (D.ℓ (t + 1)) (D.g (t + 1)) (ord (t + 1)) := rfl

lemma runOrdAfterUpdate_empty_eq_runOrdAt (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) :
    ∀ t, T.runOrdAfterUpdate k M N D ord (fun _ => []) t =
      T.toSparseCoreTool.runOrdAt k M N D ord t
  | 0 => rfl
  | t + 1 => by
    simp only [runOrdAfterUpdate, List.foldl_nil, SparseCoreTool.runOrdAt,
      runOrdAfterUpdate_empty_eq_runOrdAt T k M N D ord t]

lemma runOrdAfterRestarts_empty_eq_runOrdAt (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (t : ℕ) :
    T.runOrdAfterRestarts k M N D ord (fun _ => []) t =
      (T.toSparseCoreTool.runOrdAt k M N D ord t).1 := by
  simp only [runOrdAfterRestarts, List.foldl_nil, runOrdAfterUpdate_empty_eq_runOrdAt]

lemma runOrdAfterUpdate_congr_lt (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List Bundle.End}
    {restarts₁ restarts₂ : ℕ → List ℕ} (t : ℕ)
    (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s)
    (hord : ∀ s ≤ t, ord₁ s = ord₂ s)
    (hrest : ∀ s < t, restarts₁ s = restarts₂ s) :
    T.runOrdAfterUpdate k M N D₁ ord₁ restarts₁ t =
      T.runOrdAfterUpdate k M N D₂ ord₂ restarts₂ t := by
  induction t with
  | zero => simp [runOrdAfterUpdate, hG0, hℓ0, hg0, hord 0 (le_refl 0)]
  | succ m ih =>
    have ih' := ih (fun s hs1 hsm => hstep s hs1 (Nat.le_succ_of_le hsm))
      (fun s hsm => hord s (Nat.le_succ_of_le hsm))
      (fun s hsm => hrest s (Nat.lt_succ_of_lt hsm))
    have hm := hstep (m + 1) (Nat.succ_pos m) (le_refl _)
    have ho := hord (m + 1) (le_refl _)
    have hr := hrest m (Nat.lt_succ_self m)
    simp only [runOrdAfterUpdate, ih', hr, hm.1, hm.2.1, hm.2.2, ho]

lemma runOrdAfterRestarts_congr_le (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List Bundle.End}
    {restarts₁ restarts₂ : ℕ → List ℕ} (t : ℕ)
    (hG0 : D₁.G 0 = D₂.G 0) (hℓ0 : D₁.ℓ 0 = D₂.ℓ 0) (hg0 : D₁.g 0 = D₂.g 0)
    (hstep : ∀ s, 1 ≤ s → s ≤ t → D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s)
    (hord : ∀ s ≤ t, ord₁ s = ord₂ s)
    (hrest : ∀ s ≤ t, restarts₁ s = restarts₂ s) :
    T.runOrdAfterRestarts k M N D₁ ord₁ restarts₁ t =
      T.runOrdAfterRestarts k M N D₂ ord₂ restarts₂ t := by
  unfold runOrdAfterRestarts
  rw [T.runOrdAfterUpdate_congr_lt k M N t hG0 hℓ0 hg0 hstep hord
    (fun s hs => hrest s (Nat.le_of_lt hs)), hrest t (le_refl t)]

/-- Suffix `DynamicInstance` on branch `j` starting at stage `s₀` (right after `restarts s₀`)
under a run with orders and restarts initialized at size bounds `(M, N)`. -/
noncomputable def coreInstanceOrdFrom (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ)
    (s₀ j : ℕ) : DynamicInstance where
  G := fun δ => T.S (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j
  U := fun δ => (T.runOrdAfterUpdate k M N D ord restarts (s₀ + δ)).2 j
  g := fun δ => coreGrad (D.G (s₀ + δ))
    (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j) (D.g (s₀ + δ))
  ℓ := fun δ => coreLen
    (T.lsfs (T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)) j) (D.ℓ (s₀ + δ))

/-- Hidden circulation `c` lifted to `coreInstanceOrdFrom` for branch `j` from stage `s₀`. -/
noncomputable def coreCOrdFrom (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) (c : ℕ → ℕ → ℝ)
    (s₀ j δ : ℕ) : ℕ → ℝ :=
  let st := T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)
  let L := T.lsfs st j
  passSparseCoreC (coreGraph (D.G (s₀ + δ)) L) (T.emb st j) (passCoreC (c (s₀ + δ)))

/-- Hidden width `w` lifted to `coreInstanceOrdFrom` for branch `j` from stage `s₀`. -/
noncomputable def coreWOrdFrom (T : SparseCoreRestartTool) (k M N : ℕ) (D : DynamicInstance)
    (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) (w : ℕ → ℕ → ℝ)
    (s₀ j δ : ℕ) : ℕ → ℝ :=
  let st := T.runOrdAfterRestarts k M N D ord restarts (s₀ + δ)
  let L := T.lsfs st j
  passSparseCoreW (coreGraph (D.G (s₀ + δ)) L) (T.emb st j) (passCoreW L (w (s₀ + δ)))

/-- For a tool that ignores the orders, the run with orders and restarts is the run without
orders. -/
theorem runOrdAfterUpdate_eq {T : SparseCoreRestartTool} (hT : T.OrderFree) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) :
    ∀ t, T.runOrdAfterUpdate k M N D ord restarts t = T.runAfterUpdate k M N D restarts t
  | 0 => by simp only [runOrdAfterUpdate, runAfterUpdate, hT.1]
  | t + 1 => by
    simp only [runOrdAfterUpdate, runAfterUpdate, hT.2, runOrdAfterUpdate_eq hT k M N D ord
      restarts t]

theorem runOrdAfterRestarts_eq {T : SparseCoreRestartTool} (hT : T.OrderFree) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (restarts : ℕ → List ℕ) (t : ℕ) :
    T.runOrdAfterRestarts k M N D ord restarts t = T.runAfterRestarts k M N D restarts t := by
  simp only [runOrdAfterRestarts, runAfterRestarts, runOrdAfterUpdate_eq hT]

lemma coreInstanceOrdFrom_empty_zero (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (j : ℕ) :
    T.coreInstanceOrdFrom k M N D ord (fun _ => []) 0 j =
      T.toSparseCoreTool.coreInstanceOrdAt k M N D ord j := by
  simp only [coreInstanceOrdFrom, SparseCoreTool.coreInstanceOrdAt, Nat.zero_add,
    runOrdAfterUpdate_empty_eq_runOrdAt, runOrdAfterRestarts_empty_eq_runOrdAt]

lemma coreCOrdFrom_empty_zero (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (c : ℕ → ℕ → ℝ) (j : ℕ) :
    T.coreCOrdFrom k M N D ord (fun _ => []) c 0 j =
      T.toSparseCoreTool.coreCOrdAt k M N D ord c j := by
  funext δ e
  simp only [coreCOrdFrom, SparseCoreTool.coreCOrdAt, Nat.zero_add,
    runOrdAfterRestarts_empty_eq_runOrdAt]

lemma coreWOrdFrom_empty_zero (T : SparseCoreRestartTool) (k M N : ℕ)
    (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End) (w : ℕ → ℕ → ℝ) (j : ℕ) :
    T.coreWOrdFrom k M N D ord (fun _ => []) w 0 j =
      T.toSparseCoreTool.coreWOrdAt k M N D ord w j := by
  funext δ e
  simp only [coreWOrdFrom, SparseCoreTool.coreWOrdAt, Nat.zero_add,
    runOrdAfterRestarts_empty_eq_runOrdAt]

theorem coreInstanceOrdFrom_eq_coreInstanceFrom {T : SparseCoreRestartTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End)
    (restarts : ℕ → List ℕ) (s₀ j : ℕ) :
    T.coreInstanceOrdFrom k M N D ord restarts s₀ j =
      T.coreInstanceFrom k M N D restarts s₀ j := by
  simp only [coreInstanceOrdFrom, coreInstanceFrom, runOrdAfterUpdate_eq hT,
    runOrdAfterRestarts_eq hT]

theorem coreCOrdFrom_eq_coreCFrom {T : SparseCoreRestartTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End)
    (restarts : ℕ → List ℕ) (c : ℕ → ℕ → ℝ) (s₀ j : ℕ) :
    T.coreCOrdFrom k M N D ord restarts c s₀ j = T.coreCFrom k M N D restarts c s₀ j := by
  funext δ e
  simp only [coreCOrdFrom, coreCFrom, runOrdAfterRestarts_eq hT]

theorem coreWOrdFrom_eq_coreWFrom {T : SparseCoreRestartTool} (hT : T.OrderFree)
    (k M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List Bundle.End)
    (restarts : ℕ → List ℕ) (w : ℕ → ℕ → ℝ) (s₀ j : ℕ) :
    T.coreWOrdFrom k M N D ord restarts w s₀ j = T.coreWFrom k M N D restarts w s₀ j := by
  funext δ e
  simp only [coreWOrdFrom, coreWFrom, runOrdAfterRestarts_eq hT]

end SparseCoreRestartTool

end MinCostFlow.Chain
