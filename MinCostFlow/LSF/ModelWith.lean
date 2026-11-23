module

public import MinCostFlow.LSF.Model

/-!
# Parameterized LSF Initialization Model

This file extracts the six algorithmic choices inside `initLSF` into explicit parameters of
`initLSFWith` (and its three-parameter restriction `initLSFWithCore`):
* `T_raw` — static LSST on `(weightedCopyGraph G₀ v, weightedCopyLen G₀ ℓ₀, 1)` (or `(G₀, 1, 1)` when
  `G₀.E = ∅`).
* `r₀` — root vertex in `G₀.V`.
* `C_reps` — component representative set satisfying `IsCompReps G₀ r₀ C_reps`.
* `π` — approximate congestion edge order satisfying `IsApproxCongOrder`.
* `W_T` — static tree decomposition satisfying `IsTreeDecompSpec G₀ T₀ k W_T`.
* `thresh` — stretch clipping threshold satisfying `IsWstrThresh`.

`initLSF` in `MinCostFlow.LSF.Model` is untouched, and `initLSF_eq_initLSFWith` records the
definitional equality relating the two.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Specifications of the six algorithmic choices -/

/-- Valid component-representative set for `(G, r₀)`: contains `r₀`, lies in `G.V`, has size at
most `(components G).card`, and reaches every vertex of `G`. -/
def IsCompReps (G : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) : Prop :=
  r₀ ∈ C_reps ∧ C_reps ⊆ G.V ∧ C_reps.card ≤ (components G).card ∧
    ∀ w ∈ G.V, ∃ r ∈ C_reps, G.Connected w r

/-- Edge order `π` on `T₀` ordering `T₀.E` non-decreasingly up to a factor `α ≥ 1` with respect to
`congestion G T₀ ℓ`. -/
def IsApproxCongOrder (G T₀ : MGraph) (ℓ : ℕ → ℝ) (α : ℝ) (π : ℕ → ℕ) : Prop :=
  IsEdgeOrder T₀ π ∧
  1 ≤ α ∧
  ∀ f ∈ T₀.E, ∀ g ∈ T₀.E, π f ≤ π g → congestion G T₀ ℓ f ≤ α * congestion G T₀ ℓ g

/-- Tree decomposition specification matching the six guarantees of `pickDecomp_spec` (`lemma_B_7`
at uniform edge weights `1` and parameter `k * (hldDepthBound G₀.n + 1)`). -/
def IsTreeDecompSpec (G₀ T₀ : MGraph) (k : ℝ) (W_T : Finset (Finset ℕ)) : Prop :=
  let D1 : ℝ := ((hldDepthBound G₀.n + 1 : ℕ) : ℝ)
  (∀ W₀ ∈ W_T, PathConvex T₀ W₀) ∧
  (∀ W₀₁ ∈ W_T, ∀ W₀₂ ∈ W_T, W₀₁ ≠ W₀₂ →
    Disjoint (inducedEdges T₀ W₀₁) (inducedEdges T₀ W₀₂)) ∧
  W_T.biUnion (inducedEdges T₀) = T₀.E ∧
  ((boundary W_T).card : ℝ) ≤ 2 * (G₀.E.card : ℝ) / (k * D1) ∧
  (W_T.card : ℝ) ≤ 6 * (G₀.E.card : ℝ) / k + 6 ∧
  (∀ W₀ ∈ W_T, (G₀.vol (W₀ \ boundary W_T) : ℝ) ≤ 2240 * k * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)

/-- Stretch-clipping threshold `thresh` with upper bound constant `K_σ`. -/
def IsWstrThresh (C_lsst α : ℝ) (n : ℕ) (k thresh K_σ : ℝ) : Prop :=
  1 ≤ thresh ∧
  4 * (1 + α) * ((hldDepthBound n + 1 : ℕ) : ℝ) ^ 2 * max 1 C_lsst *
    (Real.log ((n : ℝ) + 2)) ^ 2 * k ≤ thresh ∧
  thresh ≤ K_σ * k * (Real.log ((n : ℝ) + 2)) ^ 6

/-- Combined validity predicate for the six initialization parameters. -/
structure ValidLSFParams (C_lsst α thresh K_σ : ℝ) (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ)
    (T_raw : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) (π : ℕ → ℕ)
    (W_T : Finset (Finset ℕ)) : Prop where
  /-- `T_raw` is a valid LSST on `(G_v, ℓ_v, 1)` when `G₀.E` is nonempty, else `(G₀, 1, 1)`. -/
  hT_raw : IsLSST
    (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
    (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
    (fun _ => 1)
    (C_lsst * (Real.log ((G₀.n : ℝ) + 2)) ^ 2)
    T_raw
  /-- `r₀` belongs to `G₀.V`. -/
  hr₀ : r₀ ∈ G₀.V
  /-- `C_reps` is a valid set of component representatives. -/
  hC_reps : IsCompReps G₀ r₀ C_reps
  /-- `π` approximates congestion order within factor `α`. -/
  hπ : IsApproxCongOrder
    (open Classical in if G₀.E.Nonempty then weightedCopyGraph G₀ v else G₀)
    (projectTree G₀ v T_raw)
    (open Classical in if G₀.E.Nonempty then weightedCopyLen G₀ ℓ₀ else fun _ => 1)
    α π
  /-- `W_T` satisfies the six `pickDecomp_spec` properties for `projectTree G₀ v T_raw`. -/
  hW_T : IsTreeDecompSpec G₀ (projectTree G₀ v T_raw) k W_T
  /-- `thresh` satisfies the lower and upper bounds with constant `K_σ`. -/
  hthresh : IsWstrThresh C_lsst α G₀.n k thresh K_σ

/-- Exact congestion order satisfies `IsApproxCongOrder` with factor `α = 1`. -/
lemma isApproxCongOrder_congOrder (G T : MGraph) (ℓ : ℕ → ℝ) :
    IsApproxCongOrder G T ℓ 1 (congOrder T (congestion G T ℓ)) := by
  refine ⟨congOrder_isEdgeOrder T _, le_rfl, fun f hf g hg hle => ?_⟩
  rw [one_mul]
  by_contra hlt
  push Not at hlt
  exact absurd (congOrder_isSortedByCong T (congestion G T ℓ) g hg f hf hlt) (not_lt.mpr hle)

/-- Any edge order sorting a function `c` that pointwise sandwiches `congestion G T ℓ` within
factor `[1, α]` satisfies `IsApproxCongOrder G T ℓ α π`. -/
lemma isApproxCongOrder_of_approx {G T : MGraph} {ℓ c : ℕ → ℝ} {α : ℝ} (hα : 1 ≤ α)
    (hlo : ∀ e ∈ T.E, congestion G T ℓ e ≤ c e)
    (hhi : ∀ e ∈ T.E, c e ≤ α * congestion G T ℓ e)
    {π : ℕ → ℕ} (hord : IsEdgeOrder T π)
    (hsort : ∀ f ∈ T.E, ∀ g ∈ T.E, π f ≤ π g → c f ≤ c g) :
    IsApproxCongOrder G T ℓ α π :=
  ⟨hord, hα, fun f hf g hg hle => (hlo f hf).trans ((hsort f hf g hg hle).trans (hhi g hg))⟩

/-! ## Parameterized LSF initialization -/

/-- Parameterized version of `initLSF` taking explicit `(T_raw, r₀, C_reps, π, W_T, thresh)`. -/
noncomputable def initLSFWith (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ)
    (T_raw : MGraph) (r₀ : ℕ) (C_reps : Finset ℕ) (π : ℕ → ℕ)
    (W_T : Finset (Finset ℕ)) (thresh : ℝ) : LSFState :=
  open Classical in
  let T₀ := projectTree G₀ v T_raw
  let rawWstr := fun e => levelStretchBound T₀ r₀ π G₀ (safeLen G₀ ℓ₀) e
  let E_high := G₀.E.filter (fun e => thresh ≤ rawWstr e)
  let R₀_init := C_reps ∪ boundary W_T ∪ E_high.biUnion (fun e => {G₀.tail e, G₀.head e})
  let wstr := fun e => if e ∈ G₀.E then (if thresh ≤ rawWstr e then (1 : ℝ) else rawWstr e) else 1
  let R_orig_init := upClosure (hldAuxTree T₀ r₀) r₀ R₀_init
  let F₀ := forestGivenRoots T₀ r₀ R_orig_init π
  { G₀ := G₀
    G := G₀
    v := v
    k := k
    T₀ := T₀
    T_cur := T₀
    origVert := id
    r₀ := r₀
    π := π
    R₀_init := R₀_init
    R₀_base := R₀_init
    isolatedVerts := ∅
    insertedEdges := ∅
    wstr := wstr
    W_init := refineDecomp W_T F₀
    numUpdates := 0 }

/-- Core three-parameter version of `initLSF` taking `(T_raw, r₀, W_T)` and defaulting `C_reps`,
`π`, and `thresh` to `initLSF`'s exact choices. -/
noncomputable def initLSFWithCore (C_lsst : ℝ) (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ)
    (T_raw : MGraph) (r₀ : ℕ) (W_T : Finset (Finset ℕ)) : LSFState :=
  open Classical in
  let G_v := weightedCopyGraph G₀ v
  let ℓ_v := weightedCopyLen G₀ ℓ₀
  let T₀ := projectTree G₀ v T_raw
  let π :=
    if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
    else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
  initLSFWith G₀ ℓ₀ v k T_raw r₀ (compReps G₀ r₀) π W_T (wstrThresh C_lsst G₀.n k)

/-- `initLSFWithCore` delegates to `initLSFWith`. -/
lemma initLSFWithCore_eq_initLSFWith (C_lsst : ℝ) (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ)
    (T_raw : MGraph) (r₀ : ℕ) (W_T : Finset (Finset ℕ)) :
    initLSFWithCore C_lsst G₀ ℓ₀ v k T_raw r₀ W_T =
      open Classical in
      initLSFWith G₀ ℓ₀ v k T_raw r₀ (compReps G₀ r₀)
        (if G₀.E.Nonempty then congOrder (projectTree G₀ v T_raw)
            (congestion (weightedCopyGraph G₀ v) (projectTree G₀ v T_raw) (weightedCopyLen G₀ ℓ₀))
          else congOrder (projectTree G₀ v T_raw)
            (congestion G₀ (projectTree G₀ v T_raw) (fun _ => 1)))
        W_T (wstrThresh C_lsst G₀.n k) :=
  rfl

/-- `initLSF` is definitionally equal to `initLSFWith` instantiated with `initLSF`'s defaults. -/
lemma initLSF_eq_initLSFWith (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ) :
    initLSF oracle C_lsst G₀ ℓ₀ v k =
      open Classical in
      let G_v := weightedCopyGraph G₀ v
      let ℓ_v := weightedCopyLen G₀ ℓ₀
      let T_raw := if G₀.E.Nonempty then oracle G_v ℓ_v (fun _ => 1)
        else oracle G₀ (fun _ => 1) (fun _ => 1)
      let T₀ := projectTree G₀ v T_raw
      let r₀ := pickRoot G₀
      let π :=
        if G₀.E.Nonempty then congOrder T₀ (congestion G_v T₀ ℓ_v)
        else congOrder T₀ (congestion G₀ T₀ (fun _ => 1))
      initLSFWith G₀ ℓ₀ v k T_raw r₀ (compReps G₀ r₀) π (pickDecomp G₀ T₀ r₀ k)
        (wstrThresh C_lsst G₀.n k) :=
  rfl

/-- `initLSF` is definitionally equal to `initLSFWithCore` instantiated with `initLSF`'s
`(T_raw, r₀, W_T)`. -/
lemma initLSF_eq_initLSFWithCore (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ v : ℕ → ℝ) (k : ℝ) :
    initLSF oracle C_lsst G₀ ℓ₀ v k =
      open Classical in
      let T_raw := if G₀.E.Nonempty then oracle (weightedCopyGraph G₀ v) (weightedCopyLen G₀ ℓ₀) (fun _ => 1)
        else oracle G₀ (fun _ => 1) (fun _ => 1)
      let T₀ := projectTree G₀ v T_raw
      let r₀ := pickRoot G₀
      initLSFWithCore C_lsst G₀ ℓ₀ v k T_raw r₀ (pickDecomp G₀ T₀ r₀ k) :=
  rfl

end MinCostFlow.LSF
