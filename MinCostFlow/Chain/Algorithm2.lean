module

public import MinCostFlow.Chain.Section6Quality
public import MinCostFlow.IPM.MinRatioSpec
public import MinCostFlow.Game.Defs

/-!
# Algorithm 2 (`alg:rebuildScheduleForDS`) and failure-extended min-ratio interface

This file formalizes:
1. `MinRatioFailDataStructure` and `MinRatioFailSpec`: `MinCostFlow.IPM.MinRatioSpec` extended
   with explicit failure (`Option (ℕ → ℝ)` returning `none` when a hidden-stability violation
   is detected), plus `MinRatioFailDataStructure.toMinRatioSpec_of_hiddenStable` showing
   equivalence to `IPM.MinRatioSpec` under `HiddenStable`.
2. Fresh edge-ID translation (`translateBatch`, `FreshInv`): maps arbitrary
   `MinRatioHistoryValid` batches (including same-batch delete-then-reinsert edge refreshes as
   in `EdgeRefresh`) into non-reinserting internal batches satisfying `NoBatchReinsert` while
   preserving `m`, `n`, edge lengths, gradients, circulations, inner products, `lnorm`,
   `IsValidPair`, and `HiddenStable`.
3. `Alg2Config` / `algorithm2_ds` (`algorithm2_init`, `algorithm2_update`, `algorithm2_query`,
   `algorithm2_detect`, `algorithm2_loop`): Algorithm 2 (`jtree.tex` lines 745–778) with the
   two failure checks before calling `Shift(i)`:
   * Check 1: there exists `i ≤ d` with `passes_i < 2 Ψ_game`;
   * Check 2: `s_i + 1 ≤ gameBound(r, i)` (the `Game.lemma_7_3_prefix` bound).
   Up to and including any first failing update, `algorithm2` unconditionally preserves
   `ChainInv`, `ChainBudgetInvWith`, `Query`/`Detect` invariants, LCT operation counts, and
   `s_i ≤ gameBound(r, i)` using only `SparseCoreRestartTool.IsSpecRestartNoHidden`.
-/

@[expose] public section

namespace MinCostFlow.Chain

section MinRatioFailInterface

/-- Min-ratio cycle data structure with explicit failure answer (`none` from `update`),
extending `MinCostFlow.IPM.MinRatioDataStructure` (`Option (ℕ → ℝ)`). -/
structure MinRatioFailDataStructure where
  State : Type
  init : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → State
  update : State → List MinCostFlow.Update → (ℕ → ℝ) → (ℕ → ℝ) → ℝ →
    State × Option (ℕ → ℝ)
  query : State → ℕ → ℝ
  detect : State → Finset ℕ × State

/-- State reached after a prefix of `Update` (`isUpdate = true`) and `Detect` (`isUpdate = false`)
operations on `A : MinRatioFailDataStructure`. -/
noncomputable def minRatioFailState (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → A.State
  | 0 => A.init (D.G 0) (D.g 0) (D.ℓ 0)
  | t + 1 =>
    if isUpdate (t + 1) then
      (A.update (minRatioFailState A D η isUpdate t) (D.U (t + 1))
        (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).1
    else (A.detect (minRatioFailState A D η isUpdate t)).2

/-- Optional unscaled circulation returned at update step `t + 1`. -/
noncomputable def minRatioFailOptDir (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) : Option (ℕ → ℝ) :=
  (A.update (minRatioFailState A D η isUpdate t) (D.U (t + 1))
    (D.g (t + 1)) (D.ℓ (t + 1)) (η (t + 1))).2

/-- Unscaled direction (defaulting to `0` if `update` returned `none`). -/
noncomputable def minRatioFailDirection (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) : ℕ → ℝ :=
  (minRatioFailOptDir A D η isUpdate t).getD (fun _ => 0)

/-- Scaled flow increment at stage `t`; failure (`none`) or `Detect` stages contribute `0`. -/
noncomputable def minRatioFailIncrement (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | t + 1, e =>
    match minRatioFailOptDir A D η isUpdate t with
    | some Δ =>
      if isUpdate (t + 1) ∧ e ∈ (D.G (t + 1)).E then
        -(η (t + 1) / (D.G (t + 1)).inner (D.g (t + 1)) Δ) * Δ e
      else 0
    | none => 0

/-- Maintained flow at stage `t` (sum of scaled increments). -/
noncomputable def minRatioFailFlow (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t e : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (t + 1), minRatioFailIncrement A D η isUpdate s e

/-- Last `Detect` stage `≤ t` returning `e` (`last_e` in Definition 4.5). -/
noncomputable def minRatioFailLast (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, e =>
    if isUpdate (t + 1) = false ∧ e ∈ (A.detect (minRatioFailState A D η isUpdate t)).1 then
      t + 1
    else minRatioFailLast A D η isUpdate t e

/-- Exact `Detect` output set at stage `t + 1`. -/
noncomputable def minRatioFailDetectSet (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (ε : ℝ) (t : ℕ) : Finset ℕ :=
  (D.G (t + 1)).E.filter fun e => ε ≤ D.ℓ (t + 1) e *
    ∑ s ∈ Finset.Ioc (minRatioFailLast A D η isUpdate t e) (t + 1),
      |minRatioFailIncrement A D η isUpdate s e|

/-- Whether failure (`none`) occurred strictly before stage `t` (at some update `s + 1 ≤ t`). -/
def minRatioFailFailedBefore (A : MinRatioFailDataStructure) (D : DynamicInstance)
    (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (t : ℕ) : Prop :=
  ∃ s < t, isUpdate (s + 1) = true ∧ minRatioFailOptDir A D η isUpdate s = none

/-- Failure-extended specification matching `IPM.MinRatioSpec` up to first failure. -/
def MinRatioFailSpec (A : MinRatioFailDataStructure) (κ α Ψ ε : ℝ) : Prop :=
  ∀ (D : DynamicInstance) (η : ℕ → ℝ) (isUpdate : ℕ → Bool) (T : ℕ),
    MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T →
    (∀ t ≤ T, ¬ minRatioFailFailedBefore A D η isUpdate t →
      ∀ e ∈ (D.G t).E,
        A.query (minRatioFailState A D η isUpdate t) e = minRatioFailFlow A D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      ¬ minRatioFailFailedBefore A D η isUpdate t →
      (minRatioFailOptDir A D η isUpdate t = none → ¬ D.HiddenStable (t + 1) α Ψ) ∧
      (∀ Δ, minRatioFailOptDir A D η isUpdate t = some Δ →
        (D.G (t + 1)).IsCirculation Δ ∧
        (D.HiddenStable (t + 1) α Ψ →
          (D.G (t + 1)).inner (D.g (t + 1)) Δ /
            (D.G (t + 1)).lnorm (D.ℓ (t + 1)) Δ ≤ -κ * α))) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      ¬ minRatioFailFailedBefore A D η isUpdate t →
      (A.detect (minRatioFailState A D η isUpdate t)).1 = minRatioFailDetectSet A D η isUpdate ε t)

/-- Convert a `MinRatioFailDataStructure` into an `IPM.MinRatioDataStructure` by defaulting `none`
to the zero circulation. Under `HiddenStable`, failure never occurs and the two specs agree. -/
noncomputable def MinRatioFailDataStructure.toMinRatioDS
    (A : MinRatioFailDataStructure) : MinCostFlow.IPM.MinRatioDataStructure where
  State := A.State
  init := A.init
  update := fun st U g ℓ η => let r := A.update st U g ℓ η; (r.1, r.2.getD (fun _ => 0))
  query := A.query
  detect := A.detect

lemma minRatioFail_no_failure_of_hiddenStable {A : MinRatioFailDataStructure}
    {κ α Ψ ε : ℝ} (hSpec : MinRatioFailSpec A κ α Ψ ε)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hHS : D.HiddenStable T α Ψ) :
    ∀ t ≤ T, ¬ minRatioFailFailedBefore A D η isUpdate t ∧
      (t + 1 ≤ T → isUpdate (t + 1) = true → minRatioFailOptDir A D η isUpdate t ≠ none) := by
  have hS := hSpec D η isUpdate T hHist
  have hiddenPrefix : ∀ t ≤ T, D.HiddenStable t α Ψ := by
    rintro t ht
    rcases hHS with ⟨c, w, hcw⟩
    exact ⟨c, w, fun s hs => hcw s (le_trans hs ht)⟩
  intro t
  induction t with
  | zero =>
    intro ht
    have hnf0 : ¬ minRatioFailFailedBefore A D η isUpdate 0 := by
      rintro ⟨s, hs, _⟩; omega
    refine ⟨hnf0, fun ht1 hupd hnone => ?_⟩
    exact (hS.2.1 0 ht1 hupd hnf0).1 hnone (hiddenPrefix 1 ht1)
  | succ t ih =>
    intro ht
    have ⟨hnf_t, hne_t⟩ := ih (Nat.le_of_succ_le ht)
    have hnf_s : ¬ minRatioFailFailedBefore A D η isUpdate (t + 1) := by
      rintro ⟨s, hs, hupd_s, hnone_s⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hlt | rfl
      · exact hnf_t ⟨s, hlt, hupd_s, hnone_s⟩
      · exact hne_t ht hupd_s hnone_s
    refine ⟨hnf_s, fun ht1 hupd hnone => ?_⟩
    exact (hS.2.1 (t + 1) ht1 hupd hnf_s).1 hnone (hiddenPrefix (t + 2) ht1)

lemma MinRatioFailDataStructure.toMinRatioSpec_of_hiddenStable
    {A : MinRatioFailDataStructure} {κ α Ψ ε : ℝ} (hSpec : MinRatioFailSpec A κ α Ψ ε)
    {D : DynamicInstance} {η : ℕ → ℝ} {isUpdate : ℕ → Bool} {T : ℕ}
    (hHist : MinCostFlow.IPM.MinRatioHistoryValid D isUpdate T)
    (hHS : D.HiddenStable T α Ψ) :
    (∀ t ≤ T, ∀ e ∈ (D.G t).E,
      A.toMinRatioDS.query (MinCostFlow.IPM.minRatioState A.toMinRatioDS D η isUpdate t) e =
        MinCostFlow.IPM.minRatioFlow A.toMinRatioDS D η isUpdate t e) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = true →
      (D.G (t + 1)).IsCirculation
          (MinCostFlow.IPM.minRatioDirection A.toMinRatioDS D η isUpdate t) ∧
        (D.G (t + 1)).inner (D.g (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.toMinRatioDS D η isUpdate t) /
          (D.G (t + 1)).lnorm (D.ℓ (t + 1))
            (MinCostFlow.IPM.minRatioDirection A.toMinRatioDS D η isUpdate t) ≤ -κ * α) ∧
    (∀ t, t + 1 ≤ T → isUpdate (t + 1) = false →
      (A.toMinRatioDS.detect
        (MinCostFlow.IPM.minRatioState A.toMinRatioDS D η isUpdate t)).1 =
        MinCostFlow.IPM.minRatioDetectSet A.toMinRatioDS D η isUpdate ε t) := by
  have hS := hSpec D η isUpdate T hHist
  have hNoFail := minRatioFail_no_failure_of_hiddenStable (η := η) hSpec hHist hHS
  have hSt : ∀ t, MinCostFlow.IPM.minRatioState A.toMinRatioDS D η isUpdate t =
      minRatioFailState A D η isUpdate t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      unfold MinCostFlow.IPM.minRatioState minRatioFailState
      rw [ih]
      cases isUpdate (t + 1) <;> rfl
  have hDir : ∀ t ≤ T, t + 1 ≤ T → isUpdate (t + 1) = true →
      ∃ Δ, minRatioFailOptDir A D η isUpdate t = some Δ ∧
        MinCostFlow.IPM.minRatioDirection A.toMinRatioDS D η isUpdate t = Δ := by
    intro t ht ht1 hupd
    have hne := (hNoFail t ht).2 ht1 hupd
    rcases Option.eq_none_or_eq_some (minRatioFailOptDir A D η isUpdate t) with hnone | ⟨Δ, hsome⟩
    · exact absurd hnone hne
    · refine ⟨Δ, hsome, ?_⟩
      unfold MinCostFlow.IPM.minRatioDirection
      rw [hSt t]
      change (minRatioFailOptDir A D η isUpdate t).getD (fun _ => 0) = Δ
      rw [hsome]; rfl
  have hInc : ∀ s ≤ T, ∀ e,
      MinCostFlow.IPM.minRatioIncrement A.toMinRatioDS D η isUpdate s e =
        minRatioFailIncrement A D η isUpdate s e := by
    intro s hs e
    cases s with
    | zero => rfl
    | succ s =>
      simp only [MinCostFlow.IPM.minRatioIncrement, minRatioFailIncrement]
      by_cases hcond : isUpdate (s + 1) = true
      · obtain ⟨Δ, hsome, hdir⟩ := hDir s (Nat.le_of_succ_le hs) hs hcond
        rw [hdir, hsome]
      · have hne : ¬ (isUpdate (s + 1) = true ∧ e ∈ (D.G (s + 1)).E) := fun ⟨h, _⟩ => hcond h
        rw [ite_eq_right_iff.mpr fun h => absurd h hne]
        cases minRatioFailOptDir A D η isUpdate s with
        | none => rfl
        | some Δ => simp [hcond]
  have hFlow : ∀ t ≤ T, ∀ e,
      MinCostFlow.IPM.minRatioFlow A.toMinRatioDS D η isUpdate t e =
        minRatioFailFlow A D η isUpdate t e := by
    intro t ht e
    refine Finset.sum_congr rfl fun s hs => hInc s (by
      have := Finset.mem_range.mp hs; omega) e
  have hLast : ∀ t ≤ T, ∀ e,
      MinCostFlow.IPM.minRatioLast A.toMinRatioDS D η isUpdate t e =
        minRatioFailLast A D η isUpdate t e := by
    intro t ht e
    induction t with
    | zero => rfl
    | succ t ih =>
      unfold MinCostFlow.IPM.minRatioLast minRatioFailLast
      rw [hSt t, ih (Nat.le_of_succ_le ht)]
      rfl
  refine ⟨?_, ?_, ?_⟩
  · intro t ht e he
    rw [hSt t, hFlow t ht e]
    exact hS.1 t ht (hNoFail t ht).1 e he
  · intro t ht1 hupd
    obtain ⟨Δ, hsome, hdir⟩ := hDir t (Nat.le_of_succ_le ht1) ht1 hupd
    have hU := (hS.2.1 t ht1 hupd (hNoFail t (Nat.le_of_succ_le ht1)).1).2 Δ hsome
    rw [hdir]
    have hHS_t1 : D.HiddenStable (t + 1) α Ψ := by
      rcases hHS with ⟨c, w, hcw⟩
      exact ⟨c, w, fun s hs => hcw s (le_trans hs ht1)⟩
    exact ⟨hU.1, hU.2 hHS_t1⟩
  · intro t ht1 hdet
    have hD := hS.2.2 t ht1 hdet (hNoFail t (Nat.le_of_succ_le ht1)).1
    change (A.detect (MinCostFlow.IPM.minRatioState A.toMinRatioDS D η isUpdate t)).1 = _
    rw [hSt t, hD]
    unfold minRatioFailDetectSet MinCostFlow.IPM.minRatioDetectSet
    refine Finset.filter_congr fun e _ => ?_
    rw [hLast t (Nat.le_of_succ_le ht1) e]
    have hsum : ∑ s ∈ Finset.Ioc (minRatioFailLast A D η isUpdate t e) (t + 1),
          |minRatioFailIncrement A D η isUpdate s e| =
        ∑ s ∈ Finset.Ioc (minRatioFailLast A D η isUpdate t e) (t + 1),
          |MinCostFlow.IPM.minRatioIncrement A.toMinRatioDS D η isUpdate s e| := by
      refine Finset.sum_congr rfl fun s hs => ?_
      have hsl : s ≤ t + 1 := (Finset.mem_Ioc.mp hs).2
      rw [hInc s (le_trans hsl ht1) e]
    rw [hsum]

end MinRatioFailInterface

section FreshTranslation

/-- Fresh-ID bijection invariant between external `extG` and internal `intG`. -/
structure FreshInv (extG intG : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) : Prop where
  hV : extG.V = intG.V
  hE : intG.E = extG.E.image e2i
  hLeft : ∀ e ∈ extG.E, i2e (e2i e) = e
  hRight : ∀ e' ∈ intG.E, e2i (i2e e') = e' ∧ i2e e' ∈ extG.E
  hTail : ∀ e ∈ extG.E, intG.tail (e2i e) = extG.tail e
  hHead : ∀ e ∈ extG.E, intG.head (e2i e) = extG.head e
  hLtFresh : ∀ e' ∈ intG.E, e' < nf

lemma freshInv_init (G : MGraph) :
    FreshInv G G id id (G.E.sup id + 1) where
  hV := rfl
  hE := by simp
  hLeft := fun _ _ => rfl
  hRight := fun _ he => ⟨rfl, he⟩
  hTail := fun _ _ => rfl
  hHead := fun _ _ => rfl
  hLtFresh := fun e' he => Nat.lt_succ_of_le (Finset.le_sup (f := id) he)

lemma FreshInv.m_eq {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) : intG.m = extG.m := by
  unfold MGraph.m
  rw [hF.hE]
  exact Finset.card_image_of_injOn fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this

lemma FreshInv.n_eq {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) : intG.n = extG.n := by
  unfold MGraph.n
  rw [hF.hV]

lemma FreshInv.connected {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf)
    (hConn : ∀ u ∈ extG.V, ∀ v ∈ extG.V, extG.Connected u v) :
    ∀ u ∈ intG.V, ∀ v ∈ intG.V, intG.Connected u v := by
  intro u hu v hv
  obtain ⟨P, hP⟩ := hConn u (hF.hV ▸ hu) v (hF.hV ▸ hv)
  clear hu hv
  refine ⟨P.map (fun x => (e2i x.1, x.2)), ?_⟩
  induction hP with
  | nil z => exact .nil z
  | @cons u₀ v₀ x₀ P₀ hxE hsrc _ ih =>
    have hx' : e2i x₀.1 ∈ intG.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i hxE
    have hsrc' : intG.src (e2i x₀.1, x₀.2) = u₀ := by
      cases hx : x₀.2
      · simpa [MGraph.src, hx, hF.hHead x₀.1 hxE] using hsrc
      · simpa [MGraph.src, hx, hF.hTail x₀.1 hxE] using hsrc
    have hdst' : intG.dst (e2i x₀.1, x₀.2) = extG.dst x₀ := by
      cases hx : x₀.2
      · simp [MGraph.dst, hx, hF.hTail x₀.1 hxE]
      · simp [MGraph.dst, hx, hF.hHead x₀.1 hxE]
    simpa [List.map_cons] using MGraph.IsWalk.cons hx' hsrc' (hdst' ▸ ih)

lemma FreshInv.isValid_iff {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) :
    intG.IsValid ↔ extG.IsValid := by
  constructor
  · intro h e he
    have he' : e2i e ∈ intG.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i he
    have hc := h (e2i e) he'
    rw [← hF.hV, hF.hTail e he, hF.hHead e he] at hc
    exact hc
  · intro h e' he'
    obtain ⟨heq, he⟩ := hF.hRight e' he'
    have hc := h (i2e e') he
    rw [hF.hV, ← hF.hTail (i2e e') he, ← hF.hHead (i2e e') he, heq] at hc
    exact hc

/-- Map an internal circulation/flow `Δ_int` on `intG` back to `extG`. -/
def liftEdgeFn (extG : MGraph) (e2i : ℕ → ℕ) (f_int : ℕ → ℝ) : ℕ → ℝ :=
  fun e => if e ∈ extG.E then f_int (e2i e) else 0

lemma FreshInv.isCirculation_lift {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) {Δ_int : ℕ → ℝ}
    (hC : intG.IsCirculation Δ_int) :
    extG.IsCirculation (liftEdgeFn extG e2i Δ_int) := by
  intro v hv
  have hv' : v ∈ intG.V := hF.hV ▸ hv
  have hdv := hC v hv'
  have hinj : Set.InjOn e2i extG.E := fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this
  have hsum_eq : extG.demand (liftEdgeFn extG e2i Δ_int) v = intG.demand Δ_int v := by
    unfold MGraph.demand MGraph.b
    rw [hF.hE, Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun e he => ?_
    simp [liftEdgeFn, he, hF.hTail e he, hF.hHead e he]
  rw [hsum_eq]
  exact hdv

lemma FreshInv.inner_lift {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) (g_ext : ℕ → ℝ) (Δ_int : ℕ → ℝ) :
    extG.inner g_ext (liftEdgeFn extG e2i Δ_int) =
      intG.inner (fun e' => g_ext (i2e e')) Δ_int := by
  have hinj : Set.InjOn e2i extG.E := fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this
  unfold MGraph.inner
  rw [hF.hE, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun e he => ?_
  simp [liftEdgeFn, he, hF.hLeft e he]

lemma FreshInv.lnorm_lift {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) (ℓ_ext : ℕ → ℝ) (Δ_int : ℕ → ℝ) :
    extG.lnorm ℓ_ext (liftEdgeFn extG e2i Δ_int) =
      intG.lnorm (fun e' => ℓ_ext (i2e e')) Δ_int := by
  have hinj : Set.InjOn e2i extG.E := fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this
  unfold MGraph.lnorm
  rw [hF.hE, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun e he => ?_
  simp [liftEdgeFn, he, hF.hLeft e he]

lemma FreshInv.norm1_pullback {extG intG : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    (hF : FreshInv extG intG e2i i2e nf) (w_ext : ℕ → ℝ) :
    intG.norm1 (fun e' => w_ext (i2e e')) = extG.norm1 w_ext := by
  have hinj : Set.InjOn e2i extG.E := fun e₁ h1 e₂ h2 heq => by
    have := congrArg i2e heq
    rwa [hF.hLeft e₁ h1, hF.hLeft e₂ h2] at this
  unfold MGraph.norm1
  rw [hF.hE, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun e he => ?_
  simp [hF.hLeft e he]

lemma mem_pre_of_mem_applyBatch {G : MGraph} {U : List Update} {e : ℕ}
    (he : e ∈ (G.applyBatch U).E) (hNo : ∀ u ∈ U, ¬ u.Inserts e) : e ∈ G.E := by
  induction U generalizing G with
  | nil => exact he
  | cons u rest ih =>
    have he1 := ih he fun v hv => hNo v (List.mem_cons_of_mem u hv)
    have hnu := hNo u (List.mem_cons_self)
    cases u with
    | insert a _ _ =>
      simp only [MGraph.applyUpdate, Finset.mem_insert] at he1
      rcases he1 with rfl | hmem
      · exact absurd (by constructor) hnu
      · exact hmem
    | delete a =>
      simp only [MGraph.applyUpdate] at he1
      exact Finset.mem_of_mem_erase he1
    | split _ _ _ _ =>
      simpa [MGraph.applyUpdate] using he1

/-- Translate one external `Update` into a fresh-ID internal `Update` without reinsertions. -/
def translateUpdate (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) (u : Update) :
    MGraph × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × Update :=
  match u with
  | .delete e =>
    (curExt.applyUpdate (.delete e), e2i, i2e, nf, .delete (e2i e))
  | .insert e a b =>
    let e' := nf
    (curExt.applyUpdate (.insert e a b), Function.update e2i e e',
      Function.update i2e e' e, nf + 1, .insert e' a b)
  | .split v v' St Sh =>
    (curExt.applyUpdate (.split v v' St Sh), e2i, i2e, nf,
      .split v v' (St.image e2i) (Sh.image e2i))

/-- Sequentially translate an external batch `U` into a non-reinserting internal batch. -/
def translateBatch (curExt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ) :
    List Update → MGraph × (ℕ → ℕ) × (ℕ → ℕ) × ℕ × List Update
  | [] => (curExt, e2i, i2e, nf, [])
  | u :: rest =>
    let (ext1, e2i1, i2e1, nf1, u') := translateUpdate curExt e2i i2e nf u
    let (extF, e2iF, i2eF, nfF, rest') := translateBatch ext1 e2i1 i2e1 nf1 rest
    (extF, e2iF, i2eF, nfF, u' :: rest')

lemma translateUpdate_preserves {curExt curInt : MGraph} {e2i i2e : ℕ → ℕ} {nf : ℕ}
    {u : Update} (hF : FreshInv curExt curInt e2i i2e nf) (hU : curExt.UpdateIsValid u) :
    let (ext1, e2i1, i2e1, nf1, u') := translateUpdate curExt e2i i2e nf u
    FreshInv ext1 (curInt.applyUpdate u') e2i1 i2e1 nf1 ∧
    curInt.UpdateIsValid u' ∧
    nf ≤ nf1 ∧
    (∀ e' < nf, i2e1 e' = i2e e') ∧
    (∀ e', u'.Inserts e' → nf ≤ e' ∧ e' < nf1) ∧
    (∀ e ∈ ext1.E, ¬ u.Inserts e → e ∈ curExt.E ∧ e2i1 e = e2i e) ∧
    (∀ e ∈ ext1.E, u.Inserts e → nf ≤ e2i1 e) := by
  cases u with
  | delete e =>
    dsimp only [translateUpdate, MGraph.applyUpdate, MGraph.UpdateIsValid] at hU ⊢
    have he' : e2i e ∈ curInt.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i hU
    have hE1 : curInt.E.erase (e2i e) = (curExt.E.erase e).image e2i := by
      ext x
      simp only [Finset.mem_erase, hF.hE, Finset.mem_image]
      constructor
      · rintro ⟨hne, a, ha, rfl⟩
        exact ⟨a, ⟨fun hae => hne (by rw [hae]), ha⟩, rfl⟩
      · rintro ⟨a, ⟨hane, ha⟩, rfl⟩
        refine ⟨fun heq => hane ?_, a, ha, rfl⟩
        have := congrArg i2e heq
        rwa [hF.hLeft a ha, hF.hLeft e hU] at this
    refine ⟨{
      hV := hF.hV
      hE := hE1
      hLeft := fun a ha => hF.hLeft a (Finset.mem_of_mem_erase ha)
      hRight := fun x hx =>
        let hx' := hF.hRight x (Finset.mem_of_mem_erase hx)
        ⟨hx'.1, Finset.mem_erase.mpr ⟨fun heq =>
          (Finset.mem_erase.mp hx).1 (by rw [← hx'.1, heq]), hx'.2⟩⟩
      hTail := fun a ha => hF.hTail a (Finset.mem_of_mem_erase ha)
      hHead := fun a ha => hF.hHead a (Finset.mem_of_mem_erase ha)
      hLtFresh := fun x hx => hF.hLtFresh x (Finset.mem_of_mem_erase hx) },
      he', le_refl nf, (fun _ _ => rfl), (fun _ hu => by cases hu),
      (fun _ ha _ => ⟨Finset.mem_of_mem_erase ha, rfl⟩), (fun _ _ hu => by cases hu)⟩
  | insert e a b =>
    dsimp only [translateUpdate, MGraph.applyUpdate, MGraph.UpdateIsValid] at hU ⊢
    rcases hU with ⟨heNot, haV, hbV⟩
    have hnfNot : nf ∉ curInt.E := fun hm => lt_irrefl nf (hF.hLtFresh nf hm)
    have hE1 : insert nf curInt.E = (insert e curExt.E).image (Function.update e2i e nf) := by
      ext x
      simp only [Finset.mem_insert, hF.hE, Finset.mem_image]
      constructor
      · rintro (rfl | ⟨y, hy, rfl⟩)
        · exact ⟨e, Or.inl rfl, by simp⟩
        · have hne : y ≠ e := fun h => heNot (h ▸ hy)
          exact ⟨y, Or.inr hy, by simp [Function.update, hne]⟩
      · rintro ⟨y, rfl | hy, rfl⟩
        · left; simp
        · right
          have hne : y ≠ e := fun h => heNot (h ▸ hy)
          exact ⟨y, hy, by simp [Function.update, hne]⟩
    refine ⟨{
      hV := hF.hV
      hE := hE1
      hLeft := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · simp
        · have hne : x ≠ e := fun h => heNot (h ▸ hx')
          have hxInt : e2i x ∈ curInt.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i hx'
          have hne_nf : e2i x ≠ nf := ne_of_lt (hF.hLtFresh _ hxInt)
          simp [Function.update, hne, hne_nf, hF.hLeft x hx']
      hRight := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact ⟨by simp, by simp⟩
        · have hne_nf : x ≠ nf := ne_of_lt (hF.hLtFresh x hx')
          obtain ⟨heq, hxExt⟩ := hF.hRight x hx'
          have hne_e : i2e x ≠ e := fun h => heNot (h ▸ hxExt)
          simp [Function.update, hne_nf, hne_e, heq, hxExt]
      hTail := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · simp
        · have hne : x ≠ e := fun h => heNot (h ▸ hx')
          have hxInt : e2i x ∈ curInt.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i hx'
          have hne_nf : e2i x ≠ nf := ne_of_lt (hF.hLtFresh _ hxInt)
          simp [Function.update, hne, hne_nf, hF.hTail x hx']
      hHead := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · simp
        · have hne : x ≠ e := fun h => heNot (h ▸ hx')
          have hxInt : e2i x ∈ curInt.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i hx'
          have hne_nf : e2i x ≠ nf := ne_of_lt (hF.hLtFresh _ hxInt)
          simp [Function.update, hne, hne_nf, hF.hHead x hx']
      hLtFresh := fun x hx => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · omega
        · exact lt_trans (hF.hLtFresh x hx') (Nat.lt_succ_self nf) },
      ⟨hnfNot, hF.hV ▸ haV, hF.hV ▸ hbV⟩, Nat.le_succ nf,
      fun x hx => by simp [Function.update, ne_of_lt hx],
      fun x hx => by cases hx; omega,
      fun x hx hno => by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact absurd (by constructor : Update.Inserts x (Update.insert x a b)) hno
        · have hne : x ≠ e := fun h => heNot (h ▸ hx')
          exact ⟨hx', by simp [Function.update, hne]⟩,
      fun x _ hins => by
        cases hins
        simp⟩
  | split v v' St Sh =>
    dsimp only [translateUpdate, MGraph.applyUpdate, MGraph.UpdateIsValid] at hU ⊢
    rcases hU with ⟨hvV, hv'Not, hSE, hEnd⟩
    have hV1 : insert v' curExt.V = insert v' curInt.V := by rw [hF.hV]
    have hStE : St ⊆ curExt.E := Finset.Subset.trans Finset.subset_union_left hSE
    have hShE : Sh ⊆ curExt.E := Finset.Subset.trans Finset.subset_union_right hSE
    have hSInt : St.image e2i ∪ Sh.image e2i ⊆ curInt.E := by
      intro x hx
      rw [← Finset.image_union] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rw [hF.hE]
      exact Finset.mem_image_of_mem e2i (hSE hy)
    have hEndInt : ∀ x ∈ St.image e2i ∪ Sh.image e2i, curInt.tail x = v ∨ curInt.head x = v := by
      intro x hx
      rw [← Finset.image_union] at hx
      rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
      rw [hF.hTail y (hSE hy), hF.hHead y (hSE hy)]
      exact hEnd y hy
    have hmem_t : ∀ a ∈ curExt.E, e2i a ∈ St.image e2i ↔ a ∈ St := by
      intro a ha
      constructor
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨y, hy, heq⟩
        have hya := congrArg i2e heq
        rw [hF.hLeft y (hStE hy), hF.hLeft a ha] at hya
        rwa [← hya]
      · intro hmem; exact Finset.mem_image_of_mem e2i hmem
    have hmem_h : ∀ a ∈ curExt.E, e2i a ∈ Sh.image e2i ↔ a ∈ Sh := by
      intro a ha
      constructor
      · intro hmem
        rcases Finset.mem_image.mp hmem with ⟨y, hy, heq⟩
        have hya := congrArg i2e heq
        rw [hF.hLeft y (hShE hy), hF.hLeft a ha] at hya
        rwa [← hya]
      · intro hmem; exact Finset.mem_image_of_mem e2i hmem
    refine ⟨{
      hV := hV1
      hE := hF.hE
      hLeft := hF.hLeft
      hRight := hF.hRight
      hTail := fun a ha => by
        simp only [hmem_t a ha, hF.hTail a ha]
      hHead := fun a ha => by
        simp only [hmem_h a ha, hF.hHead a ha]
      hLtFresh := hF.hLtFresh },
      ⟨hF.hV ▸ hvV, fun hm => hv'Not (hF.hV ▸ hm), hSInt, hEndInt⟩,
      le_refl nf, (fun _ _ => rfl), (fun _ hu => by cases hu),
      (fun _ ha _ => ⟨ha, rfl⟩), (fun _ _ hu => by cases hu)⟩

lemma translateBatch_preserves :
    ∀ (U : List Update) (curExt curInt : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      FreshInv curExt curInt e2i i2e nf →
      curExt.BatchIsValid U →
      let (extF, e2iF, i2eF, nfF, U') := translateBatch curExt e2i i2e nf U
      extF = curExt.applyBatch U ∧
      FreshInv extF (curInt.applyBatch U') e2iF i2eF nfF ∧
      curInt.BatchIsValid U' ∧
      NoBatchReinsert curInt U' ∧
      U'.length = U.length ∧
      nf ≤ nfF ∧
      (∀ u' ∈ U', ∀ e', u'.Inserts e' → nf ≤ e' ∧ e' < nfF) ∧
      (∀ e' < nf, i2eF e' = i2e e') ∧
      (∀ e ∈ extF.E, (∀ u ∈ U, ¬ u.Inserts e) →
        e ∈ curExt.E ∧ e2iF e = e2i e ∧ ∀ u' ∈ U', ¬ u'.Inserts (e2i e)) ∧
      (∀ e ∈ extF.E, (∃ u ∈ U, u.Inserts e) → nf ≤ e2iF e) := by
  intro U
  induction U with
  | nil =>
    intro curExt curInt e2i i2e nf hF _
    refine ⟨rfl, hF, trivial, (fun _ _ _ hu => by cases hu), rfl, le_refl nf,
      (fun _ hm _ _ => by simp at hm), (fun _ _ => rfl),
      (fun _ he _ => ⟨he, rfl, fun _ hm _ => by simp at hm⟩),
      (fun _ _ ⟨_, hm, _⟩ => by simp at hm)⟩
  | cons u rest ih =>
    intro curExt curInt e2i i2e nf hF hB
    rcases hB with ⟨hU, hRest⟩
    have h1 := translateUpdate_preserves hF hU
    dsimp only at h1
    rcases h1 with ⟨hF1, hU', hnf1, hi2e1, hIns1, hNoIns1, hYesIns1⟩
    set tu := translateUpdate curExt e2i i2e nf u
    have htu1 : tu.1 = curExt.applyUpdate u := by cases u <;> rfl
    have h2 := ih tu.1 (curInt.applyUpdate tu.2.2.2.2) tu.2.1 tu.2.2.1 tu.2.2.2.1 hF1
      (htu1 ▸ hRest)
    dsimp only [translateBatch]
    rcases h2 with ⟨hExt, hF2, hB2, _, hLen2, hnf2, hIns2, hi2e2, hNoIns2, hYesIns2⟩
    have hExt' : (translateBatch tu.1 tu.2.1 tu.2.2.1 tu.2.2.2.1 rest).1 =
        (curExt.applyUpdate u).applyBatch rest := by rw [← htu1]; exact hExt
    have hInsAll : ∀ u' ∈ tu.2.2.2.2 :: (translateBatch tu.1 tu.2.1 tu.2.2.1 tu.2.2.2.1 rest).2.2.2.2,
        ∀ e', u'.Inserts e' →
          nf ≤ e' ∧ e' < (translateBatch tu.1 tu.2.1 tu.2.2.1 tu.2.2.2.1 rest).2.2.2.1 := by
      intro u' hu' e' he'
      simp only [List.mem_cons] at hu'
      rcases hu' with rfl | hu'_rest
      · exact ⟨(hIns1 e' he').1, lt_of_lt_of_le (hIns1 e' he').2 hnf2⟩
      · exact ⟨le_trans hnf1 (hIns2 u' hu'_rest e' he').1, (hIns2 u' hu'_rest e' he').2⟩
    have hNR : NoBatchReinsert curInt
        (tu.2.2.2.2 :: (translateBatch tu.1 tu.2.1 tu.2.2.1 tu.2.2.2.1 rest).2.2.2.2) := by
      intro e' he' u' hu' hIns
      have := (hInsAll u' hu' e' hIns).1
      exact absurd (hF.hLtFresh e' he') (by omega)
    refine ⟨by simpa [tu, MGraph.applyBatch] using hExt',
      by simpa [tu, MGraph.applyBatch] using hF2,
      ⟨hU', hB2⟩, hNR, by simp [tu, hLen2], le_trans hnf1 hnf2, hInsAll,
      fun e' he' => by rw [hi2e2 e' (lt_of_lt_of_le he' hnf1), hi2e1 e' he'],
      fun e he hno => ?_, fun e he ⟨v, hv, hIns_v⟩ => ?_⟩
    · have hno_rest : ∀ v ∈ rest, ¬ v.Inserts e := fun v hv => hno v (List.mem_cons_of_mem u hv)
      obtain ⟨he_tu1, he2i_eq2, _⟩ := hNoIns2 e he hno_rest
      obtain ⟨he_pre, he2i_eq1⟩ := hNoIns1 e he_tu1 (hno u List.mem_cons_self)
      refine ⟨he_pre, he2i_eq2.trans he2i_eq1, fun u' hu' hIns => ?_⟩
      have he'_int : e2i e ∈ curInt.E := by rw [hF.hE]; exact Finset.mem_image_of_mem e2i he_pre
      exact hNR (e2i e) he'_int u' hu' hIns
    · by_cases hRestIns : ∃ w ∈ rest, w.Inserts e
      · exact le_trans hnf1 (hYesIns2 e he hRestIns)
      · push Not at hRestIns
        simp only [List.mem_cons] at hv
        rcases hv with rfl | hv_rest
        · obtain ⟨he_tu1, he2i_eq2, _⟩ := hNoIns2 e he hRestIns
          rw [he2i_eq2]
          exact hYesIns1 e he_tu1 hIns_v
        · exact absurd hIns_v (hRestIns v hv_rest)

end FreshTranslation

section Algorithm2Def

/-- Game weight bound `Ψ_game = 2 ⌈Ψ⌉₊ + ⌈log₂ (M₀ + 1)⌉ + 1`, an integer at least
`(Ψ + log(M₀ + 1)) / log 2 + 1` (`alg2PsiGame_real_le`), ensuring `WeightValid Ψ_game ‖w^{(t)}‖₁`
at every hidden-stable stage (`0 < α`). It is `O(Ψ + log M₀)` (`alg2PsiGame_le`). -/
noncomputable def alg2PsiGame (Ψ : ℝ) (M₀ : ℕ) : ℝ :=
  ((2 * ⌈Ψ⌉₊ + Nat.clog 2 (M₀ + 1) + 1 : ℕ) : ℝ)

lemma alg2PsiGame_ge_one (Ψ : ℝ) (M₀ : ℕ) : 1 ≤ alg2PsiGame Ψ M₀ := by
  unfold alg2PsiGame; exact_mod_cast Nat.le_add_left 1 _

/-- Game stretch threshold `σ_game = max 0 (σ_mwu N₀)`. -/
noncomputable def alg2SigmaGame (σ_mwu : ℕ → ℝ) (N₀ : ℕ) : ℝ :=
  max 0 (σ_mwu N₀)

/-- Total worst-case stretch cap `σ_tot = max (TP.σ k N₀) (LP.σ_last N₀)`. -/
noncomputable def alg2SigmaTot (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (N₀ : ℕ) : ℝ :=
  max (TP.σ P.k N₀) (LP.σ_last N₀)

/-- Total worst-case stretch cap with last-level vertex bound `N_last`:
`max (TP.σ k N₀) (LP.σ_last N_last)`. -/
noncomputable def alg2SigmaTotAt (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (N₀ N_last : ℕ) : ℝ :=
  max (TP.σ P.k N₀) (LP.σ_last N_last)

/-- Total worst-case stretch cap evaluating the last level at its own level-`d` size bound
`levelM TP P P.d + 1` (`jtree.tex` lines 207–222). -/
noncomputable def alg2SigmaTotOwn (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (N₀ : ℕ) : ℝ :=
  alg2SigmaTotAt TP LP P N₀ (levelM TP P P.d + 1)

/-- Explicit quality constant `κ` of **Theorem 5.1** / **Lemma 6.3**. -/
noncomputable def alg2Kappa (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (σ_mwu : ℕ → ℝ) (N₀ : ℕ) : ℝ :=
  kappaBound P.d (TP.γ_ℓ (P.M₀ ^ 2)) (alg2SigmaTot TP LP P N₀) (alg2SigmaGame σ_mwu N₀)

/-- Explicit quality constant `κ` with last-level vertex bound `N_last`. -/
noncomputable def alg2KappaAt (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (σ_mwu : ℕ → ℝ) (N₀ N_last : ℕ) : ℝ :=
  kappaBound P.d (TP.γ_ℓ (P.M₀ ^ 2)) (alg2SigmaTotAt TP LP P N₀ N_last) (alg2SigmaGame σ_mwu N₀)

/-- Explicit quality constant `κ` evaluating the last level at `levelM TP P P.d + 1`. -/
noncomputable def alg2KappaOwn (TP : SparseCoreParams) (LP : LastLevelParams)
    (P : ChainParams) (σ_mwu : ℕ → ℝ) (N₀ : ℕ) : ℝ :=
  alg2KappaAt TP LP P σ_mwu N₀ (levelM TP P P.d + 1)

/-- `Game.lemma_7_3_prefix`'s upper bound `(10 Ψ_g k)^{i+1} + ∑_{i' ≤ i} r_{i'} (10 Ψ_g k)^{i+1-i'}`
for level `i ≤ P.d`. -/
noncomputable def gameShiftBound (P : ChainParams) (Ψ_g : ℝ)
    (reb : ℕ → ℕ) (i : ℕ) : ℝ :=
  (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1) +
    ∑ i' ∈ Finset.range (i + 1),
      (reb i' : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - i')

lemma gameShiftBound_eq_game (P : ChainParams) (Ψ_g : ℝ)
    (reb : ℕ → ℕ) (i : Fin (P.d + 1)) :
    gameShiftBound P Ψ_g reb i.val =
      (10 * Ψ_g * (P.k : ℝ)) ^ (i.val + 1) +
        ∑ i' ∈ Finset.Iic i,
          (reb i'.val : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i.val + 1 - i'.val) := by
  unfold gameShiftBound
  congr 1
  have hbij : ∑ i' ∈ Finset.Iic i,
      (reb i'.val : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i.val + 1 - i'.val) =
      ∑ j ∈ Finset.range (i.val + 1),
        (reb j : ℝ) * (10 * Ψ_g * (P.k : ℝ)) ^ (i.val + 1 - j) := by
    refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
    · intro j hj
      have hjv : j ≤ i := Finset.mem_Iic.mp hj
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Fin.le_def.mp hjv))
    · intro a _ b _ h; exact Fin.ext h
    · intro j hj
      have hjv : j ≤ i.val := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      exact ⟨⟨j, lt_of_le_of_lt hjv i.isLt⟩, Finset.mem_Iic.mpr hjv, rfl⟩
    · intro _ _; rfl
  exact hbij.symm

lemma gameShiftBound_mono_reb {P : ChainParams} {Ψ_g : ℝ} (hΨ : 1 ≤ Ψ_g)
    {reb₁ reb₂ : ℕ → ℕ} (hle : ∀ j, reb₁ j ≤ reb₂ j) (i : ℕ) :
    gameShiftBound P Ψ_g reb₁ i ≤ gameShiftBound P Ψ_g reb₂ i := by
  unfold gameShiftBound
  refine add_le_add le_rfl (Finset.sum_le_sum fun j _ => ?_)
  have hk0 : (0 : ℝ) ≤ (10 * Ψ_g * (P.k : ℝ)) ^ (i + 1 - j) := by
    have : 0 ≤ (10 * Ψ_g * (P.k : ℝ)) := by positivity
    positivity
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle j) hk0

/-- Fixed parameters configuring Algorithm 2 (data only; no proof obligations). -/
structure Alg2Config where
  T : SparseCoreRestartTool
  L : LastLevelTool
  TP : SparseCoreParams
  LP : LastLevelParams
  P : ChainParams
  σ_mwu : ℕ → ℝ
  N₀ : ℕ
  α : ℝ
  Ψ : ℝ
  ε : ℝ

/-- Validity hypotheses of `Alg2Config` requiring **only** `SparseCoreRestartTool.IsSpecRestartNoHidden`
(used for unconditional preservation of invariants, `Query`, `Detect`, and worst-case bounds). -/
structure Alg2Config.ValidNoHidden (cfg : Alg2Config) : Prop where
  hTP : cfg.TP.Valid
  hLP : cfg.LP.Valid
  hT : cfg.T.IsSpecRestartNoHidden cfg.TP
  hL : cfg.L.IsSpec cfg.LP
  hσ_mwu_mono : ∀ n₁ n₂, n₁ ≤ n₂ → cfg.σ_mwu n₁ ≤ cfg.σ_mwu n₂
  hσ_mwu_nn : 0 ≤ cfg.σ_mwu cfg.N₀
  hMWU : cfg.T.ToolMWURestartNoHidden cfg.σ_mwu
  hEmb : cfg.T.ToolEmbedsSurvivingRestartNoHidden
  hNoReins : cfg.T.ToolNoReinsertRestartNoHidden
  hγM₀ : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.M₀
  hγk : cfg.TP.γ_ℓ (cfg.P.M₀ ^ 2) ≤ cfg.P.k
  hα : 0 < cfg.α

/-- Full state of Algorithm 2: Algorithm 1's `ChainState`, Game-shadowed `branD` & `passes`,
external graph & fresh edge-ID translation maps, LCT flow/detect accumulators, and LCT /
large-batch cost counters. -/
structure Alg2State (cfg : Alg2Config) where
  chain : ChainState cfg.T cfg.P
  branD : ℕ
  passes : Fin (cfg.P.d + 1) → ℕ
  extG : MGraph
  extToInt : ℕ → ℕ
  intToExt : ℕ → ℕ
  nextFresh : ℕ
  extℓ : ℕ → ℝ
  extg : ℕ → ℝ
  flow : ℕ → ℝ
  detectAccum : ℕ → ℝ
  lctUpdateOps : ℕ
  lctDetectOps : ℕ
  largeBatchEnc : ℝ
  /-- Number of `Update` calls so far. Ghost state: no program reads it. -/
  updateCount : ℕ := 0

/-- Construct `Game.GameParams` corresponding to `(cfg : Alg2Config)`. -/
noncomputable def Alg2Config.gameParams (cfg : Alg2Config) : Game.GameParams where
  d := cfg.P.d
  k := cfg.P.k
  Ψ := alg2PsiGame cfg.Ψ cfg.P.M₀
  σ := alg2SigmaGame cfg.σ_mwu cfg.N₀
  hd := cfg.P.hd
  hk := cfg.P.hk
  hΨ := alg2PsiGame_ge_one cfg.Ψ cfg.P.M₀

/-- Initialize Algorithm 2 on `(G₀, g₀, ℓ₀)`. -/
noncomputable def algorithm2_init (cfg : Alg2Config)
    (G₀ : MGraph) (g₀ ℓ₀ : ℕ → ℝ) : Alg2State cfg :=
  { chain := (algorithm1_initialize cfg.T cfg.L cfg.P (levelM cfg.TP cfg.P) cfg.N₀ G₀ ℓ₀ g₀).1
    branD := 0
    passes := fun _ => 0
    extG := G₀
    extToInt := id
    intToExt := id
    nextFresh := G₀.E.sup id + 1
    extℓ := ℓ₀
    extg := g₀
    flow := fun _ => 0
    detectAccum := fun _ => 0
    lctUpdateOps := G₀.m
    lctDetectOps := 0
    largeBatchEnc := 0 }

/-- Detect the smallest level `i < cfg.P.d` whose `rebuildCount` increased, if any. -/
def firstRebuiltLevel (d : ℕ) (oldReb newReb : ℕ → ℕ) : Option ℕ :=
  (List.range d).find? fun j => decide (oldReb j < newReb j)

/-- Select the largest level `i : Fin (cfg.P.d + 1)` with `(passes i : ℝ) < 2 * Ψ_g`. -/
noncomputable def findEligibleLevel (d : ℕ) (Ψ_g : ℝ)
    (passes : Fin (d + 1) → ℕ) : Option (Fin (d + 1)) :=
  let elig : Finset (Fin (d + 1)) := Finset.univ.filter fun i => (passes i : ℝ) < 2 * Ψ_g
  if h : elig.Nonempty then some (elig.max' h) else none

lemma findEligibleLevel_spec {d : ℕ} {Ψ_g : ℝ} {passes : Fin (d + 1) → ℕ}
    {i : Fin (d + 1)} (h : findEligibleLevel d Ψ_g passes = some i) :
    (passes i : ℝ) < 2 * Ψ_g ∧
      ∀ j : Fin (d + 1), (passes j : ℝ) < 2 * Ψ_g → j ≤ i := by
  unfold findEligibleLevel at h
  dsimp only at h
  split_ifs at h with hne
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨(Finset.mem_filter.mp (Finset.max'_mem _ hne)).2, fun j hj =>
      Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)⟩

lemma findEligibleLevel_none_iff {d : ℕ} {Ψ_g : ℝ} {passes : Fin (d + 1) → ℕ} :
    findEligibleLevel d Ψ_g passes = none ↔
      ∀ i : Fin (d + 1), 2 * Ψ_g ≤ (passes i : ℝ) := by
  unfold findEligibleLevel
  dsimp only
  split_ifs with hne
  · constructor
    · intro h; simp at h
    · intro hall
      obtain ⟨i, hi⟩ := hne
      have := (Finset.mem_filter.mp hi).2
      exact absurd (hall i) (not_le.mpr this)
  · constructor
    · intro _ i
      by_contra hlt
      exact hne ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, not_le.mp hlt⟩⟩
    · intro _; rfl

/-- Remainder helper proving termination of `algorithm2_loop` on arbitrary inputs. -/
noncomputable def shiftRemainingBudget {T : SparseCoreRestartTool} (P : ChainParams) (Ψ_g : ℝ)
    (ch : ChainState T P) : ℕ :=
  ∑ j : Fin (P.d + 1), (Nat.floor (gameShiftBound P Ψ_g ch.rebuildCount j.val) - ch.shiftCount j.val)

lemma shiftRemainingBudget_lt_of_step {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} {Ψ_g : ℝ} (ch : ChainState T P) (i : Fin (P.d + 1))
    (hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound P Ψ_g ch.rebuildCount i.val) :
    let ch' := (algorithm1_shift T L P ch i.val).1
    shiftRemainingBudget P Ψ_g ch' < shiftRemainingBudget P Ψ_g ch := by
  set ch' := (algorithm1_shift T L P ch i.val).1
  have hRebEq : ch'.rebuildCount = ch.rebuildCount := by
    dsimp only [ch', algorithm1_shift]
    split_ifs <;> rfl
  have hShEq : ch'.shiftCount =
      fun j => if j = i.val then ch.shiftCount i.val + 1 else ch.shiftCount j := by
    dsimp only [ch', algorithm1_shift]
    split_ifs with hi
    · rfl
    · have hieq : i.val = P.d := by have := i.isLt; omega
      funext j
      simp [hieq]
  have hle_floor : ch.shiftCount i.val + 1 ≤
      Nat.floor (gameShiftBound P Ψ_g ch.rebuildCount i.val) := by
    refine Nat.le_floor ?_
    exact_mod_cast hCap
  dsimp only
  unfold shiftRemainingBudget
  rw [hRebEq]
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · rw [hShEq]
    dsimp only
    by_cases hji : j.val = i.val
    · rw [ite_eq_left_iff.mpr (fun h => absurd hji h), hji]
      omega
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hji)]
  · rw [hShEq]
    dsimp only
    rw [ite_eq_left_iff.mpr (fun h => absurd rfl h)]
    omega

/-- Inner shift loop of **Algorithm 2** (`jtree.tex` lines 757–772), parameterized by the
acceptance quality threshold `κ`. -/
noncomputable def algorithm2_loopWith (cfg : Alg2Config) (κ : ℝ) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    ChainState cfg.T cfg.P × ℕ × (Fin (cfg.P.d + 1) → ℕ) × ℕ × Option (ℕ → ℝ) :=
  let Ψ_g := alg2PsiGame cfg.Ψ cfg.P.M₀
  let fc := algorithm1_findCycle ch
  let Δ_ext := liftEdgeFn extG e2i fc.1
  let offTree := (walkEdges fc.2.1 \ ch.toTreeChain.chainTree.E).card
  let lctOps' := lctOps + 2 * (offTree + 1)
  if _hGood : extG.inner g' Δ_ext / extG.lnorm ℓ' Δ_ext ≤ -(κ * cfg.α) then
    (ch, branD, passes, lctOps', some Δ_ext)
  else
    match _hElig : findEligibleLevel cfg.P.d Ψ_g passes with
    | none => (ch, branD, passes, lctOps', none)
    | some i =>
      if hCap : (ch.shiftCount i.val : ℝ) + 1 ≤ gameShiftBound cfg.P Ψ_g ch.rebuildCount i.val then
        let curB := if i.val < cfg.P.d then ch.bran i.val else branD
        let wrapped := (curB + 1) % cfg.P.k = 0
        let ch' := (algorithm1_shift cfg.T cfg.L cfg.P ch i.val).1
        let branD' := if i.val < cfg.P.d then 0 else (branD + 1) % cfg.P.k
        let passes' : Fin (cfg.P.d + 1) → ℕ := fun j =>
          if i < j then 0
          else if j = i then (if wrapped then passes i + 1 else passes i)
          else passes j
        algorithm2_loopWith cfg κ extG e2i g' ℓ' ch' branD' passes' lctOps'
      else
        (ch, branD, passes, lctOps', none)
termination_by shiftRemainingBudget cfg.P (alg2PsiGame cfg.Ψ cfg.P.M₀) ch
decreasing_by
  simpa using shiftRemainingBudget_lt_of_step ch i hCap

/-- Inner shift loop of **Algorithm 2** (`jtree.tex` lines 757–772) using `alg2Kappa` at `cfg.N₀`. -/
noncomputable def algorithm2_loop (cfg : Alg2Config) (extG : MGraph) (e2i : ℕ → ℕ)
    (g' ℓ' : ℕ → ℝ) (ch : ChainState cfg.T cfg.P) (branD : ℕ)
    (passes : Fin (cfg.P.d + 1) → ℕ) (lctOps : ℕ) :
    ChainState cfg.T cfg.P × ℕ × (Fin (cfg.P.d + 1) → ℕ) × ℕ × Option (ℕ → ℝ) :=
  algorithm2_loopWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
    extG e2i g' ℓ' ch branD passes lctOps

/-- **Algorithm 2 `Update(U, g', ℓ', η)`**, parameterized by quality threshold `κ`. -/
noncomputable def algorithm2_updateWith (cfg : Alg2Config) (κ : ℝ) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    Alg2State cfg × Option (ℕ → ℝ) :=
  let (extG', e2i', i2e', nf', U_int) :=
    translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
  let ℓ_int := fun e' => ℓ' (i2e' e')
  let g_int := fun e' => g' (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  let (branD1, passes1) :=
    match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar =>
      (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let (chEnd, branDEnd, passesEnd, lctOpsEnd, optΔ) :=
    algorithm2_loopWith cfg κ extG' e2i' g' ℓ' ch1 branD1 passes1 (st.lctUpdateOps + U_ext.length)
  let encOverflow := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
  match optΔ with
  | none =>
    ({ st with
        chain := chEnd
        branD := branDEnd
        passes := passesEnd
        extG := extG'
        extToInt := e2i'
        intToExt := i2e'
        nextFresh := nf'
        extℓ := ℓ'
        extg := g'
        lctUpdateOps := lctOpsEnd
        largeBatchEnc := encOverflow
        updateCount := st.updateCount + 1 }, none)
  | some Δ =>
    let inc : ℕ → ℝ := fun e =>
      if e ∈ extG'.E then -(η / extG'.inner g' Δ) * Δ e else 0
    ({ chain := chEnd
       branD := branDEnd
       passes := passesEnd
       extG := extG'
       extToInt := e2i'
       intToExt := i2e'
       nextFresh := nf'
       extℓ := ℓ'
       extg := g'
       flow := fun e => st.flow e + inc e
       detectAccum := fun e => st.detectAccum e + |inc e|
       lctUpdateOps := lctOpsEnd
       lctDetectOps := st.lctDetectOps
       largeBatchEnc := encOverflow
       updateCount := st.updateCount + 1 }, some Δ)

/-- **Algorithm 2 `Update(U, g', ℓ', η)`** (`alg:rebuildScheduleForDS`, `jtree.tex` lines 747–778):
translates `U` via fresh internal IDs, invokes Algorithm 1's `Update`, synchronizes rebuild
resets on `(branD, passes)`, runs `algorithm2_loop`, and updates LCT flow and `Detect`
accumulators upon returning a cycle. -/
noncomputable def algorithm2_update (cfg : Alg2Config) (st : Alg2State cfg)
    (U_ext : List Update) (g' ℓ' : ℕ → ℝ) (η : ℝ) :
    Alg2State cfg × Option (ℕ → ℝ) :=
  let (extG', e2i', i2e', nf', U_int) :=
    translateBatch st.extG st.extToInt st.intToExt st.nextFresh U_ext
  let ℓ_int := fun e' => ℓ' (i2e' e')
  let g_int := fun e' => g' (i2e' e')
  let ch1 := (algorithm1_update cfg.T cfg.L cfg.TP cfg.P cfg.N₀ st.chain U_int g_int ℓ_int).1
  let (branD1, passes1) :=
    match firstRebuiltLevel cfg.P.d st.chain.rebuildCount ch1.rebuildCount with
    | none => (st.branD, st.passes)
    | some iStar =>
      (0, fun j : Fin (cfg.P.d + 1) => if iStar ≤ j.val then 0 else st.passes j)
  let (chEnd, branDEnd, passesEnd, lctOpsEnd, optΔ) :=
    algorithm2_loopWith cfg (alg2Kappa cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)
      extG' e2i' g' ℓ' ch1 branD1 passes1 (st.lctUpdateOps + U_ext.length)
  let encOverflow := st.largeBatchEnc + largeBatchEncCap cfg.P U_int
  match optΔ with
  | none =>
    ({ st with
        chain := chEnd
        branD := branDEnd
        passes := passesEnd
        extG := extG'
        extToInt := e2i'
        intToExt := i2e'
        nextFresh := nf'
        extℓ := ℓ'
        extg := g'
        lctUpdateOps := lctOpsEnd
        largeBatchEnc := encOverflow
        updateCount := st.updateCount + 1 }, none)
  | some Δ =>
    let inc : ℕ → ℝ := fun e =>
      if e ∈ extG'.E then -(η / extG'.inner g' Δ) * Δ e else 0
    ({ chain := chEnd
       branD := branDEnd
       passes := passesEnd
       extG := extG'
       extToInt := e2i'
       intToExt := i2e'
       nextFresh := nf'
       extℓ := ℓ'
       extg := g'
       flow := fun e => st.flow e + inc e
       detectAccum := fun e => st.detectAccum e + |inc e|
       lctUpdateOps := lctOpsEnd
       lctDetectOps := st.lctDetectOps
       largeBatchEnc := encOverflow
       updateCount := st.updateCount + 1 }, some Δ)

/-- **Algorithm 2 `Query(e)`**: reads the maintained flow on edge `e`. -/
def algorithm2_query (cfg : Alg2Config) (st : Alg2State cfg) (e : ℕ) : ℝ :=
  st.flow e

/-- **Algorithm 2 `Detect()`**: returns edges in `st.extG` with `ε ≤ extℓ e * detectAccum e`,
resetting `detectAccum` on the reported edges. -/
noncomputable def algorithm2_detect (cfg : Alg2Config) (st : Alg2State cfg) :
    Finset ℕ × Alg2State cfg :=
  let S := st.extG.E.filter fun e => cfg.ε ≤ st.extℓ e * st.detectAccum e
  (S, { st with
    detectAccum := fun e => if e ∈ S then 0 else st.detectAccum e
    lctDetectOps := st.lctDetectOps + S.card + 1 })

/-- Package Algorithm 2 with quality threshold `κ` as a `MinRatioFailDataStructure`. -/
noncomputable def algorithm2_dsWith (cfg : Alg2Config) (κ : ℝ) : MinRatioFailDataStructure where
  State := Alg2State cfg
  init := fun G₀ g₀ ℓ₀ => algorithm2_init cfg G₀ g₀ ℓ₀
  update := fun st U g' ℓ' η => algorithm2_updateWith cfg κ st U g' ℓ' η
  query := fun st e => algorithm2_query cfg st e
  detect := fun st => algorithm2_detect cfg st

/-- Package Algorithm 2 as a `MinRatioFailDataStructure` using `alg2Kappa`. -/
noncomputable def algorithm2_ds (cfg : Alg2Config) : MinRatioFailDataStructure where
  State := Alg2State cfg
  init := fun G₀ g₀ ℓ₀ => algorithm2_init cfg G₀ g₀ ℓ₀
  update := fun st U g' ℓ' η => algorithm2_update cfg st U g' ℓ' η
  query := fun st e => algorithm2_query cfg st e
  detect := fun st => algorithm2_detect cfg st

/-- Package Algorithm 2 as a `MinRatioFailDataStructure` using `alg2KappaOwn` (evaluating level
`d` at `levelM cfg.TP cfg.P cfg.P.d + 1`). -/
noncomputable def algorithm2_dsOwn (cfg : Alg2Config) : MinRatioFailDataStructure :=
  algorithm2_dsWith cfg (alg2KappaOwn cfg.TP cfg.LP cfg.P cfg.σ_mwu cfg.N₀)

end Algorithm2Def

end MinCostFlow.Chain
