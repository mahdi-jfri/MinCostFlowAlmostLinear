module

public import MinCostFlow.SparseCore.Program.AssemblyModel
public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts
public import MinCostFlow.SparseCore.Program.RestartModelState
public import MinCostFlow.SparseCore.LSFInit

import MinCostFlow.DynSpanner.Invariant
import MinCostFlow.DynSpanner.Program.CanonicalSparsify

/-!
# Branch update-count predicate and run embedding from `SparseCoreOrdInput` (`AssemblyInputRun`)

Defines `BranchUpdatesBelow impl tr n`, the per-bucket spanner deletion/split history invariant
relative to the cumulative input update count `n ≤ updateThreshold k M N`, proves
`batchWithinCaps_applyBatch` (preservation of vertex/edge cap bounds across a valid batch), and
proves `sparseCoreOrdInput_exists_run`, embedding any `SparseCoreOrdInput` state into a valid
`(DynamicInstance, ordSeq, restarts, τ)` run of `runOrdAfterRestarts`.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.LSF
open MinCostFlow.SparseCore.Program.Restart

/-! ## Public update-count predicate for the branch interface -/

/-- **Model update-count invariant for a branch** (`step_runs` / `init_runs` of `AsmBranchAt`).
For a branch state `tr` reached after `n` input updates (with arbitrary restarts in between; each
restart resets active bucket spanners to `t = 0`), every component `C ∈ components tr.cs.G₀` and
bucket `b : ℤ` has:
* a valid initial spanner graph `G₀ := tr.initBunG (C, b)` with `G₀.m ≤ tr.m₀` and `G₀.n ≤ 2 * G₀.m`;
* a valid history `us : List Update` of deletions and splits from `G₀` reaching `tr.dyn (C, b)` via
  `DynSpanner.runState` with `us.length = (tr.dyn (C, b)).t`;
* cumulative vertex growth `(tr.dyn (C, b)).G.n - G₀.n = batchSplitCount us ≤ tr.splitBound` and
  `((batchSplitCount us : ℕ) : ℝ) ≤ 112 * (n : ℝ) * (Real.log ((tr.n₀ : ℝ) + 2)) ^ 2`;
* cumulative deletions `us.countP deleteTag = G₀.m - (tr.dyn (C, b)).G.m ≤ n`;
* hence `(tr.dyn (C, b)).t ≤ n + ((tr.dyn (C, b)).G.n - G₀.n)` and
  `(tr.dyn (C, b)).t ≤ tr.m₀ + tr.splitBound`. -/
def BranchUpdatesBelow {depth : ℕ} (impl : SparsifyImpl) (tr : BundleTreeState depth) (n : ℕ) :
    Prop :=
  ((n : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold tr.k tr.m₀ tr.n₀ ∧
  ∀ C ∈ components tr.cs.G₀, ∀ b : ℤ,
    let G₀ := tr.initBunG (C, b)
    let st := tr.dyn (C, b)
    G₀.IsValid ∧ G₀.m ≤ tr.m₀ ∧ G₀.n ≤ 2 * G₀.m ∧
    G₀.n ≤ st.G.n ∧ st.G.m ≤ G₀.m ∧
    st.G.n - G₀.n ≤ tr.splitBound ∧
    (((st.G.n - G₀.n : ℕ) : ℝ) ≤ 112 * (n : ℝ) * (Real.log ((tr.n₀ : ℝ) + 2)) ^ 2) ∧
    st.t ≤ n + (st.G.n - G₀.n) ∧
    st.t ≤ tr.m₀ + tr.splitBound ∧
    ∃ us : List Update,
      G₀.BatchIsValid us ∧
      (∀ u ∈ us, isDelOrSplit u) ∧
      us.length = st.t ∧
      batchSplitCount us = st.G.n - G₀.n ∧
      us.countP deleteTag = G₀.m - st.G.m ∧
      us.countP deleteTag ≤ n ∧
      st = DynSpanner.runState (L := depth) G₀ (phaseBase (G₀.n + tr.splitBound) depth)
        (canonicalSparsify impl) us us.length

/-- Applying a batch satisfying `BatchWithinCaps vCap eCap U` preserves vertex bounds `< vCap` and
edge bounds `< eCap`. -/
theorem batchWithinCaps_applyBatch {vCap eCap : ℕ} :
    ∀ {G : MGraph} {U : List Update},
      BatchWithinCaps vCap eCap U →
      (∀ x ∈ G.V, x < vCap) → (∀ e ∈ G.E, e < eCap) →
      (∀ x ∈ (G.applyBatch U).V, x < vCap) ∧ (∀ e ∈ (G.applyBatch U).E, e < eCap)
  | _, [], _, hv, he => ⟨hv, he⟩
  | G, u :: U, hcap, hv, he => by
    have hu := hcap u List.mem_cons_self
    have hrest : BatchWithinCaps vCap eCap U := fun x hx => hcap x (List.mem_cons_of_mem u hx)
    refine batchWithinCaps_applyBatch (G := G.applyUpdate u) (U := U) hrest ?_ ?_
    · intro x hx
      cases u with
      | insert e a b => exact hv x hx
      | delete e => exact hv x hx
      | split v v' St Sh =>
        simp only [MGraph.applyUpdate, Finset.mem_insert] at hx
        rcases hx with rfl | hx'
        · exact hu
        · exact hv x hx'
    · intro e hmem
      cases u with
      | insert e' a b =>
        simp only [MGraph.applyUpdate, Finset.mem_insert] at hmem
        rcases hmem with rfl | hmem'
        · exact hu
        · exact he e hmem'
      | delete e' =>
        exact he e (Finset.mem_of_mem_erase hmem)
      | split v v' St Sh => exact he e hmem

/-! ## Helper lemmas on deletions/splits and `runState` -/

theorem delOrSplit_counts :
    ∀ (G : MGraph) (us : List Update),
      G.BatchIsValid us → (∀ u ∈ us, isDelOrSplit u) →
      G.n ≤ (G.applyBatch us).n ∧
      (G.applyBatch us).m ≤ G.m ∧
      batchSplitCount us = (G.applyBatch us).n - G.n ∧
      us.countP deleteTag = G.m - (G.applyBatch us).m ∧
      us.length = batchSplitCount us + us.countP deleteTag
  | G, [], _, _ => by simp [MGraph.applyBatch, batchSplitCount]
  | G, u :: us, hBV, hds => by
    obtain ⟨hu, hrest⟩ := hBV
    have hdu := hds u List.mem_cons_self
    have hds' : ∀ x ∈ us, isDelOrSplit x := fun x hx => hds x (List.mem_cons_of_mem u hx)
    obtain ⟨hn_r, hm_r, hsp_r, hdl_r, hlen_r⟩ := delOrSplit_counts (G.applyUpdate u) us hrest hds'
    have hbatch : G.applyBatch (u :: us) = (G.applyUpdate u).applyBatch us := rfl
    rw [hbatch]
    cases u with
    | insert e a b => exact False.elim hdu
    | delete e =>
      have he : e ∈ G.E := hu
      have hn1 : (G.applyUpdate (.delete e)).n = G.n := rfl
      have hm1 : (G.applyUpdate (.delete e)).m + 1 = G.m := by
        change (G.E.erase e).card + 1 = G.E.card
        rw [Finset.card_erase_add_one he]
      simp only [batchSplitCount, isSplit, List.countP_cons, deleteTag, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] at hsp_r hdl_r hlen_r ⊢
      omega
    | split v v' St Sh =>
      have hv' : v' ∉ G.V := hu.2.1
      have hn1 : (G.applyUpdate (.split v v' St Sh)).n = G.n + 1 := by
        change (insert v' G.V).card = G.V.card + 1
        rw [Finset.card_insert_of_notMem hv']
      have hm1 : (G.applyUpdate (.split v v' St Sh)).m = G.m := rfl
      simp only [batchSplitCount, isSplit, List.countP_cons, deleteTag, List.length_cons,
        Bool.false_eq_true, ↓reduceIte] at hsp_r hdl_r hlen_r ⊢
      omega

theorem runState_t_and_G {L : ℕ} (G₀ : MGraph) (q : ℕ)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut) (us : List Update) :
    ∀ k ≤ us.length,
      (DynSpanner.runState (L := L) G₀ q sparsify us k).t = k ∧
      (DynSpanner.runState (L := L) G₀ q sparsify us k).G = G₀.applyBatch (us.take k)
  | 0, _ => by simp [DynSpanner.runState, DynSpanner.init, DynSpanner.initAt, MGraph.applyBatch]
  | k + 1, hk => by
    obtain ⟨ht, hG⟩ := runState_t_and_G G₀ q sparsify us k (by omega)
    have hsome : us[k]? = some (us[k]'(by omega)) := List.getElem?_eq_getElem (by omega)
    have hstep : DynSpanner.runState (L := L) G₀ q sparsify us (k + 1) =
        (DynSpanner.step (DynSpanner.runState (L := L) G₀ q sparsify us k) (us[k]'(by omega))
          sparsify).state := by
      simp [DynSpanner.runState, hsome]
    rw [hstep]
    have htake : us.take (k + 1) = us.take k ++ [us[k]'(by omega)] :=
      List.take_add_one.trans (by simp [hsome])
    rw [htake, applyBatch_append]
    have hsingle : (G₀.applyBatch (us.take k)).applyBatch [us[k]'(by omega)] =
        (G₀.applyBatch (us.take k)).applyUpdate (us[k]'(by omega)) := rfl
    rw [hsingle, ← hG]
    unfold DynSpanner.step
    dsimp only
    split <;> exact ⟨by simp [DynSpanner.initAt, ht], rfl⟩

theorem batchIsValid_of_graphEq {G₁ G₂ : MGraph} {us : List Update}
    (hG : GraphEq G₁ G₂) (hBV : G₁.BatchIsValid us) : G₂.BatchIsValid us := by
  induction us generalizing G₁ G₂ with
  | nil => trivial
  | cons u us ih =>
    obtain ⟨hu, hrest⟩ := hBV
    have hG' : GraphEq (G₁.applyUpdate u) (G₂.applyUpdate u) := by
      cases u with
      | insert e x y =>
        refine ⟨hG.1, by simp [MGraph.applyUpdate, hG.2.1], fun f hf => ?_⟩
        simp only [MGraph.applyUpdate, Finset.mem_insert] at hf ⊢
        rcases hf with rfl | hf'
        · simp
        · by_cases hfe : f = e
          · subst hfe; simp
          · simp [hfe, hG.2.2 f hf']
      | delete e =>
        exact ⟨hG.1, by simp [MGraph.applyUpdate, hG.2.1], fun f hf =>
          hG.2.2 f (Finset.mem_of_mem_erase hf)⟩
      | split v v' St Sh =>
        refine ⟨by simp [MGraph.applyUpdate, hG.1], hG.2.1, fun f hf => ?_⟩
        obtain ⟨ht, hh⟩ := hG.2.2 f hf
        simp [MGraph.applyUpdate, ht, hh]
    refine ⟨?_, ih hG' hrest⟩
    cases u with
    | insert e x y =>
      rcases hu with ⟨he, hx, hy⟩
      exact ⟨by rwa [← hG.2.1], by rwa [← hG.1], by rwa [← hG.1]⟩
    | delete e =>
      change e ∈ G₂.E
      rw [← hG.2.1]
      exact hu
    | split v v' St Sh =>
      rcases hu with ⟨hv, hv', hsub, hinc⟩
      refine ⟨by rwa [← hG.1], by rwa [← hG.1], by rwa [← hG.2.1], fun e he => ?_⟩
      have heE : e ∈ G₁.E := hsub he
      obtain ⟨ht, hh⟩ := hG.2.2 e heE
      rcases hinc e he with h1 | h2
      · exact Or.inl (ht.symm.trans h1)
      · exact Or.inr (hh.symm.trans h2)

/-! ## Embedding `SparseCoreOrdInput` into `runOrdAfterRestarts` -/

private lemma rotation_ext {G : MGraph} {ρ₁ ρ₂ : Rotation G} (h : ρ₁.order = ρ₂.order) :
    ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp only [Rotation.mk.injEq]; exact h

private lemma cast_rot_order {G₁ G₂ : MGraph} (h : G₁ = G₂) (ρ : Rotation G₁) :
    (h ▸ ρ : Rotation G₂).order = ρ.order := by
  cases h; rfl

private lemma cast_rotBatch {G₁ G₂ G₁' G₂' : MGraph} {U₁ U₂ : List Update} {c : ℕ}
    (h1 : G₁ = G₂) (h2 : G₁' = G₂') (hU : U₁ = U₂) (hG1 : G₁' = G₁.applyBatch U₁)
    (ρ : Rotation G₁) (σ : Rotation G₁')
    (hRB : RotationBatch c U₁ ρ (hG1 ▸ σ)) :
    RotationBatch c U₂ (h1 ▸ ρ)
      ((show G₂' = G₂.applyBatch U₂ by subst h1; subst h2; subst hU; exact hG1) ▸ (h2 ▸ σ)) := by
  subst h1; subst h2; subst hU; exact hRB

private lemma runOrdAfterUpdate_congr (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} :
    ∀ t,
      (∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
        ord₁ s = ord₂ s) →
      (∀ s < t, r₁ s = r₂ s) →
      T.runOrdAfterUpdate k M N D₁ ord₁ r₁ t = T.runOrdAfterUpdate k M N D₂ ord₂ r₂ t
  | 0, hD, _ => by
    have h0 := hD 0 le_rfl
    simp [SparseCoreRestartTool.runOrdAfterUpdate, h0.1, h0.2.2.1, h0.2.2.2.1, h0.2.2.2.2]
  | t + 1, hD, hr => by
    have ih := runOrdAfterUpdate_congr T k M N t
      (fun s hs => hD s (Nat.le_succ_of_le hs))
      (fun s hs => hr s (Nat.lt_succ_of_lt hs))
    have ht1 := hD (t + 1) le_rfl
    have hrt := hr t (Nat.lt_succ_self t)
    simp only [SparseCoreRestartTool.runOrdAfterUpdate, ih, hrt, ht1.2.1, ht1.2.2.1,
      ht1.2.2.2.1, ht1.2.2.2.2]

private lemma runOrdAfterRestarts_congr (T : SparseCoreRestartTool) (k M N : ℕ)
    {D₁ D₂ : DynamicInstance} {ord₁ ord₂ : ℕ → ℕ → List End} {r₁ r₂ : ℕ → List ℕ} (t : ℕ)
    (hD : ∀ s ≤ t, D₁.G s = D₂.G s ∧ D₁.U s = D₂.U s ∧ D₁.ℓ s = D₂.ℓ s ∧ D₁.g s = D₂.g s ∧
      ord₁ s = ord₂ s)
    (hr : ∀ s ≤ t, r₁ s = r₂ s) :
    T.runOrdAfterRestarts k M N D₁ ord₁ r₁ t = T.runOrdAfterRestarts k M N D₂ ord₂ r₂ t := by
  simp only [SparseCoreRestartTool.runOrdAfterRestarts, hr t le_rfl,
    runOrdAfterUpdate_congr T k M N t hD (fun s hs => hr s hs.le)]

/-- Every `SparseCoreOrdInput` state arises as `T.runOrdAfterRestarts k M N D ordSeq restarts τ`
for a valid `DynamicInstance` `D`, ordered rotations `OrderedUpTo D τ 2 ordSeq`, and restarts list
`restarts`, whose cumulative update count equals `n ≤ updateThreshold k M N`. -/
theorem sparseCoreOrdInput_exists_run (T : SparseCoreRestartTool) {k M N : ℕ}
    {s : T.State} {G : MGraph} {ord : ℕ → List End} {n : ℕ}
    (h : SparseCoreOrdInput T k M N s G ord n) :
    ∃ (τ : ℕ) (D : DynamicInstance) (ordSeq : ℕ → ℕ → List End) (restarts : ℕ → List ℕ),
      (D.G 0).IsValid ∧ (D.G 0).m ≤ M ∧ (D.G 0).n ≤ N ∧
      (∀ e ∈ (D.G 0).E, 0 < D.ℓ 0 e) ∧
      D.IsValid τ ∧ OrderedUpTo D τ 2 ordSeq ∧
      D.G τ = G ∧ ordSeq τ = ord ∧
      (Finset.Icc 1 τ).sum (fun r => (D.U r).length) = n ∧
      ((n : ℕ) : ℝ) ≤ SparseCoreTool.updateThreshold k M N ∧
      T.runOrdAfterRestarts k M N D ordSeq restarts τ = s := by
  induction h with
  | init G₀ ℓ₀ g₀ ord₀ hval hm hn hpos hrot =>
    let D : DynamicInstance := ⟨fun _ => G₀, fun _ => [], fun _ => g₀, fun _ => ℓ₀⟩
    obtain ⟨ρ₀, hρ₀⟩ := hrot
    refine ⟨0, D, fun _ => ord₀, fun _ => [], hval, hm, hn, hpos,
      fun t ht1 ht0 => by omega,
      ⟨fun _ => ρ₀, fun _ _ => hρ₀, fun t ht => by omega⟩,
      rfl, rfl, by simp, ?_, by simp [SparseCoreRestartTool.runOrdAfterRestarts,
        SparseCoreRestartTool.runOrdAfterUpdate, D]⟩
    unfold SparseCoreTool.updateThreshold
    simp only [Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg M) (mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _))
  | @update s₀ G₀ ord₀ n₀ _ U ℓ' g' ord' hBV hpos' hOrdB hThr ih =>
    obtain ⟨τ, D, ordSeq, restarts, hG0, hm0, hn0, hℓ0, hD, hOrd, hGτ, hordτ, hsum, _, hrun⟩ := ih
    let D' : DynamicInstance :=
      { G := fun t => if t ≤ τ then D.G t else G₀.applyBatch U
        U := fun t => if t ≤ τ then D.U t else U
        g := fun t => if t ≤ τ then D.g t else g'
        ℓ := fun t => if t ≤ τ then D.ℓ t else ℓ' }
    let ordSeq' : ℕ → ℕ → List End := fun t => if t ≤ τ then ordSeq t else ord'
    let restarts' : ℕ → List ℕ := fun t => if t ≤ τ then restarts t else []
    have hagree : ∀ t ≤ τ, D'.G t = D.G t ∧ D'.U t = D.U t ∧ D'.ℓ t = D.ℓ t ∧ D'.g t = D.g t ∧
        ordSeq' t = ordSeq t := fun t ht => by simp [D', ordSeq', ht]
    have hD'_val : D'.IsValid (τ + 1) := by
      intro t ht1 ht2
      by_cases ht : t ≤ τ
      · have h1 := hD t ht1 ht
        have htm : t - 1 ≤ τ := by omega
        simp only [D', ht, htm, ↓reduceIte]
        exact h1
      · have hteq : t = τ + 1 := by omega
        subst hteq
        have hnot : ¬ (τ + 1 ≤ τ) := by omega
        simp only [D', hnot, Nat.add_sub_cancel, le_refl, ↓reduceIte, hGτ]
        exact ⟨hBV, trivial⟩
    have hOrd' : OrderedUpTo D' (τ + 1) 2 ordSeq' := by
      obtain ⟨ρ, hρ_ord, hρ_step⟩ := hOrd
      obtain ⟨ρU, σU, hρU, hσU, hRB⟩ := hOrdB
      let ρ' : ∀ t, Rotation (D'.G t) := fun t =>
        if ht : t ≤ τ then
          (show D.G t = D'.G t by simp [D', ht]) ▸ ρ t
        else
          (show G₀.applyBatch U = D'.G t by simp [D', ht]) ▸ σU
      refine ⟨ρ', fun t ht => ?_, fun t ht => ?_⟩
      · by_cases hle : t ≤ τ
        · have h1 : (ρ' t).order = (ρ t).order := by
            dsimp only [ρ']
            rw [dite_eq_left_of_eq_true (eq_true hle)]
            exact cast_rot_order _ _
          rw [h1, hρ_ord t hle]; simp [ordSeq', hle]
        · have h1 : (ρ' t).order = σU.order := by
            dsimp only [ρ']
            rw [dite_eq_right_of_eq_false (eq_false hle)]
            exact cast_rot_order _ _
          rw [h1, hσU]; simp [ordSeq', hle]
      · by_cases hlt : t < τ
        · have ht_le : t ≤ τ := hlt.le
          have ht1_le : t + 1 ≤ τ := hlt
          obtain ⟨hGstep, hstep⟩ := hρ_step t hlt
          have hGeq : D'.G (t + 1) = (D'.G t).applyBatch (D'.U (t + 1)) := by
            simp only [D', ht_le, ht1_le, ↓reduceIte]; exact hGstep
          refine ⟨hGeq, ?_⟩
          have hD't : D.G t = D'.G t := by simp [D', ht_le]
          have hD't1 : D.G (t + 1) = D'.G (t + 1) := by simp [D', ht1_le]
          have hD'U : D.U (t + 1) = D'.U (t + 1) := by simp [D', ht1_le]
          dsimp only [ρ']
          rw [dite_eq_left_of_eq_true (eq_true ht_le), dite_eq_left_of_eq_true (eq_true ht1_le)]
          exact cast_rotBatch hD't hD't1 hD'U hGstep (ρ t) (ρ (t + 1)) hstep
        · have hteq : t = τ := by omega
          subst t
          have hnot : ¬ (τ + 1 ≤ τ) := by omega
          have hGeq : D'.G (τ + 1) = (D'.G τ).applyBatch (D'.U (τ + 1)) := by
            simp [D', hnot, hGτ]
          refine ⟨hGeq, ?_⟩
          have hD't : D.G τ = D'.G τ := by simp [D']
          have hD't1 : G₀.applyBatch U = D'.G (τ + 1) := by simp [D', hnot]
          have hD'U : U = D'.U (τ + 1) := by simp [D', hnot]
          dsimp only [ρ']
          rw [dite_eq_left_of_eq_true (eq_true le_rfl), dite_eq_right_of_eq_false (eq_false hnot)]
          have hρ_eq : ρ τ = hGτ.symm ▸ ρU := by
            apply rotation_ext
            rw [cast_rot_order, hρU, hρ_ord τ le_rfl, hordτ]
          have hRB0 : RotationBatch 2 U ρU ((rfl : G₀.applyBatch U = G₀.applyBatch U) ▸ σU) := hRB
          have hRB1 := cast_rotBatch (hGτ.symm.trans hD't) hD't1 hD'U rfl ρU σU hRB0
          have hcast : (hGτ.symm.trans hD't) ▸ ρU = hD't ▸ ρ τ := by
            rw [hρ_eq]; cases hGτ; rfl
          rwa [hcast] at hRB1
    have hsum' : (Finset.Icc 1 (τ + 1)).sum (fun r => (D'.U r).length) = n₀ + U.length := by
      have hIcc : Finset.Icc 1 (τ + 1) = insert (τ + 1) (Finset.Icc 1 τ) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hIcc, Finset.sum_insert (by simp)]
      have hsub : (Finset.Icc 1 τ).sum (fun r => (D'.U r).length) =
          (Finset.Icc 1 τ).sum (fun r => (D.U r).length) :=
        Finset.sum_congr rfl fun r hr => by simp [D', (Finset.mem_Icc.mp hr).2]
      rw [hsub, hsum]
      have hnot : ¬ (τ + 1 ≤ τ) := by omega
      simp [D', hnot, Nat.add_comm]
    have hrun' : T.runOrdAfterRestarts k M N D' ordSeq' restarts' (τ + 1) =
        (T.updateOrd s₀ U ℓ' g' ord').1 := by
      have hnot : ¬ (τ + 1 ≤ τ) := by omega
      have hprev := runOrdAfterRestarts_congr T k M N (r₁ := restarts') (r₂ := restarts) τ hagree
        (fun s hs => by dsimp only [restarts']; simp [hs])
      rw [SparseCoreRestartTool.runOrdAfterRestarts]
      simp only [restarts', hnot, ↓reduceIte, List.foldl_nil]
      rw [SparseCoreRestartTool.runOrdAfterUpdate_succ, hprev, hrun]
      simp [D', ordSeq', hnot]
    refine ⟨τ + 1, D', ordSeq', restarts', by simpa [D'] using hG0, by simpa [D'] using hm0,
      by simpa [D'] using hn0, by simpa [D'] using hℓ0, hD'_val, hOrd',
      by simp [D'], by simp [ordSeq'], hsum', hThr, hrun'⟩
  | @restart s₀ G₀ ord₀ n₀ _ j _ ih =>
    obtain ⟨τ, D, ordSeq, restarts, hG0, hm0, hn0, hℓ0, hD, hOrd, hGτ, hordτ, hsum, hThr, hrun⟩ := ih
    let restarts' : ℕ → List ℕ := fun t => if t = τ then restarts τ ++ [j] else restarts t
    have hupd_eq : T.runOrdAfterUpdate k M N D ordSeq restarts' τ =
        T.runOrdAfterUpdate k M N D ordSeq restarts τ :=
      runOrdAfterUpdate_congr T k M N τ (fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩)
        (fun s hs => by simp [restarts', Nat.ne_of_lt hs])
    have hrun' : T.runOrdAfterRestarts k M N D ordSeq restarts' τ = T.restart s₀ j := by
      rw [SparseCoreRestartTool.runOrdAfterRestarts, hupd_eq]
      simp only [restarts', ↓reduceIte, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact congrArg (fun x => T.restart x j) hrun
    exact ⟨τ, D, ordSeq, restarts', hG0, hm0, hn0, hℓ0, hD, hOrd, hGτ, hordτ, hsum, hThr, hrun'⟩

end MinCostFlow.SparseCore.Program
