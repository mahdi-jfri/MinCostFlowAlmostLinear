module

public import MinCostFlow.SparseCore.Program.BundleCapHeadroomDefs
public import MinCostFlow.SparseCore.Program.BundleInitPost
public import MinCostFlow.SparseCore.Program.BundleStepDefs
import MinCostFlow.SparseCore.BundleRunsFold
import MinCostFlow.SparseCore.Program.BundleStepCostHelpers

/-!
# Slot-block capacity headroom invariant for the bundle manager (`BundleCapHeadroom`)

Between two restarts of a bundle slot, edges can only leave the slot (via `batchDeletes U`) and
bundles can only split into nonempty parts (`byRootSplitFold` / `bundleRunsStep`); no edge ever
enters an active slot between restarts.

This file defines the deletion- and split-preserved slot capacity invariant:
* `bunNonEmpty B`: the number of nonempty bundles of `B : BundleState`.
* `bunCapHeadroomInv B bunCap := B.vertices.card + (2 * B.edges.card - bunNonEmpty B) +
  2 * B.edges.card ≤ bunCap`.
* `bunTableHeadroomInv S m`: every active slot `(B, (p, bunCap))` of a bundle table satisfies
  `bunCapHeadroomInv B bunCap`.

Main results:
1. **Initialization & restart** (`bunCapHeadroomInv_of_init`, `bunCapHeadroomInv_of_bundleStateOfSlots`,
   `bunTableHeadroomInv_initSlots`): allocating `bunCap ≥ 4 * |E_s|` for every newly initialized
   or restarted slot establishes `bunCapHeadroomInv` (since every initial chunk is nonempty).
2. **Deletions & splits** (`bunCapHeadroomInv_delete`, `bunCapHeadroomInv_runsFoldStep`,
   `bunCapHeadroomInv_byRootSplitFold`, `bunCapHeadroomInv_bundleRunsStep`,
   `bunTableHeadroomInv_tableAfterStep`): deletions and canonical root-grouped splits preserve
   `bunCapHeadroomInv` and `bunTableHeadroomInv`.
3. **Discharging `hcap_ok`** (`bunCapHeadroomInv_implies_cap_ok`,
   `bunTableHeadroomInv_implies_hcap_ok`): `bunTableHeadroomInv S₀ m` directly implies the exact
   `hcap_ok` precondition of `bunTable_step_runs` and `bunTable_step_model_runs_on`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

public section

/-! ## 1. Basic properties, initialization, deletion, and abstract split -/

/-- Every bundle state has `∑ b ∈ B.vertices, (B.ends b).card ≤ 2 * B.edges.card`. -/
theorem bunEnds_sum_le_two_mul_edges (B : BundleState) :
    (∑ b ∈ B.vertices, (B.ends b).card) ≤ 2 * B.edges.card := by
  classical
  have hcard : (edgeEnds B.edges).card = 2 * B.edges.card := by
    have hdisj : Disjoint (B.edges.image (·, true)) (B.edges.image (·, false)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      obtain ⟨e1, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨e2, _, h⟩ := Finset.mem_image.mp h2
      cases h
    have heq : edgeEnds B.edges = B.edges.image (·, true) ∪ B.edges.image (·, false) := by
      ext ⟨e, side⟩
      cases side <;> simp [edgeEnds]
    rw [heq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
      Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
    omega
  rw [← hcard]
  have hsub : B.vertices.biUnion B.ends ⊆ edgeEnds B.edges := by
    intro x hx
    obtain ⟨b, _, hxb⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxb).1
  have hdisj : Set.PairwiseDisjoint (B.vertices : Set ℕ) B.ends := by
    intro b₁ _ b₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)
  rw [← Finset.card_biUnion hdisj]
  exact Finset.card_le_card hsub

/-- Every bundle state has `bunNonEmpty B ≤ 2 * B.edges.card`. -/
theorem bunNonEmpty_le_two_mul_edges (B : BundleState) :
    bunNonEmpty B ≤ 2 * B.edges.card := by
  classical
  have h1 : bunNonEmpty B ≤
      ∑ b ∈ B.vertices.filter (fun b => (B.ends b).Nonempty), (B.ends b).card := by
    unfold bunNonEmpty
    calc (B.vertices.filter fun b => (B.ends b).Nonempty).card
        = ∑ _b ∈ B.vertices.filter (fun b => (B.ends b).Nonempty), 1 := by simp
      _ ≤ ∑ b ∈ B.vertices.filter (fun b => (B.ends b).Nonempty), (B.ends b).card :=
          Finset.sum_le_sum fun b hb => Finset.card_pos.mpr (Finset.mem_filter.mp hb).2
  exact h1.trans ((Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans
    (bunEnds_sum_le_two_mul_edges B))

/-- Monotonicity of `bunCapHeadroomInv` in `bunCap`. -/
theorem bunCapHeadroomInv_mono {B : BundleState} {c₁ c₂ : ℕ}
    (h : bunCapHeadroomInv B c₁) (hle : c₁ ≤ c₂) : bunCapHeadroomInv B c₂ :=
  le_trans h hle

/-- Congruence of `bunCapHeadroomInv` when `vertices`, `edges`, and `bundleOf` agree. -/
theorem bunCapHeadroomInv_congr {B₁ B₂ : BundleState} {bunCap : ℕ}
    (hV : B₁.vertices = B₂.vertices) (hE : B₁.edges = B₂.edges) (hbo : B₁.bundleOf = B₂.bundleOf)
    (h : bunCapHeadroomInv B₁ bunCap) : bunCapHeadroomInv B₂ bunCap := by
  have hends : ∀ b, B₁.ends b = B₂.ends b := fun b => by
    ext x; simp [BundleState.mem_ends, hE, hbo]
  have hne : bunNonEmpty B₁ = bunNonEmpty B₂ := by
    unfold bunNonEmpty
    congr 1
    ext b
    simp [hV, hends b]
  unfold bunCapHeadroomInv at h ⊢
  rwa [← hV, ← hE, ← hne]

/-- At initialization or restart (every initial bundle nonempty, so `bunNonEmpty B = B.vertices.card`),
`bunCapHeadroomInv B (4 * B.edges.card)` holds. -/
theorem bunCapHeadroomInv_of_init {B : BundleState}
    (hne : ∀ b ∈ B.vertices, (B.ends b).Nonempty) :
    bunCapHeadroomInv B (4 * B.edges.card) := by
  classical
  have hneEq : bunNonEmpty B = B.vertices.card := by
    unfold bunNonEmpty
    rw [Finset.filter_true_of_mem hne]
  have hle := bunNonEmpty_le_two_mul_edges B
  unfold bunCapHeadroomInv
  omega

/-- Every initialized chunked slot `bundleStateOfSlots (initPrefixSlots cord rList E k) E` satisfies
`bunCapHeadroomInv` at any `bunCap ≥ 4 * E.card`. -/
theorem bunCapHeadroomInv_of_bundleStateOfSlots {cord : ℕ → List End} {rList : List ℕ}
    {E : Finset ℕ} {k bunCap : ℕ}
    (hk1 : 1 ≤ k) (hr_nd : rList.Nodup) (hcord_nd : ∀ w ∈ rList, (cord w).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hcov : ∀ x : End, x.1 ∈ E → ∃ v ∈ rList, x ∈ cord v)
    (hcap : 4 * E.card ≤ bunCap) :
    bunCapHeadroomInv (bundleStateOfSlots (initPrefixSlots cord rList E k) E) bunCap := by
  obtain ⟨hne, -, -, -, hmem⟩ := bundleStateOfSlots_props hk1 hr_nd hcord_nd hcord_disj hcov
  refine bunCapHeadroomInv_mono (bunCapHeadroomInv_of_init ?_) ?_
  · intro b hb
    have hlt : b < (initPrefixSlots cord rList E k).length := Finset.mem_range.mp hb
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne b hlt)
    exact ⟨x, (hmem b hlt x).mpr hx⟩
  · exact hcap

/-- Deleting any edge set `D` preserves `bunCapHeadroomInv` (each deleted edge drops `2 * |E|` by
`2` and drops `bunNonEmpty` by at most `2`). -/
theorem bunCapHeadroomInv_delete {B : BundleState} {D : Finset ℕ} {bunCap : ℕ}
    (h : bunCapHeadroomInv B bunCap) :
    bunCapHeadroomInv { B with edges := B.edges \ D } bunCap := by
  classical
  set B' : BundleState := { B with edges := B.edges \ D }
  have hsubE : B'.edges ⊆ B.edges := Finset.sdiff_subset
  have hcardE : B'.edges.card + (B.edges ∩ D).card = B.edges.card := by
    have := Finset.card_sdiff_add_card_inter B.edges D
    simp [B']
  set lost := (B.vertices.filter fun b => (B.ends b).Nonempty) \
    (B'.vertices.filter fun b => (B'.ends b).Nonempty)
  have hlost_le : lost.card ≤ 2 * (B.edges ∩ D).card := by
    have hdisj : Set.PairwiseDisjoint (lost : Set ℕ) (fun b => B.ends b ∩ edgeEnds (B.edges ∩ D)) := by
      intro b₁ _ b₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x h1 h2
      exact hne ((Finset.mem_filter.mp (Finset.mem_inter.mp h1).1).2.symm.trans
        (Finset.mem_filter.mp (Finset.mem_inter.mp h2).1).2)
    have hsubU : lost.biUnion (fun b => B.ends b ∩ edgeEnds (B.edges ∩ D)) ⊆
        edgeEnds (B.edges ∩ D) := by
      intro x hx
      obtain ⟨_, _, hx'⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hx').2
    have hcard_inter : (edgeEnds (B.edges ∩ D)).card = 2 * (B.edges ∩ D).card := by
      have hd : Disjoint ((B.edges ∩ D).image (·, true)) ((B.edges ∩ D).image (·, false)) := by
        rw [Finset.disjoint_left]; intro x h1 h2
        obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp h1
        obtain ⟨_, _, hq⟩ := Finset.mem_image.mp h2; cases hq
      have heq : edgeEnds (B.edges ∩ D) =
          (B.edges ∩ D).image (·, true) ∪ (B.edges ∩ D).image (·, false) := by
        ext ⟨e, side⟩; cases side <;> simp [edgeEnds]
      rw [heq, Finset.card_union_of_disjoint hd,
        Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1),
        Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)]
      omega
    have hpos : ∀ b ∈ lost, 1 ≤ (B.ends b ∩ edgeEnds (B.edges ∩ D)).card := by
      intro b hb
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hb
      obtain ⟨hbV, ⟨x, hxb⟩⟩ := Finset.mem_filter.mp h1
      have hxb' : x.1 ∈ B.edges ∧ B.bundleOf x = b :=
        ⟨(mem_edgeEnds _ _).mp (Finset.mem_filter.mp hxb).1, (Finset.mem_filter.mp hxb).2⟩
      have hxD : x.1 ∈ D := by
        by_contra hnot
        have hxB' : x ∈ B'.ends b := Finset.mem_filter.mpr
          ⟨(mem_edgeEnds _ _).mpr (Finset.mem_sdiff.mpr ⟨hxb'.1, hnot⟩), hxb'.2⟩
        exact h2 (Finset.mem_filter.mpr ⟨hbV, ⟨x, hxB'⟩⟩)
      exact Finset.card_pos.mpr ⟨x, Finset.mem_inter.mpr ⟨hxb, (mem_edgeEnds _ _).mpr
        (Finset.mem_inter.mpr ⟨hxb'.1, hxD⟩)⟩⟩
    calc lost.card = ∑ _b ∈ lost, 1 := by simp
      _ ≤ ∑ b ∈ lost, (B.ends b ∩ edgeEnds (B.edges ∩ D)).card := Finset.sum_le_sum hpos
      _ = (lost.biUnion fun b => B.ends b ∩ edgeEnds (B.edges ∩ D)).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ (edgeEnds (B.edges ∩ D)).card := Finset.card_le_card hsubU
      _ = 2 * (B.edges ∩ D).card := hcard_inter
  have hsubNE : B'.vertices.filter (fun b => (B'.ends b).Nonempty) ⊆
      B.vertices.filter (fun b => (B.ends b).Nonempty) := by
    intro b hb
    obtain ⟨hbV, ⟨x, hxb⟩⟩ := Finset.mem_filter.mp hb
    have hxb1 := Finset.mem_filter.mp hxb
    exact Finset.mem_filter.mpr ⟨hbV, ⟨x, Finset.mem_filter.mpr
      ⟨(mem_edgeEnds _ _).mpr (hsubE ((mem_edgeEnds _ _).mp hxb1.1)), hxb1.2⟩⟩⟩
  have hne_diff : bunNonEmpty B = bunNonEmpty B' + lost.card := by
    unfold bunNonEmpty lost
    rw [Nat.add_comm]
    exact (Finset.card_sdiff_add_card_eq_card hsubNE).symm
  have hne1 := bunNonEmpty_le_two_mul_edges B
  have hne2 := bunNonEmpty_le_two_mul_edges B'
  unfold bunCapHeadroomInv at h ⊢
  have hVeq : B'.vertices = B.vertices := rfl
  rw [hVeq]
  omega

/-- Any step that keeps `edges` unchanged, increases `vertices.card` by `Δ`, and increases
`bunNonEmpty` by `Δ` preserves `bunCapHeadroomInv`. -/
theorem bunCapHeadroomInv_of_nonempty_split {B B' : BundleState} {bunCap Δ : ℕ}
    (h : bunCapHeadroomInv B bunCap)
    (hE : B'.edges = B.edges)
    (hV : B'.vertices.card = B.vertices.card + Δ)
    (hNE : bunNonEmpty B' = bunNonEmpty B + Δ) :
    bunCapHeadroomInv B' bunCap := by
  have h1 := bunNonEmpty_le_two_mul_edges B
  have h2 := bunNonEmpty_le_two_mul_edges B'
  unfold bunCapHeadroomInv at h ⊢
  rw [hE] at h2 ⊢
  omega

/-! ## 3. Preservation under `runsFoldStep`, `byRootSplitFold`, and `bundleRunsStep` -/

/-- One step of `runsFoldStep` with pairwise-disjoint nonempty runs covering `st.ends b` preserves
`bunCapHeadroomInv`. -/
theorem bunCapHeadroomInv_runsFoldStep {ops : List Update} {st : BundleState} {b bunCap : ℕ}
    {vruns : List (ℕ × List End)}
    (hH : bunCapHeadroomInv st bunCap)
    (hb : b ∈ st.vertices)
    (hlive : ∀ x : End, x.1 ∈ st.edges → st.bundleOf x ∈ st.vertices)
    (hn : (vruns.map Prod.snd).flatten.Nodup)
    (hcover : ∀ x, x ∈ (vruns.map Prod.snd).flatten ↔ x.1 ∈ st.edges ∧ st.bundleOf x = b)
    (hne_runs : ∀ vr ∈ vruns, vr.2 ≠ []) :
    bunCapHeadroomInv (runsFoldStep (ops, st) (b, vruns)).2 bunCap := by
  classical
  set next := st.vertices.sup id + 1
  set Δ := (vruns.drop 1).length
  set fresh : Finset ℕ := ((List.range Δ).map fun i => next + i).toFinset
  set st' := (runsFoldStep (ops, st) (b, vruns)).2
  obtain ⟨-, -, -, hE, hVmem, hOther, hNil, hHead, hFresh⟩ :=
    runsFoldStep_spec ops st b vruns hb hlive hn hcover
  have hdisj : Disjoint st.vertices fresh := by
    rw [Finset.disjoint_left]
    intro c hc hcf
    rw [List.mem_toFinset, List.mem_map] at hcf
    obtain ⟨i, _, rfl⟩ := hcf
    have hle : next + i ≤ st.vertices.sup id := Finset.le_sup (f := id) hc
    omega
  have hfresh_card : fresh.card = Δ := by
    have hnd : ((List.range Δ).map fun i => next + i).Nodup :=
      List.Nodup.map (fun _ _ h => by omega) List.nodup_range
    rw [List.toFinset_card_of_nodup hnd, List.length_map, List.length_range]
  have hVeq : st'.vertices = st.vertices ∪ fresh := by
    ext c
    rw [hVmem c, Finset.mem_union, List.mem_toFinset, List.mem_map]
    constructor
    · rintro (hc | ⟨i, hi, rfl⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, List.mem_range.mpr hi, rfl⟩
    · rintro (hc | ⟨i, hi, rfl⟩)
      · exact Or.inl hc
      · exact Or.inr ⟨i, List.mem_range.mp hi, rfl⟩
  have hVcard : st'.vertices.card = st.vertices.card + Δ := by
    rw [hVeq, Finset.card_union_of_disjoint hdisj, hfresh_card]
  have hNEeq : (st'.vertices.filter fun c => (st'.ends c).Nonempty) =
      (st.vertices.filter fun c => (st.ends c).Nonempty) ∪ fresh := by
    ext c
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, hVmem c]
    simp only [fresh, List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨hc | ⟨i, hi, rfl⟩, hne'⟩
      · by_cases hcb : c = b
        · subst hcb
          left
          refine ⟨hc, ?_⟩
          cases hv : vruns with
          | nil =>
            rw [(hNil hv).1] at hne'
            exact False.elim (Finset.not_nonempty_empty hne')
          | cons vr rest =>
            obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne_runs vr (hv ▸ List.mem_cons_self))
            have hxflat : x ∈ (vruns.map Prod.snd).flatten := by
              rw [hv]; simp only [List.map_cons, List.flatten_cons, List.mem_append]
              exact Or.inl hx
            obtain ⟨hxE, hxb⟩ := (hcover x).mp hxflat
            exact ⟨x, (BundleState.mem_ends _ _ _).mpr ⟨hxE, hxb⟩⟩
        · left
          exact ⟨hc, (hOther c hc hcb).1 ▸ hne'⟩
      · exact Or.inr ⟨i, hi, rfl⟩
    · rintro (⟨hc, hne0⟩ | ⟨i, hi, rfl⟩)
      · refine ⟨Or.inl hc, ?_⟩
        by_cases hcb : c = b
        · subst hcb
          cases hv : vruns with
          | nil =>
            obtain ⟨x, hx⟩ := hne0
            obtain ⟨hxE, hxb⟩ := (BundleState.mem_ends _ _ _).mp hx
            have hxflat := (hcover x).mpr ⟨hxE, hxb⟩
            simp [hv] at hxflat
          | cons vr rest =>
            rw [(hHead vr (by simp [hv])).1]
            obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne_runs vr (hv ▸ List.mem_cons_self))
            exact ⟨x, List.mem_toFinset.mpr hx⟩
        · rw [(hOther c hc hcb).1]; exact hne0
      · refine ⟨Or.inr ⟨i, hi, rfl⟩, ?_⟩
        rw [(hFresh i hi).1]
        have hmem : (vruns.drop 1)[i] ∈ vruns := List.mem_of_mem_drop (List.getElem_mem hi)
        obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne_runs _ hmem)
        exact ⟨x, List.mem_toFinset.mpr hx⟩
  have hNEcard : bunNonEmpty st' = bunNonEmpty st + Δ := by
    unfold bunNonEmpty
    rw [hNEeq, Finset.card_union_of_disjoint (Disjoint.mono_left (Finset.filter_subset _ _) hdisj),
      hfresh_card]
  exact bunCapHeadroomInv_of_nonempty_split hH hE hVcard hNEcard

private lemma byRootVRuns_nonempty (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ) :
    ∀ vr ∈ byRootVRuns B E src' b, vr.2 ≠ [] := by
  intro vr hvr
  have hvr' : vr ∈ rawByRootVRuns B E src' b :=
    (promoteLargestRun_perm (rawByRootVRuns B E src' b)).mem_iff.mp hvr
  simp only [rawByRootVRuns, List.mem_map] at hvr'
  obtain ⟨v, hv, rfl⟩ := hvr'
  have hv' : v ∈ finalRootsOf B E src' b := (Finset.mem_sort (· ≤ ·)).mp hv
  obtain ⟨x, hx, hxv⟩ := Finset.mem_image.mp hv'
  have hkey : endKey x ∈ ((survivingEnds B E b).filter fun y => src' y = v).image endKey :=
    Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxv⟩, rfl⟩
  have hxmem : x ∈ ((((survivingEnds B E b).filter fun y => src' y = v).image endKey).sort (· ≤ ·)).map
      endOfKey :=
    List.mem_map.mpr ⟨endKey x, (Finset.mem_sort (· ≤ ·)).mpr hkey, bundle_endOfKey_endKey x⟩
  exact List.ne_nil_of_mem hxmem

private lemma byRootVRuns_mem_run (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b v : ℕ)
    (x : End) :
    x ∈ ((((survivingEnds B E b).filter fun y => src' y = v).image endKey).sort (· ≤ ·)).map
      endOfKey ↔ x ∈ survivingEnds B E b ∧ src' x = v := by
  simp only [List.mem_map, Finset.mem_sort, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨k, ⟨y, ⟨hy, hyv⟩, rfl⟩, hxy⟩
    rw [bundle_endOfKey_endKey] at hxy
    exact hxy ▸ ⟨hy, hyv⟩
  · rintro ⟨hx, hxv⟩
    exact ⟨endKey x, ⟨x, ⟨hx, hxv⟩, rfl⟩, bundle_endOfKey_endKey x⟩

private lemma byRootVRuns_flatten_nodup (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ) :
    ((byRootVRuns B E src' b).map Prod.snd).flatten.Nodup := by
  have hperm : ((byRootVRuns B E src' b).map Prod.snd).Perm
      ((rawByRootVRuns B E src' b).map Prod.snd) :=
    (promoteLargestRun_perm (rawByRootVRuns B E src' b)).map Prod.snd
  have hraw : ((rawByRootVRuns B E src' b).map Prod.snd).flatten.Nodup := by
    unfold rawByRootVRuns
    rw [List.map_map, List.nodup_flatten]
    refine ⟨?_, ?_⟩
    · intro l hl
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
      exact List.Nodup.map (fun k₁ k₂ h => by
        have hk : endKey (endOfKey k₁) = endKey (endOfKey k₂) := congrArg endKey h
        have h1 : ∀ k, endKey (endOfKey k) = k := fun k => by
          simp only [endKey, endOfKey, decide_eq_true_eq]; split_ifs <;> omega
        simpa [h1] using hk) (Finset.sort_nodup _ _)
    · rw [List.pairwise_map]
      refine (Finset.sort_nodup (finalRootsOf B E src' b) (· ≤ ·)).imp ?_
      intro v₁ v₂ hne
      rw [List.disjoint_left]
      intro x hx1 hx2
      have h1 := ((byRootVRuns_mem_run B E src' b v₁ x).mp hx1).2
      have h2 := ((byRootVRuns_mem_run B E src' b v₂ x).mp hx2).2
      exact hne (h1.symm.trans h2)
  rw [List.nodup_flatten] at hraw ⊢
  exact ⟨fun l hl => hraw.1 l (hperm.mem_iff.mp hl),
    (hperm.pairwise_iff fun h => List.disjoint_left.mpr fun _ hx hy => List.disjoint_left.mp h hy hx).mpr hraw.2⟩

private lemma byRootVRuns_flatten_mem (B : BundleState) (E : Finset ℕ) (src' : End → ℕ) (b : ℕ)
    (hsub : E ⊆ B.edges) (x : End) :
    x ∈ ((byRootVRuns B E src' b).map Prod.snd).flatten ↔ x.1 ∈ E ∧ B.bundleOf x = b := by
  have hperm : ((byRootVRuns B E src' b).map Prod.snd).Perm
      ((rawByRootVRuns B E src' b).map Prod.snd) :=
    (promoteLargestRun_perm (rawByRootVRuns B E src' b)).map Prod.snd
  have hiff : x ∈ ((byRootVRuns B E src' b).map Prod.snd).flatten ↔
      x ∈ ((rawByRootVRuns B E src' b).map Prod.snd).flatten := by
    simp only [List.mem_flatten, hperm.mem_iff]
  rw [hiff]
  unfold rawByRootVRuns
  rw [List.map_map, List.mem_flatten]
  constructor
  · rintro ⟨l, hl, hxl⟩
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hl
    have hx := ((byRootVRuns_mem_run B E src' b v x).mp hxl).1
    simp only [survivingEnds, Finset.mem_filter, BundleState.mem_ends] at hx
    exact ⟨hx.2, hx.1.2⟩
  · rintro ⟨hxE, hxb⟩
    have hxSurv : x ∈ survivingEnds B E b :=
      Finset.mem_filter.mpr ⟨(BundleState.mem_ends _ _ _).mpr ⟨hsub hxE, hxb⟩, hxE⟩
    have hv : src' x ∈ (finalRootsOf B E src' b).sort (· ≤ ·) :=
      (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_image.mpr ⟨x, hxSurv, rfl⟩)
    refine ⟨_, List.mem_map.mpr ⟨src' x, hv, rfl⟩,
      (byRootVRuns_mem_run B E src' b (src' x) x).mpr ⟨hxSurv, rfl⟩⟩

/-- `byRootSplitFold` on `E = B₀.edges \ D` and any duplicate-free list `cands` of bundles in
`B₀.vertices` preserves `bunCapHeadroomInv`. -/
theorem bunCapHeadroomInv_byRootSplitFold {B₀ : BundleState} {D : Finset ℕ} {src' : End → ℕ}
    {dels : List Update} {cands : List ℕ} {bunCap : ℕ}
    (hH : bunCapHeadroomInv B₀ bunCap)
    (hlive : ∀ x ∈ edgeEnds B₀.edges, B₀.bundleOf x ∈ B₀.vertices)
    (hnd : cands.Nodup) (hsub : ∀ b ∈ cands, b ∈ B₀.vertices) :
    bunCapHeadroomInv (byRootSplitFold B₀ (B₀.edges \ D) src' dels cands).2 bunCap := by
  set E := B₀.edges \ D
  have hEsub : E ⊆ B₀.edges := Finset.sdiff_subset
  have hfold : ∀ (cs : List ℕ) (s : List Update × BundleState),
      cs.Nodup → (∀ b ∈ cs, b ∈ B₀.vertices) →
      bunCapHeadroomInv s.2 bunCap →
      s.2.edges = E →
      (∀ b ∈ B₀.vertices, b ∈ s.2.vertices) →
      (∀ x : End, x.1 ∈ s.2.edges → s.2.bundleOf x ∈ s.2.vertices) →
      (∀ b ∈ cs, ∀ x : End, (x.1 ∈ s.2.edges ∧ s.2.bundleOf x = b) ↔ (x.1 ∈ E ∧ B₀.bundleOf x = b)) →
      bunCapHeadroomInv ((cs.map fun b => (b, byRootVRuns B₀ E src' b)).foldl runsFoldStep s).2 bunCap := by
    intro cs
    induction cs with
    | nil => intro s _ _ hHs _ _ _ _; exact hHs
    | cons b rest ih =>
      intro s hnd' hsub' hHs hEs hVsub hliveS hmatch
      rw [List.nodup_cons] at hnd'
      simp only [List.map_cons, List.foldl_cons]
      have hbV : b ∈ s.2.vertices := hVsub b (hsub' b List.mem_cons_self)
      have hcov : ∀ x, x ∈ ((byRootVRuns B₀ E src' b).map Prod.snd).flatten ↔
          x.1 ∈ s.2.edges ∧ s.2.bundleOf x = b := fun x =>
        (byRootVRuns_flatten_mem B₀ E src' b hEsub x).trans (hmatch b List.mem_cons_self x).symm
      have hH' := bunCapHeadroomInv_runsFoldStep (ops := s.1) hHs hbV hliveS
        (byRootVRuns_flatten_nodup B₀ E src' b) hcov (byRootVRuns_nonempty B₀ E src' b)
      obtain ⟨-, -, -, hE', hV', hOther, -, hHead, hFresh⟩ :=
        runsFoldStep_spec s.1 s.2 b (byRootVRuns B₀ E src' b) hbV hliveS
          (byRootVRuns_flatten_nodup B₀ E src' b) hcov
      set st' := (runsFoldStep s (b, byRootVRuns B₀ E src' b)).2
      refine ih (runsFoldStep s (b, byRootVRuns B₀ E src' b)) hnd'.2
        (fun c hc => hsub' c (List.mem_cons_of_mem _ hc)) hH' (hE'.trans hEs)
        (fun c hc => (hV' c).mpr (Or.inl (hVsub c hc))) ?_ ?_
      · intro x hxE'
        have hxE : x.1 ∈ s.2.edges := hE' ▸ hxE'
        by_cases hxb : s.2.bundleOf x = b
        · have hxflat := (hcov x).mpr ⟨hxE, hxb⟩
          rw [List.mem_flatten] at hxflat
          obtain ⟨l, hl, hxl⟩ := hxflat
          obtain ⟨vr, hvr, rfl⟩ := List.mem_map.mp hl
          obtain ⟨idx, hidx, hget⟩ := List.getElem_of_mem hvr
          cases idx with
          | zero =>
            have hhd : (byRootVRuns B₀ E src' b).head? = some vr := by
              cases hv : byRootVRuns B₀ E src' b with
              | nil => simp [hv] at hidx
              | cons a as =>
                simp only [hv, List.getElem_cons_zero] at hget
                simp [hget]
            have hxin : x ∈ st'.ends b := by
              rw [(hHead vr hhd).1]; exact List.mem_toFinset.mpr hxl
            rw [((BundleState.mem_ends _ _ _).mp hxin).2]
            exact (hV' b).mpr (Or.inl hbV)
          | succ j =>
            have hj : j < ((byRootVRuns B₀ E src' b).drop 1).length := by simp; omega
            have hgetD : ((byRootVRuns B₀ E src' b).drop 1)[j]'hj = vr := by
              simpa [List.getElem_drop] using hget
            have hxin : x ∈ st'.ends (s.2.vertices.sup id + 1 + j) := by
              rw [(hFresh j hj).1, hgetD]; exact List.mem_toFinset.mpr hxl
            rw [((BundleState.mem_ends _ _ _).mp hxin).2]
            exact (hV' _).mpr (Or.inr ⟨j, hj, rfl⟩)
        · have hcV : s.2.bundleOf x ∈ s.2.vertices := hliveS x hxE
          have hxin : x ∈ st'.ends (s.2.bundleOf x) := by
            rw [(hOther _ hcV hxb).1]
            exact (BundleState.mem_ends _ _ _).mpr ⟨hxE, rfl⟩
          rw [((BundleState.mem_ends _ _ _).mp hxin).2]
          exact (hV' _).mpr (Or.inl hcV)
      · intro c hc x
        have hcb : c ≠ b := fun h => hnd'.1 (h ▸ hc)
        have hcV : c ∈ s.2.vertices := hVsub c (hsub' c (List.mem_cons_of_mem _ hc))
        have hend : x ∈ st'.ends c ↔ x ∈ s.2.ends c := by rw [(hOther c hcV hcb).1]
        simp only [BundleState.mem_ends] at hend
        exact hend.trans (hmatch c (List.mem_cons_of_mem _ hc) x)
  exact hfold cands (dels, { B₀ with edges := E }) hnd hsub (bunCapHeadroomInv_delete hH) rfl
    (fun _ h => h) (fun x hx => hlive x ((mem_edgeEnds _ _).mpr (hEsub hx)))
    (fun _ _ _ => Iff.rfl)

/-- Under `BundleStepReady`, `(bundleRunsStep cs B₀ k ord' U).2` preserves `bunCapHeadroomInv`. -/
theorem bunCapHeadroomInv_bundleRunsStep {cs : CompLSFState} {B₀ : BundleState} {k bunCap : ℕ}
    {ord ord' : ℕ → List End} {U : List Update}
    (hready : BundleStepReady cs B₀ k ord ord' U)
    (hH : bunCapHeadroomInv B₀ bunCap)
    (hlive : ∀ x ∈ edgeEnds B₀.edges, B₀.bundleOf x ∈ B₀.vertices) :
    bunCapHeadroomInv (bundleRunsStep cs B₀ k ord' U).2 bunCap := by
  have heq := bundleRunsStep_eq_byRoot hready
  have hnd : (exactSplitCands B₀ (B₀.edges \ batchDeletes U)
      (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src).Nodup :=
    (Finset.sort_nodup B₀.vertices (· ≤ ·)).filter _
  have hsub : ∀ b ∈ exactSplitCands B₀ (B₀.edges \ batchDeletes U)
      (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src, b ∈ B₀.vertices := fun b hb =>
    (Finset.mem_sort (· ≤ ·)).mp (List.mem_filter.mp hb).1
  have hfast := bunCapHeadroomInv_byRootSplitFold (D := batchDeletes U)
    (src' := (coreGraph (compLSFBatch cs U).G (compLSFBatch cs U).lsf).src)
    (dels := ((B₀.edges ∩ batchDeletes U).sort (· ≤ ·)).map Update.delete) hH hlive hnd hsub
  exact bunCapHeadroomInv_congr heq.2.1.symm heq.2.2.1.symm heq.2.2.2.symm hfast

/-! ## 4. Table-level preservation and discharging `hcap_ok` -/

/-- The empty bundle table trivially satisfies `bunTableHeadroomInv`. -/
theorem bunTableHeadroomInv_empty (slotCap : ℕ) :
    bunTableHeadroomInv (slotCap := slotCap) (fun _ => none) ⟨fun _ => none⟩ := by
  intro j B p bunCap hS; cases hS

/-- Multi-slot initialization preserves `bunTableHeadroomInv` whenever every newly initialized slot
spec `(s, bunCap)` has `4 * |(slotEdgesOf assigns s)| ≤ bunCap`. -/
theorem bunTableHeadroomInv_initSlots {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {m₀ : BundleTableMeta slotCap}
    {specs assigns : List (ℕ × ℕ)} {cord : ℕ → List End} {rList : List ℕ} {k h : ℕ}
    (hH₀ : bunTableHeadroomInv S₀ m₀)
    (hk1 : 1 ≤ k) (hspecs_nd : (specs.map Prod.fst).Nodup)
    (hr_nd : rList.Nodup) (hcord_nd : ∀ w ∈ rList, (cord w).Nodup)
    (hcord_disj : ∀ w₁ w₂ x, x ∈ cord w₁ → x ∈ cord w₂ → w₁ = w₂)
    (hcov : ∀ es ∈ assigns, ∀ side : Bool, ∃ v ∈ rList, (es.1, side) ∈ cord v)
    (hcap4 : ∀ sb ∈ specs, 4 * (slotEdgesOf assigns sb.1).card ≤ sb.2) :
    bunTableHeadroomInv (tableAfterInitSlots S₀ specs assigns cord rList k)
      (allocSlotBlocksMeta m₀ specs h) := by
  intro j B p bunCap hSj hm
  unfold tableAfterInitSlots at hSj
  by_cases hmem : j.1 ∈ specs.map Prod.fst
  · simp only [hmem, ↓reduceIte, Option.some.injEq] at hSj
    subst hSj
    obtain ⟨sb, hsb, hsb1⟩ := List.mem_map.mp hmem
    obtain ⟨q, hq, hqeq⟩ := List.getElem_of_mem hsb
    have hblk := allocSlotBlocksMeta_mem m₀ specs h hspecs_nd hq (by simpa [hqeq] using hsb1.symm)
    rw [hblk, Option.some.injEq, Prod.mk.injEq] at hm
    have hbunCap : bunCap = sb.2 := by rw [← hm.2, hqeq]
    rw [hbunCap]
    have hcov_j : ∀ x : End, x.1 ∈ slotEdgesOf assigns j.1 → ∃ v ∈ rList, x ∈ cord v := by
      intro x hx
      unfold slotEdgesOf at hx
      rw [List.mem_toFinset, List.mem_map] at hx
      obtain ⟨es, hes, hxe⟩ := hx
      obtain ⟨hes_in, _⟩ := List.mem_filter.mp hes
      obtain ⟨v, hv, hxv⟩ := hcov es hes_in x.2
      exact ⟨v, hv, by rwa [hxe, Prod.mk.eta] at hxv⟩
    exact bunCapHeadroomInv_of_bundleStateOfSlots hk1 hr_nd hcord_nd hcord_disj hcov_j
      (hsb1 ▸ hcap4 sb hsb)
  · simp only [hmem, ↓reduceIte] at hSj
    rw [allocSlotBlocksMeta_of_not_mem m₀ specs h hmem] at hm
    exact hH₀ j B p bunCap hSj hm

/-- `tableAfterStep` preserves `bunTableHeadroomInv` for any valid `BundleTableRepAt` and candidate
sets inside `B₀.vertices`. -/
theorem bunTableHeadroomInv_tableAfterStep {slotCap vCap eCap tbl : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap} {mem : ℕ → ℕ}
    {D : Finset ℕ} {src' : End → ℕ} {candSet : Fin slotCap → Finset ℕ}
    (hrep : BundleTableRepAt slotCap vCap eCap tbl S₀ m mem)
    (hH₀ : bunTableHeadroomInv S₀ m)
    (hcand_sub : ∀ j B₀, S₀ j = some B₀ → ∀ b ∈ candSet j, b ∈ B₀.vertices) :
    bunTableHeadroomInv (tableAfterStep S₀ D src' candSet) m := by
  intro j B p bunCap hSj hm
  unfold tableAfterStep at hSj
  cases hS₀ : S₀ j with
  | none => simp [hS₀] at hSj
  | some B₀ =>
    simp only [hS₀, Option.some.injEq] at hSj
    subst hSj
    have hslot := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 j
    simp only [hS₀, hm] at hslot
    obtain ⟨nB, hV, -, -, hlive, -⟩ := hslot.2.1
    exact bunCapHeadroomInv_byRootSplitFold (hH₀ j B₀ p bunCap hS₀ hm)
      (fun x hx => by rw [hV, Finset.mem_range]; exact hlive x hx)
      (Finset.sort_nodup (candSet j) (· ≤ ·))
      (fun b hb => hcand_sub j B₀ hS₀ b ((Finset.mem_sort (· ≤ ·)).mp hb))

/-- `bunCapHeadroomInv` directly implies `hcap_ok` of `bunTable_step_runs`:
`B.vertices.card + slotCandEndsSum ≤ bunCap`. -/
theorem bunCapHeadroomInv_implies_cap_ok {slotCap : ℕ} {S₀ : BundleTableState slotCap}
    {D : Finset ℕ} {candSet : Fin slotCap → Finset ℕ} {j : Fin slotCap} {B₀ : BundleState}
    {bunCap : ℕ} (hS : S₀ j = some B₀) (hH : bunCapHeadroomInv B₀ bunCap)
    (hsub : ∀ b ∈ candSet j, b ∈ B₀.vertices) :
    B₀.vertices.card + slotCandEndsSum S₀ D candSet j ≤ bunCap := by
  classical
  set B_del : BundleState := { B₀ with edges := B₀.edges \ D }
  have hsum_eq : slotCandEndsSum S₀ D candSet j = ∑ b ∈ candSet j, (B_del.ends b).card := by
    simp only [slotCandEndsSum, hS, B_del]
    have hnd := Finset.sort_nodup (candSet j) (· ≤ ·)
    rw [← List.sum_toFinset _ hnd]
    exact Finset.sum_congr (by ext b; simp) fun _ _ => rfl
  have hcand_le : ∑ b ∈ candSet j, (B_del.ends b).card ≤ 2 * B₀.edges.card := by
    have h1 : ∑ b ∈ candSet j, (B_del.ends b).card ≤ ∑ b ∈ B_del.vertices, (B_del.ends b).card :=
      Finset.sum_le_sum_of_subset fun b hb => hsub b hb
    have h2 : ∑ b ∈ B_del.vertices, (B_del.ends b).card ≤ 2 * B_del.edges.card :=
      bunEnds_sum_le_two_mul_edges B_del
    have h3 : B_del.edges.card ≤ B₀.edges.card := Finset.card_le_card Finset.sdiff_subset
    omega
  unfold bunCapHeadroomInv at hH
  omega

/-- `bunTableHeadroomInv` directly discharges the `hcap_ok` precondition of `bunTable_step_runs`
and `bunTable_step_model_runs_on`. -/
theorem bunTableHeadroomInv_implies_hcap_ok {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap} {D : Finset ℕ}
    (hH : bunTableHeadroomInv S₀ m) :
    ∀ (candSet : Fin slotCap → Finset ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      (∀ bun ∈ candSet j, bun ∈ B₀.vertices) →
      B₀.vertices.card + slotCandEndsSum S₀ D candSet j ≤ bunCap :=
  fun _ j B₀ ptr bunCap hS hm hsub =>
    bunCapHeadroomInv_implies_cap_ok hS (hH j B₀ ptr bunCap hS hm) hsub

/-- `bunCapHeadroomInv` implies the weaker scanned-end cap condition
`B₀.vertices.card + slotScannedEnds S₀ D cord' gs maxIdxs j ≤ bunCap`, via
`slotScannedEnds_le_slotCandEndsSum`. -/
theorem bunCapHeadroomInv_implies_scanned_cap_ok {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {D : Finset ℕ} {j : Fin slotCap} {B₀ : BundleState}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)} {maxIdxs : List ℕ}
    {bunCap : ℕ}
    (hS : S₀ j = some B₀) (hH : bunCapHeadroomInv B₀ bunCap)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j' (hj' : j' < gs.length), i ≠ j' →
      Disjoint gs[i].toFinset gs[j'].toFinset)
    (hcord_nd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup)
    (hmax_lt : ∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length)
    (hsrc_iff : ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w)
    (hbundle_in_group : ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x ∈ gs[gi].toFinset) :
    B₀.vertices.card + slotScannedEnds S₀ D cord' gs maxIdxs j ≤ bunCap := by
  have hval := (scanValidForSlot_of_scan hS hgs_nd hgs_disj hcord_nd hmax_lt hsrc_iff
    hbundle_in_group).1
  have hscan_le := slotScannedEnds_le_slotCandEndsSum hS hval
  have hcand_eq := scanCands_eq_exactSplitCands hS hgs_nd hcord_nd hmax_lt hsrc_iff
    hbundle_in_group
  have hsub : ∀ b ∈ addCandsForGroups (tableDelEdges S₀ D) cord' gs maxIdxs (fun _ => ∅)
      gs.length j, b ∈ B₀.vertices := by
    intro b hb
    rw [hcand_eq] at hb
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_filter.mp (List.mem_toFinset.mp hb)).1
  have hcap := bunCapHeadroomInv_implies_cap_ok (D := D) hS hH hsub
  omega

/-- `bunTableHeadroomInv` directly discharges the weaker scanned-end `hcap_ok` precondition of
`bunTable_step_runs` and `bunTable_step_model_runs_on`. -/
theorem bunTableHeadroomInv_implies_scanned_hcap_ok {slotCap : ℕ}
    {S₀ : BundleTableState slotCap} {m : BundleTableMeta slotCap} {D : Finset ℕ}
    {cord' : ℕ → List End} {src' : End → ℕ} {gs : List (List ℕ)}
    (hH : bunTableHeadroomInv S₀ m)
    (hgs_nd : ∀ G ∈ gs, G.Nodup)
    (hgs_disj : ∀ i (hi : i < gs.length) j' (hj' : j' < gs.length), i ≠ j' →
      Disjoint gs[i].toFinset gs[j'].toFinset)
    (hcord_nd : ∀ G ∈ gs, ∀ w ∈ G, (cord' w).Nodup)
    (hsrc_iff : ∀ j B₀, S₀ j = some B₀ →
      ∀ x ∈ edgeEnds (B₀.edges \ D), ∀ w, x ∈ cord' w ↔ src' x = w)
    (hbundle_in_group : ∀ j B₀, S₀ j = some B₀ → ∀ b ∈ B₀.vertices,
      2 ≤ (finalRootsOf B₀ (B₀.edges \ D) src' b).card →
        ∃ gi, ∃ (hgi : gi < gs.length),
          ∀ x ∈ survivingEnds B₀ (B₀.edges \ D) b, src' x ∈ gs[gi].toFinset) :
    ∀ (maxIdxs : List ℕ) (j : Fin slotCap) (B₀ : BundleState) (ptr bunCap : ℕ),
      maxIdxs.length = gs.length →
      (∀ gi (hgi : gi < gs.length), maxIdxs.getD gi 0 < gs[gi].length) →
      S₀ j = some B₀ → m.slotBlocks j = some (ptr, bunCap) →
      B₀.vertices.card + slotScannedEnds S₀ D cord' gs maxIdxs j ≤ bunCap :=
  fun _ j B₀ ptr bunCap _ hmax_lt hS hm =>
    bunCapHeadroomInv_implies_scanned_cap_ok hS (hH j B₀ ptr bunCap hS hm)
      hgs_nd hgs_disj hcord_nd hmax_lt (hsrc_iff j B₀ hS) (hbundle_in_group j B₀ hS)

end

end MinCostFlow.SparseCore.Program
