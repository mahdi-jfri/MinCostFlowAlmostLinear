module

public import MinCostFlow.HierPaths.Loss

/-!
# How the lost sets change when one terminal fails

This file prepares the proof that the loss counters (`HierPaths/LossCounters.lean`) compute
the lost sets of `HierPaths/Loss.lean`. Throughout, `F' = insert u F` with `u ∉ F`: one new
terminal `u` fails directly.

* `lost_congr`, `lost_insert_of_groupOf_ne`: the lost set of a group depends only on which of its
  own members failed. So a new failure of `u` changes only the groups on the chain of `u`.
* `card_childUnion_insert`: on that chain, the union `D` of the children's lost sets grows by
  exactly as much as the lost set of the child of `u` grows. This is the integer rule that the
  counters pass up.
* `lost_insert_eq_of_succ`: if the lost set of the child of `u` did not change, the lost set of
  its parent did not change either. This is why the counters may stop when the change is zero.
* `mem_globalLost_iff`: a terminal is globally lost exactly when it failed directly or some group
  of its chain (above the leaves) is wholly lost.
* `globalLost_insert` and `card_fullSet_insert`: the new global lost set is the old one, plus `u`,
  plus the members of the groups on the chain of `u` that become wholly lost.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The union of the lost sets of the children of group `g` at depth `j`. -/
def childUnion (x b : ℕ) (F : Finset ℕ) (j g : ℕ) : Finset ℕ :=
  (childGroups x b j g).biUnion (lost x b F (j + 1))

/-- Group `g` at depth `j` is wholly lost under `F'` but not under `F`. -/
def NewlyFull (x b : ℕ) (F F' : Finset ℕ) (j g : ℕ) : Prop :=
  lost x b F' j g = members x b j g ∧ lost x b F j g ≠ members x b j g

instance (x b : ℕ) (F F' : Finset ℕ) (j g : ℕ) : Decidable (NewlyFull x b F F' j g) := by
  unfold NewlyFull; infer_instance

/-- The terminals whose group at depth `j` is wholly lost. -/
def fullSet (x b : ℕ) (F : Finset ℕ) (j : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ x)).filter
    (fun v => lost x b F j (groupOf x b j v) = members x b j (groupOf x b j v))

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open Finset

variable {x b : ℕ} {F : Finset ℕ}

theorem lost_of_lt_childUnion {j : ℕ} (h : j < leafDepth x b) (g : ℕ) :
    lost x b F j g =
      if groupSize x b j < 4 * (childUnion x b F j g).card then members x b j g
      else childUnion x b F j g :=
  lost_of_lt h g

theorem childUnion_subset_members (j g : ℕ) : childUnion x b F j g ⊆ members x b j g := by
  rw [childUnion, members_eq_biUnion_childGroups]
  exact biUnion_mono fun c _ => lost_subset_members (j + 1) c

theorem card_lost_of_lt {j : ℕ} (h : j < leafDepth x b) (g : ℕ) :
    (lost x b F j g).card =
      if groupSize x b j < 4 * (childUnion x b F j g).card then groupSize x b j
      else (childUnion x b F j g).card := by
  rw [lost_of_lt_childUnion h]
  split_ifs
  · exact card_members g
  · rfl

/-- The lost set of a group depends only on which of its members failed. -/
theorem lost_congr {F F' : Finset ℕ} (j g : ℕ) (h : ∀ v ∈ members x b j g, v ∈ F ↔ v ∈ F') :
    lost x b F j g = lost x b F' j g := by
  induction hk : leafDepth x b - j generalizing j g with
  | zero =>
    rw [lost_of_le (by omega), lost_of_le (by omega)]
    ext v
    simp only [mem_inter]
    exact ⟨fun hv => ⟨hv.1, (h v hv.1).mp hv.2⟩, fun hv => ⟨hv.1, (h v hv.1).mpr hv.2⟩⟩
  | succ k ih =>
    have hD : childUnion x b F j g = childUnion x b F' j g := by
      unfold childUnion
      refine biUnion_congr rfl fun c hc => ih (j + 1) c (fun v hv => h v ?_) (by omega)
      rw [members_eq_biUnion_childGroups]
      exact mem_biUnion.mpr ⟨c, hc, hv⟩
    rw [lost_of_lt_childUnion (by omega), lost_of_lt_childUnion (by omega), hD]

/-- A new failure of `u` leaves the groups not containing `u` unchanged. -/
theorem lost_insert_of_groupOf_ne {u j g : ℕ} (h : groupOf x b j u ≠ g) :
    lost x b (insert u F) j g = lost x b F j g := by
  refine lost_congr j g fun v hv => ?_
  rw [mem_insert]
  constructor
  · rintro (rfl | hv')
    · exact absurd (mem_members_iff.mp hv) h
    · exact hv'
  · exact Or.inr

theorem childUnion_insert_of_groupOf_ne {u j g : ℕ} (h : groupOf x b j u ≠ g) :
    childUnion x b (insert u F) j g = childUnion x b F j g := by
  unfold childUnion
  refine biUnion_congr rfl fun c hc => lost_insert_of_groupOf_ne fun he => h ?_
  rw [← mem_childGroups_iff.mp hc, ← he, parentGroup, groupOf_succ_div]

/-- On the chain of `u`, the union of the children's lost sets grows exactly as the lost set of
the child of `u` grows. -/
theorem card_childUnion_insert (u j : ℕ) :
    (childUnion x b (insert u F) j (groupOf x b j u)).card =
      (childUnion x b F j (groupOf x b j u)).card +
        ((lost x b (insert u F) (j + 1) (groupOf x b (j + 1) u)).card -
          (lost x b F (j + 1) (groupOf x b (j + 1) u)).card) := by
  set A := childUnion x b F j (groupOf x b j u)
  set A' := childUnion x b (insert u F) j (groupOf x b j u)
  set L := lost x b F (j + 1) (groupOf x b (j + 1) u)
  set L' := lost x b (insert u F) (j + 1) (groupOf x b (j + 1) u)
  have hmono : ∀ c, lost x b F (j + 1) c ⊆ lost x b (insert u F) (j + 1) c :=
    fun c => lost_mono (subset_insert u F) (j + 1) c
  have hAA : A ⊆ A' := biUnion_mono fun c _ => hmono c
  have hLL : L ⊆ L' := hmono _
  have hX := groupOf_succ_mem_childGroups (x := x) (b := b) (j := j) u
  have hdiff : A' \ A = L' \ L := by
    ext v
    simp only [A, A', childUnion, mem_sdiff, mem_biUnion]
    constructor
    · rintro ⟨⟨c, hc, hv⟩, hn⟩
      by_cases hcu : c = groupOf x b (j + 1) u
      · subst hcu
        exact ⟨hv, fun hv' => hn ⟨_, hc, hv'⟩⟩
      · rw [lost_insert_of_groupOf_ne (Ne.symm hcu)] at hv
        exact absurd ⟨c, hc, hv⟩ hn
    · rintro ⟨hv, hn⟩
      refine ⟨⟨_, hX, hv⟩, ?_⟩
      rintro ⟨c, _, hv'⟩
      have h1 := mem_members_iff.mp (lost_subset_members (j + 1) c hv')
      have h2 := mem_members_iff.mp (lost_subset_members (j + 1) _ hv)
      rw [h2] at h1
      rw [← h1] at hv'
      exact hn hv'
  have h1 := card_sdiff_add_card_eq_card hAA
  rw [hdiff, card_sdiff_of_subset hLL] at h1
  omega

/-- If the lost set of the child of `u` did not change, neither did that of its parent. -/
theorem lost_insert_eq_of_succ {u j : ℕ} (hj : j < leafDepth x b)
    (h : lost x b (insert u F) (j + 1) (groupOf x b (j + 1) u) =
      lost x b F (j + 1) (groupOf x b (j + 1) u)) :
    lost x b (insert u F) j (groupOf x b j u) = lost x b F j (groupOf x b j u) := by
  have hc := card_childUnion_insert (x := x) (b := b) (F := F) u j
  rw [h, Nat.sub_self, Nat.add_zero] at hc
  have hsub : childUnion x b F j (groupOf x b j u) ⊆
      childUnion x b (insert u F) j (groupOf x b j u) :=
    biUnion_mono fun c _ => lost_mono (subset_insert u F) (j + 1) c
  have he := eq_of_subset_of_card_le hsub hc.le
  rw [lost_of_lt_childUnion hj, lost_of_lt_childUnion hj, he]

/-- If the lost set of the group of `u` at depth `j ≤ leafDepth` did not change, then neither did
the lost sets of the groups of `u` above it. -/
theorem lost_insert_eq_of_le {u j : ℕ} (hj : j ≤ leafDepth x b)
    (h : lost x b (insert u F) j (groupOf x b j u) = lost x b F j (groupOf x b j u))
    {i : ℕ} (hi : i ≤ j) :
    lost x b (insert u F) i (groupOf x b i u) = lost x b F i (groupOf x b i u) := by
  induction hk : j - i generalizing i with
  | zero => rwa [show i = j by omega]
  | succ k ih => exact lost_insert_eq_of_succ (by omega) (ih (by omega) (by omega))

/-- If `v` is in the lost set of its group at depth `j`, then `v` failed directly or some group of
`v` at a depth between `j` and the leaves is wholly lost. -/
private theorem failed_or_full_of_mem_lost {v j : ℕ} (h : v ∈ lost x b F j (groupOf x b j v)) :
    v ∈ F ∨ ∃ i < leafDepth x b,
      lost x b F i (groupOf x b i v) = members x b i (groupOf x b i v) := by
  induction hk : leafDepth x b - j generalizing j with
  | zero =>
    rw [lost_of_le (by omega)] at h
    exact Or.inl (mem_inter.mp h).2
  | succ k ih =>
    have hj : j < leafDepth x b := by omega
    by_cases hf : lost x b F j (groupOf x b j v) = members x b j (groupOf x b j v)
    · exact Or.inr ⟨j, hj, hf⟩
    · rw [lost_of_lt_childUnion hj] at h hf
      split_ifs at h hf with h1
      · exact absurd rfl hf
      · obtain ⟨c, _, hv⟩ := mem_biUnion.mp h
        have hc := mem_members_iff.mp (lost_subset_members (j + 1) c hv)
        rw [← hc] at hv
        exact ih hv (by omega)

/-- A terminal is globally lost exactly when it failed directly or one of its groups above the
leaves is wholly lost. -/
theorem mem_globalLost_iff {v : ℕ} :
    v ∈ globalLost x b F ↔ v < 2 ^ x ∧ (v ∈ F ∨ ∃ i < leafDepth x b,
      lost x b F i (groupOf x b i v) = members x b i (groupOf x b i v)) := by
  constructor
  · intro h
    have hv := mem_range.mp (globalLost_subset_range h)
    refine ⟨hv, failed_or_full_of_mem_lost (j := 0) ?_⟩
    rw [groupOf_zero hv, ← globalLost_eq]
    exact h
  · rintro ⟨hv, hF | ⟨i, _, hi⟩⟩
    · refine mem_globalLost_of_mem_lost hv (j := leafDepth x b) ?_
      rw [lost_of_le le_rfl]
      exact mem_inter.mpr ⟨mem_members_groupOf v, hF⟩
    · exact mem_globalLost_of_mem_lost hv (hi ▸ mem_members_groupOf v)

theorem fullSet_subset_globalLost {i : ℕ} (hi : i < leafDepth x b) :
    fullSet x b F i ⊆ globalLost x b F := by
  intro v hv
  rw [fullSet, mem_filter, mem_range] at hv
  exact mem_globalLost_iff.mpr ⟨hv.1, Or.inr ⟨i, hi, hv.2⟩⟩

theorem mem_globalLost_of_mem {v : ℕ} (hv : v < 2 ^ x) (hF : v ∈ F) : v ∈ globalLost x b F :=
  mem_globalLost_iff.mpr ⟨hv, Or.inl hF⟩

/-- The new global lost set after a failure of `u`: the old one, `u`, and the members of the
groups of `u` that become wholly lost. -/
theorem globalLost_insert {u : ℕ} (hu : u < 2 ^ x) :
    globalLost x b (insert u F) = globalLost x b F ∪ {u} ∪
      ((range (leafDepth x b)).filter
        (fun i => NewlyFull x b F (insert u F) i (groupOf x b i u))).biUnion
        (fun i => members x b i (groupOf x b i u)) := by
  ext v
  simp only [mem_union, mem_singleton, mem_biUnion, mem_filter, mem_range]
  constructor
  · intro h
    obtain ⟨hv, hF | ⟨i, hi, hfull⟩⟩ := mem_globalLost_iff.mp h
    · rcases mem_insert.mp hF with rfl | hF
      · exact Or.inl (Or.inr rfl)
      · exact Or.inl (Or.inl (mem_globalLost_of_mem hv hF))
    · by_cases hg : groupOf x b i u = groupOf x b i v
      · by_cases hold : lost x b F i (groupOf x b i v) = members x b i (groupOf x b i v)
        · exact Or.inl (Or.inl (mem_globalLost_iff.mpr ⟨hv, Or.inr ⟨i, hi, hold⟩⟩))
        · refine Or.inr ⟨i, ⟨hi, ?_⟩, ?_⟩
          · rw [hg]; exact ⟨hfull, hold⟩
          · rw [hg]; exact mem_members_groupOf v
      · rw [lost_insert_of_groupOf_ne hg] at hfull
        exact Or.inl (Or.inl (mem_globalLost_iff.mpr ⟨hv, Or.inr ⟨i, hi, hfull⟩⟩))
  · rintro ((h | rfl) | ⟨i, ⟨hi, hnew⟩, hv⟩)
    · exact globalLost_mono (subset_insert _ _) h
    · exact mem_globalLost_of_mem hu (mem_insert_self _ _)
    · have hvx : v < 2 ^ x := mem_range.mp (members_subset_range (groupOf_lt_numGroups hu) hv)
      rw [mem_members_iff] at hv
      refine mem_globalLost_iff.mpr ⟨hvx, Or.inr ⟨i, hi, ?_⟩⟩
      rw [hv]
      exact hnew.1

/-- After a failure of `u`, the terminals with a wholly lost group at depth `i` grow by the
members of the group of `u` if it becomes wholly lost, and are unchanged otherwise. -/
theorem card_fullSet_insert {u : ℕ} (hu : u < 2 ^ x) (i : ℕ) :
    (fullSet x b (insert u F) i).card = (fullSet x b F i).card +
      if NewlyFull x b F (insert u F) i (groupOf x b i u) then groupSize x b i else 0 := by
  have hsub : fullSet x b F i ⊆ fullSet x b (insert u F) i := by
    intro v hv
    rw [fullSet, mem_filter] at hv ⊢
    refine ⟨hv.1, le_antisymm (lost_subset_members i _) ?_⟩
    rw [← hv.2]
    exact lost_mono (subset_insert u F) i _
  have hdiff : fullSet x b (insert u F) i \ fullSet x b F i =
      if NewlyFull x b F (insert u F) i (groupOf x b i u) then members x b i (groupOf x b i u)
      else ∅ := by
    ext v
    simp only [fullSet, mem_sdiff, mem_filter, mem_range, not_and]
    constructor
    · rintro ⟨⟨hv, hfull⟩, hold⟩
      by_cases hg : groupOf x b i u = groupOf x b i v
      · rw [← hg] at hfull hold
        simp only [show NewlyFull x b F (insert u F) i (groupOf x b i u) from ⟨hfull, hold hv⟩,
          ↓reduceIte]
        rw [mem_members_iff, hg]
      · rw [lost_insert_of_groupOf_ne hg] at hfull
        exact absurd hfull (hold hv)
    · intro h
      split_ifs at h with hnew
      · have hvx : v < 2 ^ x := mem_range.mp (members_subset_range (groupOf_lt_numGroups hu) h)
        rw [mem_members_iff] at h
        rw [h]
        exact ⟨⟨hvx, hnew.1⟩, fun _ => hnew.2⟩
      · exact absurd h (notMem_empty v)
  have h1 := card_sdiff_add_card_eq_card hsub
  rw [hdiff] at h1
  split_ifs at h1 ⊢
  · rw [card_members] at h1; omega
  · rw [card_empty] at h1; omega

end MinCostFlow.HierPaths
