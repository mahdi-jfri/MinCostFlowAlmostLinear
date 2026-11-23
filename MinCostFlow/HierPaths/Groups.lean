module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# The groups of the terminal hierarchy

The path data structure splits its terminals `0, …, P - 1`, with `P = 2 ^ x`, again and again
into groups of consecutive numbers. Each split cuts a group into at most `B = 2 ^ b` children of
equal size. This file fixes the index arithmetic of these groups.

At depth `j` every group has size `groupSize x b j = 2 ^ (x - min x (j * b))`. So the root (depth
`0`) is all of `range P`, each further depth divides the size by `B` until it reaches one, and
from depth `⌈x / b⌉` on all groups are singletons. The group of terminal `u` at depth `j` is
`u / groupSize x b j`, and group `g` has the members `Ico (g * s) ((g + 1) * s)` with
`s = groupSize x b j`.

The main facts:
* `mem_members_iff`, `groupOf_lt_numGroups`, `disjoint_members`, `biUnion_members`: at one depth
  the groups partition `range P`;
* `members_succ_subset` and `eq_parentGroup_of_subset`: a group at depth `j + 1` lies inside
  exactly one group at depth `j`, namely group `g / branching x b j`;
* `branching_eq` and `members_eq_biUnion_children`: a group of size above one has
  `min B s` children, all of size `groupSize x b (j + 1)`;
* `even_groupSize`: sizes above one are even;
* `groupSize_eq_one`: groups at depth at least `leafDepth x b = ⌈x / b⌉` are singletons.

The children of group `g` at depth `j` are the groups of `childGroups x b j g` at depth `j + 1`
(`mem_childGroups_iff`, `members_eq_biUnion_childGroups`).

The path data structure uses this indexing of the groups.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

/-- The size of every group at depth `j`, for `2 ^ x` terminals and branching `2 ^ b`. -/
def groupSize (x b j : ℕ) : ℕ := 2 ^ (x - min x (j * b))

/-- The number of groups at depth `j`. -/
def numGroups (x b j : ℕ) : ℕ := 2 ^ min x (j * b)

/-- The index of the group of terminal `u` at depth `j`. -/
def groupOf (x b j u : ℕ) : ℕ := u / groupSize x b j

/-- The members of group `g` at depth `j`: an interval of consecutive terminals. -/
def members (x b j g : ℕ) : Finset ℕ :=
  Finset.Ico (g * groupSize x b j) ((g + 1) * groupSize x b j)

/-- The number of children of a group at depth `j`, which are groups at depth `j + 1`. -/
def branching (x b j : ℕ) : ℕ := groupSize x b j / groupSize x b (j + 1)

/-- The parent, at depth `j`, of group `g` at depth `j + 1`. -/
def parentGroup (x b j g : ℕ) : ℕ := g / branching x b j

/-- The children of group `g` at depth `j`: the groups at depth `j + 1` whose parent is `g`. -/
def childGroups (x b j g : ℕ) : Finset ℕ :=
  Finset.Ico (g * branching x b j) ((g + 1) * branching x b j)

/-- The depth `⌈x / b⌉` of the leaves: from this depth on, all groups are singletons. -/
def leafDepth (x b : ℕ) : ℕ := (x + b - 1) / b

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

variable {x b j : ℕ}

theorem groupSize_pos : 0 < groupSize x b j := Nat.two_pow_pos _

theorem groupSize_zero : groupSize x b 0 = 2 ^ x := by
  simp [groupSize]

theorem numGroups_mul_groupSize : numGroups x b j * groupSize x b j = 2 ^ x := by
  unfold numGroups groupSize
  rw [← pow_add]
  congr 1
  have := Nat.min_le_left x (j * b)
  omega

theorem card_members (g : ℕ) : (members x b j g).card = groupSize x b j := by
  simp only [members, Nat.card_Ico, Nat.succ_mul]
  omega

private theorem div_eq_iff_mem_Ico {s g u : ℕ} (hs : 0 < s) :
    u ∈ Finset.Ico (g * s) ((g + 1) * s) ↔ u / s = g := by
  rw [Finset.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hs).mpr h2)
    · exact (Nat.le_div_iff_mul_le hs).mpr h1
  · rintro rfl
    exact ⟨Nat.div_mul_le_self u _, (Nat.div_lt_iff_lt_mul hs).mp (Nat.lt_succ_self _)⟩

theorem mem_members_iff {g u : ℕ} : u ∈ members x b j g ↔ groupOf x b j u = g :=
  div_eq_iff_mem_Ico groupSize_pos

/-- Every terminal lies in its own group. -/
theorem mem_members_groupOf (u : ℕ) : u ∈ members x b j (groupOf x b j u) :=
  mem_members_iff.mpr rfl

theorem groupOf_lt_numGroups {u : ℕ} (hu : u < 2 ^ x) : groupOf x b j u < numGroups x b j := by
  unfold groupOf
  rw [Nat.div_lt_iff_lt_mul groupSize_pos, numGroups_mul_groupSize]
  exact hu

theorem members_subset_range {g : ℕ} (hg : g < numGroups x b j) :
    members x b j g ⊆ Finset.range (2 ^ x) := by
  intro u hu
  simp only [members, Finset.mem_Ico] at hu
  rw [Finset.mem_range, ← numGroups_mul_groupSize (j := j) (b := b)]
  exact lt_of_lt_of_le hu.2 (Nat.mul_le_mul_right _ hg)

theorem disjoint_members {g g' : ℕ} (h : g ≠ g') :
    Disjoint (members x b j g) (members x b j g') := by
  rw [Finset.disjoint_left]
  intro u hu hu'
  exact h ((mem_members_iff.mp hu).symm.trans (mem_members_iff.mp hu'))

/-- The groups at one depth partition the terminals. -/
theorem biUnion_members :
    (Finset.range (numGroups x b j)).biUnion (members x b j) = Finset.range (2 ^ x) := by
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨g, hg, hu⟩
    exact Finset.mem_range.mp (members_subset_range hg hu)
  · intro hu
    exact ⟨_, groupOf_lt_numGroups hu, mem_members_groupOf u⟩

/-- At depth `0` there is one group, of all terminals. -/
theorem groupOf_zero {u : ℕ} (hu : u < 2 ^ x) : groupOf x b 0 u = 0 := by
  simp [groupOf, groupSize_zero, Nat.div_eq_of_lt hu]

theorem groupSize_eq_mul_branching :
    groupSize x b j = branching x b j * groupSize x b (j + 1) := by
  unfold branching
  refine (Nat.div_mul_cancel ?_).symm
  unfold groupSize
  apply Nat.pow_dvd_pow
  have : j * b ≤ (j + 1) * b := Nat.mul_le_mul_right _ (Nat.le_succ j)
  omega

theorem branching_pos : 0 < branching x b j := by
  have h := (groupSize_pos : 0 < groupSize x b j)
  rw [groupSize_eq_mul_branching] at h
  exact Nat.pos_of_mul_pos_right h

theorem groupOf_succ_div (u : ℕ) :
    groupOf x b (j + 1) u / branching x b j = groupOf x b j u := by
  unfold groupOf
  rw [Nat.div_div_eq_div_mul, mul_comm, ← groupSize_eq_mul_branching]

/-- Two terminals in one group at depth `j + 1` are in one group at depth `j`. -/
theorem groupOf_eq_of_groupOf_succ_eq {u v : ℕ}
    (h : groupOf x b (j + 1) u = groupOf x b (j + 1) v) : groupOf x b j u = groupOf x b j v := by
  rw [← groupOf_succ_div, h, groupOf_succ_div]

/-- A group at depth `j + 1` lies inside its parent group at depth `j`. -/
theorem members_succ_subset (g : ℕ) :
    members x b (j + 1) g ⊆ members x b j (parentGroup x b j g) := by
  intro u hu
  rw [mem_members_iff] at hu ⊢
  rw [← groupOf_succ_div, hu, parentGroup]

/-- A group at depth `j + 1` lies inside no group at depth `j` except its parent. -/
theorem eq_parentGroup_of_subset {g g' : ℕ} (h : members x b (j + 1) g ⊆ members x b j g') :
    g' = parentGroup x b j g := by
  have hne : (members x b (j + 1) g).Nonempty := by
    rw [← Finset.card_pos, card_members]
    exact groupSize_pos
  obtain ⟨u, hu⟩ := hne
  have h1 := mem_members_iff.mp (h hu)
  have h2 := mem_members_iff.mp (members_succ_subset g hu)
  exact h1.symm.trans h2

/-- A group of size above one has `min (2 ^ b) s` children, for its size `s`. -/
theorem branching_eq (h : 1 < groupSize x b j) :
    branching x b j = min (2 ^ b) (groupSize x b j) := by
  unfold branching groupSize at *
  have hlt : j * b < x := by
    by_contra hc
    have : x - min x (j * b) = 0 := by omega
    rw [this] at h
    simp at h
  have hj : (j + 1) * b = j * b + b := Nat.succ_mul j b
  rw [hj]
  by_cases hb : j * b + b ≤ x
  · rw [min_eq_right hb, min_eq_right hlt.le]
    have e : x - j * b = (x - (j * b + b)) + b := by omega
    rw [e, pow_add, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    exact (min_eq_left (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))).symm
  · rw [min_eq_left (by omega : x ≤ j * b + b), min_eq_right hlt.le, Nat.sub_self, pow_zero,
      Nat.div_one]
    refine (min_eq_right (Nat.pow_le_pow_right Nat.two_pos (by omega))).symm

/-- The parent of a child `g * r + i`, `i < r`, is `g`. -/
theorem parentGroup_child (g : ℕ) {i : ℕ} (hi : i < branching x b j) :
    parentGroup x b j (g * branching x b j + i) = g := by
  rw [parentGroup, Nat.add_comm, Nat.add_mul_div_right _ _ branching_pos, Nat.div_eq_of_lt hi,
    zero_add]

/-- The children of group `g` at depth `j` are the groups `g * r + i` at depth `j + 1`, for
`i < r = branching x b j`. Their members make up the members of `g`. -/
theorem members_eq_biUnion_children (g : ℕ) :
    members x b j g = (Finset.range (branching x b j)).biUnion
      (fun i => members x b (j + 1) (g * branching x b j + i)) := by
  have hr := (branching_pos : 0 < branching x b j)
  ext u
  simp only [Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro hu
    refine ⟨groupOf x b (j + 1) u % branching x b j, Nat.mod_lt _ hr, ?_⟩
    rw [mem_members_iff]
    have h := groupOf_succ_div (x := x) (b := b) (j := j) u
    rw [mem_members_iff.mp hu] at h
    rw [← h]
    exact (Nat.div_add_mod' _ _).symm
  · rintro ⟨i, hi, hu⟩
    have h := members_succ_subset (x := x) (b := b) (j := j) _ hu
    rwa [parentGroup_child g hi] at h

theorem mem_childGroups_iff {g c : ℕ} : c ∈ childGroups x b j g ↔ parentGroup x b j c = g :=
  div_eq_iff_mem_Ico branching_pos

/-- The group of `u` at depth `j + 1` is a child of its group at depth `j`. -/
theorem groupOf_succ_mem_childGroups (u : ℕ) :
    groupOf x b (j + 1) u ∈ childGroups x b j (groupOf x b j u) :=
  mem_childGroups_iff.mpr (groupOf_succ_div u)

/-- The members of a group are the union of the members of its children. -/
theorem members_eq_biUnion_childGroups (g : ℕ) :
    members x b j g = (childGroups x b j g).biUnion (members x b (j + 1)) := by
  ext u
  rw [Finset.mem_biUnion]
  constructor
  · intro hu
    refine ⟨_, ?_, mem_members_groupOf u⟩
    rw [← mem_members_iff.mp hu]
    exact groupOf_succ_mem_childGroups u
  · rintro ⟨c, hc, hu⟩
    have h := members_succ_subset (x := x) (b := b) (j := j) c hu
    rwa [mem_childGroups_iff.mp hc] at h

theorem card_childGroups (g : ℕ) : (childGroups x b j g).card = branching x b j := by
  simp only [childGroups, Nat.card_Ico, Nat.succ_mul]
  omega

/-- Group sizes above one are even. -/
theorem even_groupSize (h : 1 < groupSize x b j) : Even (groupSize x b j) := by
  unfold groupSize at *
  have : x - min x (j * b) ≠ 0 := by
    intro h0
    rw [h0] at h
    simp at h
  exact (Nat.even_pow' this).mpr ⟨1, rfl⟩

/-- From depth `x / b` (rounded up) on, groups are singletons. -/
theorem groupSize_eq_one (hb : 0 < b) (hj : leafDepth x b ≤ j) : groupSize x b j = 1 := by
  unfold groupSize leafDepth at *
  have : x ≤ j * b := by
    have h1 := (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_of_le hj)
    rw [Nat.succ_mul] at h1
    omega
  rw [min_eq_left this, Nat.sub_self, pow_zero]

end MinCostFlow.HierPaths
