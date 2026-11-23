module

public import MinCostFlow.HierPaths.Groups
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lost terminals and their number

A deletion in the path data structure marks some terminals as *directly failed*. From the set
`F` of directly failed terminals, this file defines which terminals are *lost*. The rule works
from the leaves of the group hierarchy (`HierPaths/Groups.lean`) up to the root:

* at a leaf group (depth at least `leafDepth x b`), the lost set is `members ∩ F`;
* at a larger group `X`, let `D` be the union of the lost sets of the children. If
  `4 |D| > |X|`, the whole group is lost. Otherwise the lost set is `D`.

The lost set of the root is the *global* lost set. The idea is that a group which keeps three
quarters of its terminals still has many intact matching edges to each sibling (`exists_surviving_matching_edge`), and a
group that loses more is given up as a whole, at the price of a factor four per level.

Main results:
* `lost_subset_members` and `lost_mono`: lost sets lie in the members and grow with `F`;
* `card_lost_le`: `|lost X| ≤ 4 ^ height · |F ∩ X|`;
* `not_mem_lost_of_not_mem_globalLost`, `four_mul_card_lost_le` and `globalLost_inter_members`:
  if `u` is not globally lost, then no group containing `u` loses `u`, each such group loses at
  most a quarter of its members, and the global lost set meets it exactly in its own lost set.
-/

public section

namespace MinCostFlow.HierPaths

open Finset

/-- The lost set of group `g` at depth `j`, for the set `F` of directly failed terminals. -/
def lost (x b : ℕ) (F : Finset ℕ) (j g : ℕ) : Finset ℕ :=
  if leafDepth x b ≤ j then members x b j g ∩ F
  else
    if groupSize x b j < 4 * ((childGroups x b j g).biUnion (lost x b F (j + 1))).card then
      members x b j g
    else (childGroups x b j g).biUnion (lost x b F (j + 1))
termination_by leafDepth x b - j

/-- The globally lost terminals: the lost set of the root. -/
def globalLost (x b : ℕ) (F : Finset ℕ) : Finset ℕ := lost x b F 0 0

variable {x b : ℕ} {F : Finset ℕ}

theorem globalLost_eq : globalLost x b F = lost x b F 0 0 := by rw [globalLost]

theorem lost_of_le {j : ℕ} (h : leafDepth x b ≤ j) (g : ℕ) :
    lost x b F j g = members x b j g ∩ F := by
  rw [lost]
  simp only [eq_true h, ↓reduceIte]

theorem lost_of_lt {j : ℕ} (h : j < leafDepth x b) (g : ℕ) :
    lost x b F j g =
      if groupSize x b j < 4 * ((childGroups x b j g).biUnion (lost x b F (j + 1))).card then
        members x b j g
      else (childGroups x b j g).biUnion (lost x b F (j + 1)) := by
  rw [lost]
  simp only [eq_false (Nat.not_le.mpr h), ↓reduceIte]

/-- Lost sets lie inside the members of their group. -/
theorem lost_subset_members (j g : ℕ) : lost x b F j g ⊆ members x b j g := by
  induction h : leafDepth x b - j generalizing j g with
  | zero =>
    rw [lost_of_le (by omega)]
    exact inter_subset_left
  | succ k ih =>
    rw [lost_of_lt (by omega)]
    split_ifs
    · exact Subset.rfl
    · rw [members_eq_biUnion_childGroups]
      exact biUnion_subset_biUnion_of_subset_left _ Subset.rfl |>.trans
        (biUnion_mono fun c _ => ih (j + 1) c (by omega))

/-- Lost sets grow with the set of directly failed terminals. -/
theorem lost_mono {F F' : Finset ℕ} (hF : F ⊆ F') (j g : ℕ) :
    lost x b F j g ⊆ lost x b F' j g := by
  induction h : leafDepth x b - j generalizing j g with
  | zero =>
    rw [lost_of_le (by omega), lost_of_le (by omega)]
    exact inter_subset_inter Subset.rfl hF
  | succ k ih =>
    have hD : (childGroups x b j g).biUnion (lost x b F (j + 1)) ⊆
        (childGroups x b j g).biUnion (lost x b F' (j + 1)) :=
      biUnion_mono fun c _ => ih (j + 1) c (by omega)
    have hDm : (childGroups x b j g).biUnion (lost x b F' (j + 1)) ⊆ members x b j g := by
      rw [members_eq_biUnion_childGroups]
      exact biUnion_mono fun c _ => lost_subset_members (j + 1) c
    rw [lost_of_lt (by omega), lost_of_lt (by omega)]
    split_ifs with h1 h2 h2
    · exact Subset.rfl
    · exact absurd (lt_of_lt_of_le h1 (Nat.mul_le_mul_left 4 (card_le_card hD))) h2
    · exact hD.trans hDm
    · exact hD

/-- The children of a group have disjoint members. -/
theorem pairwiseDisjoint_childGroups (j g : ℕ) :
    (childGroups x b j g : Set ℕ).PairwiseDisjoint (members x b (j + 1)) :=
  fun _ _ _ _ hne => disjoint_members hne

/-- The sum over the children of the failed terminals they contain. -/
theorem sum_card_inter_childGroups (j g : ℕ) :
    ∑ c ∈ childGroups x b j g, (F ∩ members x b (j + 1) c).card = (F ∩ members x b j g).card := by
  rw [members_eq_biUnion_childGroups, inter_biUnion, card_biUnion]
  intro c _ c' _ hne
  exact Disjoint.mono inter_subset_right inter_subset_right (disjoint_members hne)

/-- **Loss bound.** A group of height `leafDepth x b - j` loses
at most `4 ^ height` times its number of directly failed terminals. -/
theorem card_lost_le (j g : ℕ) :
    (lost x b F j g).card ≤ 4 ^ (leafDepth x b - j) * (F ∩ members x b j g).card := by
  induction h : leafDepth x b - j generalizing j g with
  | zero =>
    rw [lost_of_le (by omega), pow_zero, one_mul, inter_comm]
  | succ k ih =>
    have hD : ((childGroups x b j g).biUnion (lost x b F (j + 1))).card ≤
        4 ^ k * (F ∩ members x b j g).card := by
      calc ((childGroups x b j g).biUnion (lost x b F (j + 1))).card
          ≤ ∑ c ∈ childGroups x b j g, (lost x b F (j + 1) c).card := card_biUnion_le
        _ ≤ ∑ c ∈ childGroups x b j g, 4 ^ k * (F ∩ members x b (j + 1) c).card :=
            sum_le_sum fun c _ => ih (j + 1) c (by omega)
        _ = 4 ^ k * (F ∩ members x b j g).card := by
            rw [← mul_sum, sum_card_inter_childGroups]
    rw [lost_of_lt (by omega), pow_succ]
    split_ifs with h1
    · rw [card_members]
      calc groupSize x b j ≤ 4 * ((childGroups x b j g).biUnion (lost x b F (j + 1))).card :=
            h1.le
        _ ≤ 4 * (4 ^ k * (F ∩ members x b j g).card) := Nat.mul_le_mul_left 4 hD
        _ = 4 ^ k * 4 * (F ∩ members x b j g).card := by rw [← Nat.mul_assoc, Nat.mul_comm 4]
    · calc _ ≤ 4 ^ k * (F ∩ members x b j g).card := hD
        _ ≤ 4 ^ k * 4 * (F ∩ members x b j g).card := by
            apply Nat.mul_le_mul_right
            exact Nat.le_mul_of_pos_right _ (by decide)

/-- **The bound `card_lost_le`** for the root: at most `4 ^ leafDepth x b · |F|` terminals are globally lost. -/
theorem card_globalLost_le : (globalLost x b F).card ≤ 4 ^ leafDepth x b * F.card := by
  have h := card_lost_le (x := x) (b := b) (F := F) 0 0
  rw [Nat.sub_zero] at h
  exact h.trans (Nat.mul_le_mul_left _ (card_le_card inter_subset_left))

theorem globalLost_subset_range : globalLost x b F ⊆ range (2 ^ x) := by
  have h := lost_subset_members (x := x) (b := b) (F := F) 0 0
  rw [members, groupSize_zero, zero_mul, zero_add, one_mul] at h
  intro u hu
  exact mem_range.mpr (mem_Ico.mp (h hu)).2

theorem globalLost_mono {F F' : Finset ℕ} (hF : F ⊆ F') : globalLost x b F ⊆ globalLost x b F' :=
  lost_mono hF 0 0

/-- If a group loses `u`, so does its parent. -/
theorem mem_lost_groupOf_of_succ {u j : ℕ} (h : u ∈ lost x b F (j + 1) (groupOf x b (j + 1) u)) :
    u ∈ lost x b F j (groupOf x b j u) := by
  by_cases hj : leafDepth x b ≤ j
  · rw [lost_of_le (by omega)] at h
    rw [lost_of_le hj]
    exact mem_inter.mpr ⟨mem_members_groupOf u, (mem_inter.mp h).2⟩
  · have hD : u ∈ (childGroups x b j (groupOf x b j u)).biUnion (lost x b F (j + 1)) :=
      mem_biUnion.mpr ⟨_, groupOf_succ_mem_childGroups u, h⟩
    rw [lost_of_lt (Nat.not_le.mp hj)]
    split_ifs
    · exact mem_members_groupOf u
    · exact hD

/-- If a group at depth `j` loses `u`, then `u` is globally lost. -/
theorem mem_globalLost_of_mem_lost {u : ℕ} (hu : u < 2 ^ x) {j : ℕ}
    (h : u ∈ lost x b F j (groupOf x b j u)) : u ∈ globalLost x b F := by
  induction j with
  | zero =>
    rw [groupOf_zero hu] at h
    exact h
  | succ j ih => exact ih (mem_lost_groupOf_of_succ h)

/-- If `u` is not globally lost, then no group containing `u` loses `u`; in particular no such
group is wholly lost. -/
theorem not_mem_lost_of_not_mem_globalLost {u : ℕ} (hu : u < 2 ^ x)
    (h : u ∉ globalLost x b F) (j : ℕ) : u ∉ lost x b F j (groupOf x b j u) :=
  fun h' => h (mem_globalLost_of_mem_lost hu h')

/-- If `u` is not globally lost, no group containing `u` is wholly lost. -/
theorem lost_ne_members_of_not_mem_globalLost {u : ℕ} (hu : u < 2 ^ x)
    (h : u ∉ globalLost x b F) (j : ℕ) :
    lost x b F j (groupOf x b j u) ≠ members x b j (groupOf x b j u) := fun he =>
  not_mem_lost_of_not_mem_globalLost hu h j (he ▸ mem_members_groupOf u)

/-- If `u` is not globally lost, every group containing `u` loses at most a quarter of its
members. -/
theorem four_mul_card_lost_le (hb : 0 < b) {u : ℕ} (hu : u < 2 ^ x) (h : u ∉ globalLost x b F) (j : ℕ) :
    4 * (lost x b F j (groupOf x b j u)).card ≤ groupSize x b j := by
  have hn := not_mem_lost_of_not_mem_globalLost hu h j
  by_cases hj : leafDepth x b ≤ j
  · have hsub : lost x b F j (groupOf x b j u) ⊆ members x b j (groupOf x b j u) \ {u} :=
      fun v hv => mem_sdiff.mpr ⟨lost_subset_members j _ hv,
        fun hvu => hn (mem_singleton.mp hvu ▸ hv)⟩
    have h1 := card_le_card hsub
    rw [card_sdiff_of_subset (singleton_subset_iff.mpr (mem_members_groupOf u)), card_members,
      card_singleton, groupSize_eq_one hb hj] at h1
    rw [groupSize_eq_one hb hj]
    omega
  · rw [lost_of_lt (Nat.not_le.mp hj)] at hn ⊢
    split_ifs with h1
    · simp only [eq_true h1, ↓reduceIte] at hn
      exact absurd (mem_members_groupOf u) hn
    · exact Nat.not_lt.mp h1

/-- If a group does not lose `u`, its lost set meets the child of `u` exactly in the lost set of
that child. -/
theorem lost_inter_members_succ {u j : ℕ} (hn : u ∉ lost x b F j (groupOf x b j u)) :
    lost x b F j (groupOf x b j u) ∩ members x b (j + 1) (groupOf x b (j + 1) u) =
      lost x b F (j + 1) (groupOf x b (j + 1) u) := by
  have hsub : members x b (j + 1) (groupOf x b (j + 1) u) ⊆ members x b j (groupOf x b j u) := by
    have h := members_succ_subset (x := x) (b := b) (j := j) (groupOf x b (j + 1) u)
    rwa [parentGroup, groupOf_succ_div] at h
  by_cases hj : leafDepth x b ≤ j
  · rw [lost_of_le hj, lost_of_le (by omega), inter_right_comm, inter_eq_right.mpr hsub]
  · rw [lost_of_lt (Nat.not_le.mp hj)] at hn ⊢
    split_ifs at hn ⊢ with h1
    · exact absurd (mem_members_groupOf u) hn
    · ext v
      simp only [mem_inter, mem_biUnion]
      constructor
      · rintro ⟨⟨c, _, hv⟩, hv'⟩
        have hc := mem_members_iff.mp (lost_subset_members (j + 1) c hv)
        rw [mem_members_iff.mp hv'] at hc
        rwa [← hc] at hv
      · intro hv
        exact ⟨⟨_, groupOf_succ_mem_childGroups u, hv⟩, lost_subset_members (j + 1) _ hv⟩

/-- If `u` is not globally lost, the global lost set meets each group containing `u` exactly in
the lost set of that group. -/
theorem globalLost_inter_members {u : ℕ} (hu : u < 2 ^ x) (h : u ∉ globalLost x b F) (j : ℕ) :
    globalLost x b F ∩ members x b j (groupOf x b j u) = lost x b F j (groupOf x b j u) := by
  induction j with
  | zero =>
    rw [groupOf_zero hu, globalLost]
    exact inter_eq_left.mpr (lost_subset_members 0 0)
  | succ j ih =>
    have hsub : members x b (j + 1) (groupOf x b (j + 1) u) ⊆
        members x b j (groupOf x b j u) := by
      have h := members_succ_subset (x := x) (b := b) (j := j) (groupOf x b (j + 1) u)
      rwa [parentGroup, groupOf_succ_div] at h
    rw [← lost_inter_members_succ (not_mem_lost_of_not_mem_globalLost hu h j), ← ih,
      inter_assoc, inter_eq_right.mpr hsub]

end MinCostFlow.HierPaths
