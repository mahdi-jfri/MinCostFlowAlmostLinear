module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The total length of the split lists of one update

At each core split of an update, the helper `outSmallSide` lists the marked ends of the smaller
of the two parts, counted in marked ends. At that time the marks are the ends of the old output
graph that the tour still holds. So a list holds the ends of the kept output edges, which the
output batch pays for, and also ends of leaving edges, which it does not pay for.

Within one update the core vertices are only split, never merged: the core batch has splits,
insertions and deletions only (`canonCoreBatch`). So the marked ends of the core lists form a
partition that only gets finer. This file bounds the total length of the split lists in that
setting by the encoding size of the restricted splits plus a log factor per leaving end. The tool
is a potential on each block `P` of marked ends, with `K` the kept ends:
`splitPot K P = |P \ K| · (⌊log₂ (|P ∩ K| + 1)⌋ + ⌊log₂ |P|⌋)`.

* `splitPot_split`: when a block splits into `P₁` and `P₂` and the helper lists the smaller one
  `Y`, then `|Y|` plus the new potential is at most `min (|P₁ ∩ K|, |P₂ ∩ K|)` plus the old
  potential. The minimum is the encoding size of the split of the output graph, less one.
* `splitPot_sum_le_of_refines`: when the blocks only get finer (and lose ends), the total
  potential does not grow.
* `splitPot_le`: a block's potential is at most `2 ⌊log₂ (|P| + 1)⌋` per leaving end.

So the total length of the lists of one update is at most the encoding size of its splits plus
`2 ⌊log₂ (2 eCap + 1)⌋` times the number of leaving ends that the tour marks at the start.

The reason for the two log terms: when the smaller part (in marked ends) also has at most as many
kept ends, its leaving ends pay, and their block halves in size. Otherwise the leaving ends of the
other part pay, and their block keeps fewer than half of the kept ends.
-/

public section

namespace MinCostFlow.SparseCore.Program

variable {α : Type*} [DecidableEq α]

/-- The potential of a block `P` of marked ends, with kept ends `K`: the number of leaving ends
times `⌊log₂ (|P ∩ K| + 1)⌋ + ⌊log₂ |P|⌋`. -/
def splitPot (K P : Finset α) : ℕ :=
  (P \ K).card * (Nat.log 2 ((P ∩ K).card + 1) + Nat.log 2 P.card)

/-- The list that the helper takes: the first part when it has at most as many marked ends. -/
def splitPick (P₁ P₂ : Finset α) : Finset α := if P₁.card ≤ P₂.card then P₁ else P₂

theorem splitPot_mono (K : Finset α) {P Q : Finset α} (h : P ⊆ Q) :
    splitPot K P ≤ splitPot K Q := by
  unfold splitPot
  apply Nat.mul_le_mul (Finset.card_le_card (Finset.sdiff_subset_sdiff h le_rfl))
  apply Nat.add_le_add
  · exact Nat.log_mono_right (Nat.add_le_add_right
      (Finset.card_le_card (Finset.inter_subset_inter h (le_refl K))) 1)
  · exact Nat.log_mono_right (Finset.card_le_card h)

/-- The potential is superadditive over disjoint blocks. -/
theorem splitPot_add_le (K : Finset α) {P₁ P₂ : Finset α} (hd : Disjoint P₁ P₂) :
    splitPot K P₁ + splitPot K P₂ ≤ splitPot K (P₁ ∪ P₂) := by
  have hcard : ((P₁ ∪ P₂) \ K).card = (P₁ \ K).card + (P₂ \ K).card := by
    rw [Finset.union_sdiff_distrib]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hd))
  have hk₁ := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Finset.card_le_card
    (Finset.inter_subset_inter (Finset.subset_union_left (s₁ := P₁) (s₂ := P₂))
      (le_refl K))) 1)
  have hk₂ := Nat.log_mono_right (b := 2) (Nat.add_le_add_right (Finset.card_le_card
    (Finset.inter_subset_inter (Finset.subset_union_right (s₁ := P₁) (s₂ := P₂))
      (le_refl K))) 1)
  have hc₁ := Nat.log_mono_right (b := 2) (Finset.card_le_card
    (Finset.subset_union_left (s₁ := P₁) (s₂ := P₂)))
  have hc₂ := Nat.log_mono_right (b := 2) (Finset.card_le_card
    (Finset.subset_union_right (s₁ := P₁) (s₂ := P₂)))
  unfold splitPot
  rw [hcard, Nat.add_mul]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add hk₁ hc₁))
    (Nat.mul_le_mul_left _ (Nat.add_le_add hk₂ hc₂))

/-- `⌊log₂ n⌋ + 1 ≤ ⌊log₂ m⌋` when `1 ≤ n` and `2 n ≤ m`. -/
private theorem log_succ_le {n m : ℕ} (hn : 1 ≤ n) (h : 2 * n ≤ m) :
    Nat.log 2 n + 1 ≤ Nat.log 2 m := by
  rw [show 2 * n = n * 2 from Nat.mul_comm 2 n] at h
  rw [← Nat.log_mul_base (by decide) (by omega)]
  exact Nat.log_mono_right (by omega)

/-- The case of `splitPot_split` where the first part has at most as many marked ends. -/
private theorem splitPot_split_left (K : Finset α) {P₁ P₂ : Finset α} (hd : Disjoint P₁ P₂)
    (hle : P₁.card ≤ P₂.card) :
    P₁.card + splitPot K P₁ + splitPot K P₂ ≤
      min (P₁ ∩ K).card (P₂ ∩ K).card + splitPot K (P₁ ∪ P₂) := by
  set k₁ := (P₁ ∩ K).card
  set k₂ := (P₂ ∩ K).card
  set l₁ := (P₁ \ K).card
  set l₂ := (P₂ \ K).card
  have hP₁ : P₁.card = k₁ + l₁ := by
    rw [add_comm]; exact (Finset.card_sdiff_add_card_inter P₁ K).symm
  have hP₂ : P₂.card = k₂ + l₂ := by
    rw [add_comm]; exact (Finset.card_sdiff_add_card_inter P₂ K).symm
  have hU : (P₁ ∪ P₂).card = P₁.card + P₂.card := Finset.card_union_of_disjoint hd
  have hUK : ((P₁ ∪ P₂) ∩ K).card = k₁ + k₂ := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hd))
  have hUL : ((P₁ ∪ P₂) \ K).card = l₁ + l₂ := by
    rw [Finset.union_sdiff_distrib]
    exact Finset.card_union_of_disjoint
      (Finset.disjoint_of_subset_left Finset.sdiff_subset
        (Finset.disjoint_of_subset_right Finset.sdiff_subset hd))
  set F := Nat.log 2 (k₁ + k₂ + 1) + Nat.log 2 (P₁.card + P₂.card)
  set F₁ := Nat.log 2 (k₁ + 1) + Nat.log 2 P₁.card
  set F₂ := Nat.log 2 (k₂ + 1) + Nat.log 2 P₂.card
  have hΨ : splitPot K (P₁ ∪ P₂) = (l₁ + l₂) * F := by
    unfold splitPot; rw [hUL, hUK, hU]
  have hΨ₁ : splitPot K P₁ = l₁ * F₁ := rfl
  have hΨ₂ : splitPot K P₂ = l₂ * F₂ := rfl
  have hF₁ : F₁ ≤ F := Nat.add_le_add (Nat.log_mono_right (by omega)) (Nat.log_mono_right (by omega))
  have hF₂ : F₂ ≤ F := Nat.add_le_add (Nat.log_mono_right (by omega)) (Nat.log_mono_right (by omega))
  rw [hΨ, hΨ₁, hΨ₂, hP₁, Nat.add_mul]
  rcases Nat.le_total k₁ k₂ with hk | hk
  · -- the leaving ends of the first part pay: their block at most halves
    rw [min_eq_left hk]
    have hpay : l₁ + l₁ * F₁ ≤ l₁ * F := by
      rcases Nat.eq_zero_or_pos l₁ with h0 | h0
      · simp [h0]
      · have hlog : Nat.log 2 P₁.card + 1 ≤ Nat.log 2 (P₁.card + P₂.card) :=
          log_succ_le (by omega) (by omega)
        have : F₁ + 1 ≤ F := by
          have := Nat.log_mono_right (b := 2) (show k₁ + 1 ≤ k₁ + k₂ + 1 by omega)
          omega
        calc l₁ + l₁ * F₁ = l₁ * (F₁ + 1) := by rw [Nat.mul_succ, Nat.add_comm]
          _ ≤ l₁ * F := Nat.mul_le_mul_left _ this
    have := Nat.mul_le_mul_left l₂ hF₂
    omega
  · rcases Nat.eq_or_lt_of_le hk with heq | hlt
    · -- equal kept counts: as in the first case
      rw [min_eq_right hk]
      have hpay : l₁ + l₁ * F₁ ≤ l₁ * F := by
        rcases Nat.eq_zero_or_pos l₁ with h0 | h0
        · simp [h0]
        · have hlog : Nat.log 2 P₁.card + 1 ≤ Nat.log 2 (P₁.card + P₂.card) :=
            log_succ_le (by omega) (by omega)
          have : F₁ + 1 ≤ F := by
            have := Nat.log_mono_right (b := 2) (show k₁ + 1 ≤ k₁ + k₂ + 1 by omega)
            omega
          calc l₁ + l₁ * F₁ = l₁ * (F₁ + 1) := by rw [Nat.mul_succ, Nat.add_comm]
            _ ≤ l₁ * F := Nat.mul_le_mul_left _ this
      have := Nat.mul_le_mul_left l₂ hF₂
      omega
    · -- the leaving ends of the second part pay: their block keeps less than half the kept ends
      rw [min_eq_right hk]
      have hl : k₁ + l₁ ≤ k₂ + l₂ := by omega
      have hpay : l₂ + l₂ * F₂ ≤ l₂ * F := by
        rcases Nat.eq_zero_or_pos l₂ with h0 | h0
        · simp [h0]
        · have hlog : Nat.log 2 (k₂ + 1) + 1 ≤ Nat.log 2 (k₁ + k₂ + 1) :=
            log_succ_le (by omega) (by omega)
          have : F₂ + 1 ≤ F := by
            have := Nat.log_mono_right (b := 2) (show P₂.card ≤ P₁.card + P₂.card by omega)
            omega
          calc l₂ + l₂ * F₂ = l₂ * (F₂ + 1) := by rw [Nat.mul_succ, Nat.add_comm]
            _ ≤ l₂ * F := Nat.mul_le_mul_left _ this
      have := Nat.mul_le_mul_left l₁ hF₁
      omega

/-- **One split.** When a block splits into the disjoint parts `P₁` and `P₂` and the helper lists
the part with fewer marked ends, the length of the list plus the new potential is at most the
smaller number of kept ends of the two parts plus the old potential. -/
theorem splitPot_split (K : Finset α) {P₁ P₂ : Finset α} (hd : Disjoint P₁ P₂) :
    (splitPick P₁ P₂).card + splitPot K P₁ + splitPot K P₂ ≤
      min (P₁ ∩ K).card (P₂ ∩ K).card + splitPot K (P₁ ∪ P₂) := by
  unfold splitPick
  split
  · exact splitPot_split_left K hd (by assumption)
  · have h := splitPot_split_left K hd.symm (by omega)
    rw [Finset.union_comm, min_comm]
    omega

/-- A block's potential is at most `2 ⌊log₂ (|P| + 1)⌋` per leaving end. -/
theorem splitPot_le (K P : Finset α) :
    splitPot K P ≤ (P \ K).card * (2 * Nat.log 2 (P.card + 1)) := by
  unfold splitPot
  apply Nat.mul_le_mul_left
  have h₁ := Nat.log_mono_right (b := 2) (show (P ∩ K).card + 1 ≤ P.card + 1 from
    Nat.add_le_add_right (Finset.card_le_card Finset.inter_subset_left) 1)
  have h₂ := Nat.log_mono_right (b := 2) (show P.card ≤ P.card + 1 by omega)
  omega

/-- The potential of the union of a family of disjoint blocks is at least the sum of their
potentials. -/
theorem splitPot_sum_le_biUnion (K : Finset α) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (blk : ι → Finset α) (hd : (s : Set ι).PairwiseDisjoint blk) :
    ∑ i ∈ s, splitPot K (blk i) ≤ splitPot K (s.biUnion blk) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.biUnion_insert]
    have hd' : (s : Set ι).PairwiseDisjoint blk :=
      hd.subset (by simp [Set.subset_insert])
    have hdisj : Disjoint (blk i) (s.biUnion blk) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hd (by simp) (by simp [hj]) (fun h => hi (h ▸ hj))
    exact le_trans (Nat.add_le_add_left (ih hd') _) (splitPot_add_le K hdisj)

/-- **Refinement.** When every new block lies in an old block (`f` names it), and the new blocks
are pairwise disjoint, the total potential does not grow. This covers the steps of an update
that are not splits listed by the helper: deletions of ends, and other splits. -/
theorem splitPot_sum_le_of_refines (K : Finset α) (V V' : Finset ℕ) (blk blk' : ℕ → Finset α)
    (f : ℕ → ℕ) (hf : ∀ v ∈ V', f v ∈ V) (hsub : ∀ v ∈ V', blk' v ⊆ blk (f v))
    (hd : (V' : Set ℕ).PairwiseDisjoint blk') :
    ∑ v ∈ V', splitPot K (blk' v) ≤ ∑ u ∈ V, splitPot K (blk u) := by
  rw [← Finset.sum_fiberwise_of_maps_to hf]
  apply Finset.sum_le_sum
  intro u _
  refine le_trans (splitPot_sum_le_biUnion K _ blk' (hd.subset ?_)) (splitPot_mono K ?_)
  · intro x hx
    exact (Finset.mem_filter.mp hx).1
  · intro x hx
    obtain ⟨v, hv, hxv⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hvV, hfv⟩ := Finset.mem_filter.mp hv
    exact hfv ▸ hsub v hvV hxv

/-- **A split step of a block family.** The block at `v` splits into the new blocks at `v` and at
the new vertex `v'`, and the other blocks stay. Then the length of the helper's list plus the
new total potential is at most the smaller kept count plus the old total potential. -/
theorem splitPot_sum_split (K : Finset α) (V : Finset ℕ) (blk blk' : ℕ → Finset α) {v v' : ℕ}
    (hv : v ∈ V) (hv' : v' ∉ V) (hother : ∀ u ∈ V, u ≠ v → blk' u = blk u)
    (hunion : blk' v ∪ blk' v' = blk v) (hd : Disjoint (blk' v) (blk' v')) :
    (splitPick (blk' v) (blk' v')).card + ∑ u ∈ insert v' V, splitPot K (blk' u) ≤
      min (blk' v ∩ K).card (blk' v' ∩ K).card + ∑ u ∈ V, splitPot K (blk u) := by
  have h := splitPot_split K hd
  rw [hunion] at h
  rw [Finset.sum_insert hv', ← Finset.add_sum_erase V _ hv, ← Finset.add_sum_erase V _ hv]
  have hrest : ∑ u ∈ V.erase v, splitPot K (blk' u) = ∑ u ∈ V.erase v, splitPot K (blk u) :=
    Finset.sum_congr rfl fun u hu => by rw [hother u (Finset.mem_of_mem_erase hu)
      (Finset.ne_of_mem_erase hu)]
  rw [hrest]
  omega

end MinCostFlow.SparseCore.Program
