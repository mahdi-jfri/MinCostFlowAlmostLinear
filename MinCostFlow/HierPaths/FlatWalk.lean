module

public import MinCostFlow.HierPaths.HierData
public import MinCostFlow.HierPaths.Substitute
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Flattening one walk of the hierarchy to the root host

A connector of a group at depth `t` stores a walk in the host of that group. To use it in the
input graph, the walk is first expanded down to the root host: each edge of the host of a group
`g` is replaced by its embedding walk in the host of the parent of `g`, and so on up to the root.
`flatWalk` does this one depth at a time with `substWalk` (`HierPaths/Substitute.lean`); it is
`substDown` along the chain of hosts of the ancestors of `g`.

Main results, for a valid hierarchy (`HierData.IsValid`):
* `flatWalk_isEdgeWalk`: a walk of the host of `g` between `u` and `v` becomes a walk of the root
  host between `u` and `v`;
* `length_flatWalk_le`: with `HierData.Bounds`, its length is at most the length of the walk times
  `∏_{k < t} d k`.

The facts about groups used here are `groupSize_le_of_le` (sizes shrink with depth) and
`parentGroup_lt_numGroups`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Expand the walk `es`, started at `s`, of the host of group `g` at depth `t` down to the root
host. -/
def flatWalk (H : HierData) (x b : ℕ) : ℕ → ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, es => es
  | t + 1, g, s, es =>
    flatWalk H x b t (parentGroup x b t g) s (substWalk (H.host (t + 1) g).edges (H.emb t g) s es)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {x b : ℕ}

theorem groupSize_succ_le (j : ℕ) : groupSize x b (j + 1) ≤ groupSize x b j := by
  rw [groupSize_eq_mul_branching (j := j)]
  exact Nat.le_mul_of_pos_left _ branching_pos

/-- Group sizes shrink with depth. -/
theorem groupSize_le_of_le {k j : ℕ} (h : k ≤ j) : groupSize x b j ≤ groupSize x b k := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (groupSize_succ_le _).trans ih

theorem parentGroup_lt_numGroups {j c : ℕ} (hc : c < numGroups x b (j + 1)) :
    parentGroup x b j c < numGroups x b j := by
  have hmem : c * groupSize x b (j + 1) ∈ members x b (j + 1) c := by
    simp only [members, Finset.mem_Ico, Nat.succ_mul]
    exact ⟨le_rfl, Nat.lt_add_of_pos_right groupSize_pos⟩
  have hlt : c * groupSize x b (j + 1) < 2 ^ x :=
    Finset.mem_range.mp (members_subset_range hc hmem)
  have h := mem_members_iff.mp (members_succ_subset (x := x) (b := b) (j := j) c hmem)
  rw [← h]
  exact groupOf_lt_numGroups hlt

theorem insideB_mono {X Y : Finset ℕ} (hXY : X ⊆ Y) {e : ℕ × ℕ} (h : insideB X e = true) :
    insideB Y e = true := by
  simp only [insideB, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨hXY h.1, hXY h.2⟩

namespace HierData

variable {H : HierData}

/-- An edge of a child host lies inside the members of the parent. -/
theorem IsValid.inside_parent (hH : H.IsValid x b) {t c : ℕ} (hs : 1 < groupSize x b (t + 1))
    (hc : c < numGroups x b (t + 1)) {i : ℕ} (hi : i < (H.host (t + 1) c).m) :
    insideB (members x b t (parentGroup x b t c)) (edgeAt (H.host (t + 1) c).edges i) = true :=
  insideB_mono (members_succ_subset c) (hH.host_inside (t + 1) c hs hc i hi)

/-- The embedding walk of an edge of a child host is a walk of the parent host. -/
theorem IsValid.emb_walk (hH : H.IsValid x b) {t c : ℕ} (hs : 1 < groupSize x b (t + 1))
    (hc : c < numGroups x b (t + 1)) {i : ℕ} (hi : i < (H.host (t + 1) c).m) :
    IsEdgeWalk (H.host t (parentGroup x b t c)).edges (edgeAt (H.host (t + 1) c).edges i).1
      (edgeAt (H.host (t + 1) c).edges i).2 (H.emb t c i) :=
  (hH.emb_ok t c hs hc i hi (hH.inside_parent hs hc hi)).1

end HierData

open HierData

/-- **Flattening keeps walks.** A walk of the host of group `g` at depth `t` (a group of size above
one) from `u` to `v` becomes a walk of the root host from `u` to `v`. -/
theorem flatWalk_isEdgeWalk {H : HierData} (hH : H.IsValid x b) :
    ∀ {t g : ℕ}, 1 < groupSize x b t → g < numGroups x b t → ∀ {u v : ℕ} {es : List ℕ},
      IsEdgeWalk (H.host t g).edges u v es →
        IsEdgeWalk (H.host 0 0).edges u v (flatWalk H x b t g u es)
  | 0, g, _, hg, u, v, es, hW => by
    have : g = 0 := by
      simp only [numGroups, Nat.zero_mul, Nat.min_zero, pow_zero] at hg; omega
    subst this
    exact hW
  | t + 1, g, hs, hg, u, v, es, hW => by
    unfold flatWalk
    refine flatWalk_isEdgeWalk hH ((hs.trans_le (groupSize_succ_le t)))
      (parentGroup_lt_numGroups hg) ?_
    exact substWalk_isEdgeWalk hW fun j hj => hH.emb_walk hs hg (hW.lt_length j hj)

/-- **Length of a flattened walk.** With the numbers `d` of `HierData.Bounds`, a walk `es` of the
host of group `g` at depth `t` becomes a root walk with at most `|es| · ∏_{k < t} d k` edges. -/
theorem length_flatWalk_le {H : HierData} (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ}
    (hB : H.Bounds x b d ρ κ) :
    ∀ {t g : ℕ}, 1 < groupSize x b t → g < numGroups x b t → ∀ {u v : ℕ} {es : List ℕ},
      IsEdgeWalk (H.host t g).edges u v es →
        (flatWalk H x b t g u es).length ≤ es.length * ∏ k ∈ Finset.range t, d k
  | 0, g, _, _, u, v, es, _ => by simp [flatWalk]
  | t + 1, g, hs, hg, u, v, es, hW => by
    unfold flatWalk
    have hW' := substWalk_isEdgeWalk hW fun j hj => hH.emb_walk hs hg (hW.lt_length j hj)
    have h1 := length_flatWalk_le hH hB (hs.trans_le (groupSize_succ_le t))
      (parentGroup_lt_numGroups hg) hW'
    have h2 : (substWalk (H.host (t + 1) g).edges (H.emb t g) u es).length ≤ es.length * d t :=
      length_substWalk_le fun j hj => hB.emb_length t g hs hg j (hW.lt_length j hj)
    calc _ ≤ (substWalk (H.host (t + 1) g).edges (H.emb t g) u es).length *
          ∏ k ∈ Finset.range t, d k := h1
      _ ≤ es.length * d t * ∏ k ∈ Finset.range t, d k := Nat.mul_le_mul_right _ h2
      _ = es.length * ∏ k ∈ Finset.range (t + 1), d k := by
        rw [Finset.prod_range_succ, Nat.mul_assoc, Nat.mul_comm (d t), ← Nat.mul_assoc]

end MinCostFlow.HierPaths
