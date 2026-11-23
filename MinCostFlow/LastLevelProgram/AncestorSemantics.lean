module

public import MinCostFlow.LSF.TreeOps
import Mathlib.Logic.Function.Iterate

/-!
# Parent walks in a rooted tree

Each parent step loses one level until it reaches the root. This relates
the parent walks used in the word machine to the tree's lowest common ancestor.
-/

public section

namespace MinCostFlow.LastLevelProgram

open LSF

/-- A parent iterate remains an ancestor and has depth reduced by its step count. -/
theorem parentIterate_spec {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (k : ℕ) :
    IsAncestor T r ((parent T r)^[k] u) u ∧
      depth T r ((parent T r)^[k] u) = depth T r u - k := by
  induction k with
  | zero => exact ⟨isAncestor_refl T r u, by simp⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let x := (parent T r)^[k] u
    have hx : x ∈ T.V := isAncestor_mem hT hu ih.1
    by_cases hr : x = r
    · have hf := forestPath_self hT.isForest r
      have hp : parent T r x = x := by simp [hr,parent,hf]
      have hz : depth T r x = 0 := by simp [hr,depth,hf]
      rw [hp]
      refine ⟨ih.1,?_⟩
      have he := ih.2
      change depth T r x = _ at he
      omega
    · refine ⟨isAncestor_trans hT hu (isAncestor_parent hT hx hr) ih.1,?_⟩
      have hd := depth_parent hT hx hr
      have he := ih.2
      change depth T r x = _ at he
      change depth T r (parent T r x) = _
      omega

/-- Each ancestor is reached at the difference in depths. -/
theorem parentIterate_eq_of_isAncestor {T : MGraph} {r u a : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (ha : IsAncestor T r a u) :
    (parent T r)^[depth T r u - depth T r a] u = a := by
  obtain ⟨hx,hd⟩ := parentIterate_spec hT hu (depth T r u - depth T r a)
  have hle := isAncestor_depth_le hT hu ha
  have he : depth T r ((parent T r)^[depth T r u - depth T r a] u) = depth T r a := by
    omega
  rcases isAncestor_total_on_ancestors hT hu hx ha with h | h
  · exact (isAncestor_eq_iff_depth hT (isAncestor_mem hT hu ha) h).mp he
  · exact ((isAncestor_eq_iff_depth hT (isAncestor_mem hT hu hx) h).mp he.symm).symm

/-- Equal-depth endpoints first meet at the depth difference from their
lowest common ancestor. -/
theorem parentIterate_firstMeeting {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (he : depth T r u = depth T r v) :
    let a := lca T r u v
    let k := depth T r u - depth T r a
    (parent T r)^[k] u = a ∧ (parent T r)^[k] v = a ∧
      ∀ j < k, (parent T r)^[j] u ≠ (parent T r)^[j] v := by
  intro a k
  have hau : IsAncestor T r a u := lca_isAncestor_left hT hu hv
  have hav : IsAncestor T r a v := lca_isAncestor_right hT hu hv
  refine ⟨parentIterate_eq_of_isAncestor hT hu hau, ?_, ?_⟩
  · change (parent T r)^[depth T r u - depth T r a] v = a
    rw [he]
    exact parentIterate_eq_of_isAncestor hT hv hav
  · intro j hj hm
    obtain ⟨hxu,hxd⟩ := parentIterate_spec hT hu j
    have hxv := (parentIterate_spec hT hv j).1
    rw [← hm] at hxv
    have hxa : IsAncestor T r ((parent T r)^[j] u) a :=
      (isAncestor_lca_iff hT hu hv).2 ⟨hxu,hxv⟩
    have hl := isAncestor_depth_le hT (lca_mem hT hu hv) hxa
    dsimp [k] at hj
    change depth T r ((parent T r)^[j] u) ≤ depth T r a at hl
    omega

/-- Above the depth of a vertex, the parent iterate is already at the root. -/
theorem parentIterate_eq_root {T : MGraph} {r u k : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hk : depth T r u ≤ k) :
    (parent T r)^[k] u = r := by
  obtain ⟨ha,hd⟩ := parentIterate_spec hT hu k
  let x := (parent T r)^[k] u
  have hx := isAncestor_mem hT hu ha
  have hz : depth T r r = 0 := by simp [depth,forestPath_self hT.isForest]
  have he : depth T r r = depth T r x := by rw [hz,hd,Nat.sub_eq_zero_of_le hk]
  exact ((isAncestor_eq_iff_depth hT hx (isAncestor_root hT hx)).mp he).symm

/-- Lifting the deeper endpoint to the shallower endpoint's depth preserves
their lowest common ancestor. -/
theorem lca_eq_lca_lifted {T : MGraph} {r u v : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hv : v ∈ T.V) (hle : depth T r v ≤ depth T r u) :
    let x := (parent T r)^[depth T r u - depth T r v] u
    depth T r x = depth T r v ∧ lca T r x v = lca T r u v := by
  intro x
  obtain ⟨hxu,hxd⟩ := parentIterate_spec hT hu (depth T r u - depth T r v)
  have hx : x ∈ T.V := isAncestor_mem hT hu hxu
  have he : depth T r x = depth T r v := by
    change depth T r x = _ at hxd
    omega
  refine ⟨he,?_⟩
  let a := lca T r u v
  let b := lca T r x v
  have hau : IsAncestor T r a u := lca_isAncestor_left hT hu hv
  have hav : IsAncestor T r a v := lca_isAncestor_right hT hu hv
  have hbx : IsAncestor T r b x := lca_isAncestor_left hT hx hv
  have hbv : IsAncestor T r b v := lca_isAncestor_right hT hx hv
  have hab : depth T r a ≤ depth T r x := he ▸ isAncestor_depth_le hT hv hav
  have hax : IsAncestor T r a x := by
    rcases isAncestor_total_on_ancestors hT hu hau hxu with h | h
    · exact h
    · have hle := isAncestor_depth_le hT (lca_mem hT hu hv) h
      change depth T r x ≤ depth T r a at hle
      have heq := (isAncestor_eq_iff_depth hT (lca_mem hT hu hv) h).mp (Nat.le_antisymm hle hab)
      change x = a at heq
      rw [heq]
      exact isAncestor_refl T r a
  exact isAncestor_antisymm hT (lca_mem hT hx hv) (lca_mem hT hu hv)
    ((isAncestor_lca_iff hT hu hv).2 ⟨isAncestor_trans hT hu hbx hxu,hbv⟩)
    ((isAncestor_lca_iff hT hx hv).2 ⟨hax,hav⟩)

end MinCostFlow.LastLevelProgram
