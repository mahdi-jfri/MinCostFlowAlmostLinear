module

public import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Binary splay tree skeletons, paths, and the Sleator–Tarjan potential

The type `AuxTree`, ancestor paths, depths, subtree surgery, subtree sizes, ranks, and the
Sleator–Tarjan potential.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

/-- Algebraic skeleton of a binary auxiliary tree with node identifiers `id`. -/
inductive AuxTree where
  | leaf : AuxTree
  | node (id : ℕ) (left right : AuxTree) : AuxTree
  deriving DecidableEq

namespace AuxTree

/-- Number of internal nodes in an `AuxTree`. -/
def countNodes : AuxTree → ℕ
  | .leaf => 0
  | .node _ l r => 1 + l.countNodes + r.countNodes

/-- List of node identifiers appearing in `t` (in structural left-node-right order). -/
def toList : AuxTree → List ℕ
  | .leaf => []
  | .node id l r => l.toList ++ [id] ++ r.toList

/-- Root identifier of an `AuxTree`, or `0` for `leaf`. -/
def rootId : AuxTree → ℕ
  | .leaf => 0
  | .node id _ _ => id

/-- Whether `t` is a non-leaf node whose root identifier is `x`. -/
def hasRoot (x : ℕ) : AuxTree → Bool
  | .leaf => false
  | .node id _ _ => id == x

/-- Swap the root's left and right children (algebraic counterpart of `revNode`). -/
def revRoot : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r => .node id r l

theorem length_toList (t : AuxTree) : t.toList.length = t.countNodes := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr => simp [toList, countNodes, ihl, ihr]; omega

theorem rootId_mem {t : AuxTree} (ht : t ≠ .leaf) : t.rootId ∈ t.toList := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r => simp [rootId, toList]

theorem hasRoot_iff {x : ℕ} {t : AuxTree} :
    t.hasRoot x = true ↔ ∃ l r, t = .node x l r := by
  cases t with
  | leaf => simp [hasRoot]
  | node id l r =>
    simp only [hasRoot, beq_iff_eq]
    constructor
    · rintro rfl; exact ⟨l, r, rfl⟩
    · rintro ⟨_, _, h⟩; cases h; rfl

theorem nodup_node_unfold {id : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node id l r).toList.Nodup) :
    l.toList.Nodup ∧ id ∉ l.toList ∧ r.toList.Nodup ∧ id ∉ r.toList ∧
      ∀ a, a ∈ l.toList → a ∉ r.toList := by
  rw [toList, List.nodup_append, List.nodup_append] at hnd
  rcases hnd with ⟨⟨hl_nd, _, hdisj_l_id⟩, hr_nd, hdisj_lr⟩
  refine ⟨hl_nd, fun hm => hdisj_l_id id hm id (List.mem_singleton.2 rfl) rfl, hr_nd,
    fun hm => hdisj_lr id (by simp) id hm rfl, fun a ha har => ?_⟩
  exact hdisj_lr a (by simp [ha]) a har rfl

/-- Logical in-order traversal of `t` given node reversal flags `rev` and an inherited
reversal parity `flip`. Under pre-flipped semantics, `rev id = true` means `id` already has
its physical children swapped, so its parity complements the parity inherited by its children. -/
def evalInorder (rev : ℕ → Bool) : AuxTree → Bool → List ℕ
  | .leaf, _ => []
  | .node id l r, false =>
      evalInorder rev l (rev id) ++ [id] ++ evalInorder rev r (rev id)
  | .node id l r, true =>
      evalInorder rev r (!(rev id)) ++ [id] ++ evalInorder rev l (!(rev id))

theorem evalInorder_true (rev : ℕ → Bool) (t : AuxTree) :
    t.evalInorder rev true = (t.evalInorder rev false).reverse := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases h : rev id <;>
        simp [evalInorder, h, ihl, ihr, List.reverse_append, List.append_assoc]

theorem evalInorder_perm (rev : ℕ → Bool) (t : AuxTree) (b : Bool) :
    (t.evalInorder rev b).Perm t.toList := by
  induction t generalizing b with
  | leaf => simp [evalInorder, toList]
  | node id l r ihl ihr =>
      cases b
      · simp only [evalInorder, toList]
        exact ((ihl (rev id)).append_right [id]).append (ihr (rev id))
      · simp only [evalInorder, toList]
        have hstep1 : ((r.evalInorder rev (!(rev id)) ++ [id]) ++ l.evalInorder rev (!(rev id))).Perm
            (l.evalInorder rev (!(rev id)) ++ (r.evalInorder rev (!(rev id)) ++ [id])) :=
          List.perm_append_comm
        have hstep2 : (l.evalInorder rev (!(rev id)) ++ (r.evalInorder rev (!(rev id)) ++ [id])).Perm
            (l.evalInorder rev (!(rev id)) ++ [id] ++ r.evalInorder rev (!(rev id))) := by
          rw [List.append_assoc]
          exact List.Perm.append_left _ List.perm_append_comm
        exact (hstep1.trans hstep2).trans (((ihl (!(rev id))).append_right [id]).append (ihr (!(rev id))))

theorem length_evalInorder (rev : ℕ → Bool) (t : AuxTree) (b : Bool) :
    (t.evalInorder rev b).length = t.countNodes := by
  induction t generalizing b with
  | leaf => rfl
  | node id l r ihl ihr =>
      cases b <;> simp [evalInorder, countNodes, ihl, ihr] <;> omega

theorem evalInorder_agree (rev₁ rev₂ : ℕ → Bool) (t : AuxTree) (b : Bool)
    (heq : ∀ u ∈ t.toList, rev₁ u = rev₂ u) :
    t.evalInorder rev₁ b = t.evalInorder rev₂ b := by
  induction t generalizing b with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hid := heq id (by simp [toList])
      have hl : ∀ u ∈ l.toList, rev₁ u = rev₂ u := fun u hu => heq u (by simp [toList, hu])
      have hr : ∀ u ∈ r.toList, rev₁ u = rev₂ u := fun u hu => heq u (by simp [toList, hu])
      cases b <;> simp only [evalInorder, hid, ihl _ hl, ihr _ hr]

/-! ### Ancestor paths, depths, and subtree surgery -/

/-- Path of ancestor node IDs from root down to `x`, or `[]` if `x ∉ t.toList`. -/
def pathTo (x : ℕ) : AuxTree → List ℕ
  | .leaf => []
  | .node id l r =>
      if x = id then [id]
      else if x ∈ l.toList then id :: l.pathTo x
      else if x ∈ r.toList then id :: r.pathTo x
      else []

/-- Depth of `x` in `t` (`0` at root or if `x ∉ t.toList`). -/
def depthOf (x : ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r =>
      if x = id then 0
      else if x ∈ l.toList then l.depthOf x + 1
      else if x ∈ r.toList then r.depthOf x + 1
      else 0

/-- Subtree of `t` rooted at `subId` (or `.leaf` if `subId ∉ t.toList`). -/
def findSubtree (subId : ℕ) : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r =>
      if id = subId then .node id l r
      else if subId ∈ l.toList then l.findSubtree subId
      else r.findSubtree subId

/-- Parent ID of `subId` inside `t` (with root parent `p₀`). -/
def parentIn (subId p₀ : ℕ) : AuxTree → ℕ
  | .leaf => p₀
  | .node id l r =>
      if id = subId then p₀
      else if subId ∈ l.toList then l.parentIn subId id
      else r.parentIn subId id

/-- Replaces subtree rooted at `subId` inside `t` with `s'`. -/
def replaceSubtree : AuxTree → ℕ → AuxTree → AuxTree
  | .leaf, _, _ => .leaf
  | .node id l r, subId, s' =>
      if id = subId then s'
      else .node id (l.replaceSubtree subId s') (r.replaceSubtree subId s')

theorem mem_pathTo {t : AuxTree} {x u : ℕ} (hu : u ∈ t.pathTo x) : u ∈ t.toList := by
  induction t with
  | leaf => simp [pathTo] at hu
  | node id l r ihl ihr =>
      simp only [pathTo] at hu
      split_ifs at hu
      · simp only [List.mem_singleton] at hu; subst hu; simp [toList]
      · simp only [List.mem_cons] at hu
        rcases hu with rfl | h
        · simp [toList]
        · simp [toList, ihl h]
      · simp only [List.mem_cons] at hu
        rcases hu with rfl | h
        · simp [toList]
        · simp [toList, ihr h]
      · simp at hu

theorem self_mem_pathTo {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) : x ∈ t.pathTo x := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [pathTo]
      by_cases h : x = id
      · simp [h]
      · simp only [h, ↓reduceIte]
        by_cases hl : x ∈ l.toList
        · simp [hl, ihl hl]
        · have hr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h1 | rfl) | h2
            · exact absurd h1 hl
            · exact absurd rfl h
            · exact h2
          simp [hl, hr, ihr hr]

theorem depthOf_root (id : ℕ) (l r : AuxTree) : (AuxTree.node id l r).depthOf id = 0 := by
  simp [depthOf]

theorem depthOf_zero_iff_root {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    t.depthOf x = 0 ↔ x = t.rootId := by
  cases t with
  | leaf => simp [toList] at hx
  | node id l r =>
      simp only [depthOf, rootId]
      by_cases heq : x = id
      · simp [heq]
      · simp only [heq, ↓reduceIte]
        by_cases hl : x ∈ l.toList
        · simp [hl]
        · have hr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h1 | rfl) | h2
            · exact absurd h1 hl
            · exact absurd rfl heq
            · exact h2
          simp [hl, hr]

theorem findSubtree_subset {t : AuxTree} {subId u : ℕ}
    (hu : u ∈ (t.findSubtree subId).toList) : u ∈ t.toList := by
  induction t with
  | leaf => simp [findSubtree, toList] at hu
  | node id l r ihl ihr =>
      simp only [findSubtree] at hu
      split_ifs at hu
      · exact hu
      · simp [toList, ihl hu]
      · simp [toList, ihr hu]

theorem findSubtree_root {t : AuxTree} (ht : t ≠ .leaf) :
    t.findSubtree t.rootId = t := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r => simp [findSubtree, rootId]

theorem findSubtree_root_of_mem {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    ∃ l' r', t.findSubtree x = .node x l' r' := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [findSubtree]
      by_cases heq : id = x
      · subst heq; exact ⟨l, r, ite_eq_left rfl⟩
      · simp only [heq, ↓reduceIte]
        simp only [toList, List.mem_append, List.mem_singleton] at hx
        rcases hx with (hxl | rfl) | hxr
        · rw [ite_eq_left hxl]; exact ihl hxl
        · exact absurd rfl heq
        · by_cases hxl : x ∈ l.toList
          · rw [ite_eq_left hxl]; exact ihl hxl
          · rw [ite_eq_right hxl]; exact ihr hxr

theorem findSubtree_nodup {t : AuxTree} {subId : ℕ}
    (hnd : t.toList.Nodup) : (t.findSubtree subId).toList.Nodup := by
  induction t with
  | leaf => simp [findSubtree, toList]
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _⟩
      simp only [findSubtree]
      split_ifs
      · exact hnd
      · exact ihl hl_nd
      · exact ihr hr_nd

theorem findSubtree_findSubtree {t : AuxTree} {g p : ℕ}
    (hnd : t.toList.Nodup) (hg : g ∈ t.toList) (hp : p ∈ (t.findSubtree g).toList) :
    (t.findSubtree g).findSubtree p = t.findSubtree p := by
  induction t with
  | leaf => simp [toList] at hg
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      by_cases heq : id = g
      · subst heq; simp [findSubtree]
      · simp only [findSubtree, heq, ↓reduceIte] at hp ⊢
        by_cases hgl : g ∈ l.toList
        · simp only [hgl, ↓reduceIte] at hp ⊢
          have hp_l : p ∈ l.toList := findSubtree_subset hp
          have hid_p : id ≠ p := fun h => hid_nl (h ▸ hp_l)
          simp only [hid_p, ↓reduceIte, hp_l]
          exact ihl hl_nd hgl hp
        · have hgr : g ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hg
            rcases hg with (h | rfl) | h
            · exact absurd h hgl
            · exact absurd rfl heq
            · exact h
          simp only [hgl, ↓reduceIte] at hp ⊢
          have hp_r : p ∈ r.toList := findSubtree_subset hp
          have hid_p : id ≠ p := fun h => hid_nr (h ▸ hp_r)
          have hp_nl : p ∉ l.toList := fun hl => hdisj_lr p hl hp_r
          simp only [hid_p, ↓reduceIte, hp_nl]
          exact ihr hr_nd hgr hp

theorem replaceSubtree_not_mem {t s' : AuxTree} {subId : ℕ}
    (h : subId ∉ t.toList) : t.replaceSubtree subId s' = t := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hne : id ≠ subId := fun heq => h (by subst heq; simp [toList])
      have hnl : subId ∉ l.toList := fun hl => h (by simp [toList, hl])
      have hnr : subId ∉ r.toList := fun hr => h (by simp [toList, hr])
      simp [replaceSubtree, hne, ihl hnl, ihr hnr]

theorem replaceSubtree_perm {t s' : AuxTree} {subId : ℕ}
    (hnd : t.toList.Nodup) (hmem : subId ∈ t.toList)
    (hs_perm : s'.toList.Perm (t.findSubtree subId).toList) :
    (t.replaceSubtree subId s').toList.Perm t.toList := by
  induction t with
  | leaf => simp [toList] at hmem
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, hdisj_lr⟩
      by_cases hid : id = subId
      · subst hid; simpa [replaceSubtree, findSubtree] using hs_perm
      · simp only [replaceSubtree, hid, ↓reduceIte, findSubtree] at hs_perm ⊢
        by_cases hnl : subId ∈ l.toList
        · simp only [hnl, ↓reduceIte] at hs_perm
          have hnr : subId ∉ r.toList := hdisj_lr subId hnl
          rw [replaceSubtree_not_mem hnr]
          simp only [toList]
          exact ((ihl hl_nd hnl hs_perm).append_right [id]).append_right r.toList
        · have hnr : subId ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hmem
            rcases hmem with (h | rfl) | h
            · exact absurd h hnl
            · exact absurd rfl hid
            · exact h
          simp only [hnl, ↓reduceIte] at hs_perm
          rw [replaceSubtree_not_mem hnl]
          simp only [toList]
          exact (ihr hr_nd hnr hs_perm).append_left (l.toList ++ [id])

theorem replaceSubtree_rootId {t s' : AuxTree} {subId : ℕ}
    (ht : t ≠ .leaf) (_hs' : s' ≠ .leaf) :
    (t.replaceSubtree subId s').rootId = if t.rootId = subId then s'.rootId else t.rootId := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r =>
      by_cases h : id = subId
      · subst h; simp [replaceSubtree, rootId]
      · simp [replaceSubtree, rootId, h]

theorem parentIn_mem_and_depth {t : AuxTree} {x p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) :
    t.parentIn x p₀ ∈ t.toList ∧
    t.depthOf (t.parentIn x p₀) + 1 = t.depthOf x ∧
    t.pathTo x = t.pathTo (t.parentIn x p₀) ++ [x] := by
  induction t generalizing p₀ with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      have hne : id ≠ x := fun h => hxr (by simp [rootId, h])
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nin_l, hr_nd, hid_nin_r, hdisj_lr⟩
      simp only [parentIn, hne, ↓reduceIte]
      by_cases hnl : x ∈ l.toList
      · simp only [hnl, ↓reduceIte, depthOf, pathTo, Ne.symm hne]
        by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hnl
          | node lid ll lr =>
              simp only [rootId] at hxlr; subst hxlr
              simp [parentIn, toList, depthOf, pathTo]
        · rcases ihl hl_nd hnl hxlr (p₀ := id) with ⟨hpm, hpd, hpp⟩
          have hpm_ne : l.parentIn x id ≠ id := fun h => hid_nin_l (h ▸ hpm)
          refine ⟨by simp [toList, hpm], ?_, ?_⟩
          · simp [hpm_ne, hpm, hpd]
          · simp [hpm_ne, hpm, hpp]
      · have hnr : x ∈ r.toList := by
          simp only [toList, List.mem_append, List.mem_singleton] at hx
          rcases hx with (hl | rfl) | hr
          · exact absurd hl hnl
          · exact absurd rfl hne
          · exact hr
        simp only [hnl, ↓reduceIte, depthOf, pathTo, Ne.symm hne]
        by_cases hxrr : x = r.rootId
        · cases r with
          | leaf => simp [toList] at hnr
          | node rid rl rr =>
              simp only [rootId] at hxrr; subst hxrr
              simp [parentIn, toList, depthOf, pathTo, hid_nin_l]
        · rcases ihr hr_nd hnr hxrr (p₀ := id) with ⟨hpm, hpd, hpp⟩
          have hpm_ne : r.parentIn x id ≠ id := fun h => hid_nin_r (h ▸ hpm)
          have hpm_nin_l : r.parentIn x id ∉ l.toList := fun hl => hdisj_lr _ hl hpm
          refine ⟨by simp [toList, hpm], ?_, ?_⟩
          · simp [hpm_ne, hpm_nin_l, hpm, hpd, hnr]
          · simp [hpm_ne, hpm_nin_l, hpm, hpp, hnr]

theorem parentIn_child_cases {t : AuxTree} {x p p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) (hp : p = t.parentIn x p₀) :
    ∃ l r, t.findSubtree p = .node p l r ∧
      ((∃ A B, l = .node x A B) ∨ (∃ C D, r = .node x C D)) := by
  induction t generalizing p₀ with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      have hne : id ≠ x := fun h => hxr (by simp [rootId, h])
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      rw [parentIn, ite_eq_right hne] at hp
      by_cases hxl : x ∈ l.toList
      · rw [ite_eq_left hxl] at hp
        by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hxl
          | node lx A B =>
              simp only [rootId] at hxlr; subst hxlr
              have hpx : p = id := by simpa [parentIn] using hp
              subst hpx
              exact ⟨.node x A B, r, by simp [findSubtree], Or.inl ⟨A, B, rfl⟩⟩
        · have hp_mem : p ∈ l.toList := hp ▸ (parentIn_mem_and_depth hl_nd hxl hxlr).1
          have hid_np : id ≠ p := fun h => hid_nl (h ▸ hp_mem)
          rcases ihl hl_nd hxl hxlr hp with ⟨sl, sr, hsub, hcas⟩
          exact ⟨sl, sr, by simpa [findSubtree, hid_np, hp_mem] using hsub, hcas⟩
      · have hxr' : x ∈ r.toList := by
          simp only [toList, List.mem_append, List.mem_singleton] at hx
          rcases hx with (h | rfl) | h
          · exact absurd h hxl
          · exact absurd rfl hne
          · exact h
        rw [ite_eq_right hxl] at hp
        by_cases hxrr : x = r.rootId
        · cases r with
          | leaf => simp [toList] at hxr'
          | node rx C D =>
              simp only [rootId] at hxrr; subst hxrr
              have hpx : p = id := by simpa [parentIn] using hp
              subst hpx
              exact ⟨l, .node x C D, by simp [findSubtree], Or.inr ⟨C, D, rfl⟩⟩
        · have hp_mem : p ∈ r.toList := hp ▸ (parentIn_mem_and_depth hr_nd hxr' hxrr).1
          have hid_np : id ≠ p := fun h => hid_nr (h ▸ hp_mem)
          have hp_nl : p ∉ l.toList := fun h => hdisj_lr p h hp_mem
          rcases ihr hr_nd hxr' hxrr hp with ⟨sl, sr, hsub, hcas⟩
          exact ⟨sl, sr, by simpa [findSubtree, hid_np, hp_nl] using hsub, hcas⟩

theorem depthOf_le_of_mem_pathTo {t : AuxTree} {x u : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hu : u ∈ t.pathTo x) :
    t.depthOf u ≤ t.depthOf x ∧ (u = x ↔ t.depthOf u = t.depthOf x) := by
  induction t with
  | leaf => simp [pathTo] at hu
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nin_l, hr_nd, hid_nin_r, hdisj_lr⟩
      simp only [pathTo] at hu
      by_cases hxid : x = id
      · subst hxid
        simp only [↓reduceIte, List.mem_singleton] at hu
        subst hu; exact ⟨Nat.le_refl _, by simp⟩
      · by_cases hnl : x ∈ l.toList
        · simp only [hxid, hnl, ↓reduceIte, List.mem_cons] at hu
          rcases hu with rfl | hu'
          · simp [depthOf, hxid, hnl, Ne.symm hxid]
          · have hu_l : u ∈ l.toList := mem_pathTo hu'
            have hu_ne : u ≠ id := fun h => hid_nin_l (h ▸ hu_l)
            rcases ihl hl_nd hnl hu' with ⟨hle, _⟩
            simp only [depthOf, hu_ne, hu_l, ↓reduceIte, hxid, hnl]
            exact ⟨Nat.succ_le_succ hle, by constructor <;> intro h <;> simp_all⟩
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl hnl
            · exact absurd rfl hxid
            · exact hr
          simp only [hxid, hnl, hnr, ↓reduceIte, List.mem_cons] at hu
          rcases hu with rfl | hu'
          · simp [depthOf, hxid, hnl, hnr, Ne.symm hxid]
          · have hu_r : u ∈ r.toList := mem_pathTo hu'
            have hu_ne : u ≠ id := fun h => hid_nin_r (h ▸ hu_r)
            have hu_nin_l : u ∉ l.toList := fun hl => hdisj_lr u hl hu_r
            rcases ihr hr_nd hnr hu' with ⟨hle, _⟩
            simp only [depthOf, hu_ne, hu_nin_l, hu_r, ↓reduceIte, hxid, hnl, hnr]
            exact ⟨Nat.succ_le_succ hle, by constructor <;> intro h <;> simp_all⟩

theorem depthOf_le_findSubtree {t : AuxTree} {x u : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hu : u ∈ (t.findSubtree x).toList) :
    t.depthOf x ≤ t.depthOf u := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nin_l, hr_nd, hid_nin_r, hdisj_lr⟩
      by_cases hid_x : id = x
      · subst hid_x; simp [depthOf]
      · by_cases hnl : x ∈ l.toList
        · simp only [findSubtree, hid_x, hnl, ↓reduceIte] at hu
          have hu_l : u ∈ l.toList := findSubtree_subset hu
          have hu_ne : u ≠ id := fun h => hid_nin_l (h ▸ hu_l)
          simp only [depthOf, Ne.symm hid_x, hnl, ↓reduceIte, hu_ne, hu_l]
          exact Nat.succ_le_succ (ihl hl_nd hnl hu)
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl hnl
            · exact absurd rfl hid_x
            · exact hr
          simp only [findSubtree, hid_x, hnl, ↓reduceIte] at hu
          have hu_r : u ∈ r.toList := findSubtree_subset hu
          have hu_ne : u ≠ id := fun h => hid_nin_r (h ▸ hu_r)
          have hu_nin_l : u ∉ l.toList := fun hl => hdisj_lr u hl hu_r
          simp only [depthOf, Ne.symm hid_x, hnl, hnr, ↓reduceIte, hu_ne, hu_nin_l, hu_r]
          exact Nat.succ_le_succ (ihr hr_nd hnr hu)

theorem not_mem_findSubtree_of_ancestor {t : AuxTree} {px x u : ℕ}
    (hnd : t.toList.Nodup) (hpx : px ∈ t.toList) (hx : x ∈ t.toList)
    (hlt : t.depthOf px < t.depthOf x) (hu : u ∈ t.pathTo px) :
    u ∉ (t.findSubtree x).toList := by
  intro hu_sub
  have h1 := (depthOf_le_of_mem_pathTo hnd hpx hu).1
  have h2 := depthOf_le_findSubtree hnd hx hu_sub
  omega

theorem root_not_mem_findSubtree {t : AuxTree} {rSub y : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hy : y ∈ (t.findSubtree rSub).toList)
    (hne : t.rootId ≠ rSub) :
    t.rootId ≠ y := by
  have hroot_mem : t.rootId ∈ t.toList := by
    cases t with
    | leaf => simp [toList] at hr
    | node id _ _ => simp [rootId, toList]
  have hdep0 : t.depthOf t.rootId = 0 := (depthOf_zero_iff_root hroot_mem).2 rfl
  have hr_nz : t.depthOf rSub ≠ 0 := fun h0 =>
    hne ((depthOf_zero_iff_root hr).1 h0).symm
  have hu := not_mem_findSubtree_of_ancestor hnd hroot_mem hr (by omega) (self_mem_pathTo hroot_mem)
  intro heq; exact hu (heq ▸ hy)

theorem replaceSubtree_depthOf_root {t s' : AuxTree} {rSub x : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hs' : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree rSub).toList) (hx : s'.rootId = x) :
    (t.replaceSubtree rSub s').depthOf x = t.depthOf rSub := by
  induction t with
  | leaf => simp [toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r
        simp only [replaceSubtree, ↓reduceIte]
        have hx0 : s'.depthOf x = 0 := hx ▸ (depthOf_zero_iff_root (rootId_mem hs')).2 rfl
        rw [hx0, depthOf_root]
      · have hx_in_s' : x ∈ s'.toList := hx ▸ rootId_mem hs'
        simp only [findSubtree, hid_r, ↓reduceIte] at hs_perm
        simp only [replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hs_perm
          have hx_l : x ∈ l.toList := findSubtree_subset (hs_perm.mem_iff.1 hx_in_s')
          have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
          have hxd : x ≠ id := fun h => hid_nl (h ▸ hx_l)
          have hrx : rSub ≠ id := Ne.symm hid_r
          have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
            replaceSubtree_perm hl_nd hrl hs_perm
          have hx_rep : x ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hx_l
          rw [replaceSubtree_not_mem hnr, depthOf, depthOf]
          simp only [hxd, hrx, hx_rep, hrl, ↓reduceIte, ihl hl_nd hrl hs_perm]
        · have hrr : rSub ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hs_perm
          have hx_r : x ∈ r.toList := findSubtree_subset (hs_perm.mem_iff.1 hx_in_s')
          have hx_nl : x ∉ l.toList := fun h => hdisj_lr x h hx_r
          have hxd : x ≠ id := fun h => hid_nr (h ▸ hx_r)
          have hrx : rSub ≠ id := Ne.symm hid_r
          have hr_perm : (r.replaceSubtree rSub s').toList.Perm r.toList :=
            replaceSubtree_perm hr_nd hrr hs_perm
          have hx_rep : x ∈ (r.replaceSubtree rSub s').toList := hr_perm.mem_iff.2 hx_r
          rw [replaceSubtree_not_mem hrl, depthOf, depthOf]
          simp only [hxd, hrx, hx_nl, hrl, hrr, hx_rep, ↓reduceIte, ihr hr_nd hrr hs_perm]

theorem findSubtree_replaceSubtree_root {t s' : AuxTree} {rSub : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hs' : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree rSub).toList) :
    (t.replaceSubtree rSub s').findSubtree s'.rootId = s' := by
  induction t with
  | leaf => simp [toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r; simp [replaceSubtree, findSubtree_root hs']
      · have hs_in : s'.rootId ∈ s'.toList := rootId_mem hs'
        simp only [findSubtree, hid_r, ↓reduceIte] at hs_perm
        simp only [replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hs_perm
          have hs_l : s'.rootId ∈ l.toList := findSubtree_subset (hs_perm.mem_iff.1 hs_in)
          have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
          have hne_id : id ≠ s'.rootId := fun h => hid_nl (h ▸ hs_l)
          have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
            replaceSubtree_perm hl_nd hrl hs_perm
          have hs_rep : s'.rootId ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hs_l
          rw [replaceSubtree_not_mem hnr, findSubtree]
          simp only [hne_id, hs_rep, ↓reduceIte]
          exact ihl hl_nd hrl hs_perm
        · have hrr : rSub ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hs_perm
          have hs_r : s'.rootId ∈ r.toList := findSubtree_subset (hs_perm.mem_iff.1 hs_in)
          have hs_nl : s'.rootId ∉ l.toList := fun h => hdisj_lr s'.rootId h hs_r
          have hne_id : id ≠ s'.rootId := fun h => hid_nr (h ▸ hs_r)
          rw [replaceSubtree_not_mem hrl, findSubtree]
          simp only [hne_id, hs_nl, ↓reduceIte]
          exact ihr hr_nd hrr hs_perm

/-! ### Subtree sizes, ranks, and Sleator–Tarjan potential -/

/-- Total tree weight `s(t)` including external virtual weights `vSize : ℕ → ℕ`. -/
def treeSize (vSize : ℕ → ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r => 1 + l.treeSize vSize + r.treeSize vSize + vSize id

theorem treeSize_eq_sum (vSize : ℕ → ℕ) (t : AuxTree) :
    t.treeSize vSize = (t.toList.map (fun y => 1 + vSize y)).sum := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      simp only [treeSize, toList, List.map_append, List.map_cons,
        List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, ihl, ihr]
      omega

theorem countNodes_le_treeSize (vSize : ℕ → ℕ) (t : AuxTree) :
    t.countNodes ≤ t.treeSize vSize := by
  induction t with
  | leaf => exact Nat.le_refl 0
  | node id l r ihl ihr => simp [countNodes, treeSize]; omega

theorem one_le_treeSize (vSize : ℕ → ℕ) {id : ℕ} {l r : AuxTree} :
    1 ≤ (AuxTree.node id l r).treeSize vSize := by
  simp [treeSize]; omega

/-- Rank `⌊log₂ s(t)⌋` (or `0` for `leaf`). -/
def rank (vSize : ℕ → ℕ) (t : AuxTree) : ℕ :=
  Nat.log 2 (t.treeSize vSize)

/-- Splay potential `Φ(t) = ∑_{u ∈ t} rank(u)`. -/
def treePhi (vSize : ℕ → ℕ) : AuxTree → ℕ
  | .leaf => 0
  | .node id l r => (AuxTree.node id l r).rank vSize + l.treePhi vSize + r.treePhi vSize

theorem findSubtree_rank_ge (vSize : ℕ → ℕ) {t : AuxTree} {x : ℕ} (hx : x ∈ t.toList) :
    Nat.log 2 (1 + vSize x) ≤ (t.findSubtree x).rank vSize := by
  rcases findSubtree_root_of_mem hx with ⟨l', r', hsub⟩
  rw [hsub, rank]
  exact Nat.log_mono_right (by simp [treeSize]; omega)

theorem treePhi_le (vSize : ℕ → ℕ) (t : AuxTree) :
    t.treePhi vSize ≤ t.countNodes * Nat.log 2 (t.treeSize vSize + 2) := by
  induction t with
  | leaf => simp [treePhi, countNodes]
  | node id l r ihl ihr =>
      have hl_le : l.treeSize vSize + 2 ≤ (AuxTree.node id l r).treeSize vSize + 2 := by
        simp [treeSize]; omega
      have hr_le : r.treeSize vSize + 2 ≤ (AuxTree.node id l r).treeSize vSize + 2 := by
        simp [treeSize]; omega
      have hrk : (AuxTree.node id l r).rank vSize ≤
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.log_mono_right (by omega)
      have hrl := Nat.log_mono_right (b := 2) hl_le
      have hrr := Nat.log_mono_right (b := 2) hr_le
      have h1 : l.treePhi vSize ≤ l.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.le_trans ihl (Nat.mul_le_mul_left _ hrl)
      have h2 : r.treePhi vSize ≤ r.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) :=
        Nat.le_trans ihr (Nat.mul_le_mul_left _ hrr)
      simp only [treePhi, countNodes]
      have hmul : (1 + l.countNodes + r.countNodes) *
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) =
          Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) +
          l.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) +
          r.countNodes * Nat.log 2 ((AuxTree.node id l r).treeSize vSize + 2) := by
        simp only [Nat.add_mul, Nat.one_mul]
      omega

theorem replaceSubtree_treeSize_add (vSize : ℕ → ℕ) {t s' : AuxTree} {rSub d1 d2 : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList)
    (hs_sz : s'.treeSize vSize = (t.findSubtree rSub).treeSize vSize)
    (hs_phi : s'.treePhi vSize + d1 ≤ (t.findSubtree rSub).treePhi vSize + d2) :
    (t.replaceSubtree rSub s').treeSize vSize = t.treeSize vSize ∧
    (t.replaceSubtree rSub s').treePhi vSize + d1 ≤ t.treePhi vSize + d2 := by
  induction t with
  | leaf => simp [toList] at hr
  | node id l r ihl ihr =>
      simp only [replaceSubtree]
      by_cases heq : id = rSub
      · subst heq; simp only [findSubtree, ↓reduceIte] at hs_sz hs_phi ⊢; exact ⟨hs_sz, hs_phi⟩
      · simp only [heq, ↓reduceIte]
        rcases nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, hdisj_lr⟩
        by_cases hnl : rSub ∈ l.toList
        · have hnr : rSub ∉ r.toList := hdisj_lr rSub hnl
          have hrep_r : r.replaceSubtree rSub s' = r := replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree rSub = l.findSubtree rSub := by
            simp [findSubtree, heq, hnl]
          rcases ihl hl_nd hnl (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_l, hphi_l⟩
          rw [hrep_r]
          have hsz : (AuxTree.node id (l.replaceSubtree rSub s') r).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by simp [treeSize, hsz_l]
          have hrank : (AuxTree.node id (l.replaceSubtree rSub s') r).rank vSize =
              (AuxTree.node id l r).rank vSize := by simp only [rank, hsz]
          refine ⟨hsz, ?_⟩
          simp only [treePhi, hrank]
          omega
        · have hnr : rSub ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (hl | rfl) | hr'
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr'
          have hrep_l : l.replaceSubtree rSub s' = l := replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree rSub = r.findSubtree rSub := by
            simp [findSubtree, heq, hnl]
          rcases ihr hr_nd hnr (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_r, hphi_r⟩
          rw [hrep_l]
          have hsz : (AuxTree.node id l (r.replaceSubtree rSub s')).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by simp [treeSize, hsz_r]
          have hrank : (AuxTree.node id l (r.replaceSubtree rSub s')).rank vSize =
              (AuxTree.node id l r).rank vSize := by simp only [rank, hsz]
          refine ⟨hsz, ?_⟩
          simp only [treePhi, hrank]
          omega

/-- Core integer logarithm inequality used in zig-zig and zig-zag steps:
if `1 ≤ a`, `1 ≤ b`, and `a + b ≤ c`, then `Nat.log 2 a + Nat.log 2 b + 1 ≤ 2 * Nat.log 2 c`. -/
theorem nat_log_add_le_of_add_le {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hsum : a + b ≤ c) :
    Nat.log 2 a + Nat.log 2 b + 1 ≤ 2 * Nat.log 2 c := by
  have hac : Nat.log 2 a ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  have hbc : Nat.log 2 b ≤ Nat.log 2 c := Nat.log_mono_right (by omega)
  by_cases h1 : Nat.log 2 a = Nat.log 2 c
  · by_cases h2 : Nat.log 2 b = Nat.log 2 c
    · have ha_pow : 2 ^ Nat.log 2 c ≤ a := by
        simpa [h1] using Nat.pow_log_le_self 2 (by omega : a ≠ 0)
      have hb_pow : 2 ^ Nat.log 2 c ≤ b := by
        simpa [h2] using Nat.pow_log_le_self 2 (by omega : b ≠ 0)
      have hc_lt : c < 2 ^ (Nat.log 2 c + 1) := Nat.lt_pow_succ_log_self (by decide : 1 < 2) c
      rw [Nat.pow_succ, Nat.mul_two] at hc_lt
      omega
    · omega
  · omega

theorem zig_right_phi_le (vSize : ℕ → ℕ) (x p : ℕ) (A B C : AuxTree) :
    let t := AuxTree.node p (AuxTree.node x A B) C
    let t' := AuxTree.node x A (AuxTree.node p B C)
    t'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hr_eq : t'.rank vSize = t.rank vSize := by simp [rank, hs_eq]
  have hrx_le : (AuxTree.node x A B).rank vSize ≤ t.rank vSize :=
    Nat.log_mono_right (by simp [t, treeSize]; omega)
  have hrp'_le : (AuxTree.node p B C).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right (by simp [t', treeSize]; omega)
  dsimp only [t, t', treePhi]
  rw [show (AuxTree.node x A (AuxTree.node p B C)).rank vSize = t'.rank vSize from rfl,
      show (AuxTree.node p (AuxTree.node x A B) C).rank vSize = t.rank vSize from rfl,
      hr_eq]
  omega

theorem zig_left_phi_le (vSize : ℕ → ℕ) (p x : ℕ) (A B C : AuxTree) :
    let t := AuxTree.node p A (AuxTree.node x B C)
    let t' := AuxTree.node x (AuxTree.node p A B) C
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hr_eq : t'.rank vSize = t.rank vSize := by simp [rank, hs_eq]
  have hrp'_le : (AuxTree.node p A B).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right (by simp [t', treeSize]; omega)
  have hrx_le : (AuxTree.node x B C).rank vSize ≤ t.rank vSize :=
    Nat.log_mono_right (by simp [t, treeSize]; omega)
  dsimp only [t, t', treePhi]
  rw [show (AuxTree.node x (AuxTree.node p A B) C).rank vSize = t'.rank vSize from rfl,
      show (AuxTree.node p A (AuxTree.node x B C)).rank vSize = t.rank vSize from rfl,
      hr_eq]
  omega

private theorem zigZig_arith {rx rp rg rx' rp' rg' : ℕ}
    (hrg : rg = rx') (hrx_rp : rx ≤ rp) (_hrx_rx' : rx ≤ rx')
    (hrp'_rx' : rp' ≤ rx') (_hrg'_rx' : rg' ≤ rx') (hlog : rx + rg' + 1 ≤ 2 * rx') :
    rx' + rp' + rg' + 3 * rx + 1 ≤ rx + rp + rg + 3 * rx' := by
  omega

theorem zigZig_right_phi_le (vSize : ℕ → ℕ) (x p g : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g (AuxTree.node p (AuxTree.node x A B) C) D
    let t' := AuxTree.node x A (AuxTree.node p B (AuxTree.node g C D))
    t'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hsum : (AuxTree.node x A B).treeSize vSize + (AuxTree.node g C D).treeSize vSize ≤
      t'.treeSize vSize := by simp [t', treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (one_le_treeSize vSize) (one_le_treeSize vSize) hsum
  have har := zigZig_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p (AuxTree.node x A B) C).rank vSize)
    (rx := (AuxTree.node x A B).rank vSize)
    (rp' := (AuxTree.node p B (AuxTree.node g C D)).rank vSize)
    (rg' := (AuxTree.node g C D).rank vSize)
    (by simp [rank, hs_eq])
    (Nat.log_mono_right (by simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    hlog
  dsimp only [t, t', treePhi]
  rw [show (AuxTree.node g (AuxTree.node p (AuxTree.node x A B) C) D).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x A (AuxTree.node p B (AuxTree.node g C D))).rank vSize =
        t'.rank vSize from rfl]
  omega

theorem zigZig_left_phi_le (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g A (AuxTree.node p B (AuxTree.node x C D))
    let t' := AuxTree.node x (AuxTree.node p (AuxTree.node g A B) C) D
    t'.treePhi vSize + 3 * (AuxTree.node x C D).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hsum : (AuxTree.node x C D).treeSize vSize + (AuxTree.node g A B).treeSize vSize ≤
      t'.treeSize vSize := by simp [t', treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (one_le_treeSize vSize) (one_le_treeSize vSize) hsum
  have har := zigZig_arith
    (rg := t.rank vSize) (rx' := t'.rank vSize)
    (rp := (AuxTree.node p B (AuxTree.node x C D)).rank vSize)
    (rx := (AuxTree.node x C D).rank vSize)
    (rp' := (AuxTree.node p (AuxTree.node g A B) C).rank vSize)
    (rg' := (AuxTree.node g A B).rank vSize)
    (by simp [rank, hs_eq])
    (Nat.log_mono_right (by simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    (Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega))
    hlog
  dsimp only [t, t', treePhi]
  rw [show (AuxTree.node g A (AuxTree.node p B (AuxTree.node x C D))).rank vSize =
        t.rank vSize from rfl,
      show (AuxTree.node x (AuxTree.node p (AuxTree.node g A B) C) D).rank vSize =
        t'.rank vSize from rfl]
  omega

theorem zigZag_lr_phi_le (vSize : ℕ → ℕ) (p x g : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g (AuxTree.node p A (AuxTree.node x B C)) D
    let t' := AuxTree.node x (AuxTree.node p A B) (AuxTree.node g C D)
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hsum : (AuxTree.node p A B).treeSize vSize + (AuxTree.node g C D).treeSize vSize ≤
      t'.treeSize vSize := by simp [t', treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (one_le_treeSize vSize) (one_le_treeSize vSize) hsum
  have hrg : t.rank vSize = t'.rank vSize := by simp [rank, hs_eq]
  have hrx_rp : (AuxTree.node x B C).rank vSize ≤ (AuxTree.node p A (AuxTree.node x B C)).rank vSize :=
    Nat.log_mono_right (by simp [treeSize]; omega)
  have hrx_rx' : (AuxTree.node x B C).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega)
  dsimp only [t, t', rank] at hlog hrg hrx_rp hrx_rx'
  dsimp only [t, t', treePhi, rank]
  omega

theorem zigZag_rl_phi_le (vSize : ℕ → ℕ) (g x p : ℕ) (A B C D : AuxTree) :
    let t := AuxTree.node g A (AuxTree.node p (AuxTree.node x B C) D)
    let t' := AuxTree.node x (AuxTree.node g A B) (AuxTree.node p C D)
    t'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  intro t t'
  have hs_eq : t'.treeSize vSize = t.treeSize vSize := by simp [t, t', treeSize]; omega
  have hsum : (AuxTree.node g A B).treeSize vSize + (AuxTree.node p C D).treeSize vSize ≤
      t'.treeSize vSize := by simp [t', treeSize]; omega
  have hlog := nat_log_add_le_of_add_le
    (one_le_treeSize vSize) (one_le_treeSize vSize) hsum
  have hrg : t.rank vSize = t'.rank vSize := by simp [rank, hs_eq]
  have hrx_rp : (AuxTree.node x B C).rank vSize ≤ (AuxTree.node p (AuxTree.node x B C) D).rank vSize :=
    Nat.log_mono_right (by simp [treeSize]; omega)
  have hrx_rx' : (AuxTree.node x B C).rank vSize ≤ t'.rank vSize :=
    Nat.log_mono_right (by dsimp only [t']; simp [treeSize]; omega)
  dsimp only [t, t', rank] at hlog hrg hrx_rp hrx_rx'
  dsimp only [t, t', treePhi, rank]
  omega

end AuxTree
end MinCostFlow.LinkCut
end
