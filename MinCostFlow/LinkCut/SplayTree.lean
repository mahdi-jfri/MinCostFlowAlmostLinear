module

public import MinCostFlow.LinkCut.SplayTreeBasic
import Mathlib.Tactic

/-!
# Pure binary splay tree skeletons and Sleator–Tarjan potential

This file defines the algebraic binary tree skeleton `AuxTree`, logical in-order traversal
under pre-flipped lazy reversal `evalInorder`, ancestor paths and depths (`pathTo`, `depthOf`,
`parentIn`, `findSubtree`, `replaceSubtree`), single rotations (`rotateAt`), subtree sizes
`treeSize`, ranks `rank`, and the integer Sleator–Tarjan potential `treePhi` (Sleator–Tarjan
1983, cited in `arXiv:2309.16629v1`, Section 4, page 13 and Section 6, page 29).

It proves all structural invariants and single/double rotation potential inequalities (`zig`,
`zigZig`, `zigZag`) purely on `AuxTree`, independent of node payloads and machine memory.
-/

@[expose] public section

namespace MinCostFlow.LinkCut

namespace AuxTree

/-! ### Single rotations (`rotateAt`) -/

/-- Rotate the left child to the root (right rotation). -/
def rotateRightRoot : AuxTree → AuxTree
  | .node p (.node x A B) r => .node x A (.node p B r)
  | t => t

/-- Rotate the right child to the root (left rotation). -/
def rotateLeftRoot : AuxTree → AuxTree
  | .node p l (.node x B C) => .node x (.node p l B) C
  | t => t

/-- Algebraic single rotation moving `x` one step toward the root (if `x` is a non-root node). -/
def rotateAt (x : ℕ) : AuxTree → AuxTree
  | .leaf => .leaf
  | .node p l r =>
      if p = x then .node p l r
      else if l.hasRoot x then rotateRightRoot (.node p l r)
      else if r.hasRoot x then rotateLeftRoot (.node p l r)
      else if x ∈ l.toList then .node p (l.rotateAt x) r
      else .node p l (r.rotateAt x)

@[simp] theorem rotateAt_leaf (x : ℕ) : AuxTree.leaf.rotateAt x = .leaf := rfl

@[simp] theorem rotateAt_root (p : ℕ) (l r : AuxTree) :
    (AuxTree.node p l r).rotateAt p = .node p l r := by
  simp [rotateAt]

theorem rotateAt_zigRight {x p : ℕ} (A B C : AuxTree) (hne : p ≠ x) :
    (AuxTree.node p (.node x A B) C).rotateAt x = .node x A (.node p B C) := by
  simp [rotateAt, hne, hasRoot, rotateRightRoot]

theorem rotateAt_zigLeft {x p : ℕ} (l C D : AuxTree) (hne : p ≠ x)
    (hl : ¬ l.hasRoot x) :
    (AuxTree.node p l (.node x C D)).rotateAt x = .node x (.node p l C) D := by
  simp only [rotateAt, hne, hl, Bool.false_eq_true, ↓reduceIte]
  simp only [hasRoot, beq_self_eq_true, ↓reduceIte, rotateLeftRoot]

theorem rotateAt_not_mem {x : ℕ} {t : AuxTree} (hx : x ∉ t.toList) :
    t.rotateAt x = t := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      have hne : p ≠ x := fun h => hx (by subst h; simp [toList])
      have hnl : x ∉ l.toList := fun h => hx (by simp [toList, h])
      have hnr : x ∉ r.toList := fun h => hx (by simp [toList, h])
      have hl_nr : ¬ l.hasRoot x := fun h => by
        obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hnl (by simp [toList])
      have hr_nr : ¬ r.hasRoot x := fun h => by
        obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h; exact hnr (by simp [toList])
      simp [rotateAt, hne, hl_nr, hr_nr, hnl, ihr hnr]

theorem rotateAt_ne_leaf {x : ℕ} {t : AuxTree} (ht : t ≠ .leaf) :
    t.rotateAt x ≠ .leaf := by
  cases t with
  | leaf => exact absurd rfl ht
  | node p l r =>
      simp only [rotateAt]
      split_ifs with h1 h2 h3 h4
      · simp
      · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h2; simp [rotateRightRoot]
      · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h3; simp [rotateLeftRoot]
      · simp
      · simp

theorem rotateAt_toList_perm (x : ℕ) (t : AuxTree) :
    (t.rotateAt x).toList.Perm t.toList := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      simp only [rotateAt]
      split_ifs with h1 h2 h3 h4
      · exact List.Perm.refl _
      · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h2
        simp [rotateRightRoot, toList, List.append_assoc]
      · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h3
        simp [rotateLeftRoot, toList, List.append_assoc]
      · simp only [toList]
        exact (ihl.append_right [p]).append_right r.toList
      · simp only [toList]
        exact ihr.append_left (l.toList ++ [p])

theorem rotateAt_treeSize (vSize : ℕ → ℕ) (x : ℕ) (t : AuxTree) :
    (t.rotateAt x).treeSize vSize = t.treeSize vSize := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      simp only [rotateAt]
      split_ifs with h1 h2 h3 h4
      · rfl
      · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h2; simp [rotateRightRoot, treeSize]; omega
      · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h3; simp [rotateLeftRoot, treeSize]; omega
      · simp [treeSize, ihl]
      · simp [treeSize, ihr]

theorem rotateAt_evalInorder {x : ℕ} {t : AuxTree} (rev : ℕ → Bool)
    (hnd : t.toList.Nodup) (hrev : x ∈ t.toList → ∀ u ∈ t.pathTo x, rev u = false) :
    (t.rotateAt x).evalInorder rev false = t.evalInorder rev false := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      by_cases hx_mem : x ∈ (AuxTree.node p l r).toList
      swap
      · rw [rotateAt_not_mem hx_mem]
      have hpath := hrev hx_mem
      rcases nodup_node_unfold hnd with ⟨hl_nd, hp_nl, hr_nd, hp_nr, hdisj_lr⟩
      by_cases hpx : p = x
      · subst hpx; simp
      · have hrev_p : rev p = false := by
          apply hpath p
          rw [pathTo]
          by_cases hnl : x ∈ l.toList
          · simp [Ne.symm hpx, hnl]
          · have hnr : x ∈ r.toList := by
              simp only [toList, List.mem_append, List.mem_singleton] at hx_mem
              rcases hx_mem with (h | rfl) | h
              · exact absurd h hnl
              · exact absurd rfl hpx
              · exact h
            simp [Ne.symm hpx, hnl, hnr]
        simp only [rotateAt, hpx, ↓reduceIte]
        by_cases hlr : l.hasRoot x
        · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp hlr
          have hrev_x : rev x = false := hpath x (by simp [pathTo, Ne.symm hpx, toList])
          simp [hlr, rotateRightRoot, evalInorder, hrev_p, hrev_x, List.append_assoc]
        · by_cases hrr : r.hasRoot x
          · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp hrr
            have hx_nl : x ∉ l.toList := fun h => hdisj_lr x h (by simp [toList])
            have hrev_x : rev x = false := hpath x (by simp [pathTo, Ne.symm hpx, hx_nl, toList])
            simp [hlr, hrr, rotateLeftRoot, evalInorder, hrev_p, hrev_x, List.append_assoc]
          · by_cases hxl : x ∈ l.toList
            · have hpath_l : ∀ u ∈ l.pathTo x, rev u = false := fun u hu =>
                hpath u (by rw [pathTo]; simp [Ne.symm hpx, hxl, hu])
              simp [hlr, hrr, hxl, evalInorder, hrev_p, ihl hl_nd (fun _ => hpath_l)]
            · have hxr : x ∈ r.toList := by
                simp only [toList, List.mem_append, List.mem_singleton] at hx_mem
                rcases hx_mem with (h | rfl) | h
                · exact absurd h hxl
                · exact absurd rfl hpx
                · exact h
              have hpath_r : ∀ u ∈ r.pathTo x, rev u = false := fun u hu =>
                hpath u (by rw [pathTo]; simp [Ne.symm hpx, hxl, hxr, hu])
              simp [hlr, hrr, hxl, evalInorder, hrev_p, ihr hr_nd (fun _ => hpath_r)]

theorem rotateAt_depthOf_self {x : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) :
    (t.rotateAt x).depthOf x = t.depthOf x - 1 := by
  induction t with
  | leaf => simp [toList] at hx
  | node p l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, hdisj_lr⟩
      by_cases hpx : p = x
      · subst hpx; simp [depthOf_root]
      · simp only [rotateAt, hpx, ↓reduceIte]
        by_cases hlr : l.hasRoot x
        · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp hlr
          simp only [hlr, ↓reduceIte, rotateRightRoot, depthOf_root]
          conv_rhs => rw [depthOf]
          simp [Ne.symm hpx, toList, depthOf_root]
        · by_cases hrr : r.hasRoot x
          · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp hrr
            have hx_nl : x ∉ l.toList := fun h => hdisj_lr x h (by simp [toList])
            simp only [hlr, hrr, Bool.false_eq_true, ↓reduceIte, rotateLeftRoot]
            conv_lhs => rw [depthOf_root]
            conv_rhs => rw [depthOf]
            simp [Ne.symm hpx, hx_nl, toList, depthOf_root]
          · by_cases hxl : x ∈ l.toList
            · have hx_ne_lr : x ≠ l.rootId := fun h => hlr (by
                cases l with
                | leaf => simp [toList] at hxl
                | node lid _ _ => simp [rootId] at h; subst h; simp [hasRoot])
              have hdep_l : 1 ≤ l.depthOf x := by
                have hnz : l.depthOf x ≠ 0 := fun h0 => hx_ne_lr ((depthOf_zero_iff_root hxl).1 h0)
                omega
              have hl_perm : (l.rotateAt x).toList.Perm l.toList := rotateAt_toList_perm x l
              simp only [hlr, hrr, hxl, Bool.false_eq_true, ↓reduceIte]
              conv_lhs => rw [depthOf.eq_def]
              conv_rhs => rw [depthOf.eq_def]
              simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte, ihl hl_nd hxl]
              omega
            · have hxr : x ∈ r.toList := by
                simp only [toList, List.mem_append, List.mem_singleton] at hx
                rcases hx with (h | rfl) | h
                · exact absurd h hxl
                · exact absurd rfl hpx
                · exact h
              have hx_ne_rr : x ≠ r.rootId := fun h => hrr (by
                cases r with
                | leaf => simp [toList] at hxr
                | node rid _ _ => simp [rootId] at h; subst h; simp [hasRoot])
              have hdep_r : 1 ≤ r.depthOf x := by
                have hnz : r.depthOf x ≠ 0 := fun h0 => hx_ne_rr ((depthOf_zero_iff_root hxr).1 h0)
                omega
              have hr_perm : (r.rotateAt x).toList.Perm r.toList := rotateAt_toList_perm x r
              simp only [hlr, hrr, hxl, Bool.false_eq_true, ↓reduceIte]
              conv_lhs => rw [depthOf.eq_def]
              conv_rhs => rw [depthOf.eq_def]
              simp only [Ne.symm hpx, hxl, hr_perm.mem_iff, hxr, ↓reduceIte, ihr hr_nd hxr]
              omega

theorem rotateAt_pathTo_subset {x y : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hy : y ∈ t.pathTo x) :
    ∀ u ∈ (t.rotateAt y).pathTo x, u ∈ t.pathTo x := by
  induction t with
  | leaf => simp [toList] at hx
  | node p l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, _, hr_nd, _, hdisj_lr⟩
      by_cases hpx : p = x
      · subst hpx; simp only [pathTo, ↓reduceIte, List.mem_singleton] at hy; subst hy; simp
      · by_cases hpy : p = y
        · subst hpy; simp
        · simp only [rotateAt, hpy, ↓reduceIte]
          by_cases hlr : l.hasRoot y
          · obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp hlr
            have hxl : x ∈ (AuxTree.node y A B).toList := by
              by_contra hnin
              have hxr : x ∈ r.toList := by
                simp only [toList, List.mem_append, List.mem_singleton] at hx hnin
                rcases hx with (h | rfl) | h
                · exact absurd h hnin
                · exact absurd rfl hpx
                · exact h
              have hyr : y ∈ r.pathTo x := by
                rw [pathTo] at hy
                simp only [Ne.symm hpx, hnin, hxr, ↓reduceIte, List.mem_cons] at hy
                rcases hy with rfl | hy'
                · exact absurd rfl hpy
                · exact hy'
              exact hdisj_lr y (by simp [toList]) (mem_pathTo hyr)
            simp only [hlr, ↓reduceIte, rotateRightRoot]
            intro u hu
            by_cases hxy : x = y
            · subst hxy
              rw [pathTo] at hu; simp only [↓reduceIte, List.mem_singleton] at hu; subst hu
              rw [pathTo]; simp [Ne.symm hpx, hxl, pathTo]
            · rw [pathTo] at hu; simp only [hxy, ↓reduceIte] at hu
              rw [pathTo]; simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons]
              rw [pathTo]; simp only [hxy, ↓reduceIte]
              by_cases hxA : x ∈ A.toList
              · simp only [hxA, ↓reduceIte, List.mem_cons] at hu ⊢
                rcases hu with rfl | huA
                · exact Or.inr (Or.inl rfl)
                · exact Or.inr (Or.inr huA)
              · have hxB : x ∈ B.toList := by
                  simp only [toList, List.mem_append, List.mem_singleton] at hxl
                  rcases hxl with (h | rfl) | h
                  · exact absurd h hxA
                  · exact absurd rfl hxy
                  · exact h
                have hxpB : x ∈ (AuxTree.node p B r).toList := by simp [toList, hxB]
                simp only [hxA, hxpB, ↓reduceIte, List.mem_cons] at hu
                simp only [hxA, hxB, ↓reduceIte, List.mem_cons]
                rcases hu with rfl | huB
                · exact Or.inr (Or.inl rfl)
                · rw [pathTo] at huB
                  simp only [Ne.symm hpx, hxB, ↓reduceIte, List.mem_cons] at huB
                  rcases huB with rfl | huB'
                  · exact Or.inl rfl
                  · exact Or.inr (Or.inr huB')
          · by_cases hrr : r.hasRoot y
            · obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp hrr
              have hx_nl : x ∉ l.toList := by
                intro hxl
                have hyl : y ∈ l.pathTo x := by
                  rw [pathTo] at hy
                  simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                  rcases hy with rfl | hy'
                  · exact absurd rfl hpy
                  · exact hy'
                exact hdisj_lr y (mem_pathTo hyl) (by simp [toList])
              have hxr : x ∈ (AuxTree.node y C D).toList := by
                simp only [toList, List.mem_append, List.mem_singleton] at hx ⊢
                rcases hx with (h | rfl) | h
                · exact absurd h hx_nl
                · exact absurd rfl hpx
                · exact h
              simp only [hlr, hrr, Bool.false_eq_true, ↓reduceIte, rotateLeftRoot]
              intro u hu
              by_cases hxy : x = y
              · subst hxy
                rw [pathTo] at hu; simp only [↓reduceIte, List.mem_singleton] at hu; subst hu
                rw [pathTo]; simp [Ne.symm hpx, hx_nl, hxr, pathTo]
              · have hx_pC : x ∈ (AuxTree.node p l C).toList ↔ x ∈ C.toList := by
                  simp only [toList, List.mem_append, List.mem_singleton]
                  constructor
                  · rintro ((h | rfl) | h); exact absurd h hx_nl; exact absurd rfl hpx; exact h
                  · intro h; exact Or.inr h
                rw [pathTo] at hu; simp only [hxy, hx_pC, ↓reduceIte] at hu
                rw [pathTo]; simp only [Ne.symm hpx, hx_nl, hxr, ↓reduceIte, List.mem_cons]
                rw [pathTo]; simp only [hxy, ↓reduceIte]
                by_cases hxC : x ∈ C.toList
                · simp only [hxC, ↓reduceIte, List.mem_cons] at hu ⊢
                  rcases hu with rfl | huC
                  · exact Or.inr (Or.inl rfl)
                  · rw [pathTo] at huC
                    simp only [Ne.symm hpx, hx_nl, hxC, ↓reduceIte, List.mem_cons] at huC
                    rcases huC with rfl | huC'
                    · exact Or.inl rfl
                    · exact Or.inr (Or.inr huC')
                · have hxD : x ∈ D.toList := by
                    simp only [toList, List.mem_append, List.mem_singleton] at hxr
                    rcases hxr with (h | rfl) | h
                    · exact absurd h hxC
                    · exact absurd rfl hxy
                    · exact h
                  simp only [hxC, hxD, ↓reduceIte, List.mem_cons] at hu ⊢
                  rcases hu with rfl | huD
                  · exact Or.inr (Or.inl rfl)
                  · exact Or.inr (Or.inr huD)
            · by_cases hyl : y ∈ l.toList
              · have hxl : x ∈ l.toList := by
                  by_contra hnin
                  have hxr : x ∈ r.toList := by
                    simp only [toList, List.mem_append, List.mem_singleton] at hx
                    rcases hx with (h | rfl) | h
                    · exact absurd h hnin
                    · exact absurd rfl hpx
                    · exact h
                  have hyr : y ∈ r.pathTo x := by
                    rw [pathTo] at hy
                    simp only [Ne.symm hpx, hnin, hxr, ↓reduceIte, List.mem_cons] at hy
                    rcases hy with rfl | hy'
                    · exact absurd rfl hpy
                    · exact hy'
                  exact hdisj_lr y hyl (mem_pathTo hyr)
                have hy_l : y ∈ l.pathTo x := by
                  rw [pathTo] at hy
                  simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                  rcases hy with rfl | hy'; exact absurd rfl hpy; exact hy'
                have hl_perm : (l.rotateAt y).toList.Perm l.toList := rotateAt_toList_perm y l
                simp only [hlr, hrr, hyl, Bool.false_eq_true, ↓reduceIte]
                intro u hu
                dsimp only [pathTo] at hu ⊢
                simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte, List.mem_cons] at hu ⊢
                rcases hu with rfl | hu'
                · exact Or.inl rfl
                · exact Or.inr (ihl hl_nd hxl hy_l u hu')
              · have hnin_l : x ∉ l.toList := fun hxl => hyl (mem_pathTo (by
                  rw [pathTo] at hy
                  simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                  rcases hy with rfl | hy'; exact absurd rfl hpy; exact hy'))
                have hxr : x ∈ r.toList := by
                  simp only [toList, List.mem_append, List.mem_singleton] at hx
                  rcases hx with (h | rfl) | h
                  · exact absurd h hnin_l
                  · exact absurd rfl hpx
                  · exact h
                have hy_r : y ∈ r.pathTo x := by
                  rw [pathTo] at hy
                  simp only [Ne.symm hpx, hnin_l, hxr, ↓reduceIte, List.mem_cons] at hy
                  rcases hy with rfl | hy'; exact absurd rfl hpy; exact hy'
                have hr_perm : (r.rotateAt y).toList.Perm r.toList := rotateAt_toList_perm y r
                simp only [hlr, hrr, hyl, Bool.false_eq_true, ↓reduceIte]
                intro u hu
                dsimp only [pathTo] at hu ⊢
                simp only [Ne.symm hpx, hnin_l, hr_perm.mem_iff, hxr, ↓reduceIte,
                  List.mem_cons] at hu ⊢
                rcases hu with rfl | hu'
                · exact Or.inl rfl
                · exact Or.inr (ihr hr_nd hxr hy_r u hu')

theorem replaceSubtree_rotateAt {t : AuxTree} {x p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) :
    let p := t.parentIn x p₀
    t.replaceSubtree p ((t.findSubtree p).rotateAt x) = t.rotateAt x := by
  induction t generalizing p₀ with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      intro p
      have hne : id ≠ x := fun h => hxr (by simp [rootId, h])
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
      by_cases hnl : x ∈ l.toList
      · by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hnl
          | node lx A B =>
              simp only [rootId] at hxlr; subst hxlr
              have hp_eq : p = id := by simp [p, parentIn, hne, hnl]
              rw [hp_eq]; simp [replaceSubtree, findSubtree]
        · have ih := ihl (p₀ := id) hl_nd hnl hxlr
          have hp_eq : p = l.parentIn x id := by simp [p, parentIn, hne, hnl]
          have hp_mem : p ∈ l.toList := hp_eq ▸ (parentIn_mem_and_depth hl_nd hnl hxlr).1
          have hp_ne_id : id ≠ p := fun h => hid_nl (h ▸ hp_mem)
          have hp_nin_r : p ∉ r.toList := hdisj_lr p hp_mem
          have ih' : l.replaceSubtree p ((l.findSubtree p).rotateAt x) = l.rotateAt x := by
            simpa [← hp_eq] using ih
          have hrep : (AuxTree.node id l r).replaceSubtree p
              (((AuxTree.node id l r).findSubtree p).rotateAt x) =
              AuxTree.node id (l.replaceSubtree p ((l.findSubtree p).rotateAt x)) r := by
            simp only [replaceSubtree, hp_ne_id, ↓reduceIte, findSubtree, hp_mem]
            rw [replaceSubtree_not_mem hp_nin_r]
          rw [hrep, ih']
          have hlr_f : ¬ l.hasRoot x := fun h => by
            obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hxlr rfl
          have hrr_f : ¬ r.hasRoot x := fun h => by
            obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h; exact hdisj_lr x hnl (by simp [toList])
          simp [rotateAt, hne, hlr_f, hrr_f, hnl]
      · have hnr : x ∈ r.toList := by
          simp only [toList, List.mem_append, List.mem_singleton] at hx
          rcases hx with (h | rfl) | h
          · exact absurd h hnl
          · exact absurd rfl hne
          · exact h
        by_cases hxrr : x = r.rootId
        · cases r with
          | leaf => simp [toList] at hnr
          | node rx C D =>
              simp only [rootId] at hxrr; subst hxrr
              have hp_eq : p = id := by simp [p, parentIn, hne, hnl]
              rw [hp_eq]; simp [replaceSubtree, findSubtree]
        · have ih := ihr (p₀ := id) hr_nd hnr hxrr
          have hp_eq : p = r.parentIn x id := by simp [p, parentIn, hne, hnl]
          have hp_mem : p ∈ r.toList := hp_eq ▸ (parentIn_mem_and_depth hr_nd hnr hxrr).1
          have hp_ne_id : id ≠ p := fun h => hid_nr (h ▸ hp_mem)
          have hp_nin_l : p ∉ l.toList := fun hl => hdisj_lr p hl hp_mem
          have ih' : r.replaceSubtree p ((r.findSubtree p).rotateAt x) = r.rotateAt x := by
            simpa [← hp_eq] using ih
          have hrep : (AuxTree.node id l r).replaceSubtree p
              (((AuxTree.node id l r).findSubtree p).rotateAt x) =
              AuxTree.node id l (r.replaceSubtree p ((r.findSubtree p).rotateAt x)) := by
            simp only [replaceSubtree, hp_ne_id, ↓reduceIte, findSubtree, hp_nin_l]
            rw [replaceSubtree_not_mem hp_nin_l]
          rw [hrep, ih']
          have hlr_f : ¬ l.hasRoot x := fun h => by
            obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hnl (by simp [toList])
          have hrr_f : ¬ r.hasRoot x := fun h => by
            obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h; exact hxrr rfl
          simp [rotateAt, hne, hlr_f, hrr_f, hnl]

theorem grandparent_child_cases {t : AuxTree} {x p g : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp : p = t.parentIn x 0) (hp_mem : p ∈ t.toList) (hpr : p ≠ t.rootId)
    (hg : g = t.parentIn p 0) :
    (∃ A B C D, t.findSubtree g = .node g (.node p (.node x A B) C) D) ∨
    (∃ A B C D, t.findSubtree g = .node g (.node p A (.node x B C)) D) ∨
    (∃ A B C D, t.findSubtree g = .node g A (.node p (.node x B C) D)) ∨
    (∃ A B C D, t.findSubtree g = .node g A (.node p B (.node x C D))) := by
  have hg_mem : g ∈ t.toList := hg ▸ (parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr).1
  rcases parentIn_child_cases hnd hp_mem hpr hg with ⟨gl, gr, hsub_g, hcas_g⟩
  rcases parentIn_child_cases hnd hx hxr hp with ⟨pl, pr, hsub_p, hcas_p⟩
  have hsub_g_nd : (t.findSubtree g).toList.Nodup := findSubtree_nodup hnd
  rw [hsub_g] at hsub_g_nd
  rcases nodup_node_unfold hsub_g_nd with ⟨_, hg_nl, _, hg_nr, hdisj_g⟩
  rcases hcas_g with ⟨gpL, gpR, rfl⟩ | ⟨gpL, gpR, rfl⟩
  · have hgp : g ≠ p := fun h => hg_nl (h ▸ by simp [toList])
    have hp_s : p ∈ (t.findSubtree g).toList := by rw [hsub_g]; simp [toList]
    have hfind : t.findSubtree p = .node p gpL gpR := by
      rw [← findSubtree_findSubtree hnd hg_mem hp_s, hsub_g]
      simp [findSubtree, hgp, toList]
    rw [hfind] at hsub_p
    injection hsub_p with _ hpl hpr_eq
    rw [← hpl, ← hpr_eq] at hcas_p
    rcases hcas_p with ⟨A, B, rfl⟩ | ⟨C, D, rfl⟩
    · exact Or.inl ⟨A, B, gpR, gr, hsub_g⟩
    · exact Or.inr (Or.inl ⟨gpL, C, D, gr, hsub_g⟩)
  · have hgp : g ≠ p := fun h => hg_nr (h ▸ by simp [toList])
    have hp_nl : p ∉ gl.toList := fun h => hdisj_g p h (by simp [toList])
    have hp_s : p ∈ (t.findSubtree g).toList := by rw [hsub_g]; simp [toList]
    have hfind : t.findSubtree p = .node p gpL gpR := by
      rw [← findSubtree_findSubtree hnd hg_mem hp_s, hsub_g]
      simp [findSubtree, hgp, hp_nl]
    rw [hfind] at hsub_p
    injection hsub_p with _ hpl hpr_eq
    rw [← hpl, ← hpr_eq] at hcas_p
    rcases hcas_p with ⟨A, B, rfl⟩ | ⟨C, D, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨gl, A, B, gpR, hsub_g⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨gl, gpL, C, D, hsub_g⟩))

/-- Sleator–Tarjan single zig step at root `t.rootId`. -/
theorem zigStep_phi_le (vSize : ℕ → ℕ) {t : AuxTree} {x : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp_root : t.parentIn x 0 = t.rootId) :
    let t' := t.rotateAt x
    t'.rootId = x ∧ t'.depthOf x = 0 ∧ t'.treeSize vSize = t.treeSize vSize ∧
    t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize ≤
      t.treePhi vSize + 3 * t'.rank vSize := by
  cases t with
  | leaf => simp [toList] at hx
  | node rid l₀ r₀ =>
      intro t'
      simp only [rootId] at hxr hp_root
      rcases parentIn_child_cases hnd hx hxr hp_root.symm with ⟨l, r, hsub, hcas⟩
      simp only [findSubtree, ↓reduceIte] at hsub
      injection hsub with _ hl_eq hr_eq
      subst hl_eq hr_eq
      have hroot : rid ≠ x := hxr.symm
      rcases nodup_node_unfold hnd with ⟨_, hl_nl, _, hr_nr, hdisj⟩
      rcases hcas with ⟨A, B, rfl⟩ | ⟨C, D, rfl⟩
      · have hrot : t' = .node x A (.node rid B r₀) := by
          dsimp only [t']; exact rotateAt_zigRight A B r₀ hroot
        have hfind_x : (AuxTree.node rid (.node x A B) r₀).findSubtree x = .node x A B := by
          simp [findSubtree, hroot, toList]
        have hsz : t'.treeSize vSize = (AuxTree.node rid (.node x A B) r₀).treeSize vSize := by
          rw [hrot]; simp [treeSize]; omega
        have hphi := zig_right_phi_le vSize x rid A B r₀
        rw [← hrot] at hphi
        refine ⟨by simp [hrot, rootId], by simp [hrot, depthOf], hsz, ?_⟩
        rw [hfind_x]; exact hphi
      · have hx_nl : x ∉ l₀.toList := fun h => hdisj x h (by simp [toList])
        have hnl_nr : ¬ l₀.hasRoot x := fun h => by
          obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hx_nl (by simp [toList])
        have hrot : t' = .node x (.node rid l₀ C) D := by
          dsimp only [t']; exact rotateAt_zigLeft l₀ C D hroot hnl_nr
        have hfind_x : (AuxTree.node rid l₀ (.node x C D)).findSubtree x = .node x C D := by
          simp [findSubtree, hroot, hx_nl]
        have hsz : t'.treeSize vSize = (AuxTree.node rid l₀ (.node x C D)).treeSize vSize := by
          rw [hrot]; simp [treeSize]; omega
        have hphi := zig_left_phi_le vSize rid x l₀ C D
        rw [← hrot] at hphi
        refine ⟨by simp [hrot, rootId], by simp [hrot, depthOf], hsz, ?_⟩
        rw [hfind_x]; exact hphi

/-- Check whether `x`, parent `p`, grandparent `g` form a zig-zig shape (left-left or right-right). -/
def isZigZig (x p g : ℕ) (t : AuxTree) : Bool :=
  match t.findSubtree g with
  | .node _ l r =>
      let ll := match l with
        | .node p' (.node x' _ _) _ => p' == p && x' == x
        | _ => false
      let rr := match r with
        | .node p' _ (.node x' _ _) => p' == p && x' == x
        | _ => false
      ll || rr
  | .leaf => false

/-- Sleator–Tarjan double rotation step (zig-zig or zig-zag) lifting `x` by 2 levels. -/
theorem doubleStep_phi_le {t : AuxTree} {x p g : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp : p = t.parentIn x 0) (hp_mem : p ∈ t.toList) (hpr : p ≠ t.rootId)
    (hg : g = t.parentIn p 0) (hg_mem : g ∈ t.toList) :
    let t' := if t.isZigZig x p g then (t.rotateAt p).rotateAt x else (t.rotateAt x).rotateAt x
    2 ≤ t.depthOf x ∧ t'.depthOf x = t.depthOf x - 2 ∧
    t'.toList.Perm t.toList ∧
    (∀ u ∈ t'.pathTo x, u ∈ t.pathTo x) ∧
    (∀ rev : ℕ → Bool, (x ∈ t.toList → ∀ u ∈ t.pathTo x, rev u = false) →
      t'.evalInorder rev false = t.evalInorder rev false) ∧
    ∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
      t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
        t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize := by
  intro t'
  have hdep1 : t.depthOf p + 1 = t.depthOf x :=
    hp ▸ (parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).2.1
  have hdep2 : t.depthOf g + 1 = t.depthOf p :=
    hg ▸ (parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr).2.1
  have hsub_nd : (t.findSubtree g).toList.Nodup := findSubtree_nodup hnd
  have hcases := grandparent_child_cases hnd hx hxr hp hp_mem hpr hg
  have lift : ∀ {s' : AuxTree},
      s' ≠ .leaf → s'.rootId = x → s'.toList.Perm (t.findSubtree g).toList →
      t' = t.replaceSubtree g s' →
      (∀ vSize, s'.treeSize vSize = (t.findSubtree g).treeSize vSize ∧
        s'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
          (t.findSubtree g).treePhi vSize + 3 * s'.rank vSize) →
      2 ≤ t.depthOf x ∧ t'.depthOf x = t.depthOf x - 2 ∧
      t'.toList.Perm t.toList ∧
      (∀ u ∈ t'.pathTo x, u ∈ t.pathTo x) ∧
      (∀ rev : ℕ → Bool, (x ∈ t.toList → ∀ u ∈ t.pathTo x, rev u = false) →
        t'.evalInorder rev false = t.evalInorder rev false) ∧
      ∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
        t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
          t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize := by
    intro s' hs' hx_root hs_perm ht'_eq hstep
    have hdep_rep : t'.depthOf x = t.depthOf g := by
      rw [ht'_eq]; exact replaceSubtree_depthOf_root hnd hg_mem hs' hs_perm hx_root
    have hperm_t' : t'.toList.Perm t.toList := by
      rw [ht'_eq]; exact replaceSubtree_perm hnd hg_mem hs_perm
    have hpath_sub : ∀ u ∈ t'.pathTo x, u ∈ t.pathTo x := by
      dsimp only [t']
      by_cases hzz : t.isZigZig x p g = true
      · simp only [hzz, ↓reduceIte]
        intro u hu
        have hp_mem_px : p ∈ t.pathTo x := by
          rw [(parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).2.2, ← hp]
          simp [self_mem_pathTo hp_mem]
        exact rotateAt_pathTo_subset hnd hx hp_mem_px u
          (rotateAt_pathTo_subset ((rotateAt_toList_perm p t).nodup_iff.mpr hnd)
            ((rotateAt_toList_perm p t).mem_iff.mpr hx)
            (self_mem_pathTo ((rotateAt_toList_perm p t).mem_iff.mpr hx)) u hu)
      · rw [ite_eq_right hzz]
        intro u hu
        exact rotateAt_pathTo_subset hnd hx (self_mem_pathTo hx) u
          (rotateAt_pathTo_subset ((rotateAt_toList_perm x t).nodup_iff.mpr hnd)
            ((rotateAt_toList_perm x t).mem_iff.mpr hx)
            (self_mem_pathTo ((rotateAt_toList_perm x t).mem_iff.mpr hx)) u hu)
    have heval_eq : ∀ rev : ℕ → Bool, (x ∈ t.toList → ∀ u ∈ t.pathTo x, rev u = false) →
        t'.evalInorder rev false = t.evalInorder rev false := by
      intro rev hrev
      dsimp only [t']
      by_cases hzz : t.isZigZig x p g = true
      · simp only [hzz, ↓reduceIte]
        have hp_path : ∀ u ∈ t.pathTo p, rev u = false := fun u hu => by
          apply hrev hx
          rw [(parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).2.2, ← hp]
          simp [hu]
        have hrot_p := rotateAt_evalInorder rev hnd (fun _ => hp_path)
        have hnd_p : (t.rotateAt p).toList.Nodup := (rotateAt_toList_perm p t).nodup_iff.mpr hnd
        have hx_p : x ∈ (t.rotateAt p).toList := (rotateAt_toList_perm p t).mem_iff.mpr hx
        have hpath_xp : ∀ u ∈ (t.rotateAt p).pathTo x, rev u = false := fun u hu =>
          hrev hx u (rotateAt_pathTo_subset hnd hx (by
            rw [(parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).2.2, ← hp]
            simp [self_mem_pathTo hp_mem]) u hu)
        rw [rotateAt_evalInorder rev hnd_p (fun _ => hpath_xp), hrot_p]
      · rw [ite_eq_right hzz]
        have hnd_x : (t.rotateAt x).toList.Nodup := (rotateAt_toList_perm x t).nodup_iff.mpr hnd
        have hpath_xx : ∀ u ∈ (t.rotateAt x).pathTo x, rev u = false := fun u hu =>
          hrev hx u (rotateAt_pathTo_subset hnd hx (self_mem_pathTo hx) u hu)
        rw [rotateAt_evalInorder rev hnd_x (fun _ => hpath_xx), rotateAt_evalInorder rev hnd hrev]
    refine ⟨by omega, by omega, hperm_t', hpath_sub, heval_eq, fun vSize => ?_⟩
    rcases hstep vSize with ⟨hsz, hphi⟩
    have hfind_after : t'.findSubtree x = s' := by
      rw [ht'_eq, ← hx_root]
      exact findSubtree_replaceSubtree_root hnd hg_mem hs' hs_perm
    have hres := replaceSubtree_treeSize_add vSize hnd hg_mem hsz (by rw [← Nat.add_assoc]; exact hphi)
    rw [hfind_after, ht'_eq]
    exact ⟨hres.1, by omega⟩
  have h_replace_rot : ∀ (rSub y : ℕ) (t₀ : AuxTree),
      t₀.toList.Nodup → rSub ∈ t₀.toList → y ∈ (t₀.findSubtree rSub).toList → y ≠ rSub →
      t₀.rotateAt y = t₀.replaceSubtree rSub ((t₀.findSubtree rSub).rotateAt y) := by
    intro rSub y t₀ hnd₀ hr₀ hy₀ hne₀
    induction t₀ with
    | leaf => simp [toList] at hr₀
    | node id l r ihl ihr =>
        rcases nodup_node_unfold hnd₀ with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
        by_cases hid_r : id = rSub
        · subst hid_r; simp [findSubtree, replaceSubtree]
        · simp only [findSubtree, hid_r, ↓reduceIte] at hy₀ ⊢
          simp only [replaceSubtree, hid_r, ↓reduceIte]
          by_cases hrl : rSub ∈ l.toList
          · simp only [hrl, ↓reduceIte] at hy₀ ⊢
            have hy_l : y ∈ l.toList := findSubtree_subset hy₀
            have hyd : id ≠ y := fun h => hid_nl (h ▸ hy_l)
            have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
            have hlr_f : ¬ l.hasRoot y := fun h => by
              obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h
              by_cases hlr' : y = rSub
              · subst hlr'; exact hne₀ rfl
              · exact root_not_mem_findSubtree hl_nd hrl hy₀ hlr' rfl
            have hrr_f : ¬ r.hasRoot y := fun h => by
              obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h; exact hdisj_lr y hy_l (by simp [toList])
            simp only [rotateAt, hyd, hlr_f, hrr_f, hy_l, Bool.false_eq_true, ↓reduceIte]
            rw [ihl hl_nd hrl hy₀, replaceSubtree_not_mem hnr]
          · have hrr : rSub ∈ r.toList := by
              simp only [toList, List.mem_append, List.mem_singleton] at hr₀
              rcases hr₀ with (h | rfl) | h
              · exact absurd h hrl
              · exact absurd rfl hid_r
              · exact h
            simp only [hrl, ↓reduceIte] at hy₀ ⊢
            have hy_r : y ∈ r.toList := findSubtree_subset hy₀
            have hyd : id ≠ y := fun h => hid_nr (h ▸ hy_r)
            have hy_nl : y ∉ l.toList := fun h => hdisj_lr y h hy_r
            have hlr_f : ¬ l.hasRoot y := fun h => by
              obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hy_nl (by simp [toList])
            have hrr_f : ¬ r.hasRoot y := fun h => by
              obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h
              by_cases hrr' : y = rSub
              · subst hrr'; exact hne₀ rfl
              · exact root_not_mem_findSubtree hr_nd hrr hy₀ hrr' rfl
            simp only [rotateAt, hyd, hlr_f, hrr_f, hy_nl, Bool.false_eq_true, ↓reduceIte]
            rw [ihr hr_nd hrr hy₀, replaceSubtree_not_mem hrl]
  have h_rot_replace : ∀ (t₀ s' : AuxTree) (rSub y : ℕ),
      t₀.toList.Nodup → rSub ∈ t₀.toList → s' ≠ .leaf →
      s'.toList.Perm (t₀.findSubtree rSub).toList →
      y ∈ s'.toList → y ≠ s'.rootId →
      (t₀.replaceSubtree rSub s').rotateAt y = t₀.replaceSubtree rSub (s'.rotateAt y) := by
    intro t₀ s' rSub y hnd₀ hr₀ hs' hs_perm hy₀ hne₀
    induction t₀ with
    | leaf => simp [toList] at hr₀
    | node id l r ihl ihr =>
        rcases nodup_node_unfold hnd₀ with ⟨hl_nd, hid_nl, hr_nd, hid_nr, hdisj_lr⟩
        by_cases hid_r : id = rSub
        · subst hid_r; simp [replaceSubtree]
        · simp only [findSubtree, hid_r, ↓reduceIte] at hs_perm
          simp only [replaceSubtree, hid_r, ↓reduceIte]
          by_cases hrl : rSub ∈ l.toList
          · simp only [hrl, ↓reduceIte] at hs_perm
            have hy_l : y ∈ l.toList := findSubtree_subset (hs_perm.mem_iff.1 hy₀)
            have hyd : id ≠ y := fun h => hid_nl (h ▸ hy_l)
            have hnr : rSub ∉ r.toList := hdisj_lr rSub hrl
            have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
              replaceSubtree_perm hl_nd hrl hs_perm
            have hy_rep : y ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hy_l
            have hl_ne : l ≠ .leaf := fun h => by subst h; simp [toList] at hrl
            have hlr_f : ¬ (l.replaceSubtree rSub s').hasRoot y := fun h => by
              obtain ⟨A, B, hAB⟩ := hasRoot_iff.mp h
              have hroot : (l.replaceSubtree rSub s').rootId = y := by rw [hAB]; rfl
              rw [replaceSubtree_rootId hl_ne hs'] at hroot
              by_cases hl_r : l.rootId = rSub
              · simp only [hl_r, ↓reduceIte] at hroot; exact hne₀ hroot.symm
              · simp only [hl_r, ↓reduceIte] at hroot
                exact root_not_mem_findSubtree hl_nd hrl (hs_perm.mem_iff.1 hy₀) hl_r hroot
            have hrr_f : ¬ r.hasRoot y := fun h => by
              obtain ⟨C, D, rfl⟩ := hasRoot_iff.mp h; exact hdisj_lr y hy_l (by simp [toList])
            rw [replaceSubtree_not_mem hnr, replaceSubtree_not_mem hnr]
            simp only [rotateAt, hyd, hlr_f, hrr_f, hy_rep, Bool.false_eq_true, ↓reduceIte]
            rw [ihl hl_nd hrl hs_perm]
          · have hrr : rSub ∈ r.toList := by
              simp only [toList, List.mem_append, List.mem_singleton] at hr₀
              rcases hr₀ with (h | rfl) | h
              · exact absurd h hrl
              · exact absurd rfl hid_r
              · exact h
            simp only [hrl, ↓reduceIte] at hs_perm
            have hy_r : y ∈ r.toList := findSubtree_subset (hs_perm.mem_iff.1 hy₀)
            have hyd : id ≠ y := fun h => hid_nr (h ▸ hy_r)
            have hy_nl : y ∉ l.toList := fun h => hdisj_lr y h hy_r
            have hr_ne : r ≠ .leaf := fun h => by subst h; simp [toList] at hrr
            have hlr_f : ¬ l.hasRoot y := fun h => by
              obtain ⟨A, B, rfl⟩ := hasRoot_iff.mp h; exact hy_nl (by simp [toList])
            have hrr_f : ¬ (r.replaceSubtree rSub s').hasRoot y := fun h => by
              obtain ⟨C, D, hCD⟩ := hasRoot_iff.mp h
              have hroot : (r.replaceSubtree rSub s').rootId = y := by rw [hCD]; rfl
              rw [replaceSubtree_rootId hr_ne hs'] at hroot
              by_cases hr_r : r.rootId = rSub
              · simp only [hr_r, ↓reduceIte] at hroot; exact hne₀ hroot.symm
              · simp only [hr_r, ↓reduceIte] at hroot
                exact root_not_mem_findSubtree hr_nd hrr (hs_perm.mem_iff.1 hy₀) hr_r hroot
            rw [replaceSubtree_not_mem hrl, replaceSubtree_not_mem hrl]
            simp only [rotateAt, hyd, hlr_f, hrr_f, hy_nl, Bool.false_eq_true, ↓reduceIte]
            rw [ihr hr_nd hrr hs_perm]
  rcases hcases with ⟨A, B, C, D, hg_eq⟩ | ⟨A, B, C, D, hg_eq⟩ |
      ⟨A, B, C, D, hg_eq⟩ | ⟨A, B, C, D, hg_eq⟩
  · have hzz : t.isZigZig x p g = true := by simp [isZigZig, hg_eq]
    rw [hg_eq] at hsub_nd
    rcases nodup_node_unfold hsub_nd with ⟨hp_nd, hg_np, _, _, _⟩
    rcases nodup_node_unfold hp_nd with ⟨_, hp_nx, _, _, _⟩
    have hgp : g ≠ p := fun h => hg_np (h ▸ by simp [toList])
    have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [toList])
    have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [toList])
    let s' := AuxTree.node x A (.node p B (.node g C D))
    have hrot_s : ((t.findSubtree g).rotateAt p).rotateAt x = s' := by
      rw [hg_eq, rotateAt_zigRight (.node x A B) C D hgp, rotateAt_zigRight A B (.node g C D) hpx]
    have hperm_s : s'.toList.Perm (t.findSubtree g).toList := by
      rw [← hrot_s]
      exact (rotateAt_toList_perm x _).trans (rotateAt_toList_perm p _)
    have ht'_eq : t' = t.replaceSubtree g s' := by
      dsimp only [t']; rw [hzz]; simp only [↓reduceIte]
      have hp_in_g : p ∈ (t.findSubtree g).toList := by rw [hg_eq]; simp [toList]
      rw [h_replace_rot g p t hnd hg_mem hp_in_g hgp.symm]
      have hs1_ne : (t.findSubtree g).rotateAt p ≠ .leaf :=
        rotateAt_ne_leaf (by rw [hg_eq]; simp)
      have hs1_perm : ((t.findSubtree g).rotateAt p).toList.Perm (t.findSubtree g).toList :=
        rotateAt_toList_perm p _
      have hx_s1 : x ∈ ((t.findSubtree g).rotateAt p).toList :=
        hs1_perm.mem_iff.mpr (by rw [hg_eq]; simp [toList])
      have hx_ne_root : x ≠ ((t.findSubtree g).rotateAt p).rootId := by
        rw [hg_eq, rotateAt_zigRight (.node x A B) C D hgp]; simp [rootId, hpx.symm]
      rw [h_rot_replace t _ g x hnd hg_mem hs1_ne hs1_perm hx_s1 hx_ne_root, hrot_s]
    refine lift (by simp [s']) rfl hperm_s ht'_eq fun vSize => ?_
    have hfind_x : t.findSubtree x = .node x A B := by
      rw [← findSubtree_findSubtree hnd hg_mem (by rw [hg_eq]; simp [toList]), hg_eq]
      simp [findSubtree, hgx, hpx, toList]
    have hsz : s'.treeSize vSize = (t.findSubtree g).treeSize vSize := by
      rw [← hrot_s, rotateAt_treeSize, rotateAt_treeSize]
    have hphi := zigZig_right_phi_le vSize x p g A B C D
    rw [← hg_eq] at hphi
    rw [hfind_x]
    exact ⟨hsz, hphi⟩
  · rw [hg_eq] at hsub_nd
    rcases nodup_node_unfold hsub_nd with ⟨hp_nd, hg_np, _, hg_nD, hdisj_g⟩
    rcases nodup_node_unfold hp_nd with ⟨_, hp_nA, _, hp_nx, hdisj_p⟩
    have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [toList])
    have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [toList])
    have hx_nA : x ∉ A.toList := fun h => hdisj_p x h (by simp [toList])
    have hp_nD : p ∉ D.toList := fun h => hdisj_g p (by simp [toList]) h
    have hzz : t.isZigZig x p g = false := by
      simp only [isZigZig, hg_eq, Bool.or_eq_false_iff]
      constructor
      · cases A with
        | leaf => rfl
        | node ax _ _ =>
            have hax : ax ≠ x := fun h => hx_nA (by subst h; simp [toList])
            simp [hax]
      · cases D with
        | leaf => rfl
        | node dp _ r' =>
            cases r' with
            | leaf => rfl
            | node _ _ _ =>
                have hdp : dp ≠ p := fun h => hp_nD (by subst h; simp [toList])
                simp [hdp]
    have hA_nx : ¬ A.hasRoot x := fun h => by
      obtain ⟨_, _, rfl⟩ := hasRoot_iff.mp h; exact hx_nA (by simp [toList])
    have hp_nx' : ¬ (AuxTree.node p A (.node x B C)).hasRoot x := by simp [hasRoot, hpx]
    have hD_nx : ¬ D.hasRoot x := fun h => by
      obtain ⟨_, _, rfl⟩ := hasRoot_iff.mp h
      exact hdisj_g x (by simp [toList]) (by simp [toList])
    let s' := AuxTree.node x (.node p A B) (.node g C D)
    have hrot_s : ((t.findSubtree g).rotateAt x).rotateAt x = s' := by
      rw [hg_eq]
      have hr1 : (AuxTree.node g (.node p A (.node x B C)) D).rotateAt x =
          AuxTree.node g ((AuxTree.node p A (.node x B C)).rotateAt x) D := by
        simp [rotateAt, hgx, hp_nx', hD_nx, toList]
      rw [hr1, rotateAt_zigLeft A B C hpx hA_nx, rotateAt_zigRight (.node p A B) C D hgx]
    have hperm_s : s'.toList.Perm (t.findSubtree g).toList := by
      rw [← hrot_s]
      exact (rotateAt_toList_perm x _).trans (rotateAt_toList_perm x _)
    have ht'_eq : t' = t.replaceSubtree g s' := by
      dsimp only [t']; rw [hzz]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hx_in_g : x ∈ (t.findSubtree g).toList := by rw [hg_eq]; simp [toList]
      rw [h_replace_rot g x t hnd hg_mem hx_in_g hgx.symm]
      have hs1_ne : (t.findSubtree g).rotateAt x ≠ .leaf :=
        rotateAt_ne_leaf (by rw [hg_eq]; simp)
      have hs1_perm : ((t.findSubtree g).rotateAt x).toList.Perm (t.findSubtree g).toList :=
        rotateAt_toList_perm x _
      have hx_s1 : x ∈ ((t.findSubtree g).rotateAt x).toList := hs1_perm.mem_iff.mpr hx_in_g
      have hx_ne_root : x ≠ ((t.findSubtree g).rotateAt x).rootId := by
        rw [hg_eq]; simp only [rotateAt, hgx, ↓reduceIte, hp_nx', hD_nx]
        simp [toList, rootId, hgx.symm]
      rw [h_rot_replace t _ g x hnd hg_mem hs1_ne hs1_perm hx_s1 hx_ne_root, hrot_s]
    refine lift (by simp [s']) rfl hperm_s ht'_eq fun vSize => ?_
    have hfind_x : t.findSubtree x = .node x B C := by
      rw [← findSubtree_findSubtree hnd hg_mem (by rw [hg_eq]; simp [toList]), hg_eq]
      simp [findSubtree, hgx, hpx, hx_nA, toList]
    have hsz : s'.treeSize vSize = (t.findSubtree g).treeSize vSize := by
      rw [← hrot_s, rotateAt_treeSize, rotateAt_treeSize]
    have hphi := zigZag_lr_phi_le vSize p x g A B C D
    rw [← hg_eq] at hphi
    rw [hfind_x]
    exact ⟨hsz, hphi⟩
  · rw [hg_eq] at hsub_nd
    rcases nodup_node_unfold hsub_nd with ⟨_, hg_nA, hp_nd, hg_np, hdisj_g⟩
    rcases nodup_node_unfold hp_nd with ⟨_, hp_nx, _, hp_nD, hdisj_p⟩
    have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [toList])
    have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [toList])
    have hp_nA : p ∉ A.toList := fun h => hdisj_g p h (by simp [toList])
    have hx_nA : x ∉ A.toList := fun h => hdisj_g x h (by simp [toList])
    have hx_nD : x ∉ D.toList := fun h => hdisj_p x (by simp [toList]) h
    have hzz : t.isZigZig x p g = false := by
      simp only [isZigZig, hg_eq, Bool.or_eq_false_iff]
      constructor
      · cases A with
        | leaf => rfl
        | node ap l' _ =>
            cases l' with
            | leaf => rfl
            | node _ _ _ =>
                have hap : ap ≠ p := fun h => hp_nA (by subst h; simp [toList])
                simp [hap]
      · cases D with
        | leaf => rfl
        | node dx _ _ =>
            have hdx : dx ≠ x := fun h => hx_nD (by subst h; simp [toList])
            simp [hdx]
    have hA_nx : ¬ A.hasRoot x := fun h => by
      obtain ⟨_, _, rfl⟩ := hasRoot_iff.mp h; exact hx_nA (by simp [toList])
    have hp_nx' : ¬ (AuxTree.node p (.node x B C) D).hasRoot x := by simp [hasRoot, hpx]
    let s' := AuxTree.node x (.node g A B) (.node p C D)
    have hrot_s : ((t.findSubtree g).rotateAt x).rotateAt x = s' := by
      rw [hg_eq]
      have hr1 : (AuxTree.node g A (.node p (.node x B C) D)).rotateAt x =
          AuxTree.node g A ((AuxTree.node p (.node x B C) D).rotateAt x) := by
        simp [rotateAt, hgx, hA_nx, hp_nx', hx_nA]
      rw [hr1, rotateAt_zigRight B C D hpx, rotateAt_zigLeft A B (.node p C D) hgx hA_nx]
    have hperm_s : s'.toList.Perm (t.findSubtree g).toList := by
      rw [← hrot_s]
      exact (rotateAt_toList_perm x _).trans (rotateAt_toList_perm x _)
    have ht'_eq : t' = t.replaceSubtree g s' := by
      dsimp only [t']; rw [hzz]; simp only [Bool.false_eq_true, ↓reduceIte]
      have hx_in_g : x ∈ (t.findSubtree g).toList := by rw [hg_eq]; simp [toList]
      rw [h_replace_rot g x t hnd hg_mem hx_in_g hgx.symm]
      have hs1_ne : (t.findSubtree g).rotateAt x ≠ .leaf :=
        rotateAt_ne_leaf (by rw [hg_eq]; simp)
      have hs1_perm : ((t.findSubtree g).rotateAt x).toList.Perm (t.findSubtree g).toList :=
        rotateAt_toList_perm x _
      have hx_s1 : x ∈ ((t.findSubtree g).rotateAt x).toList := hs1_perm.mem_iff.mpr hx_in_g
      have hx_ne_root : x ≠ ((t.findSubtree g).rotateAt x).rootId := by
        rw [hg_eq]; simp only [rotateAt, hgx, ↓reduceIte, hA_nx, hp_nx', hx_nA]
        simp [rootId, hgx.symm]
      rw [h_rot_replace t _ g x hnd hg_mem hs1_ne hs1_perm hx_s1 hx_ne_root, hrot_s]
    refine lift (by simp [s']) rfl hperm_s ht'_eq fun vSize => ?_
    have hfind_x : t.findSubtree x = .node x B C := by
      rw [← findSubtree_findSubtree hnd hg_mem (by rw [hg_eq]; simp [toList]), hg_eq]
      simp [findSubtree, hgx, hpx, hx_nA, toList]
    have hsz : s'.treeSize vSize = (t.findSubtree g).treeSize vSize := by
      rw [← hrot_s, rotateAt_treeSize, rotateAt_treeSize]
    have hphi := zigZag_rl_phi_le vSize g x p A B C D
    rw [← hg_eq] at hphi
    rw [hfind_x]
    exact ⟨hsz, hphi⟩
  · have hzz : t.isZigZig x p g = true := by simp [isZigZig, hg_eq]
    rw [hg_eq] at hsub_nd
    rcases nodup_node_unfold hsub_nd with ⟨_, hg_nA, hp_nd, hg_np, hdisj_g⟩
    rcases nodup_node_unfold hp_nd with ⟨_, hp_nB, _, hp_nx, hdisj_p⟩
    have hgp : g ≠ p := fun h => hg_np (h ▸ by simp [toList])
    have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [toList])
    have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [toList])
    have hp_nA : p ∉ A.toList := fun h => hdisj_g p h (by simp [toList])
    have hA_np : ¬ A.hasRoot p := fun h => by
      obtain ⟨_, _, rfl⟩ := hasRoot_iff.mp h; exact hp_nA (by simp [toList])
    have hx_nA : x ∉ A.toList := fun h => hdisj_g x h (by simp [toList])
    have hx_nB : x ∉ B.toList := fun h => hdisj_p x h (by simp [toList])
    have hgAB_nx : ¬ (AuxTree.node g A B).hasRoot x := fun h => by
      obtain ⟨_, _, h_eq⟩ := hasRoot_iff.mp h
      injection h_eq with hgx_eq; exact hgx hgx_eq
    let s' := AuxTree.node x (.node p (.node g A B) C) D
    have hrot_s : ((t.findSubtree g).rotateAt p).rotateAt x = s' := by
      rw [hg_eq, rotateAt_zigLeft A B (.node x C D) hgp hA_np,
          rotateAt_zigLeft (.node g A B) C D hpx hgAB_nx]
    have hperm_s : s'.toList.Perm (t.findSubtree g).toList := by
      rw [← hrot_s]
      exact (rotateAt_toList_perm x _).trans (rotateAt_toList_perm p _)
    have ht'_eq : t' = t.replaceSubtree g s' := by
      dsimp only [t']; rw [hzz]; simp only [↓reduceIte]
      have hp_in_g : p ∈ (t.findSubtree g).toList := by rw [hg_eq]; simp [toList]
      rw [h_replace_rot g p t hnd hg_mem hp_in_g hgp.symm]
      have hs1_ne : (t.findSubtree g).rotateAt p ≠ .leaf :=
        rotateAt_ne_leaf (by rw [hg_eq]; simp)
      have hs1_perm : ((t.findSubtree g).rotateAt p).toList.Perm (t.findSubtree g).toList :=
        rotateAt_toList_perm p _
      have hx_s1 : x ∈ ((t.findSubtree g).rotateAt p).toList :=
        hs1_perm.mem_iff.mpr (by rw [hg_eq]; simp [toList])
      have hx_ne_root : x ≠ ((t.findSubtree g).rotateAt p).rootId := by
        rw [hg_eq, rotateAt_zigLeft A B (.node x C D) hgp hA_np]; simp [rootId, hpx.symm]
      rw [h_rot_replace t _ g x hnd hg_mem hs1_ne hs1_perm hx_s1 hx_ne_root, hrot_s]
    refine lift (by simp [s']) rfl hperm_s ht'_eq fun vSize => ?_
    have hfind_x : t.findSubtree x = .node x C D := by
      rw [← findSubtree_findSubtree hnd hg_mem (by rw [hg_eq]; simp [toList]), hg_eq]
      simp [findSubtree, hgx, hpx, hx_nA, hx_nB]
    have hsz : s'.treeSize vSize = (t.findSubtree g).treeSize vSize := by
      rw [← hrot_s, rotateAt_treeSize, rotateAt_treeSize]
    have hphi := zigZig_left_phi_le vSize g p x A B C D
    rw [← hg_eq] at hphi
    rw [hfind_x]
    exact ⟨hsz, hphi⟩
