module

public import MinCostFlow.LinkCut.Prog.SplayStepPushPath

/-!
Pure binary auxiliary-tree rotation `AuxTree.rotateAt` and its structural invariants:
`toList` permutation, `Nodup`, `treeSize`, `evalInorder`, `depthOf_self`, and
`rotateAt_pathTo_subset`.
-/

namespace MinCostFlow.LinkCut.Prog

@[expose] public section

/-- Algebraic single rotation moving `x` one step toward the root (if `x` is a non-root node).
Children are matched by constructor so leaf sentinels (`rootId = 0`) never falsely match `x = 0`. -/
def AuxTree.rotateAt (x : ℕ) : AuxTree → AuxTree
  | .leaf => .leaf
  | .node p l r =>
      if p = x then .node p l r
      else
        match l with
        | .node lx A B =>
            if lx = x then .node lx A (.node p B r)
            else
              match r with
              | .node rx C D =>
                  if rx = x then .node rx (.node p (.node lx A B) C) D
                  else if x ∈ l.toList then .node p ((AuxTree.node lx A B).rotateAt x) r
                  else .node p (.node lx A B) ((AuxTree.node rx C D).rotateAt x)
              | .leaf => .node p ((AuxTree.node lx A B).rotateAt x) .leaf
        | .leaf =>
            match r with
            | .node rx C D =>
                if rx = x then .node rx (.node p .leaf C) D
                else .node p .leaf ((AuxTree.node rx C D).rotateAt x)
            | .leaf => .node p .leaf .leaf

@[simp] theorem AuxTree.rotateAt_leaf (x : ℕ) : AuxTree.leaf.rotateAt x = .leaf := rfl

@[simp] theorem AuxTree.rotateAt_root (p : ℕ) (l r : AuxTree) :
    (AuxTree.node p l r).rotateAt p = .node p l r := by
  cases l <;> cases r <;> simp [rotateAt]

theorem AuxTree.rotateAt_zigRight {x p : ℕ} (A B C : AuxTree) (hne : p ≠ x) :
    (AuxTree.node p (.node x A B) C).rotateAt x = .node x A (.node p B C) := by
  cases C <;> simp [rotateAt, hne]

theorem AuxTree.rotateAt_zigLeft {x p : ℕ} (l C D : AuxTree) (hne : p ≠ x)
    (hl : l = .leaf ∨ l.rootId ≠ x) :
    (AuxTree.node p l (.node x C D)).rotateAt x = .node x (.node p l C) D := by
  cases l with
  | leaf => simp [rotateAt, hne]
  | node lx A B =>
      have hlx : lx ≠ x := by
        rcases hl with h | h
        · cases h
        · simpa [rootId] using h
      simp [rotateAt, hne, hlx]

theorem AuxTree.rotateAt_not_mem {x : ℕ} {t : AuxTree} (hx : x ∉ t.toList) :
    t.rotateAt x = t := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      have hne : p ≠ x := fun h => hx (by subst h; simp [toList])
      have hnl : x ∉ l.toList := fun h => hx (by simp [toList, h])
      have hnr : x ∉ r.toList := fun h => hx (by simp [toList, h])
      have ihl' := ihl hnl
      have ihr' := ihr hnr
      cases l with
      | leaf =>
          cases r with
          | leaf => simp [rotateAt, hne]
          | node rx C D =>
              have hrx : rx ≠ x := fun h => hnr (by subst h; simp [toList])
              simp only [rotateAt, hne, ↓reduceIte, hrx]
              exact congrArg (AuxTree.node p .leaf) ihr'
      | node lx A B =>
          have hlx : lx ≠ x := fun h => hnl (by subst h; simp [toList])
          cases r with
          | leaf =>
              simp only [rotateAt, hne, ↓reduceIte, hlx]
              exact congrArg (fun u => AuxTree.node p u .leaf) ihl'
          | node rx C D =>
              have hrx : rx ≠ x := fun h => hnr (by subst h; simp [toList])
              simp only [rotateAt, hne, ↓reduceIte, hlx, hrx, hnl]
              exact congrArg (AuxTree.node p (AuxTree.node lx A B)) ihr'

theorem AuxTree.rotateAt_ne_leaf {x : ℕ} {t : AuxTree} (ht : t ≠ .leaf) :
    t.rotateAt x ≠ .leaf := by
  cases t with
  | leaf => exact absurd rfl ht
  | node p l r =>
      by_cases hne : p = x
      · subst hne; simp
      · cases l <;> cases r <;> simp [rotateAt, hne] <;> split_ifs <;> simp

theorem AuxTree.rotateAt_toList_perm (x : ℕ) (t : AuxTree) :
    (t.rotateAt x).toList.Perm t.toList := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      by_cases hne : p = x
      · subst hne; simp
      · cases l with
        | leaf =>
            cases r with
            | leaf => simp [rotateAt, hne]
            | node rx C D =>
                by_cases hrx : rx = x
                · simp only [rotateAt, hne, ↓reduceIte, hrx, toList]
                  simp [List.append_assoc]
                · simp only [rotateAt, hne, ↓reduceIte, hrx, toList]
                  exact ihr.append_left [p]
        | node lx A B =>
            by_cases hlx : lx = x
            · subst hlx
              rw [AuxTree.rotateAt_zigRight A B r hne]
              simp [toList, List.append_assoc]
            · cases r with
              | leaf =>
                  simp only [rotateAt, hne, ↓reduceIte, hlx, toList]
                  exact (ihl.append_right [p]).append_right []
              | node rx C D =>
                  by_cases hrx : rx = x
                  · simp only [rotateAt, hne, ↓reduceIte, hlx, hrx, toList, List.append_assoc]
                    rfl
                  · by_cases hmem : x ∈ (AuxTree.node lx A B).toList
                    · simp only [rotateAt, hne, ↓reduceIte, hlx, hrx, hmem, ↓reduceIte]
                      simp only [toList]
                      exact (ihl.append_right [p]).append_right (AuxTree.node rx C D).toList
                    · simp only [rotateAt, hne, ↓reduceIte, hlx, hrx, hmem, ↓reduceIte]
                      simp only [toList]
                      exact ihr.append_left ((AuxTree.node lx A B).toList ++ [p])

theorem AuxTree.rotateAt_nodup {x : ℕ} {t : AuxTree} (hnd : t.toList.Nodup) :
    (t.rotateAt x).toList.Nodup :=
  (AuxTree.rotateAt_toList_perm x t).nodup_iff.2 hnd

theorem AuxTree.rotateAt_treeSize (vSize : ℕ → ℕ) (x : ℕ) (t : AuxTree) :
    (t.rotateAt x).treeSize vSize = t.treeSize vSize := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      by_cases hne : p = x
      · subst hne; simp
      · cases l with
        | leaf =>
            cases r with
            | leaf => simp [rotateAt, hne]
            | node rx C D =>
                by_cases hrx : rx = x
                · simp [rotateAt, hne, hrx, treeSize]; omega
                · simp [rotateAt, hne, hrx, treeSize] at ihr ⊢; exact ihr
        | node lx A B =>
            by_cases hlx : lx = x
            · subst hlx
              rw [AuxTree.rotateAt_zigRight A B r hne]
              simp [treeSize]; omega
            · cases r with
              | leaf =>
                  simp [rotateAt, hne, hlx, treeSize] at ihl ⊢; exact ihl
              | node rx C D =>
                  by_cases hrx : rx = x
                  · simp [rotateAt, hne, hlx, hrx, treeSize]; omega
                  · by_cases hmem : x ∈ (AuxTree.node lx A B).toList
                    · simp [rotateAt, hne, hlx, hrx, hmem, treeSize] at ihl ⊢; exact ihl
                    · simp [rotateAt, hne, hlx, hrx, hmem, treeSize] at ihr ⊢; exact ihr

theorem AuxTree.rotateAt_evalInorder {x : ℕ} {t : AuxTree} (rev : ℕ → Bool)
    (hnd : t.toList.Nodup) (hrev : x ∈ t.toList → ∀ u ∈ t.pathTo x, rev u = false) :
    (t.rotateAt x).evalInorder rev false = t.evalInorder rev false := by
  induction t with
  | leaf => rfl
  | node p l r ihl ihr =>
      by_cases hx_mem : x ∈ (AuxTree.node p l r).toList
      swap
      · rw [AuxTree.rotateAt_not_mem hx_mem]
      have hpath := hrev hx_mem
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, _⟩, hr_nd, _⟩
      by_cases hpx : p = x
      · subst hpx; simp
      · have hrev_p : rev p = false := by
          apply hpath p
          rw [AuxTree.pathTo]
          by_cases hnl : x ∈ l.toList
          · simp [Ne.symm hpx, hnl]
          · have hnr : x ∈ r.toList := by
              simp only [toList, List.mem_append, List.mem_singleton] at hx_mem
              rcases hx_mem with (h | rfl) | h
              · exact absurd h hnl
              · exact absurd rfl hpx
              · exact h
            simp [Ne.symm hpx, hnl, hnr]
        cases l with
        | leaf =>
            cases r with
            | leaf => simp [rotateAt, hpx]
            | node rx C D =>
                by_cases hrx : rx = x
                · have hrev_x : rev x = false := by
                    subst hrx
                    exact hpath rx (AuxTree.self_mem_pathTo hx_mem)
                  simp only [rotateAt, hpx, ↓reduceIte, hrx]
                  subst hrx
                  simp [evalInorder, hrev_p, hrev_x, List.append_assoc]
                · have hxr : x ∈ (AuxTree.node rx C D).toList := by
                    simp only [toList, List.mem_nil_iff, false_or, List.mem_append,
                      List.mem_singleton] at hx_mem ⊢
                    rcases hx_mem with rfl | h
                    · exact absurd rfl hpx
                    · exact h
                  have hpath_r : ∀ u ∈ (AuxTree.node rx C D).pathTo x, rev u = false := fun u hu => by
                    apply hpath u
                    rw [AuxTree.pathTo]
                    have hnin_leaf : x ∉ AuxTree.leaf.toList := by simp [toList]
                    simp [Ne.symm hpx, hnin_leaf, hxr, hu]
                  have ihr' := ihr hr_nd (fun _ => hpath_r)
                  simp only [rotateAt, hpx, ↓reduceIte, hrx]
                  simp [evalInorder, hrev_p, ihr']
        | node lx A B =>
            by_cases hlx : lx = x
            · have hrev_x : rev x = false := by
                subst hlx
                apply hpath lx
                simp [pathTo, Ne.symm hpx, toList]
              subst hlx
              rw [AuxTree.rotateAt_zigRight A B r hpx]
              simp [evalInorder, hrev_p, hrev_x, List.append_assoc]
            · cases r with
              | leaf =>
                  have hxl : x ∈ (AuxTree.node lx A B).toList := by
                    simp only [toList, List.mem_append, List.mem_singleton, List.mem_nil_iff,
                      or_false] at hx_mem ⊢
                    rcases hx_mem with h | rfl
                    · exact h
                    · exact absurd rfl hpx
                  have hpath_l : ∀ u ∈ (AuxTree.node lx A B).pathTo x, rev u = false := fun u hu => by
                    apply hpath u
                    rw [AuxTree.pathTo]
                    simp [Ne.symm hpx, hxl, hu]
                  have ihl' := ihl hl_nd (fun _ => hpath_l)
                  simp only [rotateAt, hpx, ↓reduceIte, hlx]
                  simp [evalInorder, hrev_p, ihl']
              | node rx C D =>
                  by_cases hrx : rx = x
                  · have hrev_x : rev x = false := by
                      subst hrx
                      exact hpath rx (AuxTree.self_mem_pathTo hx_mem)
                    simp only [rotateAt, hpx, ↓reduceIte, hlx, hrx]
                    subst hrx
                    simp [evalInorder, hrev_p, hrev_x, List.append_assoc]
                  · by_cases hxl : x ∈ (AuxTree.node lx A B).toList
                    · have hpath_l : ∀ u ∈ (AuxTree.node lx A B).pathTo x, rev u = false :=
                        fun u hu => hpath u (by rw [AuxTree.pathTo]; simp [Ne.symm hpx, hxl, hu])
                      have ihl' := ihl hl_nd (fun _ => hpath_l)
                      simp only [rotateAt, hpx, ↓reduceIte, hlx, hrx, hxl]
                      simp [evalInorder, hrev_p, ihl']
                    · have hxr : x ∈ (AuxTree.node rx C D).toList := by
                        simp only [toList, List.mem_append, List.mem_singleton] at hx_mem hxl ⊢
                        rcases hx_mem with (h | rfl) | h
                        · exact absurd h hxl
                        · exact absurd rfl hpx
                        · exact h
                      have hpath_r : ∀ u ∈ (AuxTree.node rx C D).pathTo x, rev u = false :=
                        fun u hu => hpath u (by rw [AuxTree.pathTo]; simp [Ne.symm hpx, hxl, hxr, hu])
                      have ihr' := ihr hr_nd (fun _ => hpath_r)
                      simp only [rotateAt, hpx, ↓reduceIte, hlx, hrx, hxl]
                      simp [evalInorder, hrev_p, ihr']

private theorem depthOf_root (id : ℕ) (l r : AuxTree) :
    (AuxTree.node id l r).depthOf id = 0 := by
  rw [AuxTree.depthOf]; simp

private theorem depthOf_pos_of_mem_ne_root {id x : ℕ} {l r : AuxTree}
    (hx : x ∈ (AuxTree.node id l r).toList) (hne : id ≠ x) :
    1 ≤ (AuxTree.node id l r).depthOf x := by
  rw [AuxTree.depthOf]
  simp only [Ne.symm hne, ↓reduceIte]
  by_cases hxl : x ∈ l.toList
  · simp [hxl]
  · have hxr : x ∈ r.toList := by
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hx
      rcases hx with (h | rfl) | h
      · exact absurd h hxl
      · exact absurd rfl hne
      · exact h
    simp [hxl, hxr]

theorem AuxTree.rotateAt_depthOf_self {x : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) :
    (t.rotateAt x).depthOf x = t.depthOf x - 1 := by
  induction t with
  | leaf => simp [toList] at hx
  | node p l r ihl ihr =>
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, _⟩, hr_nd, hdisj_lr⟩
      have hdisj_lr' : ∀ u ∈ l.toList, u ∉ r.toList := fun u hu hr => hdisj_lr u (Or.inl hu) u hr rfl
      by_cases hpx : p = x
      · subst hpx; simp [depthOf_root]
      · cases l with
        | leaf =>
            cases r with
            | leaf =>
                simp only [toList, List.mem_nil_iff, List.mem_append, List.mem_singleton] at hx
                rcases hx with (h | rfl) | h <;> [cases h; exact absurd rfl hpx; cases h]
            | node rx C D =>
                have hxr : x ∈ (AuxTree.node rx C D).toList := by
                  simp only [toList, List.mem_nil_iff, false_or, List.mem_append,
                    List.mem_singleton] at hx ⊢
                  rcases hx with rfl | h
                  · exact absurd rfl hpx
                  · exact h
                by_cases hrx : rx = x
                · subst hrx
                  simp only [rotateAt, hpx, ↓reduceIte]
                  rw [depthOf_root]
                  conv_rhs => rw [AuxTree.depthOf]
                  have hnin_leaf : rx ∉ AuxTree.leaf.toList := by simp [toList]
                  simp [Ne.symm hpx, hnin_leaf, hxr, depthOf_root]
                · have ih := ihr hr_nd hxr
                  have hx_not_leaf : x ∉ AuxTree.leaf.toList := by simp [toList]
                  have hdep_r : 1 ≤ (AuxTree.node rx C D).depthOf x :=
                    depthOf_pos_of_mem_ne_root hxr hrx
                  simp only [rotateAt, hpx, ↓reduceIte, hrx]
                  conv_lhs => rw [AuxTree.depthOf]
                  conv_rhs => rw [AuxTree.depthOf]
                  have hr_perm : ((AuxTree.node rx C D).rotateAt x).toList.Perm
                      (AuxTree.node rx C D).toList := rotateAt_toList_perm x _
                  simp only [Ne.symm hpx, hx_not_leaf, hr_perm.mem_iff, hxr, ↓reduceIte]
                  rw [ih]; omega
        | node lx A B =>
            by_cases hlx : lx = x
            · subst hlx
              rw [AuxTree.rotateAt_zigRight A B r hpx]
              rw [depthOf_root]
              conv_rhs => rw [AuxTree.depthOf]
              simp [Ne.symm hpx, toList, depthOf_root]
            · cases r with
              | leaf =>
                  have hxl : x ∈ (AuxTree.node lx A B).toList := by
                    simp only [toList, List.mem_append, List.mem_singleton, List.mem_nil_iff,
                      or_false] at hx ⊢
                    rcases hx with h | rfl
                    · exact h
                    · exact absurd rfl hpx
                  have ih := ihl hl_nd hxl
                  have hl_perm : ((AuxTree.node lx A B).rotateAt x).toList.Perm
                      (AuxTree.node lx A B).toList := rotateAt_toList_perm x _
                  have hdep_l : 1 ≤ (AuxTree.node lx A B).depthOf x :=
                    depthOf_pos_of_mem_ne_root hxl hlx
                  simp only [rotateAt, hpx, ↓reduceIte, hlx]
                  conv_lhs => rw [AuxTree.depthOf]
                  conv_rhs => rw [AuxTree.depthOf]
                  simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte]
                  rw [ih]; omega
              | node rx C D =>
                  by_cases hrx : rx = x
                  · subst hrx
                    have hnin_l : rx ∉ (AuxTree.node lx A B).toList := fun hl =>
                      hdisj_lr' rx hl (by simp [toList])
                    simp only [rotateAt, hpx, ↓reduceIte, hlx]
                    rw [depthOf_root]
                    conv_rhs => rw [AuxTree.depthOf]
                    have hrx_in : rx ∈ (AuxTree.node rx C D).toList := by simp [toList]
                    simp [Ne.symm hpx, hnin_l, hrx_in, depthOf_root]
                  · by_cases hxl : x ∈ (AuxTree.node lx A B).toList
                    · have ih := ihl hl_nd hxl
                      have hl_perm : ((AuxTree.node lx A B).rotateAt x).toList.Perm
                          (AuxTree.node lx A B).toList := rotateAt_toList_perm x _
                      have hdep_l : 1 ≤ (AuxTree.node lx A B).depthOf x :=
                        depthOf_pos_of_mem_ne_root hxl hlx
                      simp only [rotateAt, hpx, ↓reduceIte, hlx, hrx, hxl]
                      conv_lhs => rw [AuxTree.depthOf]
                      conv_rhs => rw [AuxTree.depthOf]
                      simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte]
                      rw [ih]; omega
                    · have hxr : x ∈ (AuxTree.node rx C D).toList := by
                        simp only [toList, List.mem_append, List.mem_singleton] at hx hxl ⊢
                        rcases hx with (h | rfl) | h
                        · exact absurd h hxl
                        · exact absurd rfl hpx
                        · exact h
                      have ih := ihr hr_nd hxr
                      have hdep_r : 1 ≤ (AuxTree.node rx C D).depthOf x :=
                        depthOf_pos_of_mem_ne_root hxr hrx
                      have hr_perm : ((AuxTree.node rx C D).rotateAt x).toList.Perm
                          (AuxTree.node rx C D).toList := rotateAt_toList_perm x _
                      simp only [rotateAt, hpx, ↓reduceIte, hlx, hrx, hxl]
                      conv_lhs => rw [AuxTree.depthOf]
                      conv_rhs => rw [AuxTree.depthOf]
                      simp only [Ne.symm hpx, hxl, hr_perm.mem_iff, hxr, ↓reduceIte]
                      rw [ih]; omega

theorem AuxTree.rotateAt_pathTo_subset {x y : ℕ} {t : AuxTree}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hy : y ∈ t.pathTo x) :
    ∀ u ∈ (t.rotateAt y).pathTo x, u ∈ t.pathTo x := by
  induction t with
  | leaf => simp [toList] at hx
  | node p l r ihl ihr =>
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, _⟩, hr_nd, hdisj_lr⟩
      have hdisj_lr' : ∀ u ∈ l.toList, u ∉ r.toList := fun u hu hr => hdisj_lr u (Or.inl hu) u hr rfl
      by_cases hpx : p = x
      · subst hpx
        simp only [pathTo, ↓reduceIte, List.mem_singleton] at hy
        subst hy
        simp
      · by_cases hpy : p = y
        · subst hpy
          simp
        · cases l with
          | leaf =>
              have hxr : x ∈ r.toList := by
                simp only [toList, List.mem_nil_iff, false_or, List.mem_append,
                  List.mem_singleton] at hx
                rcases hx with rfl | h
                · exact absurd rfl hpx
                · exact h
              cases r with
              | leaf => simp [toList] at hxr
              | node rx C D =>
                  by_cases hrx : rx = y
                  · subst hrx
                    intro u hu
                    simp only [rotateAt, hpy, ↓reduceIte] at hu
                    have hnin_leaf : x ∉ AuxTree.leaf.toList := by simp [toList]
                    rw [AuxTree.pathTo]; simp only [Ne.symm hpx, hnin_leaf, hxr, ↓reduceIte]
                    by_cases hxu : x = rx
                    · subst hxu
                      rw [AuxTree.pathTo] at hu
                      simp only [↓reduceIte, List.mem_singleton] at hu
                      subst hu; rw [AuxTree.pathTo]; simp
                    · rw [AuxTree.pathTo] at hu
                      simp only [hxu, ↓reduceIte] at hu
                      by_cases hxC : x ∈ C.toList
                      · have hx_pC : x ∈ (AuxTree.node p .leaf C).toList := by
                          simp [toList, hxC]
                        simp only [hx_pC, ↓reduceIte, List.mem_cons] at hu
                        rw [AuxTree.pathTo]; simp only [hxu, hxC, ↓reduceIte, List.mem_cons]
                        rcases hu with rfl | huC
                        · exact Or.inr (Or.inl rfl)
                        · rw [AuxTree.pathTo] at huC
                          simp only [Ne.symm hpx, hnin_leaf, hxC, ↓reduceIte, List.mem_cons] at huC
                          rcases huC with rfl | huC'
                          · exact Or.inl rfl
                          · exact Or.inr (Or.inr huC')
                      · have hx_pC : x ∉ (AuxTree.node p .leaf C).toList := by
                          simp [toList, Ne.symm hpx, hxC]
                        simp only [hx_pC, ↓reduceIte] at hu
                        by_cases hxD : x ∈ D.toList
                        · simp only [hxD, ↓reduceIte, List.mem_cons] at hu
                          rw [AuxTree.pathTo]; simp only [hxu, hxC, hxD, ↓reduceIte, List.mem_cons]
                          rcases hu with rfl | huD
                          · exact Or.inr (Or.inl rfl)
                          · exact Or.inr (Or.inr huD)
                        · simp only [hxD, ↓reduceIte, List.mem_nil_iff] at hu
                  · have hy_r : y ∈ (AuxTree.node rx C D).pathTo x := by
                      rw [AuxTree.pathTo] at hy
                      have hnin_leaf : x ∉ AuxTree.leaf.toList := by simp [toList]
                      simp only [Ne.symm hpx, hnin_leaf, hxr, ↓reduceIte, List.mem_cons] at hy
                      rcases hy with rfl | hy'
                      · exact absurd rfl hpy
                      · exact hy'
                    have hr_perm : ((AuxTree.node rx C D).rotateAt y).toList.Perm
                        (AuxTree.node rx C D).toList := rotateAt_toList_perm y _
                    intro u hu
                    simp only [rotateAt, hpy, ↓reduceIte, hrx] at hu
                    have hnin_leaf : x ∉ AuxTree.leaf.toList := by simp [toList]
                    rw [AuxTree.pathTo] at hu ⊢
                    simp only [Ne.symm hpx, hnin_leaf, hr_perm.mem_iff, hxr, ↓reduceIte,
                      List.mem_cons] at hu ⊢
                    rcases hu with rfl | hu'
                    · exact Or.inl rfl
                    · exact Or.inr (ihr hr_nd hxr hy_r u hu')
          | node lx A B =>
              by_cases hlx : lx = y
              · subst hlx
                have hxl : x ∈ (AuxTree.node lx A B).toList := by
                  by_contra hnin
                  have hxr : x ∈ r.toList := by
                    simp only [toList, List.mem_append, List.mem_singleton] at hx
                    rcases hx with (h | rfl) | h
                    · rw [AuxTree.toList] at hnin
                      rcases h with (h1 | h1) | h1 <;> exact absurd (by simp [h1]) hnin
                    · exact absurd rfl hpx
                    · exact h
                  have hpath_r : lx ∈ r.pathTo x := by
                    rw [AuxTree.pathTo] at hy
                    simp only [Ne.symm hpx, hnin, hxr, ↓reduceIte, List.mem_cons] at hy
                    rcases hy with rfl | hy'
                    · exact absurd rfl hpy
                    · exact hy'
                  exact hdisj_lr' lx (by simp [toList]) (AuxTree.mem_pathTo hpath_r)
                intro u hu
                rw [AuxTree.rotateAt_zigRight A B r hpy] at hu
                by_cases hxu : x = lx
                · subst hxu
                  rw [AuxTree.pathTo] at hu
                  simp only [↓reduceIte, List.mem_singleton] at hu
                  subst hu
                  rw [AuxTree.pathTo]; simp [Ne.symm hpx, hxl, pathTo]
                · rw [AuxTree.pathTo] at hu
                  simp only [hxu, ↓reduceIte] at hu
                  by_cases hxA : x ∈ A.toList
                  · simp only [hxA, ↓reduceIte, List.mem_cons] at hu
                    rw [AuxTree.pathTo]; simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons]
                    rw [AuxTree.pathTo]; simp only [hxu, hxA, ↓reduceIte, List.mem_cons]
                    rcases hu with rfl | huA
                    · exact Or.inr (Or.inl rfl)
                    · exact Or.inr (Or.inr huA)
                  · have hx_pB : x ∈ (AuxTree.node p B r).toList := by
                      simp only [toList, List.mem_append, List.mem_singleton] at hx ⊢
                      have hnin_A : x ∉ A.toList := hxA
                      rcases hx with (h | rfl) | h
                      · rcases h with (hA | rfl) | hB
                        · exact absurd hA hnin_A
                        · exact absurd rfl hxu
                        · exact Or.inl (Or.inl hB)
                      · exact Or.inl (Or.inr rfl)
                      · exact Or.inr h
                    simp only [hxA, ↓reduceIte, hx_pB, List.mem_cons] at hu
                    rw [AuxTree.pathTo]; simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons]
                    rw [AuxTree.pathTo]; simp only [hxu, hxA, ↓reduceIte]
                    by_cases hxB : x ∈ B.toList
                    · simp only [hxB, ↓reduceIte, List.mem_cons]
                      rcases hu with rfl | huB
                      · exact Or.inr (Or.inl rfl)
                      · rw [AuxTree.pathTo] at huB
                        simp only [Ne.symm hpx, hxB, ↓reduceIte, List.mem_cons] at huB
                        rcases huB with rfl | huB'
                        · exact Or.inl rfl
                        · exact Or.inr (Or.inr huB')
                    · exfalso
                      simp only [toList, List.mem_append, List.mem_singleton] at hxl
                      rcases hxl with (h | rfl) | h <;> contradiction
              · cases r with
                | leaf =>
                    have hxl : x ∈ (AuxTree.node lx A B).toList := by
                      simp only [toList, List.mem_append, List.mem_singleton, List.mem_nil_iff,
                        or_false] at hx ⊢
                      rcases hx with h | rfl
                      · exact h
                      · exact absurd rfl hpx
                    have hy_l : y ∈ (AuxTree.node lx A B).pathTo x := by
                      rw [AuxTree.pathTo] at hy
                      simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                      rcases hy with rfl | hy'
                      · exact absurd rfl hpy
                      · exact hy'
                    have hl_perm : ((AuxTree.node lx A B).rotateAt y).toList.Perm
                        (AuxTree.node lx A B).toList := rotateAt_toList_perm y _
                    intro u hu
                    simp only [rotateAt, hpy, ↓reduceIte, hlx] at hu
                    rw [AuxTree.pathTo] at hu ⊢
                    simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte, List.mem_cons] at hu ⊢
                    rcases hu with rfl | hu'
                    · exact Or.inl rfl
                    · exact Or.inr (ihl hl_nd hxl hy_l u hu')
                | node rx C D =>
                    by_cases hrx : rx = y
                    · subst hrx
                      have hnin_l : x ∉ (AuxTree.node lx A B).toList := by
                        intro hxl
                        have hy_l : rx ∈ (AuxTree.node lx A B).pathTo x := by
                          rw [AuxTree.pathTo] at hy
                          simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                          rcases hy with rfl | hy'
                          · exact absurd rfl hpy
                          · exact hy'
                        exact hdisj_lr' rx (AuxTree.mem_pathTo hy_l) (by simp [toList])
                      have hxr : x ∈ (AuxTree.node rx C D).toList := by
                        simp only [toList, List.mem_append, List.mem_singleton] at hx hnin_l ⊢
                        rcases hx with (h | rfl) | h
                        · exact absurd h hnin_l
                        · exact absurd rfl hpx
                        · exact h
                      intro u hu
                      simp only [rotateAt, hpy, ↓reduceIte, hlx] at hu
                      by_cases hxu : x = rx
                      · subst hxu
                        rw [AuxTree.pathTo] at hu
                        simp only [↓reduceIte, List.mem_singleton] at hu
                        subst hu
                        have hnin_l' : ¬(u ∈ A.toList ∨ u = lx ∨ u ∈ B.toList) := by
                          intro h; apply hnin_l
                          rcases h with h | rfl | h
                          · simp [toList, h]
                          · simp [toList]
                          · simp [toList, h]
                        rw [AuxTree.pathTo]; simp [Ne.symm hpx, hnin_l', toList, pathTo]
                      · have hx_pnode : x ∈ (AuxTree.node p (.node lx A B) C).toList ↔ x ∈ C.toList := by
                          simp only [toList, List.mem_append, List.mem_singleton] at hnin_l ⊢
                          constructor
                          · intro h
                            rcases h with (h1 | rfl) | h2
                            · exact absurd h1 hnin_l
                            · exact absurd rfl hpx
                            · exact h2
                          · intro h; exact Or.inr h
                        rw [AuxTree.pathTo] at hu
                        simp only [hxu, hx_pnode, ↓reduceIte] at hu
                        rw [AuxTree.pathTo]; simp only [Ne.symm hpx, hnin_l, hxr, ↓reduceIte, List.mem_cons]
                        rw [AuxTree.pathTo]; simp only [hxu]
                        by_cases hxC : x ∈ C.toList
                        · simp only [hxC, ↓reduceIte, List.mem_cons] at hu ⊢
                          rcases hu with rfl | huC
                          · exact Or.inr (Or.inl rfl)
                          · rw [AuxTree.pathTo] at huC
                            simp only [Ne.symm hpx, hnin_l, hxC, ↓reduceIte] at huC
                            rw [List.mem_cons] at huC
                            rcases huC with rfl | huC'
                            · exact Or.inl rfl
                            · exact Or.inr (Or.inr huC')
                        · simp only [hxC, ↓reduceIte] at hu ⊢
                          by_cases hxD : x ∈ D.toList
                          · simp only [hxD, ↓reduceIte, List.mem_cons] at hu ⊢
                            rcases hu with rfl | huD
                            · exact Or.inr (Or.inl rfl)
                            · exact Or.inr (Or.inr huD)
                          · simp only [hxD, ↓reduceIte, List.mem_nil_iff] at hu
                    · by_cases hyl : y ∈ (AuxTree.node lx A B).toList
                      · have hxl : x ∈ (AuxTree.node lx A B).toList := by
                          by_contra hnin
                          have hxr' : x ∈ (AuxTree.node rx C D).toList := by
                            simp only [toList, List.mem_append, List.mem_singleton] at hx hnin ⊢
                            rcases hx with (h | rfl) | h
                            · exact absurd h hnin
                            · exact absurd rfl hpx
                            · exact h
                          have hy_r : y ∈ (AuxTree.node rx C D).pathTo x := by
                            rw [AuxTree.pathTo] at hy
                            simp only [Ne.symm hpx, hnin, hxr', ↓reduceIte, List.mem_cons] at hy
                            rcases hy with rfl | hy'
                            · exact absurd rfl hpy
                            · exact hy'
                          exact hdisj_lr' y hyl (AuxTree.mem_pathTo hy_r)
                        have hy_l : y ∈ (AuxTree.node lx A B).pathTo x := by
                          rw [AuxTree.pathTo] at hy
                          simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                          rcases hy with rfl | hy'
                          · exact absurd rfl hpy
                          · exact hy'
                        have hl_perm : ((AuxTree.node lx A B).rotateAt y).toList.Perm
                            (AuxTree.node lx A B).toList := rotateAt_toList_perm y _
                        intro u hu
                        simp only [rotateAt, hpy, ↓reduceIte, hlx, hrx, hyl] at hu
                        rw [AuxTree.pathTo] at hu ⊢
                        simp only [Ne.symm hpx, hl_perm.mem_iff, hxl, ↓reduceIte, List.mem_cons] at hu ⊢
                        rcases hu with rfl | hu'
                        · exact Or.inl rfl
                        · exact Or.inr (ihl hl_nd hxl hy_l u hu')
                      · have hnin_l : x ∉ (AuxTree.node lx A B).toList := fun hxl =>
                          hyl (AuxTree.mem_pathTo (by
                            rw [AuxTree.pathTo] at hy
                            simp only [Ne.symm hpx, hxl, ↓reduceIte, List.mem_cons] at hy
                            rcases hy with rfl | hy'
                            · exact absurd rfl hpy
                            · exact hy'))
                        have hxr : x ∈ (AuxTree.node rx C D).toList := by
                          simp only [toList, List.mem_append, List.mem_singleton] at hx hnin_l ⊢
                          rcases hx with (h | rfl) | h
                          · exact absurd h hnin_l
                          · exact absurd rfl hpx
                          · exact h
                        have hy_r : y ∈ (AuxTree.node rx C D).pathTo x := by
                          rw [AuxTree.pathTo] at hy
                          simp only [Ne.symm hpx, hnin_l, hxr, ↓reduceIte, List.mem_cons] at hy
                          rcases hy with rfl | hy'
                          · exact absurd rfl hpy
                          · exact hy'
                        have hr_perm : ((AuxTree.node rx C D).rotateAt y).toList.Perm
                            (AuxTree.node rx C D).toList := rotateAt_toList_perm y _
                        intro u hu
                        simp only [rotateAt, hpy, ↓reduceIte, hlx, hrx, hyl] at hu
                        rw [AuxTree.pathTo] at hu ⊢
                        simp only [Ne.symm hpx, hnin_l, hr_perm.mem_iff, hxr, ↓reduceIte,
                          List.mem_cons] at hu ⊢
                        rcases hu with rfl | hu'
                        · exact Or.inl rfl
                        · exact Or.inr (ihr hr_nd hxr hy_r u hu')

end

end MinCostFlow.LinkCut.Prog
