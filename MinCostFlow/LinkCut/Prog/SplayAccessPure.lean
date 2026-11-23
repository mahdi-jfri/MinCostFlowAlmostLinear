module

public import MinCostFlow.LinkCut.Prog.SplayRotate
public import MinCostFlow.LinkCut.Prog.SplayStepPushPath

/-!
Pure `AuxTree` structural, double-rotation, potential, and permutation lemmas supporting
`splayDouble_exec`, `splayLoop_runs`, `splayBody_runs`, and `splayForest_runs`.
-/

namespace MinCostFlow.LinkCut.Prog

@[expose] public section

theorem nodup_node_unfold {id : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node id l r).toList.Nodup) :
    l.toList.Nodup ∧ id ∉ l.toList ∧ r.toList.Nodup ∧
      ∀ a, (a ∈ l.toList ∨ a = id) → a ∉ r.toList := by
  rw [AuxTree.toList, List.nodup_append] at hnd
  rcases hnd with ⟨hnd1, hr_nd, hdisj⟩
  rw [List.nodup_append, List.nodup_cons] at hnd1
  rcases hnd1 with ⟨hl_nd, _, hdisj1⟩
  refine ⟨hl_nd, fun hm => hdisj1 id hm id (List.mem_singleton.2 rfl) rfl, hr_nd, fun a ha har => ?_⟩
  simp only [List.mem_append, List.mem_singleton] at hdisj
  exact hdisj a ha a har rfl

theorem rootId_ne_of_not_mem {t : AuxTree} {y : ℕ} (hy : y ∉ t.toList) :
    ∀ a l r, t = .node a l r → a ≠ y := by
  intro a l r h ha
  rw [h, ha] at hy
  exact hy (by simp [AuxTree.toList])

theorem AuxTree.depthOf_rootId {t : AuxTree} (ht : t ≠ .leaf) :
    t.depthOf t.rootId = 0 := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r => simp [AuxTree.depthOf, AuxTree.rootId]

theorem AuxTree.root_not_mem_findSubtree {t : AuxTree} {rSub y : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hy : y ∈ (t.findSubtree rSub).toList)
    (hne : t.rootId ≠ rSub) : t.rootId ≠ y := by
  have hdep_root : t.depthOf t.rootId = 0 := by
    cases t with
    | leaf => simp [AuxTree.toList] at hr
    | node id l r => simp [AuxTree.depthOf, AuxTree.rootId]
  have hr_nz : t.depthOf rSub ≠ 0 := fun h0 =>
    hne ((AuxTree.depthOf_zero_iff_root hr).1 h0).symm
  have hlt : t.depthOf t.rootId < t.depthOf rSub := by omega
  have hroot_mem : t.rootId ∈ t.toList := by
    cases t with
    | leaf => simp [AuxTree.toList] at hr
    | node id l r => simp [AuxTree.rootId, AuxTree.toList]
  have hu := AuxTree.not_mem_findSubtree_of_ancestor hnd hroot_mem hr hlt
    (AuxTree.self_mem_pathTo hroot_mem)
  intro heq
  exact hu (heq ▸ hy)

theorem AuxTree.findSubtree_root {t : AuxTree} (ht : t ≠ .leaf) :
    t.findSubtree t.rootId = t := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r => simp [AuxTree.findSubtree, AuxTree.rootId]

theorem mem_node_of_eq {a id : ℕ} {l r : AuxTree} (h : a = id) :
    a ∈ (AuxTree.node id l r).toList := by
  subst h; simp [AuxTree.toList]

theorem mem_node_left_of_eq {a lid id : ℕ} {l1 l2 r : AuxTree} (h : a = lid) :
    a ∈ (AuxTree.node id (.node lid l1 l2) r).toList := by
  subst h; simp [AuxTree.toList]

theorem mem_node_right_of_eq {a rid id : ℕ} {l r1 r2 : AuxTree} (h : a = rid) :
    a ∈ (AuxTree.node id l (.node rid r1 r2)).toList := by
  subst h; simp [AuxTree.toList]

theorem AuxTree.findSubtree_findSubtree {t : AuxTree} {g p : ℕ}
    (hnd : t.toList.Nodup) (hg : g ∈ t.toList) (hp : p ∈ (t.findSubtree g).toList) :
    (t.findSubtree g).findSubtree p = t.findSubtree p := by
  induction t with
  | leaf => simp [AuxTree.toList] at hg
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hdisj_lr⟩
      by_cases heq : id = g
      · subst heq; simp [AuxTree.findSubtree]
      · simp only [AuxTree.findSubtree, heq, ↓reduceIte] at hp ⊢
        by_cases hgl : g ∈ l.toList
        · simp only [hgl, ↓reduceIte] at hp ⊢
          have hp_l : p ∈ l.toList := AuxTree.findSubtree_subset hp
          have hid_p : id ≠ p := fun h => hid_nl (h ▸ hp_l)
          simp only [hid_p, ↓reduceIte, hp_l]
          exact ihl hl_nd hgl hp
        · have hgr : g ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hg
            rcases hg with (h | rfl) | h
            · exact absurd h hgl
            · exact absurd rfl heq
            · exact h
          simp only [hgl, ↓reduceIte] at hp ⊢
          have hp_r : p ∈ r.toList := AuxTree.findSubtree_subset hp
          have hid_p : id ≠ p := fun h => hdisj_lr id (Or.inr rfl) (h ▸ hp_r)
          have hp_nl : p ∉ l.toList := fun hl => hdisj_lr p (Or.inl hl) hp_r
          simp only [hid_p, ↓reduceIte, hp_nl]
          exact ihr hr_nd hgr hp

theorem AuxTree.rotateAt_recurse_left {p x : ℕ} {l r : AuxTree}
    (hp : p ≠ x)
    (hl : ∀ lx l1 l2, l = .node lx l1 l2 → lx ≠ x)
    (hr : ∀ rx r1 r2, r = .node rx r1 r2 → rx ≠ x)
    (hxl : x ∈ l.toList) :
    (AuxTree.node p l r).rotateAt x = .node p (l.rotateAt x) r := by
  cases l with
  | leaf => simp [AuxTree.toList] at hxl
  | node lx A B =>
      have hlx : lx ≠ x := hl lx A B rfl
      cases r with
      | leaf => simp [AuxTree.rotateAt, hp, hlx]
      | node rx C D =>
          have hrx : rx ≠ x := hr rx C D rfl
          simp [AuxTree.rotateAt, hp, hlx, hrx, hxl]

theorem AuxTree.rotateAt_recurse_right {p x : ℕ} {l r : AuxTree}
    (hp : p ≠ x)
    (hl : ∀ lx l1 l2, l = .node lx l1 l2 → lx ≠ x)
    (hr : ∀ rx r1 r2, r = .node rx r1 r2 → rx ≠ x)
    (hxnl : x ∉ l.toList) (hne_r : r ≠ .leaf) :
    (AuxTree.node p l r).rotateAt x = .node p l (r.rotateAt x) := by
  cases l with
  | leaf =>
      cases r with
      | leaf => exact absurd rfl hne_r
      | node rx C D =>
          have hrx : rx ≠ x := hr rx C D rfl
          simp [AuxTree.rotateAt, hp, hrx]
  | node lx A B =>
      have hlx : lx ≠ x := hl lx A B rfl
      cases r with
      | leaf => exact absurd rfl hne_r
      | node rx C D =>
          have hrx : rx ≠ x := hr rx C D rfl
          simp [AuxTree.rotateAt, hp, hlx, hrx, hxnl]

theorem AuxTree.rotateAt_of_ancestor {t : AuxTree} {rSub y : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList)
    (hy : y ∈ (t.findSubtree rSub).toList) (hne : y ≠ rSub) :
    t.rotateAt y = t.replaceSubtree rSub ((t.findSubtree rSub).rotateAt y) := by
  induction t with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r; simp [AuxTree.findSubtree, AuxTree.replaceSubtree]
      · simp only [AuxTree.findSubtree, hid_r, ↓reduceIte] at hy ⊢
        simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hy ⊢
          have hy_l : y ∈ l.toList := AuxTree.findSubtree_subset hy
          have hyd : id ≠ y := fun h => hid_nl (h ▸ hy_l)
          have hnr : rSub ∉ r.toList := fun h => hdisj_lr rSub (Or.inl hrl) h
          have hy_nr : y ∉ r.toList := fun h => hdisj_lr y (Or.inl hy_l) h
          have hl_child : ∀ lx l1 l2, l = .node lx l1 l2 → lx ≠ y := by
            intro lx l1 l2 hl_eq h_eq
            have hl_r : l.rootId = lx := by rw [hl_eq]; rfl
            rw [← hl_r] at h_eq
            by_cases hrx : l.rootId = rSub
            · exact hne (h_eq ▸ hrx)
            · exact AuxTree.root_not_mem_findSubtree hl_nd hrl hy hrx h_eq
          have hr_child : ∀ rx r1 r2, r = .node rx r1 r2 → rx ≠ y :=
            rootId_ne_of_not_mem hy_nr
          rw [AuxTree.rotateAt_recurse_left hyd hl_child hr_child hy_l,
              ihl hl_nd hrl hy, AuxTree.replaceSubtree_not_mem hnr]
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hy ⊢
          have hy_r : y ∈ r.toList := AuxTree.findSubtree_subset hy
          have hyd : id ≠ y := fun h => hdisj_lr id (Or.inr rfl) (h ▸ hy_r)
          have hy_nl : y ∉ l.toList := fun h => hdisj_lr y (Or.inl h) hy_r
          have hl_child : ∀ lx l1 l2, l = .node lx l1 l2 → lx ≠ y :=
            rootId_ne_of_not_mem hy_nl
          have hr_child : ∀ rx r1 r2, r = .node rx r1 r2 → rx ≠ y := by
            intro rx r1 r2 hr_eq h_eq
            have hr_r : r.rootId = rx := by rw [hr_eq]; rfl
            rw [← hr_r] at h_eq
            by_cases hrx : r.rootId = rSub
            · exact hne (h_eq ▸ hrx)
            · exact AuxTree.root_not_mem_findSubtree hr_nd hrr hy hrx h_eq
          have hr_ne : r ≠ .leaf := by
            cases r with
            | leaf => simp [AuxTree.toList] at hrr
            | node _ _ _ => simp
          rw [AuxTree.rotateAt_recurse_right hyd hl_child hr_child hy_nl hr_ne,
              ihr hr_nd hrr hy, AuxTree.replaceSubtree_not_mem hrl]

theorem AuxTree.rotateAt_replaceSubtree {t s' : AuxTree} {rSub y : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hs' : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree rSub).toList)
    (hy : y ∈ s'.toList) (hne : y ≠ s'.rootId) :
    (t.replaceSubtree rSub s').rotateAt y = t.replaceSubtree rSub (s'.rotateAt y) := by
  induction t with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r; simp [AuxTree.replaceSubtree]
      · simp only [AuxTree.findSubtree, hid_r, ↓reduceIte] at hs_perm
        simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hs_perm
          have hy_l : y ∈ l.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hy)
          have hyd : id ≠ y := fun h => hid_nl (h ▸ hy_l)
          have hnr : rSub ∉ r.toList := fun h => hdisj_lr rSub (Or.inl hrl) h
          have hy_nr : y ∉ r.toList := fun h => hdisj_lr y (Or.inl hy_l) h
          have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
            AuxTree.replaceSubtree_perm hl_nd hrl hs_perm
          have hy_rep : y ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hy_l
          have hl_ne : l ≠ .leaf := by
            cases l with
            | leaf => simp [AuxTree.toList] at hrl
            | node _ _ _ => simp
          have hl_child : ∀ lx l1 l2, l.replaceSubtree rSub s' = .node lx l1 l2 → lx ≠ y := by
            intro lx l1 l2 hl_eq h_eq
            have hroot : (l.replaceSubtree rSub s').rootId = lx := by rw [hl_eq]; rfl
            rw [AuxTree.replaceSubtree_rootId hl_ne hs'] at hroot
            by_cases hl_r : l.rootId = rSub
            · simp only [hl_r, ↓reduceIte] at hroot
              exact hne (hroot.trans h_eq).symm
            · simp only [hl_r, ↓reduceIte] at hroot
              exact AuxTree.root_not_mem_findSubtree hl_nd hrl (hs_perm.mem_iff.1 hy) hl_r
                (hroot.trans h_eq)
          have hr_child : ∀ rx r1 r2, r = .node rx r1 r2 → rx ≠ y :=
            rootId_ne_of_not_mem hy_nr
          rw [AuxTree.replaceSubtree_not_mem hnr, AuxTree.replaceSubtree_not_mem hnr,
              AuxTree.rotateAt_recurse_left hyd hl_child hr_child hy_rep,
              ihl hl_nd hrl hs_perm]
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hs_perm
          have hy_r : y ∈ r.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hy)
          have hyd : id ≠ y := fun h => hdisj_lr id (Or.inr rfl) (h ▸ hy_r)
          have hy_nl : y ∉ l.toList := fun h => hdisj_lr y (Or.inl h) hy_r
          have hr_perm : (r.replaceSubtree rSub s').toList.Perm r.toList :=
            AuxTree.replaceSubtree_perm hr_nd hrr hs_perm
          have hr_ne : r ≠ .leaf := by
            cases r with
            | leaf => simp [AuxTree.toList] at hrr
            | node _ _ _ => simp
          have hrep_ne : r.replaceSubtree rSub s' ≠ .leaf := by
            intro h
            have hsz := hr_perm.mem_iff.2 hrr
            rw [h, AuxTree.toList] at hsz; simp at hsz
          have hl_child : ∀ lx l1 l2, l = .node lx l1 l2 → lx ≠ y :=
            rootId_ne_of_not_mem hy_nl
          have hr_child : ∀ rx r1 r2, r.replaceSubtree rSub s' = .node rx r1 r2 → rx ≠ y := by
            intro rx r1 r2 hr_eq h_eq
            have hroot : (r.replaceSubtree rSub s').rootId = rx := by rw [hr_eq]; rfl
            rw [AuxTree.replaceSubtree_rootId hr_ne hs'] at hroot
            by_cases hr_r : r.rootId = rSub
            · simp only [hr_r, ↓reduceIte] at hroot
              exact hne (hroot.trans h_eq).symm
            · simp only [hr_r, ↓reduceIte] at hroot
              exact AuxTree.root_not_mem_findSubtree hr_nd hrr (hs_perm.mem_iff.1 hy) hr_r
                (hroot.trans h_eq)
          rw [AuxTree.replaceSubtree_not_mem hrl, AuxTree.replaceSubtree_not_mem hrl,
              AuxTree.rotateAt_recurse_right hyd hl_child hr_child hy_nl hrep_ne,
              ihr hr_nd hrr hs_perm]

theorem AuxTree.replaceSubtree_depthOf_root {t s' : AuxTree} {rSub x : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hs' : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree rSub).toList) (hx : s'.rootId = x) :
    (t.replaceSubtree rSub s').depthOf x = t.depthOf rSub := by
  induction t with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r
        simp only [AuxTree.replaceSubtree, ↓reduceIte]
        rw [← hx, AuxTree.depthOf_rootId hs', AuxTree.depthOf]
        simp
      · have hx_in_s' : x ∈ s'.toList := by
          cases s' with
          | leaf => exact absurd rfl hs'
          | node sid sl sr => simp only [AuxTree.rootId] at hx; subst hx; simp [AuxTree.toList]
        simp only [AuxTree.findSubtree, hid_r, ↓reduceIte] at hs_perm
        simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hs_perm
          have hx_l : x ∈ l.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hx_in_s')
          have hnr : rSub ∉ r.toList := fun h => hdisj_lr rSub (Or.inl hrl) h
          have hxd : x ≠ id := fun h => hid_nl (h ▸ hx_l)
          have hrx : rSub ≠ id := Ne.symm hid_r
          have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
            AuxTree.replaceSubtree_perm hl_nd hrl hs_perm
          have hx_rep : x ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hx_l
          rw [AuxTree.replaceSubtree_not_mem hnr, AuxTree.depthOf, AuxTree.depthOf]
          simp only [hxd, hrx, hx_rep, hrl, ↓reduceIte]
          rw [ihl hl_nd hrl hs_perm]
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hs_perm
          have hx_r : x ∈ r.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hx_in_s')
          have hx_nl : x ∉ l.toList := fun h => hdisj_lr x (Or.inl h) hx_r
          have hxd : x ≠ id := fun h => hdisj_lr id (Or.inr rfl) (h ▸ hx_r)
          have hrx : rSub ≠ id := Ne.symm hid_r
          have hr_perm : (r.replaceSubtree rSub s').toList.Perm r.toList :=
            AuxTree.replaceSubtree_perm hr_nd hrr hs_perm
          have hx_rep : x ∈ (r.replaceSubtree rSub s').toList := hr_perm.mem_iff.2 hx_r
          rw [AuxTree.replaceSubtree_not_mem hrl, AuxTree.depthOf, AuxTree.depthOf]
          simp only [hxd, hrx, hx_nl, hrl, hrr, hx_rep, ↓reduceIte]
          rw [ihr hr_nd hrr hs_perm]

theorem AuxTree.findSubtree_replaceSubtree_root {t s' : AuxTree} {rSub : ℕ}
    (hnd : t.toList.Nodup) (hr : rSub ∈ t.toList) (hs' : s' ≠ .leaf)
    (hs_perm : s'.toList.Perm (t.findSubtree rSub).toList) :
    (t.replaceSubtree rSub s').findSubtree s'.rootId = s' := by
  induction t with
  | leaf => simp [AuxTree.toList] at hr
  | node id l r ihl ihr =>
      rcases nodup_node_unfold hnd with ⟨hl_nd, hid_nl, hr_nd, hdisj_lr⟩
      by_cases hid_r : id = rSub
      · subst hid_r; simp [AuxTree.replaceSubtree, AuxTree.findSubtree_root hs']
      · have hs_in : s'.rootId ∈ s'.toList := by
          cases s' with
          | leaf => exact absurd rfl hs'
          | node sid _ _ => simp [AuxTree.rootId, AuxTree.toList]
        simp only [AuxTree.findSubtree, hid_r, ↓reduceIte] at hs_perm
        simp only [AuxTree.replaceSubtree, hid_r, ↓reduceIte]
        by_cases hrl : rSub ∈ l.toList
        · simp only [hrl, ↓reduceIte] at hs_perm
          have hs_l : s'.rootId ∈ l.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hs_in)
          have hnr : rSub ∉ r.toList := fun h => hdisj_lr rSub (Or.inl hrl) h
          have hne_id : id ≠ s'.rootId := fun h => hid_nl (h ▸ hs_l)
          have hl_perm : (l.replaceSubtree rSub s').toList.Perm l.toList :=
            AuxTree.replaceSubtree_perm hl_nd hrl hs_perm
          have hs_rep : s'.rootId ∈ (l.replaceSubtree rSub s').toList := hl_perm.mem_iff.2 hs_l
          rw [AuxTree.replaceSubtree_not_mem hnr, AuxTree.findSubtree]
          simp only [hne_id, hs_rep, ↓reduceIte]
          exact ihl hl_nd hrl hs_perm
        · have hrr : rSub ∈ r.toList := by
            simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (h | rfl) | h
            · exact absurd h hrl
            · exact absurd rfl hid_r
            · exact h
          simp only [hrl, ↓reduceIte] at hs_perm
          have hs_r : s'.rootId ∈ r.toList := AuxTree.findSubtree_subset (hs_perm.mem_iff.1 hs_in)
          have hs_nl : s'.rootId ∉ l.toList := fun h => hdisj_lr s'.rootId (Or.inl h) hs_r
          have hne_id : id ≠ s'.rootId := fun h => hdisj_lr id (Or.inr rfl) (h ▸ hs_r)
          rw [AuxTree.replaceSubtree_not_mem hrl, AuxTree.findSubtree]
          simp only [hne_id, hs_nl, ↓reduceIte]
          exact ihr hr_nd hrr hs_perm

theorem AuxTree.grandparent_child_cases {t : AuxTree} {x p g : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp : p = t.parentIn x 0) (hp_mem : p ∈ t.toList) (hpr : p ≠ t.rootId)
    (hg : g = t.parentIn p 0) :
    (∃ A B C D, t.findSubtree g = .node g (.node p (.node x A B) C) D) ∨
    (∃ A B C D, t.findSubtree g = .node g (.node p A (.node x B C)) D) ∨
    (∃ A B C D, t.findSubtree g = .node g A (.node p (.node x B C) D)) ∨
    (∃ A B C D, t.findSubtree g = .node g A (.node p B (.node x C D))) := by
  have hg_mem : g ∈ t.toList := hg ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr).1
  rcases AuxTree.parentIn_child_cases hnd hp_mem hpr hg with ⟨gl, gr, hsub_g, hcas_g⟩
  rcases AuxTree.parentIn_child_cases hnd hx hxr hp with ⟨pl, pr, hsub_p, hcas_p⟩
  have hsub_g_nd : (t.findSubtree g).toList.Nodup := AuxTree.findSubtree_nodup hnd
  rw [hsub_g] at hsub_g_nd
  rcases nodup_node_unfold hsub_g_nd with ⟨_, hg_nl, _, hdisj_g⟩
  rcases hcas_g with ⟨gpL, gpR, rfl⟩ | ⟨_, gpL, gpR, rfl⟩
  · have hgp : g ≠ p := fun h => hg_nl (h ▸ by simp [AuxTree.toList])
    have hp_s : p ∈ (t.findSubtree g).toList := by rw [hsub_g]; simp [AuxTree.toList]
    have hfind : t.findSubtree p = .node p gpL gpR := by
      rw [← AuxTree.findSubtree_findSubtree hnd hg_mem hp_s, hsub_g]
      simp [AuxTree.findSubtree, hgp, AuxTree.toList]
    rw [hfind] at hsub_p
    injection hsub_p with _ hpl hpr_eq
    rw [← hpl, ← hpr_eq] at hcas_p
    rcases hcas_p with ⟨A, B, rfl⟩ | ⟨_, C, D, rfl⟩
    · exact Or.inl ⟨A, B, gpR, gr, hsub_g⟩
    · exact Or.inr (Or.inl ⟨gpL, C, D, gr, hsub_g⟩)
  · have hgp : g ≠ p := fun h => hdisj_g g (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
    have hp_nl : p ∉ gl.toList := fun h => hdisj_g p (Or.inl h) (by simp [AuxTree.toList])
    have hp_s : p ∈ (t.findSubtree g).toList := by rw [hsub_g]; simp [AuxTree.toList]
    have hfind : t.findSubtree p = .node p gpL gpR := by
      rw [← AuxTree.findSubtree_findSubtree hnd hg_mem hp_s, hsub_g]
      simp [AuxTree.findSubtree, hgp, hp_nl]
    rw [hfind] at hsub_p
    injection hsub_p with _ hpl hpr_eq
    rw [← hpl, ← hpr_eq] at hcas_p
    rcases hcas_p with ⟨A, B, rfl⟩ | ⟨_, C, D, rfl⟩
    · exact Or.inr (Or.inr (Or.inl ⟨gl, A, B, gpR, hsub_g⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨gl, gpL, C, D, hsub_g⟩))

theorem AuxTree.double_zigZig_right (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree)
    (hnd : (AuxTree.node g (.node p (.node x A B) C) D).toList.Nodup) :
    let s := AuxTree.node g (.node p (.node x A B) C) D
    let s' := (s.rotateAt p).rotateAt x
    s' = .node x A (.node p B (.node g C D)) ∧
    s.findSubtree x = .node x A B ∧
    s'.treeSize vSize = s.treeSize vSize ∧
    s'.treePhi vSize + 3 * (AuxTree.node x A B).rank vSize + 1 ≤
      s.treePhi vSize + 3 * s'.rank vSize := by
  intro s s'
  rcases nodup_node_unfold hnd with ⟨hp_nd, hg_np, _, _⟩
  rcases nodup_node_unfold hp_nd with ⟨_, hp_nx, _, _⟩
  have hgp : g ≠ p := fun h => hg_np (h ▸ by simp [AuxTree.toList])
  have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [AuxTree.toList])
  have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [AuxTree.toList])
  have hrot_eq : s' = .node x A (.node p B (.node g C D)) := by
    dsimp only [s', s]
    rw [AuxTree.rotateAt_zigRight (.node x A B) C D hgp]
    rw [AuxTree.rotateAt_zigRight A B (.node g C D) hpx]
  have hfind_x : s.findSubtree x = .node x A B := by
    dsimp only [s]
    simp only [AuxTree.findSubtree, hgx, hpx, AuxTree.toList, List.mem_append, List.mem_singleton,
      or_true, true_or, ↓reduceIte]
  refine ⟨hrot_eq, hfind_x, ?_, ?_⟩
  · dsimp only [s']; rw [AuxTree.rotateAt_treeSize, AuxTree.rotateAt_treeSize]
  · rw [hrot_eq]; exact zigZig_right_phi_le vSize x p g A B C D

theorem AuxTree.double_zigZig_left (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree)
    (hnd : (AuxTree.node g A (.node p B (.node x C D))).toList.Nodup) :
    let s := AuxTree.node g A (.node p B (.node x C D))
    let s' := (s.rotateAt p).rotateAt x
    s' = .node x (.node p (.node g A B) C) D ∧
    s.findSubtree x = .node x C D ∧
    s'.treeSize vSize = s.treeSize vSize ∧
    s'.treePhi vSize + 3 * (AuxTree.node x C D).rank vSize + 1 ≤
      s.treePhi vSize + 3 * s'.rank vSize := by
  intro s s'
  rcases nodup_node_unfold hnd with ⟨_, _, hp_nd, hdisj_g⟩
  rcases nodup_node_unfold hp_nd with ⟨_, hp_nB, _, hdisj_p⟩
  have hgp : g ≠ p := fun h => hdisj_g g (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
  have hgx : g ≠ x := fun h => hdisj_g g (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
  have hpx : p ≠ x := fun h => hdisj_p p (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
  have hp_nA : p ∉ A.toList := fun h => hdisj_g p (Or.inl h) (by simp [AuxTree.toList])
  have hx_nA : x ∉ A.toList := fun h => hdisj_g x (Or.inl h) (by simp [AuxTree.toList])
  have hx_nB : x ∉ B.toList := fun h => hdisj_p x (Or.inl h) (by simp [AuxTree.toList])
  have hA_p : A = .leaf ∨ A.rootId ≠ p := by
    cases A with
    | leaf => exact Or.inl rfl
    | node a l r => exact Or.inr (rootId_ne_of_not_mem hp_nA a l r rfl)
  have hB_x : B = .leaf ∨ B.rootId ≠ x := by
    cases B with
    | leaf => exact Or.inl rfl
    | node b l r => exact Or.inr (rootId_ne_of_not_mem hx_nB b l r rfl)
  have hrot_eq : s' = .node x (.node p (.node g A B) C) D := by
    dsimp only [s', s]
    rw [AuxTree.rotateAt_zigLeft A B (.node x C D) hgp hA_p]
    rw [AuxTree.rotateAt_zigLeft (.node g A B) C D hpx (Or.inr (by simp [AuxTree.rootId, hgx]))]
  have hfind_x : s.findSubtree x = .node x C D := by
    dsimp only [s]
    simp only [AuxTree.findSubtree, hgx, hx_nA, hpx, hx_nB, ↓reduceIte]
  refine ⟨hrot_eq, hfind_x, ?_, ?_⟩
  · dsimp only [s']; rw [AuxTree.rotateAt_treeSize, AuxTree.rotateAt_treeSize]
  · rw [hrot_eq]; exact zigZig_left_phi_le vSize g p x A B C D

theorem AuxTree.double_zigZag_lr (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree)
    (hnd : (AuxTree.node g (.node p A (.node x B C)) D).toList.Nodup) :
    let s := AuxTree.node g (.node p A (.node x B C)) D
    let s' := (s.rotateAt x).rotateAt x
    s' = .node x (.node p A B) (.node g C D) ∧
    s.findSubtree x = .node x B C ∧
    s'.treeSize vSize = s.treeSize vSize ∧
    s'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      s.treePhi vSize + 3 * s'.rank vSize := by
  intro s s'
  rcases nodup_node_unfold hnd with ⟨hp_nd, hg_np, _, hdisj_g⟩
  rcases nodup_node_unfold hp_nd with ⟨_, _, _, hdisj_p⟩
  have hgx : g ≠ x := fun h => hg_np (h ▸ by simp [AuxTree.toList])
  have hpx : p ≠ x := fun h => hdisj_p p (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
  have hx_nA : x ∉ A.toList := fun h => hdisj_p x (Or.inl h) (by simp [AuxTree.toList])
  have hx_nD : x ∉ D.toList := fun h => hdisj_g x (Or.inl (by simp [AuxTree.toList])) h
  have hA_x : A = .leaf ∨ A.rootId ≠ x := by
    cases A with
    | leaf => exact Or.inl rfl
    | node a l r => exact Or.inr (rootId_ne_of_not_mem hx_nA a l r rfl)
  have hl_child : ∀ lx l1 l2, AuxTree.node p A (.node x B C) = .node lx l1 l2 → lx ≠ x := by
    intro lx l1 l2 h; cases h; exact hpx
  have hr_child : ∀ rx r1 r2, D = .node rx r1 r2 → rx ≠ x :=
    rootId_ne_of_not_mem hx_nD
  have hrot_eq : s' = .node x (.node p A B) (.node g C D) := by
    dsimp only [s', s]
    rw [AuxTree.rotateAt_recurse_left hgx hl_child hr_child (by simp [AuxTree.toList])]
    rw [AuxTree.rotateAt_zigLeft A B C hpx hA_x]
    rw [AuxTree.rotateAt_zigRight (.node p A B) C D hgx]
  have hfind_x : s.findSubtree x = .node x B C := by
    dsimp only [s]
    simp only [AuxTree.findSubtree, hgx, hx_nA, hpx, AuxTree.toList, List.mem_append,
      List.mem_singleton, or_true, true_or, ↓reduceIte]
  refine ⟨hrot_eq, hfind_x, ?_, ?_⟩
  · dsimp only [s']; rw [AuxTree.rotateAt_treeSize, AuxTree.rotateAt_treeSize]
  · rw [hrot_eq]; exact zigZag_lr_phi_le vSize p x g A B C D

theorem AuxTree.double_zigZag_rl (vSize : ℕ → ℕ) (g p x : ℕ) (A B C D : AuxTree)
    (hnd : (AuxTree.node g A (.node p (.node x B C) D)).toList.Nodup) :
    let s := AuxTree.node g A (.node p (.node x B C) D)
    let s' := (s.rotateAt x).rotateAt x
    s' = .node x (.node g A B) (.node p C D) ∧
    s.findSubtree x = .node x B C ∧
    s'.treeSize vSize = s.treeSize vSize ∧
    s'.treePhi vSize + 3 * (AuxTree.node x B C).rank vSize + 1 ≤
      s.treePhi vSize + 3 * s'.rank vSize := by
  intro s s'
  rcases nodup_node_unfold hnd with ⟨_, _, hp_nd, hdisj_g⟩
  rcases nodup_node_unfold hp_nd with ⟨_, hp_nx, _, _⟩
  have hgx : g ≠ x := fun h => hdisj_g g (Or.inr rfl) (h ▸ by simp [AuxTree.toList])
  have hpx : p ≠ x := fun h => hp_nx (h ▸ by simp [AuxTree.toList])
  have hx_nA : x ∉ A.toList := fun h => hdisj_g x (Or.inl h) (by simp [AuxTree.toList])
  have hA_x : A = .leaf ∨ A.rootId ≠ x := by
    cases A with
    | leaf => exact Or.inl rfl
    | node a l r => exact Or.inr (rootId_ne_of_not_mem hx_nA a l r rfl)
  have hl_child : ∀ lx l1 l2, A = .node lx l1 l2 → lx ≠ x :=
    rootId_ne_of_not_mem hx_nA
  have hr_child : ∀ rx r1 r2, AuxTree.node p (.node x B C) D = .node rx r1 r2 → rx ≠ x := by
    intro rx r1 r2 h; cases h; exact hpx
  have hrot_eq : s' = .node x (.node g A B) (.node p C D) := by
    dsimp only [s', s]
    rw [AuxTree.rotateAt_recurse_right hgx hl_child hr_child hx_nA (by simp)]
    rw [AuxTree.rotateAt_zigRight B C D hpx]
    rw [AuxTree.rotateAt_zigLeft A B (.node p C D) hgx hA_x]
  have hfind_x : s.findSubtree x = .node x B C := by
    dsimp only [s]
    simp only [AuxTree.findSubtree, hgx, hx_nA, hpx, AuxTree.toList, List.mem_append,
      List.mem_singleton, or_true, true_or, ↓reduceIte]
  refine ⟨hrot_eq, hfind_x, ?_, ?_⟩
  · dsimp only [s']; rw [AuxTree.rotateAt_treeSize, AuxTree.rotateAt_treeSize]
  · rw [hrot_eq]; exact zigZag_rl_phi_le vSize g x p A B C D

theorem AuxTree.doubleStep_lift {t s' : AuxTree} {x p g : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hp : p = t.parentIn x 0) (hp_mem : p ∈ t.toList) (hpr : p ≠ t.rootId)
    (hg : g = t.parentIn p 0) (hg_mem : g ∈ t.toList)
    (hs' : s' ≠ .leaf) (hx_root : s'.rootId = x)
    (hs_perm : s'.toList.Perm (t.findSubtree g).toList)
    (hstep : ∀ vSize, s'.treeSize vSize = (t.findSubtree g).treeSize vSize ∧
      s'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
        (t.findSubtree g).treePhi vSize + 3 * s'.rank vSize) :
    let t' := t.replaceSubtree g s'
    2 ≤ t.depthOf x ∧
    t'.depthOf x = t.depthOf x - 2 ∧
    ∀ vSize, t'.treeSize vSize = t.treeSize vSize ∧
      t'.treePhi vSize + 3 * (t.findSubtree x).rank vSize + 1 ≤
        t.treePhi vSize + 3 * (t'.findSubtree x).rank vSize := by
  intro t'
  have hdep1 : t.depthOf p + 1 = t.depthOf x :=
    hp ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hx hxr).2.1
  have hdep2 : t.depthOf g + 1 = t.depthOf p :=
    hg ▸ (AuxTree.parentIn_mem_and_depth (p₀ := 0) hnd hp_mem hpr).2.1
  have hdep_rep : t'.depthOf x = t.depthOf g :=
    AuxTree.replaceSubtree_depthOf_root hnd hg_mem hs' hs_perm hx_root
  refine ⟨by omega, by omega, fun vSize => ?_⟩
  rcases hstep vSize with ⟨hsz, hphi⟩
  have hfind_after : t'.findSubtree x = s' := by
    rw [← hx_root]
    exact AuxTree.findSubtree_replaceSubtree_root hnd hg_mem hs' hs_perm
  have hphi' : s'.treePhi vSize + (3 * (t.findSubtree x).rank vSize + 1) ≤
      (t.findSubtree g).treePhi vSize + 3 * s'.rank vSize := by
    omega
  have hres := AuxTree.replaceSubtree_treeSize_add vSize hnd hg_mem hsz hphi'
  have hres1 : t'.treeSize vSize = t.treeSize vSize := hres.1
  have hres2 : t'.treePhi vSize + (3 * (t.findSubtree x).rank vSize + 1) ≤
      t.treePhi vSize + 3 * s'.rank vSize := hres.2
  rw [hfind_after]
  exact ⟨hres1, by omega⟩

theorem exists_perm_cons_of_mem {α : Type*} {a : α} {xs : List α} (h : a ∈ xs) :
    ∃ rest, xs.Perm (a :: rest) := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | hb
      · exact ⟨bs, List.Perm.refl _⟩
      · rcases ih hb with ⟨rest, hperm⟩
        exact ⟨b :: rest, (hperm.cons b).trans (List.Perm.swap a b rest)⟩

theorem list_perm_flatMap {α β : Type*} {xs ys : List α} (f : α → List β)
    (hp : xs.Perm ys) : (xs.flatMap f).Perm (ys.flatMap f) := by
  induction hp with
  | nil => simp
  | cons a _ ih => simpa [List.flatMap_cons] using ih.append_left (f a)
  | swap a b l =>
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact (List.perm_append_comm).append_right (l.flatMap f)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem AuxTree.evalInorder_false_of_all_false {t : AuxTree} {rev : ℕ → Bool}
    (hrev : ∀ u ∈ t.toList, rev u = false) :
    t.evalInorder rev false = t.toList := by
  induction t with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hr_id : rev id = false := hrev id (by simp [AuxTree.toList])
      have hl := ihl fun u hu => hrev u (by simp [AuxTree.toList, hu])
      have hr := ihr fun u hu => hrev u (by simp [AuxTree.toList, hu])
      simp [AuxTree.evalInorder, AuxTree.toList, hr_id, hl, hr]

end

end MinCostFlow.LinkCut.Prog
