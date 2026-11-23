module

public import MinCostFlow.LinkCut.Prog.SplayRotatePure

/-!
Subtree surgery lemmas for `AuxTree.rotateAt` (`replaceSubtree_rotateAt`,
`replaceSubtree_treeSize_add`, `parentIn_child_cases`, `rotateAt_zig_phi_le`,
`mem_pathTo_parent`), non-structural/non-aggregate offset preservation (`IsNonStructNonAggOff`),
and `evalMemSteps` agreement / local rotation invariance.
-/

namespace MinCostFlow.LinkCut.Prog

open MinCostFlow.Num

@[expose] public section

theorem AuxTree.replaceSubtree_rotateAt {t : AuxTree} {x p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) :
    let p := t.parentIn x p₀
    t.replaceSubtree p ((t.findSubtree p).rotateAt x) = t.rotateAt x := by
  induction t generalizing p₀ with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      intro p
      have hne : id ≠ x := fun h => hxr (by simp [rootId, h])
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
      have hid_nin_l : id ∉ l.toList := fun h => hdisj_id_l id h id rfl rfl
      have hdisj_lr' : ∀ u ∈ l.toList, u ∉ r.toList := fun u hu hr => hdisj_lr u (Or.inl hu) u hr rfl
      by_cases hnl : x ∈ l.toList
      · by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hnl
          | node lx A B =>
              simp only [rootId] at hxlr
              subst hxlr
              have hp_eq : p = id := by
                simp [p, parentIn, hne, hnl]
              rw [hp_eq]
              simp [replaceSubtree, findSubtree]
        · have ih := ihl (p₀ := id) hl_nd hnl hxlr
          have hp_eq : p = l.parentIn x id := by
            simp only [p, parentIn, hne, ↓reduceIte, hnl]
          have hp_mem : p ∈ l.toList := by
            rw [hp_eq]
            exact (AuxTree.parentIn_mem_and_depth hl_nd hnl hxlr).1
          have hp_ne_id : id ≠ p := fun h => hid_nin_l (h ▸ hp_mem)
          have hp_nin_r : p ∉ r.toList := hdisj_lr' p hp_mem
          have ih' : l.replaceSubtree p ((l.findSubtree p).rotateAt x) = l.rotateAt x := by
            simpa [← hp_eq] using ih
          have hrep : (AuxTree.node id l r).replaceSubtree p
              (((AuxTree.node id l r).findSubtree p).rotateAt x) =
              AuxTree.node id (l.replaceSubtree p ((l.findSubtree p).rotateAt x)) r := by
            simp only [replaceSubtree, hp_ne_id, ↓reduceIte, findSubtree, hp_mem]
            rw [AuxTree.replaceSubtree_not_mem hp_nin_r]
          rw [hrep, ih']
          cases l with
          | leaf => simp [toList] at hnl
          | node lx A B =>
              have hlx : lx ≠ x := by simpa [rootId] using Ne.symm hxlr
              cases r with
              | leaf => simp [rotateAt, hne, hlx]
              | node rx C D =>
                  have hrx : rx ≠ x := fun h => hdisj_lr' x hnl (by subst h; simp [toList])
                  simp [rotateAt, hne, hlx, hrx, hnl]
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
              simp only [rootId] at hxrr
              subst hxrr
              have hp_eq : p = id := by
                simp [p, parentIn, hne, hnl]
              rw [hp_eq]
              simp [replaceSubtree, findSubtree]
        · have ih := ihr (p₀ := id) hr_nd hnr hxrr
          have hp_eq : p = r.parentIn x id := by
            simp only [p, parentIn, hne, ↓reduceIte, hnl]
          have hp_mem : p ∈ r.toList := by
            rw [hp_eq]
            exact (AuxTree.parentIn_mem_and_depth hr_nd hnr hxrr).1
          have hid_nin_r : id ∉ r.toList := fun h => hdisj_lr id (Or.inr rfl) id h rfl
          have hp_ne_id : id ≠ p := fun h => hid_nin_r (h ▸ hp_mem)
          have hp_nin_l : p ∉ l.toList := fun hl => hdisj_lr' p hl hp_mem
          have ih' : r.replaceSubtree p ((r.findSubtree p).rotateAt x) = r.rotateAt x := by
            simpa [← hp_eq] using ih
          have hrep : (AuxTree.node id l r).replaceSubtree p
              (((AuxTree.node id l r).findSubtree p).rotateAt x) =
              AuxTree.node id l (r.replaceSubtree p ((r.findSubtree p).rotateAt x)) := by
            simp only [replaceSubtree, hp_ne_id, ↓reduceIte, findSubtree, hp_nin_l]
            rw [AuxTree.replaceSubtree_not_mem hp_nin_l]
          rw [hrep, ih']
          cases l with
          | leaf =>
              cases r with
              | leaf => simp [toList] at hnr
              | node rx C D =>
                  have hrx : rx ≠ x := by simpa [rootId] using Ne.symm hxrr
                  simp [rotateAt, hne, hrx]
          | node lx A B =>
              have hlx : lx ≠ x := fun h => hnl (by subst h; simp [toList])
              cases r with
              | leaf => simp [toList] at hnr
              | node rx C D =>
                  have hrx : rx ≠ x := by simpa [rootId] using Ne.symm hxrr
                  simp [rotateAt, hne, hlx, hrx, hnl]

theorem AuxTree.replaceSubtree_treeSize_add (vSize : ℕ → ℕ) {t s' : AuxTree} {rSub d1 d2 : ℕ}
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
        have hnd' := hnd
        simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _⟩, hr_nd, hdisj_lr⟩
        by_cases hnl : rSub ∈ l.toList
        · have hnr : rSub ∉ r.toList := fun hrm => hdisj_lr rSub (Or.inl hnl) rSub hrm rfl
          have hrep_r : r.replaceSubtree rSub s' = r := AuxTree.replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree rSub = l.findSubtree rSub := by
            simp [findSubtree, heq, hnl]
          rcases ihl hl_nd hnl (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_l, hphi_l⟩
          rw [hrep_r]
          have hsz : (AuxTree.node id (l.replaceSubtree rSub s') r).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by
            simp [treeSize, hsz_l]
          have hrank : (AuxTree.node id (l.replaceSubtree rSub s') r).rank vSize =
              (AuxTree.node id l r).rank vSize := by
            simp only [rank, hsz]
          refine ⟨hsz, ?_⟩
          simp only [treePhi, hrank]
          omega
        · have hnr : rSub ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hr
            rcases hr with (hl | rfl) | hr'
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr'
          have hrep_l : l.replaceSubtree rSub s' = l := AuxTree.replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree rSub = r.findSubtree rSub := by
            simp [findSubtree, heq, hnl]
          rcases ihr hr_nd hnr (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_r, hphi_r⟩
          rw [hrep_l]
          have hsz : (AuxTree.node id l (r.replaceSubtree rSub s')).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by
            simp [treeSize, hsz_r]
          have hrank : (AuxTree.node id l (r.replaceSubtree rSub s')).rank vSize =
              (AuxTree.node id l r).rank vSize := by
            simp only [rank, hsz]
          refine ⟨hsz, ?_⟩
          simp only [treePhi, hrank]
          omega

theorem AuxTree.findSubtree_nodup {t : AuxTree} {subId : ℕ}
    (hnd : t.toList.Nodup) : (t.findSubtree subId).toList.Nodup := by
  induction t with
  | leaf => simp [findSubtree, toList]
  | node id l r ihl ihr =>
      have hnd0 := hnd
      simp only [toList, List.nodup_append, List.nodup_cons] at hnd
      rcases hnd with ⟨⟨hl_nd, _⟩, hr_nd, _⟩
      simp only [findSubtree]
      split_ifs
      · exact hnd0
      · exact ihl hl_nd
      · exact ihr hr_nd

theorem AuxTree.parentIn_root {t : AuxTree} {p₀ : ℕ} (ht : t ≠ .leaf) :
    t.parentIn t.rootId p₀ = p₀ := by
  cases t with
  | leaf => exact absurd rfl ht
  | node id l r => simp [rootId, parentIn]

theorem AuxTree.parentIn_child_cases {t : AuxTree} {x p p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) (hp : p = t.parentIn x p₀) :
    ∃ sl sr, t.findSubtree p = .node p sl sr ∧
      ((∃ A B, sl = .node x A B) ∨
       ((sl = .leaf ∨ sl.rootId ≠ x) ∧ ∃ C D, sr = .node x C D)) := by
  induction t generalizing p₀ with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      have hne : id ≠ x := fun h => hxr (by simp [rootId, h])
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
      have hid_nin_l : id ∉ l.toList := fun h => hdisj_id_l id h id rfl rfl
      have hid_nin_r : id ∉ r.toList := fun h => hdisj_lr id (Or.inr rfl) id h rfl
      have hdisj_lr' : ∀ u ∈ l.toList, u ∉ r.toList := fun u hu hr => hdisj_lr u (Or.inl hu) u hr rfl
      by_cases hnl : x ∈ l.toList
      · by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hnl
          | node lx A B =>
              simp only [rootId] at hxlr
              subst hxlr
              have hp_eq : p = id := by
                rw [hp]; simp [parentIn, hne, hnl]
              subst hp_eq
              exact ⟨.node x A B, r, by simp [findSubtree], Or.inl ⟨A, B, rfl⟩⟩
        · have hp' : p = l.parentIn x id := by
            rw [hp]; simp [parentIn, hne, hnl]
          have hpm : p ∈ l.toList := hp' ▸ (AuxTree.parentIn_mem_and_depth hl_nd hnl hxlr).1
          have hne_idp : id ≠ p := fun h => hid_nin_l (h ▸ hpm)
          rcases ihl hl_nd hnl hxlr hp' with ⟨sl, sr, hsub, hcas⟩
          exact ⟨sl, sr, by simp [findSubtree, hne_idp, hpm, hsub], hcas⟩
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
              simp only [rootId] at hxrr
              subst hxrr
              have hp_eq : p = id := by
                rw [hp]; simp [parentIn, hne, hnl]
              subst hp_eq
              have hl_cond : l = .leaf ∨ l.rootId ≠ x := by
                cases l with
                | leaf => exact Or.inl rfl
                | node lx A B =>
                    exact Or.inr fun h => hnl (by subst h; simp [rootId, toList])
              exact ⟨l, .node x C D, by simp [findSubtree], Or.inr ⟨hl_cond, C, D, rfl⟩⟩
        · have hp' : p = r.parentIn x id := by
            rw [hp]; simp [parentIn, hne, hnl]
          have hpm : p ∈ r.toList := hp' ▸ (AuxTree.parentIn_mem_and_depth hr_nd hnr hxrr).1
          have hne_idp : id ≠ p := fun h => hid_nin_r (h ▸ hpm)
          have hnin_l : p ∉ l.toList := fun hl => hdisj_lr' p hl hpm
          rcases ihr hr_nd hnr hxrr hp' with ⟨sl, sr, hsub, hcas⟩
          exact ⟨sl, sr, by simp [findSubtree, hne_idp, hnin_l, hsub], hcas⟩

theorem AuxTree.rotateAt_zig_phi_le (vSize : ℕ → ℕ) {t : AuxTree} {x : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId)
    (hpar : t.parentIn x 0 = t.rootId) :
    (t.rotateAt x).rootId = x ∧
    (t.rotateAt x).rank vSize = t.rank vSize ∧
    (t.rotateAt x).treePhi vSize + 3 * (t.findSubtree x).rank vSize ≤
      t.treePhi vSize + 3 * (t.rotateAt x).rank vSize := by
  rcases AuxTree.parentIn_child_cases hnd hx hxr hpar.symm with ⟨sl, sr, hsub, hcas⟩
  cases t with
  | leaf => simp [toList] at hx
  | node p l r =>
      simp only [rootId, findSubtree, ↓reduceIte] at hsub
      rcases hsub with ⟨rfl, rfl⟩
      have hpx : p ≠ x := fun h => hxr (by simp [rootId, h])
      rcases hcas with ⟨A, B, rfl⟩ | ⟨hl_c, C, D, rfl⟩
      · have hrot : (AuxTree.node p (.node x A B) sr).rotateAt x = .node x A (.node p B sr) :=
          AuxTree.rotateAt_zigRight A B sr hpx
        have hfind : (AuxTree.node p (.node x A B) sr).findSubtree x = .node x A B := by
          have hxl : x ∈ (AuxTree.node x A B).toList := by simp [toList]
          simp [findSubtree, hpx, hxl]
        have hrk : (AuxTree.node x A (.node p B sr)).rank vSize =
            (AuxTree.node p (.node x A B) sr).rank vSize := by
          simp only [rank, treeSize]; congr 1; omega
        rw [hrot, hfind]
        exact ⟨rfl, hrk, zig_right_phi_le vSize x p A B sr⟩
      · have hrot : (AuxTree.node p sl (.node x C D)).rotateAt x = .node x (.node p sl C) D :=
          AuxTree.rotateAt_zigLeft sl C D hpx hl_c
        have hnin : x ∉ sl.toList := by
          rcases hl_c with rfl | hlne
          · simp [toList]
          · simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
              List.mem_singleton] at hnd
            exact fun hl => hnd.2.2 x (Or.inl hl) x (by simp) rfl
        have hfind : (AuxTree.node p sl (.node x C D)).findSubtree x = .node x C D := by
          simp [findSubtree, hpx, hnin]
        have hrk : (AuxTree.node x (.node p sl C) D).rank vSize =
            (AuxTree.node p sl (.node x C D)).rank vSize := by
          simp only [rank, treeSize]; congr 1; omega
        rw [hrot, hfind]
        exact ⟨rfl, hrk, zig_left_phi_le vSize p x sl C D⟩

theorem AuxTree.parentIn_p0_irrel {t : AuxTree} {y p₁ p₂ : ℕ}
    (hy : y ∈ t.toList) (hyr : y ≠ t.rootId) :
    t.parentIn y p₁ = t.parentIn y p₂ := by
  induction t generalizing p₁ p₂ with
  | leaf => simp [toList] at hy
  | node id l r ihl ihr =>
      have hne : id ≠ y := fun h => hyr (by simp [rootId, h])
      rw [AuxTree.parentIn, AuxTree.parentIn]
      simp only [hne, ↓reduceIte]

theorem AuxTree.mem_pathTo_parent {t : AuxTree} {x y : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hy : y ∈ t.pathTo x) (hyr : y ≠ t.rootId) :
    t.parentIn y 0 ∈ t.pathTo x := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, _⟩, hr_nd, hdisj_lr⟩
      have hdisj_lr' : ∀ u ∈ l.toList, u ∉ r.toList := fun u hu hr => hdisj_lr u (Or.inl hu) u hr rfl
      have hne : id ≠ y := fun h => hyr (by simp [rootId, h])
      by_cases hix : id = x
      · subst hix
        rw [AuxTree.pathTo] at hy
        simp only [↓reduceIte, List.mem_singleton] at hy
        exact absurd hy.symm hne
      · by_cases hnl : x ∈ l.toList
        · have hy_l : y ∈ l.pathTo x := by
            rw [AuxTree.pathTo] at hy
            simp only [Ne.symm hix, hnl, ↓reduceIte, List.mem_cons] at hy
            rcases hy with rfl | hy'
            · exact absurd rfl hne
            · exact hy'
          have hyl_mem : y ∈ l.toList := AuxTree.mem_pathTo hy_l
          rw [AuxTree.parentIn]; simp only [hne, ↓reduceIte, hyl_mem]
          rw [AuxTree.pathTo]; simp only [Ne.symm hix, hnl, ↓reduceIte]
          by_cases hylr : y = l.rootId
          · cases l with
            | leaf => simp [toList] at hyl_mem
            | node ly ll lr =>
                simp only [rootId] at hylr
                subst hylr
                rw [AuxTree.parentIn]; simp
          · rw [AuxTree.parentIn_p0_irrel hyl_mem hylr]
            exact List.mem_cons_of_mem id (ihl hl_nd hnl hy_l hylr)
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (h | rfl) | h
            · exact absurd h hnl
            · exact absurd rfl hix
            · exact h
          have hy_r : y ∈ r.pathTo x := by
            rw [AuxTree.pathTo] at hy
            simp only [Ne.symm hix, hnl, hnr, ↓reduceIte, List.mem_cons] at hy
            rcases hy with rfl | hy'
            · exact absurd rfl hne
            · exact hy'
          have hyr_mem : y ∈ r.toList := AuxTree.mem_pathTo hy_r
          have hnin_l : y ∉ l.toList := fun hl => hdisj_lr' y hl hyr_mem
          rw [AuxTree.parentIn]; simp only [hne, ↓reduceIte, hnin_l]
          rw [AuxTree.pathTo]; simp only [Ne.symm hix, hnl, hnr, ↓reduceIte]
          by_cases hyrr : y = r.rootId
          · cases r with
            | leaf => simp [toList] at hyr_mem
            | node ry rl rr =>
                simp only [rootId] at hyrr
                subst hyrr
                rw [AuxTree.parentIn]; simp
          · rw [AuxTree.parentIn_p0_irrel hyr_mem hyrr]
            exact List.mem_cons_of_mem id (ihr hr_nd hnr hy_r hyrr)

/-! ### Non-structural / non-aggregate node fields and `evalMemSteps` agreement -/

/-- Node fields never modified by tree pointer rewiring or `pullBody`. -/
@[reducible] def IsNonStructNonAggOff (off : ℕ) : Prop :=
  off < NODE_STRIDE ∧
  off ≠ OFF_LEFT ∧ off ≠ OFF_RIGHT ∧ off ≠ OFF_PARENT ∧ off ≠ OFF_PPAR ∧
  off ≠ OFF_VCNT ∧ off ≠ OFF_CSUM_FWD ∧ off ≠ OFF_CSUM_BWD ∧
  off ≠ OFF_MIN1_HAS ∧ off ≠ OFF_MIN1_VAL ∧ off ≠ OFF_MIN1_FIRST ∧ off ≠ OFF_MIN1_LAST ∧
  off ≠ OFF_MIN2_HAS ∧ off ≠ OFF_MIN2_VAL ∧ off ≠ OFF_MIN2_FIRST ∧ off ≠ OFF_MIN2_LAST

theorem isStaticPayloadOff_nonStruct {off : ℕ} (h : IsStaticPayloadOff off) :
    IsNonStructNonAggOff off := by
  simp only [IsStaticPayloadOff] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- Per-node payload/tag pointer soundness needed by `evalMemSteps`. -/
def NodeNonStructOk (h L arenaHi hp nodesBase : ℕ) (mem : ℕ → ℕ) (u : ℕ) : Prop :=
  nodeField mem nodesBase u OFF_HASE ≤ 1 ∧
  nodeField mem nodesBase u OFF_HAS_TAG ≤ 1 ∧
  (nodeField mem nodesBase u OFF_HASE = 1 →
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_FLOW_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_AF_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_AB_PTR) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_COST_FWD) ∧
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_COST_BWD)) ∧
  (nodeField mem nodesBase u OFF_HAS_TAG = 1 →
    NumPtrOk mem arenaHi hp h L (nodeField mem nodesBase u OFF_TAG_PTR))

theorem TreeMemMatch.nodeNonStructOk {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap par pp u : ℕ}
    {t : AuxTree} (ht : TreeMemMatch w h L mem nodesBase cap t par pp) (hu : u ∈ t.toList) :
    NodeNonStructOk h L (nodesBase + NODE_STRIDE * (cap + 1)) (mem (nodesBase - 1)) nodesBase mem u := by
  induction t generalizing par pp with
  | leaf => simp [AuxTree.toList] at hu
  | node id l r ihl ihr =>
      rcases ht with ⟨_, _, _, _, _, _, _, _, hhe, _, _, hht, _, _, _, _, he1, _, _, _, ht1, _, _, _, _, _, _, hl, hr⟩
      simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
      rcases hu with (hul | rfl) | hur
      · exact ihl hl hul
      · refine ⟨hhe, hht, ?_, fun h => (ht1 h).1⟩
        intro h1
        obtain ⟨k1, k2, k3, k4, k5, _⟩ := he1 h1
        exact ⟨k1, k2, k3, k4, k5⟩
      · exact ihr hr hur

theorem nodeTagInt_agree_nonStruct {h L arenaHi hp nodesBase u : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hu_ok : NodeNonStructOk h L arenaHi hp nodesBase mem₁ u)
    (hnode : ∀ off, IsNonStructNonAggOff off →
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hheap : ∀ a, arenaHi ≤ a → a < hp → mem₂ a = mem₁ a) :
    nodeTagInt mem₂ nodesBase h L u = nodeTagInt mem₁ nodesBase h L u := by
  have hht := hnode OFF_HAS_TAG (by decide)
  have htn := hnode OFF_TAG_NEG (by decide)
  have htp := hnode OFF_TAG_PTR (by decide)
  by_cases h0 : nodeField mem₁ nodesBase u OFF_HAS_TAG = 0
  · simp [nodeTagInt, hht, h0]
  · have h1 : nodeField mem₁ nodesBase u OFF_HAS_TAG = 1 :=
      eq_one_of_le_one_ne_zero hu_ok.2.1 h0
    have hptr_ok : OptNumPtrOk mem₁ arenaHi hp h L (nodeField mem₁ nodesBase u OFF_TAG_PTR) :=
      Or.inr (hu_ok.2.2.2 h1).2
    simp only [nodeTagInt, hht, htn, htp, h0, ↓reduceIte, optIntVal_agree_heap hheap hptr_ok]

theorem nodeOwnRawStep_agree_nonStruct {h L arenaHi hp nodesBase u : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hu_ok : NodeNonStructOk h L arenaHi hp nodesBase mem₁ u)
    (hnode : ∀ off, IsNonStructNonAggOff off →
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hheap : ∀ a, arenaHi ≤ a → a < hp → mem₂ a = mem₁ a) :
    nodeOwnRawStep mem₂ nodesBase h L u = nodeOwnRawStep mem₁ nodesBase h L u := by
  have hhe := hnode OFF_HASE (by decide)
  by_cases h0 : nodeField mem₁ nodesBase u OFF_HASE = 0
  · simp [nodeOwnRawStep, hhe, h0]
  · have h1 : nodeField mem₁ nodesBase u OFF_HASE = 1 :=
      eq_one_of_le_one_ne_zero hu_ok.1 h0
    obtain ⟨kfl, kaf, kab, kcf, kcb⟩ := hu_ok.2.2.1 h1
    simp only [nodeOwnRawStep, hhe, h0, ↓reduceIte,
      hnode OFF_DIR (by decide), hnode OFF_EID (by decide), hnode OFF_EU (by decide),
      hnode OFF_EV (by decide), hnode OFF_COST_FWD (by decide), hnode OFF_COST_BWD (by decide),
      hnode OFF_AF_PTR (by decide), hnode OFF_AB_PTR (by decide), hnode OFF_FLOW_PTR (by decide),
      intVal_agree_heap hheap kcf.2.1 kcf.2.2.1,
      intVal_agree_heap hheap kcb.2.1 kcb.2.2.1,
      intVal_agree_heap hheap kaf.2.1 kaf.2.2.1,
      intVal_agree_heap hheap kab.2.1 kab.2.2.1,
      intVal_agree_heap hheap kfl.2.1 kfl.2.2.1]

theorem evalMemSteps_agree_nonStruct {h L arenaHi hp nodesBase : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    {q : AuxTree}
    (hq_ok : ∀ u ∈ q.toList, NodeNonStructOk h L arenaHi hp nodesBase mem₁ u)
    (hnode : ∀ u ∈ q.toList, ∀ off, IsNonStructNonAggOff off →
      nodeField mem₂ nodesBase u off = nodeField mem₁ nodesBase u off)
    (hheap : ∀ a, arenaHi ≤ a → a < hp → mem₂ a = mem₁ a)
    (flipAcc : Bool) (δAcc : ℤ) :
    evalMemSteps mem₂ nodesBase h L q flipAcc δAcc =
      evalMemSteps mem₁ nodesBase h L q flipAcc δAcc := by
  induction q generalizing flipAcc δAcc with
  | leaf => rfl
  | node id l r ihl ihr =>
      have hid_mem : id ∈ (AuxTree.node id l r).toList := by simp [AuxTree.toList]
      have hl_ok : ∀ u ∈ l.toList, _ := fun u hu => hq_ok u (by simp [AuxTree.toList, hu])
      have hr_ok : ∀ u ∈ r.toList, _ := fun u hu => hq_ok u (by simp [AuxTree.toList, hu])
      have hl_node : ∀ u ∈ l.toList, _ := fun u hu => hnode u (by simp [AuxTree.toList, hu])
      have hr_node : ∀ u ∈ r.toList, _ := fun u hu => hnode u (by simp [AuxTree.toList, hu])
      have hrev : revFlag mem₂ nodesBase id = revFlag mem₁ nodesBase id := by
        simp [revFlag, hnode id hid_mem OFF_REV (by decide)]
      have htag : nodeTagInt mem₂ nodesBase h L id = nodeTagInt mem₁ nodesBase h L id :=
        nodeTagInt_agree_nonStruct (hq_ok id hid_mem) (hnode id hid_mem) hheap
      have hown : nodeOwnRawStep mem₂ nodesBase h L id = nodeOwnRawStep mem₁ nodesBase h L id :=
        nodeOwnRawStep_agree_nonStruct (hq_ok id hid_mem) (hnode id hid_mem) hheap
      simp only [evalMemSteps, hrev, htag, hown]
      cases flipAcc
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [ihl hl_ok hl_node _ _, ihr hr_ok hr_node _ _]
      · simp only [↓reduceIte, RawStep.flip]
        rw [ihr hr_ok hr_node _ _, ihl hl_ok hl_node _ _]

theorem evalMemSteps_zigRight {h L nodesBase p x : ℕ} {mem : ℕ → ℕ} (A B C : AuxTree)
    (hp_rev : revFlag mem nodesBase p = false) (hx_rev : revFlag mem nodesBase x = false)
    (hp_ht : nodeField mem nodesBase p OFF_HAS_TAG = 0)
    (hx_ht : nodeField mem nodesBase x OFF_HAS_TAG = 0) :
    evalMemSteps mem nodesBase h L (.node x A (.node p B C)) false 0 =
      evalMemSteps mem nodesBase h L (.node p (.node x A B) C) false 0 := by
  have hp_tag : nodeTagInt mem nodesBase h L p = 0 := by simp [nodeTagInt, hp_ht]
  have hx_tag : nodeTagInt mem nodesBase h L x = 0 := by simp [nodeTagInt, hx_ht]
  simp only [evalMemSteps, hp_rev, hx_rev, hp_tag, hx_tag, Bool.false_xor,
    Bool.false_eq_true, ↓reduceIte, add_zero, List.append_assoc]

theorem evalMemSteps_zigLeft {h L nodesBase p x : ℕ} {mem : ℕ → ℕ} (A B C : AuxTree)
    (hp_rev : revFlag mem nodesBase p = false) (hx_rev : revFlag mem nodesBase x = false)
    (hp_ht : nodeField mem nodesBase p OFF_HAS_TAG = 0)
    (hx_ht : nodeField mem nodesBase x OFF_HAS_TAG = 0) :
    evalMemSteps mem nodesBase h L (.node x (.node p A B) C) false 0 =
      evalMemSteps mem nodesBase h L (.node p A (.node x B C)) false 0 := by
  have hp_tag : nodeTagInt mem nodesBase h L p = 0 := by simp [nodeTagInt, hp_ht]
  have hx_tag : nodeTagInt mem nodesBase h L x = 0 := by simp [nodeTagInt, hx_ht]
  simp only [evalMemSteps, hp_rev, hx_rev, hp_tag, hx_tag, Bool.false_xor,
    Bool.false_eq_true, ↓reduceIte, add_zero, List.append_assoc]

end

end MinCostFlow.LinkCut.Prog
