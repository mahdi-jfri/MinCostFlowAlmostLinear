module

public import MinCostFlow.LinkCut.Prog.SplayStepSurgery

/-!
Core helper infrastructure for the splay-tree Word-RAM verification:
- static payload offsets (`IsStaticPayloadOff`),
- expression evaluation helpers,
- memory framing (`MemPreservedOutside` and `LctFrame` updates),
- `evalMemSteps` commutation, shift, and `IntMinAgg` scaling identities,
- pure `AuxTree` subtree replacement preserving `TreeMemMatch`,
- `SplayProgramOk` linking `MinCostFlow.Num` contracts with splay procedure bodies.
-/

namespace MinCostFlow.LinkCut.Prog

open WordRAM MinCostFlow.Num

public section AuxTreeSurgery

theorem AuxTree.replaceSubtree_perm {t s' : AuxTree} {x : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hs_perm : s'.toList.Perm (t.findSubtree x).toList) :
    (t.replaceSubtree x s').toList.Perm t.toList := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [replaceSubtree]
      by_cases heq : id = x
      · subst heq; simpa [findSubtree] using hs_perm
      · simp only [heq, ↓reduceIte, toList]
        have hnd' := hnd
        simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _⟩, hr_nd, hdisj_lr⟩
        by_cases hnl : x ∈ l.toList
        · have hnr : x ∉ r.toList := fun hr => hdisj_lr x (Or.inl hnl) x hr rfl
          have hrep_r : r.replaceSubtree x s' = r := AuxTree.replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree x = l.findSubtree x := by
            simp [findSubtree, heq, hnl]
          rw [hrep_r]
          exact ((ihl hl_nd hnl (by simpa [hfind] using hs_perm)).append_right [id]).append_right r.toList
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr
          have hrep_l : l.replaceSubtree x s' = l := AuxTree.replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree x = r.findSubtree x := by
            simp [findSubtree, heq, hnl]
          rw [hrep_l]
          simpa [List.append_assoc] using
            (ihr hr_nd hnr (by simpa [hfind] using hs_perm)).append_left (l.toList ++ [id])

theorem AuxTree.replaceSubtree_treeSize_treePhi (vSize : ℕ → ℕ) {t s' : AuxTree} {x : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hs_sz : s'.treeSize vSize = (t.findSubtree x).treeSize vSize)
    (hs_phi : s'.treePhi vSize = (t.findSubtree x).treePhi vSize) :
    (t.replaceSubtree x s').treeSize vSize = t.treeSize vSize ∧
    (t.replaceSubtree x s').treePhi vSize = t.treePhi vSize := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [replaceSubtree]
      by_cases heq : id = x
      · subst heq; simp only [findSubtree, ↓reduceIte] at hs_sz hs_phi ⊢; exact ⟨hs_sz, hs_phi⟩
      · simp only [heq, ↓reduceIte]
        have hnd' := hnd
        simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _⟩, hr_nd, hdisj_lr⟩
        by_cases hnl : x ∈ l.toList
        · have hnr : x ∉ r.toList := fun hr => hdisj_lr x (Or.inl hnl) x hr rfl
          have hrep_r : r.replaceSubtree x s' = r := AuxTree.replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree x = l.findSubtree x := by
            simp [findSubtree, heq, hnl]
          rcases ihl hl_nd hnl (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_l, hphi_l⟩
          rw [hrep_r]
          have hsz : (AuxTree.node id (l.replaceSubtree x s') r).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by
            simp [treeSize, hsz_l]
          have hrank : (AuxTree.node id (l.replaceSubtree x s') r).rank vSize =
              (AuxTree.node id l r).rank vSize := by
            simp only [rank, hsz]
          exact ⟨hsz, by simp [treePhi, hrank, hphi_l]⟩
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr
          have hrep_l : l.replaceSubtree x s' = l := AuxTree.replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree x = r.findSubtree x := by
            simp [findSubtree, heq, hnl]
          rcases ihr hr_nd hnr (by simpa [hfind] using hs_sz) (by simpa [hfind] using hs_phi) with
            ⟨hsz_r, hphi_r⟩
          rw [hrep_l]
          have hsz : (AuxTree.node id l (r.replaceSubtree x s')).treeSize vSize =
              (AuxTree.node id l r).treeSize vSize := by
            simp [treeSize, hsz_r]
          have hrank : (AuxTree.node id l (r.replaceSubtree x s')).rank vSize =
              (AuxTree.node id l r).rank vSize := by
            simp only [rank, hsz]
          exact ⟨hsz, by simp [treePhi, hrank, hphi_r]⟩

theorem AuxTree.replaceSubtree_depth_path {t s' : AuxTree} {x u : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList)
    (hs_perm : s'.toList.Perm (t.findSubtree x).toList)
    (hs_dp : ∀ z, s'.depthOf z = (t.findSubtree x).depthOf z ∧
      s'.pathTo z = (t.findSubtree x).pathTo z) :
    (t.replaceSubtree x s').depthOf u = t.depthOf u ∧
    (t.replaceSubtree x s').pathTo u = t.pathTo u := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      simp only [replaceSubtree]
      by_cases heq : id = x
      · subst heq; simp only [findSubtree, ↓reduceIte] at hs_dp ⊢; exact hs_dp u
      · simp only [heq, ↓reduceIte]
        have hnd' := hnd
        simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
          List.mem_singleton] at hnd'
        rcases hnd' with ⟨⟨hl_nd, _⟩, hr_nd, hdisj_lr⟩
        by_cases hnl : x ∈ l.toList
        · have hnr : x ∉ r.toList := fun hr => hdisj_lr x (Or.inl hnl) x hr rfl
          have hrep_r : r.replaceSubtree x s' = r := AuxTree.replaceSubtree_not_mem hnr
          have hfind : (AuxTree.node id l r).findSubtree x = l.findSubtree x := by
            simp [findSubtree, heq, hnl]
          have hs_perm_l : s'.toList.Perm (l.findSubtree x).toList := by simpa [hfind] using hs_perm
          have hl_perm : (l.replaceSubtree x s').toList.Perm l.toList :=
            AuxTree.replaceSubtree_perm hl_nd hnl hs_perm_l
          rcases ihl hl_nd hnl hs_perm_l (fun z => by simpa [hfind] using hs_dp z) with
            ⟨hd_l, hp_l⟩
          rw [hrep_r]
          simp only [depthOf, pathTo, hl_perm.mem_iff, hd_l, hp_l, and_self]
        · have hnr : x ∈ r.toList := by
            simp only [toList, List.mem_append, List.mem_singleton] at hx
            rcases hx with (hl | rfl) | hr
            · exact absurd hl hnl
            · exact absurd rfl heq
            · exact hr
          have hrep_l : l.replaceSubtree x s' = l := AuxTree.replaceSubtree_not_mem hnl
          have hfind : (AuxTree.node id l r).findSubtree x = r.findSubtree x := by
            simp [findSubtree, heq, hnl]
          have hs_perm_r : s'.toList.Perm (r.findSubtree x).toList := by simpa [hfind] using hs_perm
          have hr_perm : (r.replaceSubtree x s').toList.Perm r.toList :=
            AuxTree.replaceSubtree_perm hr_nd hnr hs_perm_r
          rcases ihr hr_nd hnr hs_perm_r (fun z => by simpa [hfind] using hs_dp z) with
            ⟨hd_r, hp_r⟩
          rw [hrep_l]
          simp only [depthOf, pathTo, hr_perm.mem_iff, hd_r, hp_r, and_self]

@[expose] def AuxTree.pushDownRoot : AuxTree → AuxTree
  | .leaf => .leaf
  | .node id l r => .node id l.revRoot r.revRoot

theorem AuxTree.pushDownRoot_rootId (t : AuxTree) : t.pushDownRoot.rootId = t.rootId := by
  cases t <;> rfl

theorem AuxTree.pushDownRoot_toList_perm (t : AuxTree) : t.pushDownRoot.toList.Perm t.toList := by
  cases t with
  | leaf => rfl
  | node id l r =>
      simp only [pushDownRoot, toList]
      exact (l.revRoot_toList_perm.append_right [id]).append r.revRoot_toList_perm

theorem AuxTree.pushDownRoot_treeSize (vSize : ℕ → ℕ) (t : AuxTree) :
    t.pushDownRoot.treeSize vSize = t.treeSize vSize := by
  cases t <;> simp [pushDownRoot, treeSize, revRoot_treeSize]

theorem AuxTree.pushDownRoot_treePhi (vSize : ℕ → ℕ) (t : AuxTree) :
    t.pushDownRoot.treePhi vSize = t.treePhi vSize := by
  cases t with
  | leaf => rfl
  | node id l r =>
      have hrank : (AuxTree.node id l.revRoot r.revRoot).rank vSize =
          (AuxTree.node id l r).rank vSize := by
        simp [rank, treeSize, l.revRoot_treeSize vSize, r.revRoot_treeSize vSize]
      simp [pushDownRoot, treePhi, hrank, l.revRoot_treePhi vSize, r.revRoot_treePhi vSize]

theorem AuxTree.pushDownRoot_depth_path {t : AuxTree} (hnd : t.toList.Nodup) (u : ℕ) :
    t.pushDownRoot.depthOf u = t.depthOf u ∧ t.pushDownRoot.pathTo u = t.pathTo u := by
  cases t with
  | leaf => exact ⟨rfl, rfl⟩
  | node id l r =>
      simp only [toList, List.nodup_append, List.nodup_cons] at hnd
      rcases hnd with ⟨⟨hl_nd, _⟩, hr_nd, _⟩
      simp only [pushDownRoot, depthOf, pathTo, l.revRoot_toList_perm.mem_iff,
        r.revRoot_toList_perm.mem_iff, l.revRoot_depthOf u hl_nd, r.revRoot_depthOf u hr_nd,
        l.revRoot_pathTo u hl_nd, r.revRoot_pathTo u hr_nd, and_self]

theorem AuxTree.parentIn_mem_and_depth {t : AuxTree} {x p₀ : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) :
    t.parentIn x p₀ ∈ t.toList ∧
    t.depthOf (t.parentIn x p₀) + 1 = t.depthOf x ∧
    t.pathTo x = t.pathTo (t.parentIn x p₀) ++ [x] := by
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
      simp only [parentIn, hne, ↓reduceIte]
      by_cases hnl : x ∈ l.toList
      · simp only [hnl, ↓reduceIte, depthOf, pathTo, Ne.symm hne]
        by_cases hxlr : x = l.rootId
        · cases l with
          | leaf => simp [toList] at hnl
          | node lid ll lr =>
              simp only [rootId] at hxlr
              subst hxlr
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
              simp only [rootId] at hxrr
              subst hxrr
              have hid_nin : id ∉ l.toList := hid_nin_l
              simp [parentIn, toList, depthOf, pathTo, hid_nin]
        · rcases ihr hr_nd hnr hxrr (p₀ := id) with ⟨hpm, hpd, hpp⟩
          have hpm_ne : r.parentIn x id ≠ id := fun h => hid_nin_r (h ▸ hpm)
          have hpm_nin_l : r.parentIn x id ∉ l.toList :=
            fun hl => hdisj_lr (r.parentIn x id) (Or.inl hl) (r.parentIn x id) hpm rfl
          refine ⟨by simp [toList, hpm], ?_, ?_⟩
          · simp [hpm_ne, hpm_nin_l, hpm, hpd, hnr]
          · simp [hpm_ne, hpm_nin_l, hpm, hpp, hnr]

theorem AuxTree.depthOf_le_of_mem_pathTo {t : AuxTree} {x u : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hu : u ∈ t.pathTo x) :
    t.depthOf u ≤ t.depthOf x ∧ (u = x ↔ t.depthOf u = t.depthOf x) := by
  induction t with
  | leaf => simp [pathTo] at hu
  | node id l r ihl ihr =>
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
      have hid_nin_l : id ∉ l.toList := fun h => hdisj_id_l id h id rfl rfl
      have hid_nin_r : id ∉ r.toList := fun h => hdisj_lr id (Or.inr rfl) id h rfl
      simp only [pathTo] at hu
      by_cases hxid : x = id
      · subst hxid
        simp only [↓reduceIte, List.mem_singleton] at hu
        subst hu; exact ⟨Nat.le_refl _, by simp⟩
      · by_cases hnl : x ∈ l.toList
        · simp only [hxid, hnl, ↓reduceIte, List.mem_cons] at hu
          rcases hu with rfl | hu'
          · simp [depthOf, hxid, hnl, Ne.symm hxid]
          · have hu_l : u ∈ l.toList := AuxTree.mem_pathTo hu'
            have hu_ne : u ≠ id := fun h => hid_nin_l (h ▸ hu_l)
            rcases ihl hl_nd hnl hu' with ⟨hle, heq⟩
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
          · have hu_r : u ∈ r.toList := AuxTree.mem_pathTo hu'
            have hu_ne : u ≠ id := fun h => hid_nin_r (h ▸ hu_r)
            have hu_nin_l : u ∉ l.toList := fun hl => hdisj_lr u (Or.inl hl) u hu_r rfl
            rcases ihr hr_nd hnr hu' with ⟨hle, heq⟩
            simp only [depthOf, hu_ne, hu_nin_l, hu_r, ↓reduceIte, hxid, hnl, hnr]
            exact ⟨Nat.succ_le_succ hle, by constructor <;> intro h <;> simp_all⟩

theorem AuxTree.depthOf_le_findSubtree {t : AuxTree} {x u : ℕ}
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hu : u ∈ (t.findSubtree x).toList) :
    t.depthOf x ≤ t.depthOf u := by
  induction t with
  | leaf => simp [toList] at hx
  | node id l r ihl ihr =>
      have hnd' := hnd
      simp only [toList, List.nodup_append, List.nodup_cons, List.mem_append,
        List.mem_singleton] at hnd'
      rcases hnd' with ⟨⟨hl_nd, _, hdisj_id_l⟩, hr_nd, hdisj_lr⟩
      have hid_nin_l : id ∉ l.toList := fun h => hdisj_id_l id h id rfl rfl
      have hid_nin_r : id ∉ r.toList := fun h => hdisj_lr id (Or.inr rfl) id h rfl
      by_cases hid_x : id = x
      · subst hid_x; simp [depthOf]
      · by_cases hnl : x ∈ l.toList
        · simp only [findSubtree, hid_x, hnl, ↓reduceIte] at hu
          have hu_l : u ∈ l.toList := AuxTree.findSubtree_subset hu
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
          have hu_r : u ∈ r.toList := AuxTree.findSubtree_subset hu
          have hu_ne : u ≠ id := fun h => hid_nin_r (h ▸ hu_r)
          have hu_nin_l : u ∉ l.toList := fun hl => hdisj_lr u (Or.inl hl) u hu_r rfl
          simp only [depthOf, Ne.symm hid_x, hnl, hnr, ↓reduceIte, hu_ne, hu_nin_l, hu_r]
          exact Nat.succ_le_succ (ihr hr_nd hnr hu)

theorem AuxTree.not_mem_findSubtree_of_ancestor {t : AuxTree} {px x u : ℕ}
    (hnd : t.toList.Nodup) (hpx : px ∈ t.toList) (hx : x ∈ t.toList)
    (hlt : t.depthOf px < t.depthOf x) (hu : u ∈ t.pathTo px) :
    u ∉ (t.findSubtree x).toList := by
  intro hu_sub
  have h1 := (AuxTree.depthOf_le_of_mem_pathTo hnd hpx hu).1
  have h2 := AuxTree.depthOf_le_findSubtree hnd hx hu_sub
  omega

theorem AuxTree.rootId_eq_zero_iff_leaf {t : AuxTree} {w h L : ℕ} {mem : ℕ → ℕ}
    {nodesBase cap p pp : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p pp) :
    t.rootId = 0 ↔ t = .leaf := by
  cases t with
  | leaf => simp [rootId]
  | node x l r =>
      rcases ht with ⟨hx1, _⟩
      simp only [rootId]
      constructor
      · intro h; omega
      · intro h; cases h

theorem TreeMemMatch.parent_pos_of_ne_root {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x : ℕ}
    {t : AuxTree} {p₀ pp₀ : ℕ}
    (ht : TreeMemMatch w h L mem nodesBase cap t p₀ pp₀)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) (hxr : x ≠ t.rootId) :
    1 ≤ t.parentIn x p₀ :=
  (ht.nodup_perm_mem (AuxTree.parentIn_mem_and_depth hnd hx hxr).1).1

theorem TreeMemMatch.parent_zero_iff_root {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap x pp₀ : ℕ}
    {t : AuxTree} (ht : TreeMemMatch w h L mem nodesBase cap t 0 pp₀)
    (hnd : t.toList.Nodup) (hx : x ∈ t.toList) :
    nodeField mem nodesBase x OFF_PARENT = 0 ↔ x = t.rootId := by
  rw [AuxTree.parentIn_eq_nodeField ht hx]
  by_cases hxr : x = t.rootId
  · subst hxr
    cases t with
    | leaf => simp [AuxTree.toList] at hx
    | node y l r => simp [AuxTree.rootId, AuxTree.parentIn]
  · have hpos := ht.parent_pos_of_ne_root hnd hx hxr
    simp only [hxr, iff_false]; omega

theorem TreeMemMatch.rootAggs {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap parId pp : ℕ}
    (h0 : SlotZeroOk mem nodesBase) {s : AuxTree}
    (hs : TreeMemMatch w h L mem nodesBase cap s parId pp) :
    nodeField mem nodesBase s.rootId OFF_VCNT =
      listVcnt mem nodesBase (s.evalInorder (revFlag mem nodesBase) false) ∧
    optIntVal mem h L (nodeField mem nodesBase s.rootId OFF_CSUM_FWD) =
      wrap h L (listRawCost (evalMemSteps mem nodesBase h L s false 0)) ∧
    optIntVal mem h L (nodeField mem nodesBase s.rootId OFF_CSUM_BWD) =
      wrap h L (-listRawCost (evalMemSteps mem nodesBase h L s false 0)) ∧
    nodeIntMinAgg1 mem nodesBase h L s.rootId =
      listIntMinAgg ((evalMemSteps mem nodesBase h L s false 0).map fun r => (r.nodeId, r.dirAvail)) ∧
    nodeIntMinAgg2 mem nodesBase h L s.rootId =
      listIntMinAgg ((evalMemSteps mem nodesBase h L s false 0).map fun r => (r.nodeId, r.flip.dirAvail)) := by
  cases s with
  | leaf =>
      simp only [AuxTree.rootId, AuxTree.evalInorder, evalMemSteps, listVcnt, listRawCost,
        listIntMinAgg, List.map_nil, List.sum_nil, neg_zero, nodeField, optIntVal,
        nodeIntMinAgg1, nodeIntMinAgg2]
      simp [h0 OFF_VCNT (by decide), h0 OFF_CSUM_FWD (by decide), h0 OFF_CSUM_BWD (by decide),
        h0 OFF_MIN1_HAS (by decide), h0 OFF_MIN1_VAL (by decide), h0 OFF_MIN1_FIRST (by decide),
        h0 OFF_MIN1_LAST (by decide), h0 OFF_MIN2_HAS (by decide), h0 OFF_MIN2_VAL (by decide),
        h0 OFF_MIN2_FIRST (by decide), h0 OFF_MIN2_LAST (by decide), wrap_of_fits (fits_zero h L)]
  | node y l r =>
      rcases hs with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
        _, _, _, _, _, _, _, _, _, _, ⟨hvc, hsf, hsb, _, hm1, hm2⟩, _, _⟩
      exact ⟨hvc, hsf, hsb, hm1, hm2⟩

theorem TreeMemMatch.listVcnt_lt_pow {w h L : ℕ} {mem : ℕ → ℕ} {nodesBase cap parId pp : ℕ}
    (hbase : nodesBase + NODE_STRIDE * (cap + 1) < 2 ^ w)
    {t : AuxTree} (ht : TreeMemMatch w h L mem nodesBase cap t parId pp) (hnd : t.toList.Nodup) :
    listVcnt mem nodesBase (t.evalInorder (revFlag mem nodesBase) false) < 2 ^ w := by
  have hlen : ∀ (seq : List ℕ), seq.Nodup → (∀ u ∈ seq, 1 ≤ u ∧ u ≤ cap) → seq.length ≤ cap := by
    intro seq hnd_s hb_s
    have hsub : seq.toFinset ⊆ ((List.range cap).map (· + 1)).toFinset := by
      intro u hu
      rw [List.mem_toFinset] at hu ⊢
      rcases hb_s u hu with ⟨hu1, hu2⟩
      exact List.mem_map.mpr ⟨u - 1, List.mem_range.mpr (by omega), by omega⟩
    have hc := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd_s] at hc
    have hc2 : ((List.range cap).map (· + 1)).toFinset.card ≤ cap := by
      calc ((List.range cap).map (· + 1)).toFinset.card
        _ ≤ ((List.range cap).map (· + 1)).length := List.toFinset_card_le _
        _ = cap := by simp
    omega
  have hle_len : ∀ seq, (∀ u ∈ seq, 1 ≤ u ∧ u ≤ cap) →
      (∀ u ∈ seq, nodeField mem nodesBase u OFF_ISV ≤ 1) →
      listVcnt mem nodesBase seq ≤ seq.length := by
    intro seq hb_s hisv
    induction seq with
    | nil => simp [listVcnt]
    | cons u us ih =>
        have h1 := hisv u (by simp)
        have h2 := ih (fun v hv => hb_s v (by simp [hv])) (fun v hv => hisv v (by simp [hv]))
        simp [listVcnt]; omega
  have hisv_t : ∀ u ∈ t.toList, nodeField mem nodesBase u OFF_ISV ≤ 1 := by
    clear hlen hle_len hnd
    induction t generalizing parId pp with
    | leaf => intro _ hu; simp [AuxTree.toList] at hu
    | node y l r ihl ihr =>
        rcases ht with ⟨_, _, _, _, _, _, _, hiv, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, _, _, _, _, hl, hr⟩
        intro u hu
        simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hu
        rcases hu with (hlm | rfl) | hrm
        · exact ihl hl u hlm
        · exact hiv
        · exact ihr hr u hrm
  have hperm := t.evalInorder_perm (revFlag mem nodesBase) false
  have hseq_nd : (t.evalInorder (revFlag mem nodesBase) false).Nodup := hperm.nodup_iff.2 hnd
  have hseq_b : ∀ u ∈ t.evalInorder (revFlag mem nodesBase) false, 1 ≤ u ∧ u ≤ cap :=
    fun u hu => ht.nodup_perm_mem (hperm.mem_iff.1 hu)
  have hseq_isv : ∀ u ∈ t.evalInorder (revFlag mem nodesBase) false,
      nodeField mem nodesBase u OFF_ISV ≤ 1 :=
    fun u hu => hisv_t u (hperm.mem_iff.1 hu)
  have h1 := hle_len _ hseq_b hseq_isv
  have h2 := hlen _ hseq_nd hseq_b
  unfold NODE_STRIDE at hbase
  omega

end AuxTreeSurgery

/-! ### Helper stepping lemmas and `SplayProgramOk` -/

section Helpers

theorem runs_seq_call_body_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body s : Stmt} {st : State} {vs : List ℕ} {B k T : ℕ}
    {Q_call : ℕ → (ℕ → ℕ) → Prop} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body)
    (hargs : evalArgs w st args = some vs)
    (hbody : ∀ pos, ∃ o st₁ c₁, Runs w p ω body (startState vs st.mem pos) o st₁ c₁ ∧
      Q_call o.value st₁.mem ∧ c₁ ≤ B)
    (hrest : ∀ v mem' pos', Q_call v mem' →
      ∃ o st' c₂, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c₂ ∧ Q o st' ∧ (k + argsSize args + B + 2) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hbody st.pos with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  rcases hrest o₁.value st₁.mem st₁.pos hq₁ with ⟨o₂, st', c₂, hr₂, hq₂, hc₂⟩
  have hcall : Runs w p ω (.call r f args) st .normal
      { st₁ with regs := Function.update st.regs r o₁.value } (argsSize args + c₁ + 1) :=
    runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl, rfl⟩
  have hst₁ : { st₁ with regs := Function.update st.regs r o₁.value } =
      { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos } := by
    cases st₁; rfl
  rw [hst₁] at hcall
  exact ⟨o₂, st', (argsSize args + c₁ + 1) + c₂ + 1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall, hr₂, rfl⟩), hq₂, by omega⟩

theorem runs_call_body_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {body : Stmt} {st : State} {vs : List ℕ} {B k T : ℕ}
    {Q_call : ℕ → (ℕ → ℕ) → Prop} {Q : Outcome → State → Prop}
    (hproc : p.procs[f]? = some body)
    (hargs : evalArgs w st args = some vs)
    (hbody : ∀ pos, ∃ o st₁ c₁, Runs w p ω body (startState vs st.mem pos) o st₁ c₁ ∧
      Q_call o.value st₁.mem ∧ c₁ ≤ B)
    (hpost : ∀ v mem' pos', Q_call v mem' →
      Q .normal { mem := mem', regs := Function.update st.regs r v, pos := pos' })
    (hc : k + argsSize args + B + 1 ≤ T) :
    ∃ o st' c, Runs w p ω (.call r f args) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  rcases hbody st.pos with ⟨o₁, st₁, c₁, hr₁, hq₁, hc₁⟩
  have hst₁ : { st₁ with regs := Function.update st.regs r o₁.value } =
      { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos } := by
    cases st₁; rfl
  refine ⟨.normal, { mem := st₁.mem, regs := Function.update st.regs r o₁.value, pos := st₁.pos },
    argsSize args + c₁ + 1, ?_, hpost o₁.value st₁.mem st₁.pos hq₁, by omega⟩
  rw [← hst₁]
  exact runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl, rfl⟩

end Helpers

public section

/-- Program-layout and arithmetic-contract predicate witnessing that `p` installs all `Num`
and splay bodies at `sp` for word size `w` and limb width `h`. -/
structure SplayProgramOk (w h : ℕ) (p : Program) (sp : SplayProcs) : Prop where
  hh : 0 < h
  hw : 2 * h + 2 ≤ w
  zero_ok : MeetsContract w p sp.numZero (zeroContract w h)
  copy_ok : MeetsContract w p sp.numCopy (copyContract w h)
  add_ok : MeetsContract w p sp.numAdd (addContract w h)
  sub_ok : MeetsContract w p sp.numSub (subtractContract w h)
  less_ok : MeetsContract w p sp.numLess (lessContract w h)
  equal_ok : MeetsContract w p sp.numEqual (equalContract w h)
  revNode_eq : p.procs[sp.revNode]? = some revNodeBody
  applyTag_eq : p.procs[sp.applyTag]? = some (applyTagBody sp)
  pushDown_eq : p.procs[sp.pushDown]? = some (pushDownBody sp)
  pull_eq : p.procs[sp.pull]? = some (pullBody sp)
  pushPath_eq : p.procs[sp.pushPath]? = some (pushPathBody sp)
  rotate_eq : p.procs[sp.rotate]? = some (rotateBody sp)
  splay_eq : p.procs[sp.splay]? = some (splayBody sp)

theorem splayProgramOk_of_hasAt {w h : ℕ} {p : Program} {b : ℕ}
    (hh : 0 < h) (hw : 2 * h + 2 ≤ w)
    (hp : p.HasAt b (splayBodies (SplayProcs.atBase b) h)) :
    SplayProgramOk w h p (SplayProcs.atBase b) := by
  have hw1 : 1 < 2 ^ w := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hb_lt : base h < 2 ^ w := base_lt_word hw
  dsimp only [splayBodies] at hp
  have hr6 := hasAt_append_right hp
  have hl5 := hasAt_append_left hp
  have hp5 := hasAt_append_right hl5
  have hl4 := hasAt_append_left hl5
  have hp4 := hasAt_append_right hl4
  have hl3 := hasAt_append_left hl4
  have hp3 := hasAt_append_right hl3
  have hl2 := hasAt_append_left hl3
  have hp2 := hasAt_append_right hl2
  have hl1 := hasAt_append_left hl2
  have hp1 := hasAt_append_right hl1
  have hp0 := hasAt_append_left hl1
  have hzero_len : (zeroModule (SplayProcs.atBase b).numZero).length = 1 := by
    simp [zeroModule]
  have hcopy_len : (copyModule (SplayProcs.atBase b).numCopy).length = 1 := by
    simp [copyModule]
  have hadd_len : (addModule (SplayProcs.atBase b).numAdd h).length = 2 := by
    simp [addModule, addCarryBody]
  have hsub_len : (subtractModule (SplayProcs.atBase b).numSub h).length = 5 := by
    simp [subtractModule, negateModule, addModule]
  have hless_len : (lessModule (SplayProcs.atBase b).numLess h).length = 3 := by
    simp [lessModule]
  have hequal_len : (equalModule (SplayProcs.atBase b).numEqual).length = 1 := by
    simp [equalModule]
  simp only [List.length_append, hzero_len, hcopy_len, hadd_len, hsub_len,
    hless_len, hequal_len] at hp1 hp2 hp3 hp4 hp5 hr6
  rw [show b + 1 + 1 = b + 2 by omega] at hp2
  rw [show b + 1 + 1 + 2 = b + 4 by omega] at hp3
  rw [show b + 1 + 1 + 2 + 5 = b + 9 by omega] at hp4
  rw [show b + 1 + 1 + 2 + 5 + 3 = b + 12 by omega] at hp5
  rw [show b + 1 + 1 + 2 + 5 + 3 + 1 = b + 13 by omega] at hr6
  refine ⟨hh, hw,
    zero_meetsContract (by simpa [SplayProcs.atBase] using hp0),
    copy_meetsContract hw1 (by simpa [SplayProcs.atBase] using hp1),
    add_meetsContract hh hw (by simpa [SplayProcs.atBase] using hp2),
    subtract_meetsContract hh hw (by simpa [SplayProcs.atBase] using hp3),
    less_meetsContract hh hw1 hb_lt (by simpa [SplayProcs.atBase] using hp4),
    equal_meetsContract hw1 (by simpa [SplayProcs.atBase] using hp5),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [SplayProcs.atBase] using hr6 0 (by simp)
  · simpa [SplayProcs.atBase] using hr6 1 (by simp)
  · simpa [SplayProcs.atBase] using hr6 2 (by simp)
  · simpa [SplayProcs.atBase] using hr6 3 (by simp)
  · simpa [SplayProcs.atBase] using hr6 4 (by simp)
  · simpa [SplayProcs.atBase] using hr6 5 (by simp)
  · simpa [SplayProcs.atBase] using hr6 6 (by simp)

end

end MinCostFlow.LinkCut.Prog
