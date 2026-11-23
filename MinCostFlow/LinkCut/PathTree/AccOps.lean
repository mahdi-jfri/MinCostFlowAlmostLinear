module

public import MinCostFlow.LinkCut.Gen.Cut
public import MinCostFlow.LinkCut.PathTree.Acc
import MinCostFlow.LinkCut.ForestSplices
import MinCostFlow.LinkCut.SplayLazy
import MinCostFlow.LinkCut.ForestModelSplice
import MinCostFlow.LinkCut.ForestExposeOps

/-!
# Which roots cut and link create

This file continues `PathTree.Acc` with the two operations that change the forest. For each, it
shows `RootAcc` with the nodes the program notes (`cutNotes`, `linkNotes`), and `Keep` with the
active nodes, so free nodes do not change.

For cut, the reroot and expose are handled by `lctPathSummary_rootAcc`. After that, the model
works in the exposed tree of `v` only. The push at the left child of `v` makes no new root,
because the tree keeps its root `v`. The splay of the edge slot makes the slot the new root.
Splitting off the two children makes the children roots. All of these nodes are noted.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- A nonzero child of a node of a tree is in the tree. -/
theorem SubtreeInv.child_mem {P : LctPayload α σ τ} {s : SplayState α σ τ} :
    ∀ {t : AuxTree} {rp z : ℕ}, SplayState.SubtreeInv P s rp t → z ∈ t.toList →
      ((s.nodes z).left ≠ 0 → (s.nodes z).left ∈ t.toList) ∧
      ((s.nodes z).right ≠ 0 → (s.nodes z).right ∈ t.toList)
  | .leaf, _, _, _, hz => by simp [AuxTree.toList] at hz
  | .node id l r, rp, z, h, hz => by
    obtain ⟨-, hl, hr, -, -, -, -, hsl, hsr⟩ := h
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz ⊢
    rcases hz with (hz | rfl) | hz
    · have := SubtreeInv.child_mem hsl hz
      exact ⟨fun h => Or.inl (Or.inl (this.1 h)), fun h => Or.inl (Or.inl (this.2 h))⟩
    · refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [hl] at h ⊢
        cases l with
        | leaf => simp [AuxTree.rootId] at h
        | node => exact Or.inl (Or.inl (AuxTree.rootId_mem (by simp)))
      · rw [hr] at h ⊢
        cases r with
        | leaf => simp [AuxTree.rootId] at h
        | node => exact Or.inr (AuxTree.rootId_mem (by simp))
    · have := SubtreeInv.child_mem hsr hz
      exact ⟨fun h => Or.inr (this.1 h), fun h => Or.inr (this.2 h)⟩

theorem keep_setPar (s : SplayState α σ τ) (x p : ℕ) :
    Keep s (s.setPar x p) (fun z => z = x) := keep_updateNode _ _ _

/-- `detachRootChildren x` changes only `x` and its nonzero children. -/
theorem keep_detachRootChildren (P : LctPayload α σ τ) (s : SplayState α σ τ) (x : ℕ) :
    Keep s (SplayState.detachRootChildren P s x) (fun z => z = x ∨
      (z ≠ 0 ∧ z = (s.nodes x).left) ∨ (z ≠ 0 ∧ z = (s.nodes x).right)) := by
  intro z hz
  push_neg at hz
  obtain ⟨hzx, hza, hzb⟩ := hz
  unfold SplayState.detachRootChildren
  split_ifs with h0
  · rfl
  unfold SplayState.pull
  rw [if_neg h0]
  dsimp only
  rw [SplayState.nodes_updateNode_ne _ hzx]
  simp only [SplayState.setRight, SplayState.setLeft, SplayState.nodes_updateNode_ne _ hzx]
  have hza' : ¬ (s.nodes x).left = 0 → z ≠ (s.nodes x).left := fun ha h =>
    hza (by rw [h]; exact ha) h
  have hzb' : ¬ (s.nodes x).right = 0 → z ≠ (s.nodes x).right := fun hb h =>
    hzb (by rw [h]; exact hb) h
  split_ifs <;>
    simp (disch := first | exact hza' ‹_› | exact hzb' ‹_›) only [SplayState.setPar,
      SplayState.setPpar, SplayState.nodes_updateNode_ne]

theorem mem_dcNotes {s : SplayState α σ τ} {x z : ℕ} {S : List ℕ} (hx : x ≠ 0)
    (hz : z = x ∨ z = (s.nodes x).left ∨ z = (s.nodes x).right) : z ∈ dcNotes s x S := by
  simp only [dcNotes, if_neg hx, mem_noteList]
  tauto

theorem subset_dcNotes (s : SplayState α σ τ) (x : ℕ) (S : List ℕ) : S ⊆ dcNotes s x S := by
  intro z hz
  unfold dcNotes
  split_ifs
  · exact hz
  · simp only [mem_noteList]; tauto

theorem mem_rerootExposeNotes_right {P : LctPayload α σ τ} {st : LctState α σ τ} {u v : ℕ}
    (S : List ℕ) (hv : v ≠ 0) : v ∈ rerootExposeNotes P st u v S :=
  mem_exposeNotes_self _ hv

theorem subset_rerootExposeNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)
    (S : List ℕ) : S ⊆ rerootExposeNotes P st u v S := fun _ h =>
  subset_exposeNotes P _ v _ (subset_exposeNotes P st u S h)

theorem subset_cutNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (S : List ℕ) :
    S ⊆ cutNotes P st u v S := by
  intro z hz
  unfold cutNotes
  split_ifs
  · exact hz
  · exact subset_dcNotes _ _ _ (subset_rerootExposeNotes P st u v S hz)
  · exact subset_rerootExposeNotes P st u v S hz

/-- `lctCut` notes every root it creates, and changes only active nodes. -/
theorem lctCut_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    (u v : ℕ) (I : List ℕ) :
    RootAcc st.splay (lctCut P st u v).splay (fun z => z ∈ cutNotes P st u v I) ∧
      Keep st.splay (lctCut P st u v).splay (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  by_cases hg : u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v
  · rw [lctCut_guard hg]
    exact ⟨RootAcc.refl _ _, fun _ _ => rfl⟩
  have hcn : cutNotes P st u v I = if ((cutMid P st u v).splay.nodes v).sz = 3 ∧
      cutUc P st u v = u then
      dcNotes (SplayState.splay P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v))
        (cutNe P st u v) (rerootExposeNotes P st u v I)
      else rerootExposeNotes P st u v I := by
    unfold cutNotes; rw [if_neg hg]
  push_neg at hg
  obtain ⟨hu0, hv0, huv, hnu, hnv⟩ := hg
  have hu_v : isVertex st.n u := ⟨by omega, hnu⟩
  have hv_v : isVertex st.n v := ⟨by omega, hnv⟩
  obtain ⟨tu, htu, hu⟩ := List.mem_flatMap.mp (isVertex_mem_active W hu_v)
  obtain ⟨tv, htv, hv⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv_v)
  -- The reroot and expose.
  obtain ⟨hRA₁, hK₁⟩ := lctPathSummary_rootAcc hL W htu hu hu_v htv hv I
  change RootAcc st.splay (cutMid P st u v).splay _ at hRA₁
  change Keep st.splay (cutMid P st u v).splay _ at hK₁
  rcases lctReroot_spec hL W htu hu hu_v with ⟨trees1, -, depth1, -, W1, hperm1, -⟩
  have hv1 : v ∈ trees1.flatMap AuxTree.toList :=
    hperm1.mem_iff.mpr (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)
  obtain ⟨tv1, htv1, hv1⟩ := List.mem_flatMap.mp hv1
  rcases lctExpose_spec hL W1 htv1 hv1 with
    ⟨trees2, Lv, ht2, W2, hperm2, -, -, hpp2, -, hrev2, -⟩
  change LctInvWith P (cutMid P st u v) trees2 fl depth1 at W2
  change ((cutMid P st u v).splay.nodes v).ppar = 0 at hpp2
  set t_exp := AuxTree.node v Lv .leaf with ht_exp
  have hact2 : ∀ z, z ∈ t_exp.toList → z ∈ trees.flatMap AuxTree.toList := fun z hz =>
    hperm1.mem_iff.mp (hperm2.mem_iff.mp (List.mem_flatMap.mpr ⟨t_exp, ht2, hz⟩))
  rw [lctCut_open hu0 hv0 huv hnu hnv]
  by_cases hsz : ((cutMid P st u v).splay.nodes v).sz = 3
  swap
  · rw [if_pos hsz, hcn, if_neg (fun h => hsz h.1)]
    exact ⟨hRA₁, hK₁⟩
  rw [if_neg (not_not.mpr hsz)]
  -- The push at the left child of `v`.
  have ht2_inv := W2.treesInv t_exp ht2
  have hl0_mem : cutL0 P st u v ∈ t_exp.toList := by
    have hcnt : (AuxTree.node v Lv AuxTree.leaf).countNodes = 3 := by
      rw [← hsz]; exact ht2_inv.sub.2.2.2.2.2.1.symm
    have hLv : Lv ≠ .leaf := by
      rintro rfl; simp [AuxTree.countNodes] at hcnt
    have hl : cutL0 P st u v = Lv.rootId := ht2_inv.sub.2.1
    rw [hl]
    simp [t_exp, AuxTree.toList, AuxTree.rootId_mem hLv]
  rcases SplayState.pushDown_preserves_TreeInv hL ht2_inv hl0_mem with
    ⟨hpd_inv, hpd_perm, hpd_rt, -, -, -, -, -, -, hpd_ppar, hpd_out, hpd_ev⟩
  set t_pd := SplayState.pushDownTree (cutMid P st u v).splay (cutL0 P st u v) t_exp
  change SplayState.TreeInv P (cutPd P st u v) t_pd at hpd_inv
  change ∀ z ∉ t_exp.toList, (cutPd P st u v).nodes z = _ at hpd_out
  have hK₂ : Keep (cutMid P st u v).splay (cutPd P st u v) (fun z => z ∈ t_exp.toList) :=
    fun z hz => hpd_out z hz
  have hRA₂ : RootAcc (cutMid P st u v).splay (cutPd P st u v) (fun z => z = v) := by
    refine rootAcc_of_keep hK₂ fun z hz h0 => ?_
    have := (SubtreeInv.root_of_par_zero hpd_inv.sub (hpd_perm.mem_iff.mpr hz) h0).1
    rw [this, hpd_rt]; rfl
  have hK₁₂ := hK₁.trans hK₂ (fun _ h => h) hact2
  by_cases huc : cutUc P st u v = u
  swap
  · rw [if_pos huc, hcn, if_neg (fun h => huc h.2)]
    refine ⟨hRA₁.trans hRA₂ (fun _ h => h) fun z hz => ?_, hK₁₂⟩
    exact (by rw [hz]; exact mem_rerootExposeNotes_right I hv0)
  rw [if_neg (not_not.mpr huc), hcn, if_pos ⟨hsz, huc⟩]
  dsimp only
  -- The splay of the edge slot.
  have hpd_ne : t_pd ≠ .leaf := by
    intro h
    have h1 := hpd_perm.length_eq
    rw [h] at h1
    simp [t_exp, AuxTree.toList] at h1
  obtain ⟨W3, -, -, -⟩ := replaceSameIds_spec W2 ht2 hpd_ne hpd_inv hpd_perm hpd_ev hpd_ppar
    hpd_out
  have hne_mem : cutNe P st u v ∈ t_pd.toList := by
    unfold cutNe
    split_ifs with hr
    · exact hpd_perm.mem_iff.mpr hl0_mem
    · exact (SubtreeInv.child_mem hpd_inv.sub (hpd_perm.mem_iff.mpr hl0_mem)).2 hr
  have hne0 : cutNe P st u v ≠ 0 := SubtreeInv.ne_zero hpd_inv.sub hne_mem
  obtain ⟨hRA₃, hK₃⟩ := splay_rootAcc hL W3 List.mem_cons_self hne_mem
  rcases lctSplayTree_spec hL W3 List.mem_cons_self hne_mem with
    ⟨t', -, -, hperm', -, -, -, W4, -⟩
  set s_cut := SplayState.splay P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v)
  change RootAcc (cutPd P st u v) s_cut _ at hRA₃
  change Keep (cutPd P st u v) s_cut _ at hK₃
  -- The split into three singletons.
  have hK₄ : Keep s_cut ((SplayState.detachRootChildren P s_cut (cutNe P st u v)).setPar
      (cutNe P st u v) st.freeHead) (fun z => z = cutNe P st u v ∨
        (z ≠ 0 ∧ z = (s_cut.nodes (cutNe P st u v)).left) ∨
        (z ≠ 0 ∧ z = (s_cut.nodes (cutNe P st u v)).right)) :=
    (keep_detachRootChildren P s_cut _).trans (keep_setPar _ _ _) (fun _ h => h)
      (fun _ h => Or.inl h)
  have ht'_inv := W4.treesInv t' List.mem_cons_self
  have hne' : cutNe P st u v ∈ t'.toList := hperm'.mem_iff.mpr hne_mem
  have hch := SubtreeInv.child_mem ht'_inv.sub hne'
  have hM₄ : ∀ z, (z = cutNe P st u v ∨
      (z ≠ 0 ∧ z = (s_cut.nodes (cutNe P st u v)).left) ∨
      (z ≠ 0 ∧ z = (s_cut.nodes (cutNe P st u v)).right)) → z ∈ t_exp.toList := by
    rintro z (rfl | ⟨h0, rfl⟩ | ⟨h0, rfl⟩)
    · exact hpd_perm.mem_iff.mp hne_mem
    · exact hpd_perm.mem_iff.mp (hperm'.mem_iff.mp (hch.1 h0))
    · exact hpd_perm.mem_iff.mp (hperm'.mem_iff.mp (hch.2 h0))
  have hRA₄ := rootAcc_of_keep hK₄ (N := fun z => z ∈ dcNotes s_cut (cutNe P st u v)
    (rerootExposeNotes P st u v I)) fun z hz _ => by
      rcases hz with h | ⟨-, h⟩ | ⟨-, h⟩
      · exact mem_dcNotes hne0 (Or.inl h)
      · exact mem_dcNotes hne0 (Or.inr (Or.inl h))
      · exact mem_dcNotes hne0 (Or.inr (Or.inr h))
  have hR := mem_rerootExposeNotes_right (P := P) (st := st) (u := u) I hv0
  have hRA₁₂ : RootAcc st.splay (cutPd P st u v)
      (fun z => z ∈ rerootExposeNotes P st u v I) :=
    hRA₁.trans hRA₂ (fun _ h => h) (fun z hz => by rw [hz]; exact hR)
  have hRA₁₃ : RootAcc st.splay s_cut (fun z => z ∈ dcNotes s_cut (cutNe P st u v)
      (rerootExposeNotes P st u v I)) :=
    hRA₁₂.trans hRA₃ (fun z hz => subset_dcNotes _ _ _ hz)
      (fun z hz => mem_dcNotes hne0 (Or.inl hz))
  exact ⟨hRA₁₃.trans hRA₄ (fun _ h => h) (fun _ h => h),
    (hK₁₂.trans hK₃ (fun _ h => h) (fun z hz => hact2 z (hpd_perm.mem_iff.mp hz))).trans hK₄
      (fun _ h => h) (fun z hz => hact2 z (hM₄ z hz))⟩

/-- `setPpar` changes neither parents nor summaries, so it makes no new root. -/
theorem rootAcc_setPpar (s : SplayState α σ τ) (x pp : ℕ) (N : ℕ → Prop) :
    RootAcc s (s.setPpar x pp) N := by
  intro z hz
  right
  simp only [SplayState.setPpar, SplayState.nodes_updateNode] at hz ⊢
  split_ifs at hz ⊢ with h
  · subst h; exact ⟨hz, rfl⟩
  · exact ⟨hz, rfl⟩

theorem lctLink_guard {P : LctPayload α σ τ} {st : LctState α σ τ} {u v : ℕ} {e : α}
    (h : u = 0 ∨ v = 0 ∨ u = v ∨ st.freeHead = 0) : lctLink P st u v e = st := by
  unfold lctLink lctLinkCost
  rw [if_pos (by simp only [beq_iff_eq, Bool.or_eq_true]; tauto)]

/-- `lctLink` notes every root it creates. It changes only active nodes and the free slot it
takes. -/
theorem lctLink_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {u v : ℕ} (hu_v : isVertex st.n u) (hv_v : isVertex st.n v) (e : α) (S : List ℕ) :
    RootAcc st.splay (lctLink P st u v e).splay (fun z => z ∈ linkNotes P st u v S) ∧
      Keep st.splay (lctLink P st u v e).splay
        (fun z => z ∈ trees.flatMap AuxTree.toList ∨ z = st.freeHead) := by
  by_cases hg : u = 0 ∨ v = 0 ∨ u = v ∨ st.freeHead = 0
  · rw [lctLink_guard hg]
    exact ⟨RootAcc.refl _ _, fun _ _ => rfl⟩
  have hln : linkNotes P st u v S =
      noteList (exposeNotes P (lctReroot P st v) u (exposeNotes P st v S)) st.freeHead := by
    unfold linkNotes; rw [if_neg hg]
  push_neg at hg
  obtain ⟨hu0, hv0, huv, hf0⟩ := hg
  rw [lctLink_eq hu0 hv0 huv hf0, hln]
  dsimp only
  have hu_act := isVertex_mem_active W hu_v
  obtain ⟨tv, htv, hv⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv_v)
  obtain ⟨hRA₁, hK₁⟩ := lctReroot_rootAcc hL W htv hv S
  rcases lctReroot_spec hL W htv hv hv_v with ⟨trees1, -, depth1, -, W1, hperm1, -⟩
  change LctInvWith P (lctReroot P st v) trees1 fl depth1 at W1
  obtain ⟨tu, htu, hu⟩ := List.mem_flatMap.mp (hperm1.mem_iff.mpr hu_act)
  obtain ⟨hRA₂, hK₂⟩ := lctReroot_rootAcc hL W1 htu hu (exposeNotes P st v S)
  change RootAcc _ (linkMid P st u v).splay _ at hRA₂
  change Keep _ (linkMid P st u v).splay _ at hK₂
  have hK₃ : Keep (linkMid P st u v).splay
      (SplayState.makeSingleton P (linkMid P st u v).splay st.freeHead e u)
      (fun z => z = st.freeHead) := by
    unfold SplayState.makeSingleton SplayState.setNode; exact keep_updateNode _ _ _
  have hRA₃ := rootAcc_one hK₃ (N := fun z => z ∈ noteList
    (exposeNotes P (lctReroot P st v) u (exposeNotes P st v S)) st.freeHead)
    (mem_noteList.mpr (Or.inr rfl))
  have hK₄ : Keep (SplayState.makeSingleton P (linkMid P st u v).splay st.freeHead e u)
      ((SplayState.makeSingleton P (linkMid P st u v).splay st.freeHead e u).setPpar v
        st.freeHead) (fun z => z = v) := keep_updateNode _ _ _
  refine ⟨((hRA₁.trans hRA₂ (fun z hz => subset_exposeNotes P _ u _ hz) (fun _ h => h)).trans
      hRA₃ (fun z hz => mem_noteList.mpr (Or.inl hz)) (fun _ h => h)).trans
      (rootAcc_setPpar _ _ _ _) (fun _ h => h) (fun _ h => h), ?_⟩
  exact ((hK₁.trans hK₂ (fun _ h => Or.inl h)
    (fun z hz => Or.inl (hperm1.mem_iff.mp hz))).trans hK₃ (fun _ h => h)
    (fun _ h => Or.inr h)).trans hK₄ (fun _ h => h) (fun z hz => Or.inl (hz ▸ List.mem_flatMap.mpr ⟨tv, htv, hv⟩))

end MinCostFlow.LinkCut.Gen
