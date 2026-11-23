module

public import MinCostFlow.LinkCut.Gen.Reroot
public import MinCostFlow.LinkCut.ForestExposeSpec
import MinCostFlow.LinkCut.ForestReversals
import MinCostFlow.LinkCut.ForestModelOps

/-!
# Which roots an expose creates

Find-ready keeps a stack of noted nodes, with the invariant that every auxiliary-tree root with
a ready summary is on the stack. The tree programs note nodes in `detachRight` (`drNotes`). This
file shows, in the model, that this is enough for `lctExpose`: after the expose, every node with
`par = 0` was noted, or it had `par = 0` before and its summary did not change
(`lctExpose_rootAcc`). It also shows that nodes outside the auxiliary trees do not change.

`RootAcc s s' N` says the first fact for one change of state with noted set `N`; `Keep s s' M`
says that nodes outside `M` do not change. Both compose along a run.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- Every root of `s'` is noted, or was a root of `s` with the same summary. -/
def RootAcc (s s' : SplayState α σ τ) (N : ℕ → Prop) : Prop :=
  ∀ z, (s'.nodes z).par = 0 → N z ∨ ((s.nodes z).par = 0 ∧ (s'.nodes z).sum = (s.nodes z).sum)

/-- Nodes outside `M` do not change. -/
def Keep (s s' : SplayState α σ τ) (M : ℕ → Prop) : Prop :=
  ∀ z, ¬ M z → s'.nodes z = s.nodes z

theorem RootAcc.trans {s₀ s₁ s₂ : SplayState α σ τ} {N₁ N₂ N : ℕ → Prop}
    (h₁ : RootAcc s₀ s₁ N₁) (h₂ : RootAcc s₁ s₂ N₂) (hN₁ : ∀ z, N₁ z → N z)
    (hN₂ : ∀ z, N₂ z → N z) : RootAcc s₀ s₂ N := by
  intro z hz
  rcases h₂ z hz with h | ⟨hp, hs⟩
  · exact Or.inl (hN₂ z h)
  · rcases h₁ z hp with h | ⟨hp', hs'⟩
    · exact Or.inl (hN₁ z h)
    · exact Or.inr ⟨hp', hs.trans hs'⟩

theorem RootAcc.refl (s : SplayState α σ τ) (N : ℕ → Prop) : RootAcc s s N :=
  fun _ hz => Or.inr ⟨hz, rfl⟩

theorem Keep.trans {s₀ s₁ s₂ : SplayState α σ τ} {M₁ M₂ M : ℕ → Prop}
    (h₁ : Keep s₀ s₁ M₁) (h₂ : Keep s₁ s₂ M₂) (hM₁ : ∀ z, M₁ z → M z)
    (hM₂ : ∀ z, M₂ z → M z) : Keep s₀ s₂ M :=
  fun z hz => (h₂ z fun h => hz (hM₂ z h)).trans (h₁ z fun h => hz (hM₁ z h))

/-- If nodes outside `M` do not change and every root in `M` is noted, then `RootAcc`. -/
theorem rootAcc_of_keep {s s' : SplayState α σ τ} {M N : ℕ → Prop} (hk : Keep s s' M)
    (hM : ∀ z, M z → (s'.nodes z).par = 0 → N z) : RootAcc s s' N := by
  intro z hz
  by_cases h : M z
  · exact Or.inl (hM z h hz)
  · have := hk z h
    exact Or.inr ⟨by rw [← this]; exact hz, by rw [this]⟩

/-- In a tree that meets `SubtreeInv`, only the root can have parent `0`, and then the parent
given to `SubtreeInv` is `0`. Every node of the tree is nonzero. -/
theorem SubtreeInv.root_of_par_zero {P : LctPayload α σ τ} {s : SplayState α σ τ} :
    ∀ {t : AuxTree} {rp z : ℕ}, SplayState.SubtreeInv P s rp t → z ∈ t.toList →
      (s.nodes z).par = 0 → z = t.rootId ∧ rp = 0
  | .leaf, _, _, _, hz, _ => by simp [AuxTree.toList] at hz
  | .node id l r, rp, z, h, hz, h0 => by
    obtain ⟨hid, -, -, hpar, -, -, -, hl, hr⟩ := h
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | hz
    · exact absurd (SubtreeInv.root_of_par_zero hl hz h0).2 hid
    · exact ⟨rfl, hpar ▸ h0⟩
    · exact absurd (SubtreeInv.root_of_par_zero hr hz h0).2 hid

theorem SubtreeInv.ne_zero {P : LctPayload α σ τ} {s : SplayState α σ τ} :
    ∀ {t : AuxTree} {rp z : ℕ}, SplayState.SubtreeInv P s rp t → z ∈ t.toList → z ≠ 0
  | .leaf, _, _, _, hz => by simp [AuxTree.toList] at hz
  | .node id l r, rp, z, h, hz => by
    obtain ⟨hid, -, -, -, -, -, -, hl, hr⟩ := h
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | hz
    · exact SubtreeInv.ne_zero hl hz
    · exact hid
    · exact SubtreeInv.ne_zero hr hz

/-- A node of an auxiliary tree with parent `0` is the root of that tree. -/
theorem _root_.MinCostFlow.LinkCut.LctInvWith.root_of_par_zero {P : LctPayload α σ τ} {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {t : AuxTree} (ht : t ∈ trees) {z : ℕ} (hz : z ∈ t.toList)
    (h0 : (st.splay.nodes z).par = 0) : z = t.rootId :=
  (SubtreeInv.root_of_par_zero (W.treesInv t ht).sub hz h0).1

/-- `attachRight u x` changes only the nodes `u` and `x`. -/
theorem attachRight_keep (P : LctPayload α σ τ) (s : SplayState α σ τ) (u x : ℕ) :
    Keep s (SplayState.attachRight P s u x) fun z => z = u ∨ z = x := by
  intro z hz
  push_neg at hz
  by_cases hu : u = 0
  · simp [SplayState.attachRight, hu]
  rw [attachRight_eq hu]
  unfold SplayState.pull attachRightMid
  rw [if_neg hu]
  split_ifs <;>
    simp [SplayState.setRight, SplayState.setPar, SplayState.setPpar,
      SplayState.nodes_updateNode_ne _ hz.1, SplayState.nodes_updateNode_ne _ hz.2]

/-- Splaying `x` in tree `t`: the only new root is `x`, and nodes outside `t` do not change. -/
theorem splay_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {t : AuxTree} {x : ℕ} (ht : t ∈ trees) (hx : x ∈ t.toList) :
    RootAcc st.splay (SplayState.splay P st.splay (2 * st.n + 1) x) (fun z => z = x) ∧
      Keep st.splay (SplayState.splay P st.splay (2 * st.n + 1) x) (fun z => z ∈ t.toList) := by
  rcases lctSplayTree_spec hL W ht hx with
    ⟨t', -, hrt, hperm, -, -, -, hW1, -, -, -, hout, -⟩
  have hk : Keep st.splay (SplayState.splay P st.splay (2 * st.n + 1) x)
      (fun z => z ∈ t.toList) := fun z hz => hout z hz
  refine ⟨rootAcc_of_keep hk fun z hz h0 => ?_, hk⟩
  have := hW1.root_of_par_zero List.mem_cons_self (hperm.mem_iff.mpr hz) h0
  rw [this, hrt]

/-- `detachRight x` then `attachRight x prev.rootId`, as in one step of the expose loop: the
only new roots are `x` and the old right child of `x`. Nodes outside the two trees do not
change. -/
theorem detachAttach_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {x : ℕ} {L R prev : AuxTree}
    (ht : AuxTree.node x L R ∈ trees) (hprev : prev ∈ trees)
    (hne : AuxTree.node x L R ≠ prev)
    (hrev : (st.splay.nodes x).rev = false) (htag : (st.splay.nodes x).tag = P.idTag)
    (hpp : (st.splay.nodes prev.rootId).ppar = x) :
    let s₂ := SplayState.attachRight P (SplayState.detachRight P st.splay x) x prev.rootId
    RootAcc st.splay s₂ (fun z => z = x ∨ (z ≠ 0 ∧ z = (st.splay.nodes x).right)) ∧
      Keep st.splay s₂ (fun z => z ∈ (AuxTree.node x L R).toList ∨ z ∈ prev.toList) := by
  intro s₂
  have hTI := W.treesInv _ ht
  have hdet := SplayState.detachRight_preserves hL hTI hrev htag
  have hout₁ := hdet.2.2.2.2.2.2.2
  have hexp := exposeStep_heavy_light hL W ht hprev hne hrev htag hpp
  have hW₂ := hexp.1
  have hk : Keep st.splay s₂ (fun z => z ∈ (AuxTree.node x L R).toList ∨ z ∈ prev.toList) := by
    intro z hz
    push_neg at hz
    have hzx : z ≠ x := fun h => hz.1 (by simp [AuxTree.toList, h])
    have hzp : z ≠ prev.rootId := fun h => hz.2 (h ▸ AuxTree.rootId_mem (W.treesNonEmpty _ hprev))
    rw [attachRight_keep P _ x prev.rootId z (by push_neg; exact ⟨hzx, hzp⟩)]
    exact hout₁ z hz.1
  refine ⟨rootAcc_of_keep hk fun z hz h0 => ?_, hk⟩
  have hright : (st.splay.nodes x).right = R.rootId := hTI.sub.2.2.1
  -- the trees after the step
  have hnodup := hTI.nodup
  have hx_nR : x ∉ R.toList := by
    simp only [AuxTree.toList] at hnodup
    intro h
    have := List.nodup_append.mp hnodup
    exact this.2.2 x (by simp) x h rfl
  rcases hz with hz | hz
  · simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | hz) | hz
    · left
      have := hW₂.root_of_par_zero (t := AuxTree.node x L prev) List.mem_cons_self
        (by simp [AuxTree.toList, hz]) h0
      exact this
    · exact Or.inl hz
    · -- `z` is in the old right subtree, which is a tree of its own now
      right
      have hRne : R ≠ AuxTree.leaf := by rintro rfl; simp [AuxTree.toList] at hz
      have hR_ne_tL : R ≠ AuxTree.node x L AuxTree.leaf := by
        rintro rfl; exact hx_nR (by simp [AuxTree.toList])
      have hR_ne_prev : R ≠ prev := by
        rintro rfl
        have hzT : z ∈ (AuxTree.node x L R).toList := by simp [AuxTree.toList, hz]
        exact hne (flatMap_mem_unique W.activeNodup ht hprev hzT hz)
      have hRmem : R ∈ ((if R = AuxTree.leaf then trees else AuxTree.node x L AuxTree.leaf :: R ::
          trees.erase (AuxTree.node x L R)).erase (AuxTree.node x L AuxTree.leaf)).erase prev := by
        rw [if_neg hRne]
        refine (List.mem_erase_of_ne hR_ne_prev).mpr ((List.mem_erase_of_ne hR_ne_tL).mpr ?_)
        simp
      have := hW₂.root_of_par_zero (List.mem_cons_of_mem _ hRmem) hz h0
      exact ⟨SubtreeInv.ne_zero (hW₂.treesInv _ (List.mem_cons_of_mem _ hRmem)).sub hz,
        this.trans hright.symm⟩
  · left
    exact hW₂.root_of_par_zero (t := AuxTree.node x L prev) List.mem_cons_self
      (by simp [AuxTree.toList, hz]) h0

end MinCostFlow.LinkCut.Gen

namespace MinCostFlow.LinkCut.Gen

open MinCostFlow.LinkCut

variable {α σ τ : Type*}

theorem mem_drNotes_self {s : SplayState α σ τ} {x : ℕ} {S : List ℕ} (hx : x ≠ 0) :
    x ∈ drNotes s x S := by
  unfold drNotes
  rw [if_neg hx]
  split_ifs <;> simp [mem_noteList]

theorem mem_drNotes_right {s : SplayState α σ τ} {x : ℕ} {S : List ℕ} (hx : x ≠ 0)
    (hr : (s.nodes x).right ≠ 0) : (s.nodes x).right ∈ drNotes s x S := by
  unfold drNotes
  rw [if_neg hx, if_neg hr]
  simp [mem_noteList]

theorem subset_drNotes (s : SplayState α σ τ) (x : ℕ) (S : List ℕ) : S ⊆ drNotes s x S := by
  intro z hz
  unfold drNotes
  split_ifs <;> simp [mem_noteList, hz]

theorem subset_exposeLoopNotes (P : LctPayload α σ τ) :
    ∀ (k : ℕ) (st : LctState α σ τ) (last : ℕ) (S : List ℕ), S ⊆ exposeLoopNotes P st k last S
  | 0, _, _, _ => fun _ h => h
  | k + 1, st, last, S => by
    intro z hz
    unfold exposeLoopNotes
    split_ifs
    · exact hz
    · exact subset_exposeLoopNotes P k _ _ _ (subset_drNotes _ _ _ hz)

/-- One step of the expose loop notes every root it creates, and changes only nodes of the
auxiliary trees. -/
theorem exposeStep_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {t_prev : AuxTree} {last : ℕ} (ht_prev : t_prev ∈ trees) (ht_rt : t_prev.rootId = last)
    (hp_nz : (st.splay.nodes last).ppar ≠ 0) (S : List ℕ) :
    RootAcc st.splay (lctExposeStep P st last).1.splay
        (fun z => z ∈ drNotes (SplayState.splay P st.splay (2 * st.n + 1)
          (st.splay.nodes last).ppar) (st.splay.nodes last).ppar S) ∧
      Keep st.splay (lctExposeStep P st last).1.splay
        (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  set p := (st.splay.nodes last).ppar with hp_def
  set active := trees.flatMap AuxTree.toList with hactive
  set par0 := inducedSubPar P st.splay trees with hpar0
  have hp_act : p ∈ active := by
    rw [hp_def, ← ht_rt]
    exact W.pparActive t_prev ht_prev (by rw [ht_rt, ← hp_def]; exact hp_nz)
  rcases List.mem_flatMap.mp hp_act with ⟨tp, htp, hp_tp⟩
  let h_prev := listHead0 (treeIds P st.splay t_prev)
  have hh_mem : h_prev ∈ t_prev.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty t_prev ht_prev)
  have hh_act : h_prev ∈ active := List.mem_flatMap.mpr ⟨t_prev, ht_prev, hh_mem⟩
  have hpar_h : par0 h_prev = p := by
    rw [hpar0, inducedSubPar_eq_of_mem (P := P) (s := st.splay) W.activeNodup ht_prev hh_mem]
    have hne : treeIds P st.splay t_prev ≠ [] := treeIds_ne_nil (W.treesNonEmpty t_prev ht_prev)
    cases hids : treeIds P st.splay t_prev with
    | nil => exact absurd hids hne
    | cons a rest => simp [h_prev, listHead0, hids, chainPred, ht_rt, hp_def]
  have htp_ne : tp ≠ t_prev := by
    intro heq
    have hp_prev : p ∈ t_prev.toList := heq ▸ hp_tp
    have hrc := tree_reaches_head W ht_prev hp_prev
    have hle := depth_le_of_reaches (fun _ hx hp => W.subPar_mem_active hx hp) W.acyclic
      active.length h_prev p hrc hp_act
    have hlt := W.acyclic h_prev hh_act (by rw [← hpar0, hpar_h]; exact hp_nz)
    rw [← hpar0, hpar_h] at hlt
    omega
  obtain ⟨hRA₁, hK₁⟩ := splay_rootAcc hL W htp hp_tp
  rcases lctSplayTree_spec hL W htp hp_tp with
    ⟨tp', htp'_ne, htp'_rt, htp'_perm, -, hrev_p, htag_p, hW1, -, -, -, hout1, -⟩
  cases htp'_eq : tp' with
  | leaf => exact absurd htp'_eq htp'_ne
  | node pr L R =>
    have hpr : pr = p := by simpa [htp'_eq, AuxTree.rootId] using htp'_rt
    rw [hpr] at htp'_eq
    let trees1 := AuxTree.node p L R :: trees.erase tp
    have htp'_mem : AuxTree.node p L R ∈ trees1 := List.mem_cons_self
    have ht_prev_er : t_prev ∈ trees.erase tp := (List.mem_erase_of_ne htp_ne.symm).mpr ht_prev
    have ht_prev_1 : t_prev ∈ trees1 := List.mem_cons_of_mem _ ht_prev_er
    have htp'_ne_prev : AuxTree.node p L R ≠ t_prev := fun h => by
      have hp_mem : p ∈ t_prev.toList := h ▸ (by simp [AuxTree.toList])
      exact htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hp_tp hp_mem)
    have hW1' : LctInvWith P (LctState.mk st.n (SplayState.splay P st.splay (2 * st.n + 1) p)
        st.freeHead) trees1 fl d := by simpa [trees1, htp'_eq] using hW1
    have hdisj : ∀ w ∈ t_prev.toList, w ∉ tp.toList := fun w hw hm =>
      htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hm hw)
    have hpp_prev1 : ((SplayState.splay P st.splay (2 * st.n + 1) p).nodes
        t_prev.rootId).ppar = p := by
      rw [hout1 t_prev.rootId (hdisj _ (AuxTree.rootId_mem (W.treesNonEmpty t_prev ht_prev))),
        ht_rt]
    obtain ⟨hRA₂, hK₂⟩ := detachAttach_rootAcc hL hW1' htp'_mem ht_prev_1 htp'_ne_prev hrev_p
      htag_p hpp_prev1
    have hstep : (lctExposeStep P st last).1.splay = SplayState.attachRight P
        (SplayState.detachRight P (SplayState.splay P st.splay (2 * st.n + 1) p) p)
        p t_prev.rootId := by
      rw [lctExposeStep_splay, ← hp_def, ht_rt]
    rw [hstep]
    have hperm : ∀ z, z ∈ (AuxTree.node p L R).toList → z ∈ tp.toList := fun z hz =>
      htp'_perm.mem_iff.mp (by rw [htp'_eq]; exact hz)
    refine ⟨hRA₁.trans hRA₂ (fun z hz => by subst hz; exact mem_drNotes_self hp_nz) ?_, hK₁.trans hK₂
      (fun z hz => List.mem_flatMap.mpr ⟨tp, htp, hz⟩) ?_⟩
    · rintro z (rfl | ⟨hz0, rfl⟩)
      · exact mem_drNotes_self hp_nz
      · exact mem_drNotes_right hp_nz hz0
    · rintro z (hz | hz)
      · exact List.mem_flatMap.mpr ⟨tp, htp, hperm z hz⟩
      · exact List.mem_flatMap.mpr ⟨t_prev, ht_prev, hz⟩

/-- `detachRight x` at the root of a tree: the only new roots are `x` and its old right child. -/
theorem detachRight_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {x : ℕ} {L R : AuxTree} (ht : AuxTree.node x L R ∈ trees)
    (hrev : (st.splay.nodes x).rev = false) (htag : (st.splay.nodes x).tag = P.idTag) :
    RootAcc st.splay (SplayState.detachRight P st.splay x)
        (fun z => z = x ∨ (z ≠ 0 ∧ z = (st.splay.nodes x).right)) ∧
      Keep st.splay (SplayState.detachRight P st.splay x)
        (fun z => z ∈ (AuxTree.node x L R).toList) := by
  have hTI := W.treesInv _ ht
  have hout := (SplayState.detachRight_preserves hL hTI hrev htag).2.2.2.2.2.2.2
  have hW₁ := (detachRight_spec hL W ht hrev htag).1
  have hk : Keep st.splay (SplayState.detachRight P st.splay x)
      (fun z => z ∈ (AuxTree.node x L R).toList) := fun z hz => hout z hz
  refine ⟨rootAcc_of_keep hk fun z hz h0 => ?_, hk⟩
  have hright : (st.splay.nodes x).right = R.rootId := hTI.sub.2.2.1
  simp only [AuxTree.toList, List.mem_append, List.mem_singleton] at hz
  by_cases hR : R = AuxTree.leaf
  · subst hR
    simp only [AuxTree.toList, List.not_mem_nil, or_false] at hz
    left
    have := hW₁.root_of_par_zero (t := AuxTree.node x L AuxTree.leaf) (by simpa using ht)
      (by simp [AuxTree.toList, hz]) h0
    exact this
  have hmem : ∀ t, t = AuxTree.node x L AuxTree.leaf ∨ t = R → t ∈
      (if R = AuxTree.leaf then trees else AuxTree.node x L AuxTree.leaf :: R ::
        trees.erase (AuxTree.node x L R)) := by
    rintro t (rfl | rfl) <;> simp [hR]
  rcases hz with (hz | hz) | hz
  · exact Or.inl (hW₁.root_of_par_zero (hmem _ (Or.inl rfl)) (by simp [AuxTree.toList, hz]) h0)
  · exact Or.inl hz
  · right
    exact ⟨SubtreeInv.ne_zero (hW₁.treesInv _ (hmem _ (Or.inr rfl))).sub hz,
      (hW₁.root_of_par_zero (hmem _ (Or.inr rfl)) hz h0).trans hright.symm⟩

/-- The expose loop notes every root it creates, and changes only nodes of the auxiliary
trees. -/
theorem exposeLoop_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) :
    ∀ (fuel : ℕ) {st : LctState α σ τ} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
      {t_last : AuxTree} {last v : ℕ} {par0 : ℕ → ℕ} {active0 : List ℕ},
      LctInvWith P st trees fl d → t_last ∈ trees → t_last.rootId = last →
      v ∈ t_last.toList → listLast0 (treeIds P st.splay t_last) = v →
      (∀ z, inducedSubPar P st.splay trees z = par0 z) →
      (trees.flatMap AuxTree.toList).Perm active0 → ∀ S : List ℕ,
      RootAcc st.splay (lctExposeLoop P st fuel last).1.splay
          (fun z => z ∈ exposeLoopNotes P st fuel last S) ∧
        Keep st.splay (lctExposeLoop P st fuel last).1.splay (fun z => z ∈ active0)
  | 0, st, _, _, _, _, last, _, _, _, _, _, _, _, _, _, _, S => by
    exact ⟨RootAcc.refl _ _, fun _ _ => rfl⟩
  | fuel + 1, st, trees, fl, d, t_last, last, v, par0, active0, W, ht_last, ht_rt, hv_last,
      hlast, hpar_eq, hact_perm0, S => by
    by_cases hp0 : (st.splay.nodes last).ppar = 0
    · have h1 : (lctExposeLoop P st (fuel + 1) last).1 = st := by
        simp [lctExposeLoop, hp0]
      have h2 : exposeLoopNotes P st (fuel + 1) last S = S := by
        simp [exposeLoopNotes, hp0]
      rw [h1, h2]
      exact ⟨RootAcc.refl _ _, fun _ _ => rfl⟩
    rcases lctExposeStep_spec hL W ht_last ht_rt hv_last hlast hp0 par0 hpar_eq active0
      hact_perm0 with
      ⟨trees1, L1, ht1_mem, hv1, hW1, hact_perm1, hpar1, -, hlast1, -⟩
    obtain ⟨hRA, hK⟩ := exposeStep_rootAcc hL W ht_last ht_rt hp0 S
    obtain ⟨hRA', hK'⟩ := exposeLoop_rootAcc hL fuel hW1 ht1_mem rfl hv1 hlast1 hpar1 hact_perm1
      (drNotes (SplayState.splay P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar)
        (st.splay.nodes last).ppar S)
    have h1 : (lctExposeLoop P st (fuel + 1) last).1 =
        (lctExposeLoop P (lctExposeStep P st last).1 fuel (st.splay.nodes last).ppar).1 := by
      simp [lctExposeLoop, hp0, lctExposeStep]
    have h2 : exposeLoopNotes P st (fuel + 1) last S =
        exposeLoopNotes P (lctExposeStep P st last).1 fuel (st.splay.nodes last).ppar
          (drNotes (SplayState.splay P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar)
            (st.splay.nodes last).ppar S) := by
      simp [exposeLoopNotes, hp0]
    rw [h1, h2]
    exact ⟨hRA.trans hRA' (fun z hz => subset_exposeLoopNotes P _ _ _ _ hz) (fun _ h => h),
      hK.trans hK' (fun z hz => hact_perm0.mem_iff.mp hz) (fun _ h => h)⟩

/-- `lctExpose` notes every root it creates (`exposeNotes`), and changes only nodes of the
auxiliary trees. -/
theorem lctExpose_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) (S : List ℕ) :
    RootAcc st.splay (lctExpose P st v).splay (fun z => z ∈ exposeNotes P st v S) ∧
      Keep st.splay (lctExpose P st v).splay (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  have hv0 : v ≠ 0 := SubtreeInv.ne_zero (W.treesInv _ htv).sub hv
  set F := 2 * st.n + 1 with hF
  set s0 := SplayState.splay P st.splay F v with hs0
  obtain ⟨hRA₀, hK₀⟩ := splay_rootAcc hL W htv hv
  rcases lctSplayTree_spec hL W htv hv with
    ⟨t0', ht0'_ne, ht0'_rt, ht0'_perm, -, hrev0, htag0, hW0, -, -, -, -, -⟩
  cases ht0'_eq : t0' with
  | leaf => exact absurd ht0'_eq ht0'_ne
  | node vr L0 R0 =>
    have hvr : vr = v := by simpa [ht0'_eq, AuxTree.rootId] using ht0'_rt
    rw [hvr] at ht0'_eq
    have hW0' : LctInvWith P (LctState.mk st.n s0 st.freeHead)
        (AuxTree.node v L0 R0 :: trees.erase tv) fl d := by simpa [ht0'_eq] using hW0
    obtain ⟨hRA₁, hK₁⟩ := detachRight_rootAcc hL hW0' List.mem_cons_self hrev0 htag0
    rcases lctExposeInit_spec hL W htv hv with
      ⟨trees1, L1, ht1_mem, hv1, hW1, hact_perm1, hpar1, -, hlast1, -⟩
    obtain ⟨hRA₂, hK₂⟩ := exposeLoop_rootAcc hL F hW1 ht1_mem rfl hv1 hlast1 hpar1 hact_perm1
      (drNotes s0 v S)
    have hfuel : 2 * st.n - (AuxTree.node v L1 AuxTree.leaf).treeSize
        (vSize P (exposeStart P st v).splay (trees1.flatMap AuxTree.toList)
          (inducedSubPar P st.splay trees) trees1) < F := by omega
    rcases lctExposeLoop_spec hL F hW1 ht1_mem (last := v) rfl hv1 hlast1 hpar1 hact_perm1
      hfuel with
      ⟨trees2, t_loop, ht2_mem, -, hv2, -, -, hW2, hact_perm2, -⟩
    have hn2 : (lctExposeLoop P (exposeStart P st v) F v).1.n = st.n :=
      lctExposeLoop_n P F (exposeStart P st v) v
    obtain ⟨hRA₃, hK₃⟩ := splay_rootAcc hL hW2 ht2_mem hv2
    change RootAcc _ (SplayState.splay P _ (2 * (lctExposeLoop P (exposeStart P st v) F v).1.n + 1)
      v) _ at hRA₃
    change Keep _ (SplayState.splay P _ (2 * (lctExposeLoop P (exposeStart P st v) F v).1.n + 1)
      v) _ at hK₃
    rw [hn2] at hRA₃ hK₃
    have hperm0 : ∀ z, z ∈ (AuxTree.node v L0 R0).toList → z ∈ tv.toList := fun z hz =>
      ht0'_perm.mem_iff.mp (by rw [ht0'_eq]; exact hz)
    have hloopN : ∀ z, z ∈ drNotes s0 v S → z ∈ exposeNotes P st v S := fun z hz =>
      subset_exposeLoopNotes P _ _ _ _ hz
    refine ⟨((hRA₀.trans hRA₁ (N := fun z => z ∈ drNotes s0 v S)
      (fun z hz => by subst hz; exact mem_drNotes_self hv0) ?_).trans hRA₂ hloopN
      (fun _ h => h)).trans hRA₃ (fun _ h => h)
      (fun z hz => by subst hz; exact hloopN _ (mem_drNotes_self hv0)), ?_⟩
    · rintro z (rfl | ⟨hz0, rfl⟩)
      · exact mem_drNotes_self hv0
      · exact mem_drNotes_right hv0 hz0
    · have hact : ∀ z, z ∈ tv.toList → z ∈ trees.flatMap AuxTree.toList := fun z hz =>
        List.mem_flatMap.mpr ⟨tv, htv, hz⟩
      exact ((hK₀.trans hK₁ hact (fun z hz => hact z (hperm0 z hz))).trans hK₂ (fun _ h => h)
        (fun _ h => h)).trans hK₃ (fun _ h => h)
        (fun z hz => hact_perm2.mem_iff.mp (List.mem_flatMap.mpr ⟨t_loop, ht2_mem, hz⟩))

end MinCostFlow.LinkCut.Gen

/-! ### Reroot, path summary, path apply -/

namespace MinCostFlow.LinkCut.Gen

open MinCostFlow.LinkCut

variable {α σ τ : Type*}

theorem keep_updateNode (s : SplayState α σ τ) (x : ℕ) (f : SplayNode α σ τ → SplayNode α σ τ) :
    Keep s (s.updateNode x f) (fun z => z = x) := fun _ hz =>
  SplayState.nodes_updateNode_ne s hz f

theorem keep_revNode (P : LctPayload α σ τ) (s : SplayState α σ τ) (x : ℕ) :
    Keep s (SplayState.revNode P s x) (fun z => z = x) := by
  unfold SplayState.revNode
  split_ifs
  · exact fun _ _ => rfl
  · exact keep_updateNode _ _ _

theorem keep_applyTagNode (P : LctPayload α σ τ) (s : SplayState α σ τ) (x : ℕ) (t : τ) :
    Keep s (SplayState.applyTagNode P s x t) (fun z => z = x) := by
  unfold SplayState.applyTagNode
  split_ifs
  · exact fun _ _ => rfl
  · exact keep_updateNode _ _ _

theorem mem_exposeNotes_self {P : LctPayload α σ τ} {st : LctState α σ τ} {v : ℕ}
    (S : List ℕ) (hv : v ≠ 0) : v ∈ exposeNotes P st v S :=
  subset_exposeLoopNotes P _ _ _ _ (mem_drNotes_self hv)

theorem subset_exposeNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) (S : List ℕ) :
    S ⊆ exposeNotes P st v S := fun _ h =>
  subset_exposeLoopNotes P _ _ _ _ (subset_drNotes _ _ _ h)

/-- A change at one node `x` that is noted. -/
theorem rootAcc_one {s s' : SplayState α σ τ} {x : ℕ} {N : ℕ → Prop}
    (hk : Keep s s' (fun z => z = x)) (hx : N x) : RootAcc s s' N :=
  rootAcc_of_keep hk fun z hz _ => hz ▸ hx

theorem lctReroot_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {tv : AuxTree} {v : ℕ} (htv : tv ∈ trees) (hv : v ∈ tv.toList) (S : List ℕ) :
    RootAcc st.splay (lctReroot P st v).splay (fun z => z ∈ exposeNotes P st v S) ∧
      Keep st.splay (lctReroot P st v).splay (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  have hv0 : v ≠ 0 := SubtreeInv.ne_zero (W.treesInv _ htv).sub hv
  obtain ⟨hRA, hK⟩ := lctExpose_rootAcc hL W htv hv S
  rw [lctReroot_splay]
  refine ⟨hRA.trans (rootAcc_one (keep_revNode P _ v) (mem_exposeNotes_self S hv0))
    (fun _ h => h) (fun _ h => h), hK.trans (keep_revNode P _ v) (fun _ h => h) ?_⟩
  intro z hz; subst hz; exact List.mem_flatMap.mpr ⟨tv, htv, hv⟩

/-- Reroot at `u`, then expose `v`: every new root is noted (`rerootExposeNotes`). -/
theorem lctPathSummary_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList)
    (hu_v : isVertex st.n u) (htv : tv ∈ trees) (hv : v ∈ tv.toList) (S : List ℕ) :
    RootAcc st.splay (lctPathSummary P st u v).1.splay
        (fun z => z ∈ rerootExposeNotes P st u v S) ∧
      Keep st.splay (lctPathSummary P st u v).1.splay
        (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  obtain ⟨hRA₁, hK₁⟩ := lctReroot_rootAcc hL W htu hu S
  rcases lctReroot_spec hL W htu hu hu_v with ⟨trees', -, depth', -, W', hperm, -⟩
  have hv' : v ∈ trees'.flatMap AuxTree.toList :=
    hperm.mem_iff.mpr (List.mem_flatMap.mpr ⟨tv, htv, hv⟩)
  rcases List.mem_flatMap.mp hv' with ⟨tv', htv', hv'⟩
  obtain ⟨hRA₂, hK₂⟩ := lctExpose_rootAcc hL W' htv' hv' (exposeNotes P st u S)
  rw [lctPathSummary_fst]
  exact ⟨hRA₁.trans hRA₂ (fun z hz => subset_exposeNotes P _ v _ hz) (fun _ h => h),
    hK₁.trans hK₂ (fun _ h => h) (fun z hz => hperm.mem_iff.mp hz)⟩

theorem lctPathApply_rootAcc {P : LctPayload α σ τ} (hL : P.Laws) {st : LctState α σ τ}
    {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith P st trees fl d)
    {tu tv : AuxTree} {u v : ℕ} (htu : tu ∈ trees) (hu : u ∈ tu.toList)
    (hu_v : isVertex st.n u) (htv : tv ∈ trees) (hv : v ∈ tv.toList) (t : τ) (S : List ℕ) :
    RootAcc st.splay (lctPathApply P st u v t).splay
        (fun z => z ∈ rerootExposeNotes P st u v S) ∧
      Keep st.splay (lctPathApply P st u v t).splay
        (fun z => z ∈ trees.flatMap AuxTree.toList) := by
  have hv0 : v ≠ 0 := SubtreeInv.ne_zero (W.treesInv _ htv).sub hv
  obtain ⟨hRA, hK⟩ := lctPathSummary_rootAcc hL W htu hu hu_v htv hv S
  rw [lctPathSummary_fst] at hRA hK
  rw [lctPathApply_splay]
  refine ⟨hRA.trans (rootAcc_one (keep_applyTagNode P _ v t) (mem_exposeNotes_self _ hv0))
    (fun _ h => h) (fun _ h => h), hK.trans (keep_applyTagNode P _ v t) (fun _ h => h) ?_⟩
  intro z hz; subst hz; exact List.mem_flatMap.mpr ⟨tv, htv, hv⟩

end MinCostFlow.LinkCut.Gen
