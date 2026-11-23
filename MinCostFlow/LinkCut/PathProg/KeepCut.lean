module

public import MinCostFlow.LinkCut.PathProg.KeepOps

/-!
# A cut keeps `StateOk`

The only new fact a cut needs is the shape of the slot `ne` it frees: no children and no path
parent. When the cut splays `ne`, the exposed tree has three nodes and its root has no path
parent (`cutPd_tree`), so after the splay `ne` has no path parent. Then the cut detaches both
children of `ne` and links `ne` into the free list, which changes neither its path parent nor its
(now empty) children (`dc_shape`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.Path SplayState

variable {α σ τ : Type*}

theorem clearUp_ppar {s : SplayState α σ τ} {x : ℕ} (h : (s.nodes x).ppar = 0) (a : ℕ) :
    ((Gen.clearUp s a).nodes x).ppar = 0 := by
  unfold Gen.clearUp
  split_ifs
  · exact h
  · by_cases hxa : x = a
    · subst hxa; simp [setPpar]
    · simp only [setPpar, setPar, nodes_updateNode_ne _ hxa]; exact h

/-- After detaching the children of a node with no path parent and setting its parent, the
node has no children and no path parent. -/
theorem dc_shape (P : LctPayload α σ τ) (s : SplayState α σ τ) {x : ℕ} (hx : x ≠ 0)
    (hp : (s.nodes x).ppar = 0) (fh : ℕ) :
    (((detachRootChildren P s x).setPar x fh).nodes x).left = 0 ∧
      (((detachRootChildren P s x).setPar x fh).nodes x).right = 0 ∧
      (((detachRootChildren P s x).setPar x fh).nodes x).ppar = 0 := by
  rw [detachRootChildren_eq hx]
  simp only [setPar, nodes_updateNode_self]
  unfold pull
  rw [ite_eq_right hx]
  simp only [nodes_updateNode_self]
  unfold detachChildrenMid
  simp only [setRight, setLeft, nodes_updateNode_self]
  exact ⟨trivial, trivial, clearUp_ppar (clearUp_ppar hp _) _⟩

theorem lctCut_n (s : PathTreeState) (u v : ℕ) : (lctCut pathPayload s u v).n = s.n := by
  unfold lctCut lctCutCost
  repeat' (dsimp only; split_ifs)
  all_goals rfl

/-- In the cut that splays its slot, the slot lies in a tree of three nodes whose root has no path
parent. -/
theorem cutPd_tree {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) {u v : ℕ} (hu : isVertex s.n u)
    (hv : isVertex s.n v) (hsz : ((cutMid pathPayload s u v).splay.nodes v).sz = 3) :
    ∃ t, TreeInv pathPayload (cutPd pathPayload s u v) t ∧ cutNe pathPayload s u v ∈ t.toList ∧
      t.countNodes = 3 ∧ ((cutPd pathPayload s u v).nodes t.rootId).ppar = 0 := by
  have hL := pathPayload_laws
  have hu_act := isVertex_mem_active W hu
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp hu_act
  obtain ⟨trees1, Lu, depth1, -, hW1, hact1, -⟩ := lctReroot_spec hL W htu hut hu
  have hv1 : v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (isVertex_mem_active W hv)
  obtain ⟨tv1, htv1, hvt1⟩ := List.mem_flatMap.mp hv1
  obtain ⟨trees2, Lv, ht2, hW2, -, -, -, hpp2, -, hrev2, -⟩ := lctExpose_spec hL hW1 htv1 hvt1
  have hmid : (lctExposeCost pathPayload (lctRerootCost pathPayload s u).1 v).1 =
      cutMid pathPayload s u v := rfl
  rw [hmid] at hW2 hrev2 hpp2
  have ht2_inv := hW2.treesInv _ ht2
  have hsz_v : ((cutMid pathPayload s u v).splay.nodes v).sz = 1 + Lv.countNodes := by
    have h := ht2_inv.sub.2.2.2.2.2.1
    simpa [AuxTree.countNodes] using h
  have hLv : Lv ≠ .leaf := by
    rintro rfl; simp [AuxTree.countNodes] at hsz_v; omega
  have hl0 : cutL0 pathPayload s u v = Lv.rootId := by
    have h := ht2_inv.sub.2.1
    show ((cutMid pathPayload s u v).splay.nodes v).left = _
    simpa [hrev2] using h
  have hl0_mem : cutL0 pathPayload s u v ∈ (AuxTree.node v Lv .leaf).toList := by
    rw [hl0]; simp [AuxTree.toList, AuxTree.rootId_mem hLv]
  obtain ⟨hpd, hperm, hroot, -, -, -, -, -, -, hppar, -⟩ :=
    pushDown_preserves_TreeInv hL ht2_inv hl0_mem
  change TreeInv pathPayload (cutPd pathPayload s u v) _ at hpd
  change ((cutPd pathPayload s u v).nodes _).ppar = _ at hppar
  generalize pushDownTree (cutMid pathPayload s u v).splay (cutL0 pathPayload s u v)
    (AuxTree.node v Lv .leaf) = t at hpd hperm hroot hppar
  have hl0_t : cutL0 pathPayload s u v ∈ t.toList := hperm.symm.mem_iff.mp hl0_mem
  refine ⟨t, hpd, ?_, ?_, ?_⟩
  · unfold cutNe
    split_ifs with hr
    · exact hl0_t
    · exact (SubtreeInv.child_mem hpd.sub hl0_t).2 hr
  · rw [← AuxTree.length_toList, hperm.length_eq, AuxTree.length_toList]
    simp only [AuxTree.countNodes] at hsz_v ⊢
    omega
  · rw [hppar]; exact hpp2

/-- The slot a cut frees has no children and no path parent. -/
theorem cut_ne_shape {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) {u v : ℕ} (hu : isVertex s.n u)
    (hv : isVertex s.n v) (hsz : ((cutMid pathPayload s u v).splay.nodes v).sz = 3) :
    let s' := (SplayState.detachRootChildren pathPayload (SplayState.splay pathPayload
      (cutPd pathPayload s u v) (2 * s.n + 1) (cutNe pathPayload s u v))
      (cutNe pathPayload s u v)).setPar (cutNe pathPayload s u v) s.freeHead
    (s'.nodes (cutNe pathPayload s u v)).left = 0 ∧
      (s'.nodes (cutNe pathPayload s u v)).right = 0 ∧
      (s'.nodes (cutNe pathPayload s u v)).ppar = 0 := by
  obtain ⟨t, ht, hne, hc, hpp⟩ := cutPd_tree W hu hv hsz
  have hfuel : t.depthOf (cutNe pathPayload s u v) < 2 * s.n + 1 := by
    have := depthOf_lt_countNodes hne
    have := hu.1
    have := hu.2
    omega
  obtain ⟨t', -, -, -, -, -, hpp', -⟩ := splay_preserves_and_phi pathPayload_laws ht hne hfuel
  exact dc_shape _ _ (SubtreeInv_nonZero ht.sub hne) (hpp'.trans hpp) _

theorem freeHead_mem {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) :
    s.freeHead = 0 ∨ s.freeHead ∈ free := by
  have hfl := W.freeListInv
  cases free with
  | nil => exact Or.inl hfl
  | cons e rest => exact Or.inr (hfl.2.1 ▸ List.mem_cons_self)

/-- If the free head after a cut is a new nonzero slot, it has no children and no path parent. -/
theorem cut_freeHead_shape {s : PathTreeState} {trees : List AuxTree} {free : List ℕ}
    {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth) {u v : ℕ}
    (hu : isVertex s.n u) (hv : isVertex s.n v)
    (h0 : (lctCut pathPayload s u v).freeHead ≠ 0) (hn : (lctCut pathPayload s u v).freeHead ∉ free) :
    let s' := (lctCut pathPayload s u v).splay
    let e := (lctCut pathPayload s u v).freeHead
    (s'.nodes e).left = 0 ∧ (s'.nodes e).right = 0 ∧ (s'.nodes e).ppar = 0 := by
  intro s' e
  have hold : ¬ (s.freeHead ≠ 0 ∧ s.freeHead ∉ free) := by
    rintro ⟨h1, h2⟩; rcases freeHead_mem W with h | h <;> contradiction
  by_cases huv : u = v
  · rw [lctCut_guard (Or.inr (Or.inr (Or.inl huv)))] at h0 hn
    exact absurd ⟨h0, hn⟩ hold
  have hu0 := isVertex_ne_zero hu
  have hv0 := isVertex_ne_zero hv
  have hopen := lctCut_open (P := pathPayload) (st := s) hu0 hv0 huv hu.2 hv.2
  have hf := cutMid_freeHead pathPayload s u v
  simp only [s', e] at *
  rw [hopen] at h0 hn ⊢
  split_ifs at h0 hn ⊢ with h1 h2
  · rw [hf] at h0 hn; exact absurd ⟨h0, hn⟩ hold
  · rw [hf] at h0 hn; exact absurd ⟨h0, hn⟩ hold
  · exact cut_ne_shape W hu hv (not_not.mp h1)

/-- A cut keeps pointers in range. -/
theorem ptrOk_cut {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) (hP : PtrOk (2 * s.n) s.splay) {u v : ℕ}
    (hu : isVertex s.n u) (hv : isVertex s.n v) :
    PtrOk (2 * (lctCut pathPayload s u v).n) (lctCut pathPayload s u v).splay := by
  rw [lctCut_n]
  by_cases huv : u = v
  · rw [lctCut_guard (Or.inr (Or.inr (Or.inl huv)))]; exact hP
  have hu' : u ≤ 2 * s.n := by have := hu.2; omega
  have hv' : v ≤ 2 * s.n := by have := hv.2; omega
  have hmid : PtrOk (2 * s.n) (cutMid pathPayload s u v).splay := by
    have h := hP.reroot (P := pathPayload) (st := s) hu'
    exact h.expose (st := lctReroot pathPayload s u) hv'
  have hl0 : cutL0 pathPayload s u v ≤ 2 * s.n := (hmid v hv').1
  have hpd : PtrOk (2 * s.n) (cutPd pathPayload s u v) := hmid.pushDown hl0
  rw [lctCut_open (isVertex_ne_zero hu) (isVertex_ne_zero hv) huv hu.2 hv.2]
  split_ifs
  · exact hmid
  · exact hpd
  · have hne : cutNe pathPayload s u v ≤ 2 * s.n := by
      unfold cutNe
      split_ifs
      · exact hl0
      · exact (hpd _ hl0).2.1
    exact ((hpd.splay hne).detachRootChildren hne).setPar hne (freeHead_le W)

/-- A cut between two vertices keeps `StateOk`. -/
theorem stateOk_cut {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {u v : ℕ} (hu : isVertex s.n u) (hv : isVertex s.n v) :
    StateOk (lctCut pathPayload s u v) (cutNotes pathPayload s u v S) := by
  have hptr := ptrOk_cut W hP hu hv
  obtain ⟨hacc, hkeep⟩ := lctCut_rootAcc pathPayload_laws W u v S
  obtain ⟨-, -, -, -, -, -, -, hE1⟩ := stateOk_reroot W hI hF hP hE hu
  have hS := subset_cutNotes pathPayload s u v S
  have hn : (lctCut pathPayload s u v).n = (lctReroot pathPayload s u).n := by
    rw [lctCut_n, lctReroot_n]
  obtain ⟨-, -, hspec⟩ := lctCut_spec pathPayload_laws W u v
  split_ifs at hspec with hadj
  · obtain ⟨trees1, depth1, ne, eVal, trees', depth', -, W', hne_e, -, -, -, -, -, -, hact', -,
      -, -, hpairs'⟩ := hspec
    refine ⟨hptr, ⟨trees', ne :: free, depth', W', ?_, ?_⟩, ?_⟩
    · exact readyIdx_step W W' hacc (fun z hz => Or.inl (hact'.subset (List.mem_cons_of_mem _ hz)))
        hI hS (fun _ h => h)
    · refine freeShape_step hF hkeep fun e he => ?_
      rcases List.mem_cons.mp he with rfl | he'
      · right
        have hfh : (lctCut pathPayload s u v).freeHead = e := W'.freeListInv.2.1
        have h0 : (lctCut pathPayload s u v).freeHead ≠ 0 := by
          rw [hfh]; have := hne_e.1; omega
        have hnf : (lctCut pathPayload s u v).freeHead ∉ free := by
          rw [hfh]; exact (List.nodup_cons.mp W'.freeNodup).1
        have := cut_freeHead_shape W hu hv h0 hnf
        rw [hfh] at this
        exact this
      · exact Or.inl ⟨he', not_active_of_free W he'⟩
    · refine vals_of_pairsVE W' fun p hp hx => ?_
      exact pairsVE_of_vals hE1 trees1 p (hpairs'.subset (List.mem_cons_of_mem _ hp))
        (hn ▸ hx)
  · rcases hspec with heq | ⟨trees1, depth1, trees', depth', -, W', -, hact', -, hpairs'⟩
    · have heq' : lctCut pathPayload s u v = s := heq
      rw [heq']
      exact ⟨hP, ⟨trees, free, depth, W, fun t ht hr => hS (hI t ht hr), hF⟩, hE⟩
    · refine ⟨hptr, ⟨trees', free, depth', W', ?_, freeShape_keep W hF hkeep⟩, ?_⟩
      · exact readyIdx_step W W' hacc (fun z hz => Or.inl (hact'.subset hz)) hI hS (fun _ h => h)
      · refine vals_of_pairsVE W' fun p hp hx => ?_
        exact pairsVE_of_vals hE1 trees1 p (hpairs'.subset hp) (hn ▸ hx)

end MinCostFlow.LinkCut.PathProg
