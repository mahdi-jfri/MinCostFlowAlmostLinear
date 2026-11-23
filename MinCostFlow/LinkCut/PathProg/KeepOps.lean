module

public import MinCostFlow.LinkCut.PathProg.Keep
public import MinCostFlow.LinkCut.PathTree.Write

/-!
# Path update, link and point write keep `StateOk`

A path update changes only the tag, value and summary of the exposed node, and the model keeps
its invariant (`lctPathApply_spec`). A link takes the free slot at the head of the free list
and notes it, so the slots left on the list keep their shape. A point write changes only the
value and summary of the exposed slot.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.PathTree
  MinCostFlow.LinkCut.Path

/-- Connectivity in the contract is connectivity of the represented forest. -/
theorem conn_iff {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) {u v : ℕ} (hu : isVertex s.n u)
    (hv : isVertex s.n v) :
    pathTreeConnected s u v ↔
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length u =
        subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length v := by
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp (isVertex_mem_active W hu)
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv)
  obtain ⟨-, -, -, -, -, hiff, -⟩ := lctConnected_spec pathPayload_laws W htu hut htv hvt
  exact hiff

theorem freeHead_le {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload s trees free depth) : s.freeHead ≤ 2 * s.n := by
  have hfl := W.freeListInv
  cases free with
  | nil => have : s.freeHead = 0 := hfl; omega
  | cons e rest =>
    obtain ⟨-, he, -⟩ := hfl
    have := (W.freeValid e List.mem_cons_self).2
    omega

/-- A path update between two connected vertices keeps `StateOk`. -/
theorem stateOk_apply {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {u v : ℕ} (hu : isVertex s.n u) (hv : isVertex s.n v)
    (hconn : pathTreeConnected s u v) (t : PathTag) :
    StateOk (lctPathApply pathPayload s u v t) (rerootExposeNotes pathPayload s u v S) := by
  have hsum := stateOk_summary W hI hF hP hE hu hv
  rw [lctPathSummary_fst] at hsum
  obtain ⟨tu, htu, hut⟩ := List.mem_flatMap.mp (isVertex_mem_active W hu)
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp (isVertex_mem_active W hv)
  obtain ⟨trees', Lx, depth', -, W', hperm, -⟩ :=
    lctPathApply_spec pathPayload_laws W htu hut hu htv hvt ((conn_iff W hu hv).mp hconn) t
  obtain ⟨hacc, hkeep⟩ := lctPathApply_rootAcc pathPayload_laws W htu hut hu htv hvt t S
  have hv0 := isVertex_ne_zero hv
  refine ⟨?_, ⟨trees', free, depth', W', ?_, freeShape_keep W hF hkeep⟩, ?_⟩
  · rw [lctPathApply_n, lctPathApply_splay]
    have hp := hsum.ptr
    rw [lctExpose_n, lctReroot_n] at hp
    exact hp.applyTagNode (by have := hv.2; omega)
  · exact readyIdx_step W W' hacc (fun z hz => Or.inl (hperm.subset hz)) hI
      (subset_rerootExposeNotes _ _ _ _ _) (fun _ h => h)
  · intro x hx
    have hE' := hsum.vals
    rw [lctPathApply_n] at hx
    rw [lctPathApply_splay]
    unfold SplayState.applyTagNode
    rw [ite_eq_right hv0]
    by_cases hxv : x = v
    · subst hxv
      rw [SplayState.nodes_updateNode_self]
      show pathPayload.actVal t _ = none
      rw [hE' x (by rw [lctExpose_n, lctReroot_n]; exact hx)]
      rfl
    · rw [SplayState.nodes_updateNode_ne _ hxv]
      exact hE' x (by rw [lctExpose_n, lctReroot_n]; exact hx)

theorem lctLink_n (s : PathTreeState) (u v : ℕ) (e : Option PathEdgeValue) :
    (lctLink pathPayload s u v e).n = s.n := by
  unfold lctLink lctLinkCost
  repeat' (dsimp only; split_ifs)
  all_goals rfl

/-- A link of two vertices that are not connected, with a free slot, keeps `StateOk`. -/
theorem stateOk_link {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {u v : ℕ} (hu : isVertex s.n u) (hv : isVertex s.n v)
    (hnc : ¬ pathTreeConnected s u v) (hf : s.freeHead ≠ 0) (e : Option PathEdgeValue) :
    StateOk (lctLink pathPayload s u v e) (linkNotes pathPayload s u v S) := by
  cases free with
  | nil => exact absurd (W.freeListInv : s.freeHead = 0) hf
  | cons ne rest =>
  have hdisc := fun h => hnc ((conn_iff W hu hv).mpr h)
  obtain ⟨trees2, depth2, trees', depth', -, W', hact2, hact', -, -, -, hpairs', -⟩ :=
    lctLink_spec pathPayload_laws W rfl hu hv hdisc e
  obtain ⟨hacc, hkeep⟩ := lctLink_rootAcc pathPayload_laws W hu hv e S
  have hfh : s.freeHead = ne := W.freeListInv.2.1
  have hne_edge := W.freeValid ne List.mem_cons_self
  have hnd := W.freeNodup
  have huv : u ≠ v := fun h => hdisc (congrArg _ h)
  have hln : linkNotes pathPayload s u v S = noteList (exposeNotes pathPayload
      (lctReroot pathPayload s v) u (exposeNotes pathPayload s v S)) s.freeHead := by
    unfold linkNotes
    rw [ite_eq_right (by have := isVertex_ne_zero hu; have := isVertex_ne_zero hv; tauto)]
  refine ⟨?_, ⟨trees', rest, depth', W', ?_, ?_⟩, ?_⟩
  · rw [lctLink_n]
    exact hP.link (by have := hu.2; omega) (by have := hv.2; omega) (freeHead_le W)
  · refine readyIdx_step W W' hacc (fun z hz => ?_) hI (fun z hz => ?_) (fun _ h => h)
    · rcases List.mem_cons.mp (hact'.subset hz) with rfl | hz'
      · right; rw [hln, mem_noteList, hfh]; exact Or.inr rfl
      · exact Or.inl (hact2.subset hz')
    · rw [hln, mem_noteList]
      exact Or.inl (subset_exposeNotes _ _ _ _ (subset_exposeNotes _ _ _ _ hz))
  · refine freeShape_step hF hkeep fun x hx => Or.inl ⟨List.mem_cons_of_mem _ hx, ?_⟩
    rintro (ha | rfl)
    · exact not_active_of_free W (List.mem_cons_of_mem _ hx) ha
    · rw [hfh] at hx; exact (List.nodup_cons.mp hnd).1 hx
  · obtain ⟨trees1, d1, W1, -, -, -, -, hE1⟩ := stateOk_reroot W hI hF hP hE hv
    have hu1 : isVertex (lctReroot pathPayload s v).n u := by rw [lctReroot_n]; exact hu
    have hE2 := vals_reroot W1 hE1 hu1
    refine vals_of_pairsVE W' fun p hp hx => ?_
    rcases List.mem_cons.mp (hpairs'.subset hp) with rfl | hp'
    · rw [lctLink_n] at hx
      exact absurd ⟨hx, hne_edge⟩ not_vertex_and_edge
    · have := pairsVE_of_vals hE2 trees2 p hp'
      rw [lctLink_n] at hx
      exact this (by rw [lctReroot_n, lctReroot_n]; exact hx)

/-- A point write at an active edge slot keeps `StateOk`. -/
theorem stateOk_write {s : PathTreeState} {S : List ℕ} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} (W : LctInvWith pathPayload s trees free depth)
    (hI : ReadyIdx s trees S) (hF : FreeShape s free) (hP : PtrOk (2 * s.n) s.splay)
    (hE : ValsOnEdges s) {x : ℕ} (hx : isEdgeSlot s.n x)
    (hxa : x ∈ trees.flatMap AuxTree.toList) (val : Option PathEdgeValue) :
    StateOk (pathTreeWrite s x val) (exposeNotes pathPayload s x S) := by
  obtain ⟨tx, htx, hxt⟩ := List.mem_flatMap.mp hxa
  obtain ⟨trees', W', hpairs⟩ := pathTreeWrite_forestPairs W htx hxt val
  obtain ⟨hacc, hkeep⟩ := lctExpose_rootAcc pathPayload_laws W htx hxt S
  have hx0 : x ≠ 0 := by have := hx.1; omega
  have hkx : Keep (lctExpose pathPayload s x).splay (pathTreeWrite s x val).splay
      (fun z => z = x) := fun z hz => pathTreeWrite_node_of_ne s hz val
  have hE1 := vals_expose W hE hxa
  have hn : (pathTreeWrite s x val).n = s.n := by rw [pathTreeWrite_n, lctExpose_n]
  refine ⟨?_, ⟨trees', free, depth, W', ?_, ?_⟩, ?_⟩
  · rw [hn, pathTreeWrite_splay]
    unfold pointWriteSplay
    have hp := hP.expose (P := pathPayload) (st := s) (active_le W hxa)
    exact (hp.updateNode_ptrs (hp x (active_le W hxa))).pull (active_le W hxa)
  · refine readyIdx_step W W' (hacc.trans (rootAcc_one hkx (mem_exposeNotes_self S hx0))
      (fun _ h => h) (fun _ h => h)) (fun z hz => Or.inl ?_) hI
      (subset_exposeNotes _ _ _ _) (fun _ h => h)
    have hm : z ∈ (forestPairs pathPayload (pathTreeWrite s x val).splay trees').map Prod.fst :=
      (forestPairs_fst_perm _ trees').symm.subset hz
    obtain ⟨⟨y, w⟩, hp, rfl⟩ := List.mem_map.mp hm
    rcases (hpairs y w).mp hp with ⟨rfl, -⟩ | ⟨-, hp'⟩
    · exact hxa
    · exact (forestPairs_fst_perm s.splay trees).subset (List.mem_map_of_mem hp')
  · exact freeShape_keep W hF (hkeep.trans hkx (fun _ h => h) (fun z h => h ▸ hxa))
  · intro y hy
    rw [hn] at hy
    rw [pathTreeWrite_value]
    have hyx : y ≠ x := fun h => not_vertex_and_edge ⟨hy, h ▸ hx⟩
    rw [ite_eq_right hyx]
    exact hE1 y (by rw [lctExpose_n]; exact hy)

end MinCostFlow.LinkCut.PathProg
