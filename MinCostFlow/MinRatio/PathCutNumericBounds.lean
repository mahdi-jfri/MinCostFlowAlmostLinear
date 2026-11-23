module

public import MinCostFlow.MinRatio.PathSplayNumericBounds
import MinCostFlow.MinRatio.PathAccountNumericBounds
import MinCostFlow.LinkCut.ForestExposeSpec

/-!
# Numeric bounds on the edge selected by Cut

The cut of an exposed edge in Section 6 (pages 29–30) pushes the left
child, inspects its pointers, and splays the selected edge slot.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut

private theorem cut_children_of_inorder
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {edge u v : ℕ} {l r : AuxTree}
    (hnd : (AuxTree.node edge l r).toList.Nodup)
    (hrev : (s.nodes edge).rev = false)
    (hids : treeIds pathPayload s (.node edge l r) = [u, edge, v]) :
    l = .node u .leaf .leaf ∧ r = .node v .leaf .leaf := by
  let rev := fun z => (s.nodes z).rev
  have he : l.evalInorder rev false ++ [edge] ++ r.evalInorder rev false = [u, edge, v] := by
    simpa [treeIds, SplayState.evalPairs_map_fst, AuxTree.evalInorder, hrev, rev] using hids
  have hdiff : edge ≠ u := by
    have hp := AuxTree.evalInorder_perm rev (.node edge l r) false
    unfold treeIds at hids
    rw [SplayState.evalPairs_map_fst] at hids
    rw [hids] at hp
    have hn := hp.nodup_iff.mpr hnd
    intro h
    subst u
    exact (List.nodup_cons.mp hn).1 (by simp)
  obtain ⟨_, hnL, _, _, _⟩ := AuxTree.nodup_node_unfold hnd
  have hleft : l.evalInorder rev false = [u] ∧ r.evalInorder rev false = [v] := by
    cases hl : l.evalInorder rev false with
    | nil => simp [hl, hdiff] at he
    | cons a tail =>
      cases tail with
      | nil => simpa [hl] using he
      | cons b tail =>
        have hbe : b = edge := by
          rw [hl] at he
          have hh := congrArg (fun xs : List ℕ => xs[1]?) he
          change some b = some edge at hh
          exact Option.some.inj hh
        exact (hnL ((AuxTree.evalInorder_perm rev l false).mem_iff.mp
          (by simp [hl, ← hbe]))).elim
  have single {t : AuxTree} {id : ℕ} (h : t.evalInorder rev false = [id]) :
      t = .node id .leaf .leaf := by
    have hp := AuxTree.evalInorder_perm rev t false
    rw [h] at hp
    have hlen := hp.length_eq
    rw [List.length_singleton, AuxTree.length_toList] at hlen
    cases t with
    | leaf => simp [AuxTree.countNodes] at hlen
    | node j a b =>
      have hj : j = id := by
        have hm : j ∈ [id] := hp.mem_iff.mpr (by simp [AuxTree.toList])
        simpa using hm
      subst j
      cases a <;> cases b <;> simp [AuxTree.countNodes] at hlen ⊢
      omega
  exact ⟨single hleft.1, single hleft.2⟩

/-- Returning the detached edge slot to the free list does not enlarge any
of its numeric fields beyond the bound on its former edge record. -/
theorem cutReleasedSlot_nodeBound
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {edge u v free : ℕ} {B : ℤ}
    (ht : SplayState.TreeInv pathPayload s
      (.node edge (.node u .leaf .leaf) (.node v .leaf .leaf)))
    (hval : ∀ value, (s.nodes edge).val = some value →
      |value.gradient| ≤ B ∧ |value.length| ≤ B ∧ |value.flow| ≤ B ∧ |value.detector| ≤ B)
    (htag : (s.nodes edge).tag = pathPayload.idTag) (hB : 0 ≤ B) :
    PathNodeBound B (((s.detachRootChildren pathPayload edge).setPar edge free).nodes edge) := by
  obtain ⟨_, hu, _, hv, _⟩ := AuxTree.nodup_node_unfold ht.nodup
  have heu : edge ≠ u := fun h => hu (by simp [AuxTree.toList, h])
  have hev : edge ≠ v := fun h => hv (by simp [AuxTree.toList, h])
  have edgeNZ : edge ≠ 0 := SplayState.SubtreeInv_nonZero ht.sub (by simp [AuxTree.toList])
  have uNZ : u ≠ 0 := SplayState.SubtreeInv_nonZero ht.sub (by simp [AuxTree.toList])
  have vNZ : v ≠ 0 := SplayState.SubtreeInv_nonZero ht.sub (by simp [AuxTree.toList])
  have hleft : (s.nodes edge).left = u := ht.sub.2.1
  have hright : (s.nodes edge).right = v := ht.sub.2.2.1
  let slim := ((((s.setPar u 0).setPpar u 0).setPar v 0).setPpar v 0).setLeft edge 0 |>.setRight edge 0
  have hslim : slim.nodes edge = { s.nodes edge with left := 0, right := 0 } := by
    simp [slim, SplayState.setLeft, SplayState.setRight, SplayState.setPar, SplayState.setPpar,
      heu, hev]
  have hnode : ((s.detachRootChildren pathPayload edge).setPar edge free).nodes edge =
      { s.nodes edge with
        left := 0, right := 0, par := free, sz := 1
        sum := pathPayload.single edge (s.nodes edge).val } := by
    unfold SplayState.detachRootChildren
    simp only [edgeNZ, ite_false, hleft, hright, uNZ, vNZ]
    change ((slim.pull pathPayload edge).setPar edge free).nodes edge = _
    simp [SplayState.setPar, SplayState.pull, edgeNZ, hslim, pathPayload_laws.combine_empty_left,
      pathPayload_laws.combine_empty_right]
  rw [hnode]
  have hflow : |(s.nodes edge).tag.flow| ≤ B := by
    simpa [htag, pathPayload, PathTag.zero] using hB
  have hdetect : |(s.nodes edge).tag.detector| ≤ B := by
    simpa [htag, pathPayload, PathTag.zero] using hB
  refine ⟨hval, ?_, ?_, ?_, hflow, hdetect⟩
  all_goals
    cases h : (s.nodes edge).val with
    | none => simp [pathPayload, PathSummary.single, PathSummary.empty, hB]
    | some v =>
      obtain ⟨hg, hl, _, hd⟩ := hval v h
      simp [pathPayload, PathSummary.single, hg, hl, hd]


/-- After Cut identifies its edge slot, the final splay and splice preserve the tag budget. -/
theorem lctCutSplaySplice_route_bound
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {edge u v : ℕ} {B : ℤ}
    (ht : t ∈ trees) (hx : edge ∈ t.toList)
    (hids : treeIds pathPayload st.splay t = [u, edge, v])
    (hpp : (st.splay.nodes t.rootId).ppar = 0) (he : isEdgeSlot st.n edge)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let splayed := st.splay.splay pathPayload (2 * st.n + 1) edge
    let next : PathTreeState :=
      ⟨st.n, (splayed.detachRootChildren pathPayload edge).setPar edge st.freeHead, edge⟩
    ∃ ts, LctInvWith pathPayload next ts (edge :: freeList) depth ∧
      (∀ c ∈ ts, ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) ∧
      (∀ C : ℤ, 0 ≤ C →
        (∀ i val, (i, some val) ∈ SplayState.evalPairs pathPayload st.splay t false pathPayload.idTag →
          |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C) →
        PathNodeBound C (next.splay.nodes edge)) := by
  dsimp only
  obtain ⟨t', htne, hroot, _, hpp', hrev, htag, W', _, _, _, _, hev, _⟩ :=
    lctSplayTree_spec pathPayload_laws W ht hx
  obtain ⟨_, _, _, _, W'', frame, hb''⟩ := lctSplayTree_route_bound W ht hx hb
  have hb' := lct_route_bound_of_same_state W'' W' hb''
  have hi : treeIds pathPayload (st.splay.splay pathPayload (2 * st.n + 1) edge) t' = [u, edge, v] := by
    unfold treeIds at hids ⊢
    rwa [hev]
  cases t' with
  | leaf => exact (htne rfl).elim
  | node id l r =>
    change id = edge at hroot
    subst id
    have hm : AuxTree.node edge l r ∈ AuxTree.node edge l r :: trees.erase t := List.mem_cons_self
    obtain ⟨hl, hr⟩ := cut_children_of_inorder (W'.treesInv _ hm).nodup hrev hi
    subst l r
    have hsplice := lctCutSplice_route_bound W' hm hrev htag (hpp'.trans hpp) he hb'
    refine ⟨_, hsplice.1, hsplice.2, ?_, ?_⟩
    · intro z hz
      have hz' : z ∉ (AuxTree.node edge (.node u .leaf .leaf) (.node v .leaf .leaf)).toList :=
        fun hz' => hz (lct_active_mem_of_same_freeList W W' rfl (List.mem_flatMap.mpr ⟨_, hm, hz'⟩))
      have hzList : z ∉ [u, edge, v] := by simpa [AuxTree.toList] using hz'
      have hne : z ≠ edge := fun he => hzList (by simp [he])
      let sp := st.splay.splay pathPayload (2 * st.n + 1) edge
      change ((sp.detachRootChildren pathPayload edge).setPar edge st.freeHead).nodes z = _
      rw [SplayState.setPar, SplayState.nodes_updateNode_ne _ hne]
      exact ((SplayState.detachRootChildren_preserves pathPayload_laws (W'.treesInv _ hm)
        hrev htag).2.2.2.2.2.2 z hzList).trans
          (frame z (fun hm => hz (List.mem_flatMap.mpr ⟨_, ht, hm⟩)))

    · intro C hC bounds
      apply cutReleasedSlot_nodeBound (W'.treesInv _ hm) _ htag hC
      intro val hval
      apply bounds edge val
      rw [← hev, evalPairs_of_rev_false pathPayload_laws hrev htag, hval]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

private theorem twoNodeShape {t : AuxTree} (h : t.countNodes = 2) :
    (∃ a b, t = .node a .leaf (.node b .leaf .leaf)) ∨
      ∃ a b, t = .node a (.node b .leaf .leaf) .leaf := by
  cases t with
  | leaf => simp [AuxTree.countNodes] at h
  | node a l r =>
    cases l with
    | leaf =>
      cases r with
      | leaf => simp [AuxTree.countNodes] at h
      | node b rl rr =>
        have hs : rl.countNodes = 0 ∧ rr.countNodes = 0 := by
          simp only [AuxTree.countNodes] at h
          omega
        have hl : rl = .leaf := by cases rl <;> simp_all [AuxTree.countNodes]
        have hr : rr = .leaf := by cases rr <;> simp_all [AuxTree.countNodes]
        exact Or.inl ⟨a, b, by rw [hl, hr]⟩
    | node b ll lr =>
      have hs : ll.countNodes = 0 ∧ lr.countNodes = 0 ∧ r.countNodes = 0 := by
        simp only [AuxTree.countNodes] at h
        omega
      have hl : ll = .leaf := by cases ll <;> simp_all [AuxTree.countNodes]
      have hm : lr = .leaf := by cases lr <;> simp_all [AuxTree.countNodes]
      have hr : r = .leaf := by cases r <;> simp_all [AuxTree.countNodes]
      exact Or.inr ⟨a, b, by rw [hl, hm, hr]⟩

/-- The two pointer tests on a clean three-node exposure recover its in-order
endpoint and edge. -/
theorem lctCutCandidates_treeIds
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {v : ℕ} {l : AuxTree}
    (ht : SplayState.TreeInv pathPayload s (.node v l .leaf))
    (hsize : l.countNodes = 2)
    (hv : (s.nodes v).rev = false)
    (hl : (s.nodes l.rootId).rev = false) :
    let left := (s.nodes v).left
    let right := (s.nodes left).right
    let u := if right == 0 then (s.nodes left).left else left
    let edge := if right == 0 then left else right
    treeIds pathPayload s (.node v l .leaf) = [u, edge, v] := by
  dsimp only
  have outer := ht.sub
  rw [SplayState.SubtreeInv.eq_2] at outer
  rw [outer.2.1]
  rcases twoNodeShape hsize with ⟨a, b, rfl⟩ | ⟨a, b, rfl⟩
  · have hchild := outer.2.2.2.2.2.2.2.1
    rw [SplayState.SubtreeInv.eq_2] at hchild
    change (s.nodes a).rev = false at hl
    have hr : (s.nodes a).right = b := hchild.2.2.1
    have hn : b ≠ 0 := SplayState.SubtreeInv_nonZero hchild.2.2.2.2.2.2.2.2
      (by simp [AuxTree.toList])
    simp [AuxTree.rootId, hr, hn, treeIds, SplayState.evalPairs_map_fst, AuxTree.evalInorder, hv, hl]
  · have hchild := outer.2.2.2.2.2.2.2.1
    rw [SplayState.SubtreeInv.eq_2] at hchild
    change (s.nodes a).rev = false at hl
    have hr : (s.nodes a).right = 0 := hchild.2.2.1
    have hleft : (s.nodes a).left = b := hchild.2.1
    simp [AuxTree.rootId, hr, hleft, treeIds, SplayState.evalPairs_map_fst, AuxTree.evalInorder, hv, hl]

/-- Pushing the exposed left child leaves the three-node path order intact
and lets the program read it from the child pointers. -/
theorem lctCutPush_route_bound
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {v : ℕ} {l : AuxTree} {B : ℤ}
    (ht : AuxTree.node v l .leaf ∈ trees)
    (hsize : (st.splay.nodes v).sz = 3)
    (hrev : (st.splay.nodes v).rev = false)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let t := AuxTree.node v l .leaf
    let left := (st.splay.nodes v).left
    let next := { st with splay := st.splay.pushDown pathPayload left }
    let t' := st.splay.pushDownTree left t
    let ts := t' :: trees.erase t
    let right := (next.splay.nodes left).right
    let u := if right == 0 then (next.splay.nodes left).left else left
    let edge := if right == 0 then left else right
    LctInvWith pathPayload next ts freeList depth ∧
      (∀ c ∈ ts, ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (next.splay.nodes t'.rootId).ppar = (st.splay.nodes v).ppar ∧
      treeIds pathPayload next.splay t' = treeIds pathPayload st.splay t ∧
      treeIds pathPayload next.splay t' = [u, edge, v] ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) ∧
      SplayState.evalPairs pathPayload next.splay t' false pathPayload.idTag =
        SplayState.evalPairs pathPayload st.splay t false pathPayload.idTag := by
  intro t left next t' ts right u edge
  have hinv := W.treesInv t ht
  have hs := hinv.sub
  rw [show t = .node v l .leaf from rfl, SplayState.SubtreeInv.eq_2] at hs
  have hleft : left = l.rootId := hs.2.1
  have hc : l.countNodes = 2 := by
    have h := hs.2.2.2.2.2.1
    dsimp only [AuxTree.countNodes] at h
    omega
  have hne : l ≠ .leaf := by intro h; simp [h, AuxTree.countNodes] at hc
  have hm : left ∈ l.toList := hleft.symm ▸ AuxTree.rootId_mem hne
  have hm' : left ∈ t.toList := by simp [t, AuxTree.toList, hm]
  have hvl : v ∉ l.toList := (AuxTree.nodup_node_unfold hinv.nodup).2.1
  have hnl : v ≠ left := fun h => hvl (h ▸ hm)
  have hfind : t.findSubtree left = l := by
    have hx : v ≠ l.rootId := hleft ▸ hnl
    simp [t, AuxTree.findSubtree, hleft, hx, AuxTree.rootId_mem hne, AuxTree.findSubtree_root hne]
  obtain ⟨hi, hp, hroot, _, _, _, hrevLeft, _, hout, hpp, frame, heval⟩ :=
    SplayState.pushDown_preserves_TreeInv pathPayload_laws hinv hm'
  have hvFrame : next.splay.nodes v = st.splay.nodes v := hout v (by rwa [hfind])
  have hV : (next.splay.nodes v).rev = false := hvFrame.symm ▸ hrev
  obtain ⟨W', hb'⟩ := lctPushDown_route_bound W ht hm' hb
  refine ⟨W', hb', hpp, congrArg (List.map Prod.fst) heval, ?_,
    fun z hz => frame z (fun hm => hz (List.mem_flatMap.mpr ⟨t, ht, hm⟩)), heval⟩
  cases eqTree : t' with
  | leaf =>
    have h := hp.mem_iff.mpr hm'
    change left ∈ t'.toList at h
    simp [eqTree, AuxTree.toList] at h
  | node id a b =>
    change t'.rootId = v at hroot
    rw [eqTree] at hroot
    change id = v at hroot
    subst id
    change SplayState.TreeInv pathPayload next.splay t' at hi
    rw [eqTree] at hi
    have hSub := hi.sub
    rw [SplayState.SubtreeInv.eq_2] at hSub
    have hleft' : a.rootId = left := hSub.2.1.symm.trans (congrArg SplayNode.left hvFrame)
    have hb0 : b.rootId = 0 := hSub.2.2.1.symm.trans (congrArg SplayNode.right hvFrame |>.trans hs.2.2.1)
    have hbLeaf : b = .leaf := by
      cases b with
      | leaf => rfl
      | node id bl br => exact (hSub.2.2.2.2.2.2.2.2.1 hb0).elim
    subst b
    have ha : a.countNodes = 2 := by
      have h := hp.length_eq
      change t'.toList.length = t.toList.length at h
      rw [eqTree, AuxTree.length_toList, AuxTree.length_toList] at h
      simp only [t, AuxTree.countNodes] at h
      omega
    exact lctCutCandidates_treeIds hi ha hV (by rw [hleft']; exact hrevLeft) |>.trans
      (by rw [hvFrame])

private theorem cutVertex_mem_active
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth) {v : ℕ} (hv : isVertex st.n v) :
    v ∈ trees.flatMap AuxTree.toList := by
  have h := W.verticesActive (v - 1) (by have := hv.1; have := hv.2; omega)
  simpa [vid, Nat.sub_add_cancel hv.1] using h

private theorem expose_freeHead (st : PathTreeState) (v : ℕ) :
    (lctExpose pathPayload st v).freeHead = st.freeHead :=
  lctExposeLoop_freeHead pathPayload (2 * st.n + 1)
    { st with splay := (st.splay.splay pathPayload (2 * st.n + 1) v).detachRight pathPayload v } v

/-- Cutting an existing edge preserves the route bound and releases its slot. -/
theorem lctCut_route_bound
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {u v : ℕ} {B : ℤ} (hu : isVertex st.n u) (hv : isVertex st.n v) (huv : u ≠ v)
    (hadj : let par := inducedSubPar pathPayload st.splay trees
      ∃ edge ∈ trees.flatMap AuxTree.toList, (par v = edge ∧ par edge = u) ∨
        (par u = edge ∧ par edge = v))
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let next := lctCut pathPayload st u v
    ∃ edge ts d, LctInvWith pathPayload next ts (edge :: freeList) d ∧
      (∀ c ∈ ts, ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) ∧
      (∀ C : ℤ, 0 ≤ C →
        (∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
          |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C) →
        PathNodeBound C (next.splay.nodes edge) ∧
        (∀ i val, (i, some val) ∈ forestPairs pathPayload next.splay ts →
          |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C)) := by
  dsimp only
  have hadj' := And.intro hu (And.intro hv (And.intro huv hadj))
  have hs := (lctCut_spec pathPayload_laws W u v).2.2
  simp only [dite_eq_left hadj'] at hs
  obtain ⟨trr, dr, edge, released, tf, df, WR, Wf, he, hea, _, _, _, _, _, _, _, _, _, hpermF⟩ := hs
  have headFinal : (lctCutCost pathPayload st u v).1.freeHead = edge := Wf.freeListInv.2.1
  have hhead : st.freeHead ≠ edge := by
    cases hfl : freeList with
    | nil =>
      have h := W.freeListInv
      rw [hfl] at h
      change st.freeHead = 0 at h
      rw [h]
      have he₁ := he.1
      omega
    | cons e rest =>
      have h := W.freeListInv
      rw [hfl] at h
      have heq := h.2.1
      intro he'
      have hm : edge ∈ freeList := by rw [hfl, ← he', heq]; exact List.mem_cons_self
      exact (W.partitionSlots edge he).mp hea hm
  let first := lctReroot pathPayload st u
  let exposed := lctExpose pathPayload first v
  have hfh : exposed.freeHead = st.freeHead :=
    (expose_freeHead first v).trans (expose_freeHead st u)
  have hstop : (u == 0 || v == 0 || u == v || st.n < u || st.n < v) = false := by
    simp [Nat.ne_of_gt hu.1, Nat.ne_of_gt hv.1, huv, Nat.not_lt_of_ge hu.2, Nat.not_lt_of_ge hv.2]
  have hsize : (exposed.splay.nodes v).sz = 3 := by
    by_contra h
    have ht : ((exposed.splay.nodes v).sz != 3) = true := by simp [h]
    have hh : (lctCutCost pathPayload st u v).1.freeHead = exposed.freeHead := by
      simp [lctCutCost, hstop, show (lctExposeCost pathPayload (lctRerootCost pathPayload st u).1 v).1 =
        exposed from rfl, ht]
    exact hhead (hfh.symm.trans (hh.symm.trans headFinal))
  obtain ⟨tu, htu, hum⟩ := List.mem_flatMap.mp (cutVertex_mem_active W hu)
  obtain ⟨ts, d, W₁, hb₁, frame₁⟩ := lctReroot_route_bound W htu hum hu hb
  have hv₁ : isVertex first.n v := hv
  obtain ⟨tv, htv, hvm⟩ := List.mem_flatMap.mp (cutVertex_mem_active W₁ hv₁)
  obtain ⟨es, W₂, hb₂, frame₂⟩ := lctExpose_route_bound_and_frame W₁ htv hvm hb₁
  obtain ⟨as, leftTree, ha, WA, _, _, hpermA, hpp, _, hrev, _, _⟩ :=
    lctExpose_spec pathPayload_laws W₁ htv hvm
  have hbA := lct_route_bound_of_same_state W₂ WA hb₂
  let left := (exposed.splay.nodes v).left
  let pushed := { exposed with splay := exposed.splay.pushDown pathPayload left }
  let right := (pushed.splay.nodes left).right
  let candidate := if right == 0 then (pushed.splay.nodes left).left else left
  let candidateEdge := if right == 0 then left else right
  have eqEx : (lctExposeCost pathPayload (lctRerootCost pathPayload st u).1 v).1 = exposed := rfl
  have hc : candidate = u := by
    by_contra hn
    have ht : (candidate != u) = true := by simp [hn]
    simp only [candidate, right, pushed, left] at ht
    have hh : (lctCutCost pathPayload st u v).1.freeHead = exposed.freeHead := by
      simp only [lctCutCost, hstop, Bool.false_eq_true, ite_false, eqEx, hsize,
        bne_self_eq_false, ht, ite_true]
    exact hhead (hfh.symm.trans (hh.symm.trans headFinal))
  let result : PathTreeState := ⟨st.n,
    (SplayState.detachRootChildren pathPayload
      (pushed.splay.splay pathPayload (2 * st.n + 1) candidateEdge) candidateEdge).setPar
        candidateEdge pushed.freeHead, candidateEdge⟩
  have hc' : (candidate != u) = false := by simp [hc]
  simp only [candidate, right, pushed, left] at hc'
  have eqResult : (lctCutCost pathPayload st u v).1 = result := by
    simp only [lctCutCost, hstop, Bool.false_eq_true, ite_false, eqEx, hsize, bne_self_eq_false, hc']
    rfl
  have heq : candidateEdge = edge := (congrArg LctState.freeHead eqResult).symm.trans headFinal
  let tr := exposed.splay.pushDownTree left (.node v leftTree .leaf)
  obtain ⟨WP, hbP, hpP, _, hids, frameP, evalP⟩ := lctCutPush_route_bound WA ha hsize hrev hbA
  have hids' : treeIds pathPayload pushed.splay tr = [u, candidateEdge, v] := by
    change treeIds pathPayload pushed.splay tr = [candidate, candidateEdge, v] at hids
    rwa [hc] at hids
  have hed : candidateEdge ∈ tr.toList := (mem_treeIds_iff pathPayload pushed.splay tr _).mp
    (by rw [hids']; simp)
  have heP : isEdgeSlot pushed.n candidateEdge := by rw [heq]; exact he
  obtain ⟨bs, WB, hbB, frameB, freed⟩ := lctCutSplaySplice_route_bound WP List.mem_cons_self hed hids'
    (hpP.trans hpp) heP hbP
  change ∃ e ts d, LctInvWith pathPayload (lctCutCost pathPayload st u v).1 ts (e :: freeList) d ∧
    (∀ c ∈ ts, ∀ y ∈ c.toList, pathTagRouteMagnitude (lctCutCost pathPayload st u v).1.splay
      (c.pathTo y) ≤ B) ∧ (∀ z ∉ trees.flatMap AuxTree.toList,
      (lctCutCost pathPayload st u v).1.splay.nodes z = st.splay.nodes z) ∧
    (∀ C : ℤ, 0 ≤ C →
      (∀ i val, (i, some val) ∈ forestPairs pathPayload st.splay trees →
        |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C) →
      PathNodeBound C ((lctCutCost pathPayload st u v).1.splay.nodes e) ∧
      (∀ i val, (i, some val) ∈ forestPairs pathPayload (lctCutCost pathPayload st u v).1.splay ts →
        |val.gradient| ≤ C ∧ |val.length| ≤ C ∧ |val.flow| ≤ C ∧ |val.detector| ≤ C))
  rw [eqResult]
  have heResult : result = ⟨pushed.n,
      (SplayState.detachRootChildren pathPayload
        (pushed.splay.splay pathPayload (2 * pushed.n + 1) candidateEdge) candidateEdge).setPar candidateEdge pushed.freeHead,
      candidateEdge⟩ := rfl
  rw [heResult]
  refine ⟨candidateEdge, bs, d, WB, hbB, ?_, ?_⟩
  · intro z hz
    have hz₁ : z ∉ ts.flatMap AuxTree.toList := fun hm => hz (lct_active_mem_of_same_freeList W W₁ rfl hm)
    have hzA : z ∉ as.flatMap AuxTree.toList := fun hm => hz₁ (lct_active_mem_of_same_freeList W₁ WA rfl hm)
    have hzP : z ∉ (tr :: as.erase (.node v leftTree .leaf)).flatMap AuxTree.toList := fun hm =>
      hzA (lct_active_mem_of_same_freeList WA WP rfl hm)
    exact (frameB z hzP).trans ((frameP z hzA).trans ((frame₂ z hz₁).trans (frame₁ z hz)))

  · intro C hC bounds
    constructor
    · apply freed C hC
      intro i val hm
      rw [evalP] at hm
      have hmA : (i, some val) ∈ forestPairs pathPayload exposed.splay as :=
        List.mem_flatMap.mpr ⟨_, ha, hm⟩
      exact pathForestAccounts_reroot_bound W htu hum hu W₁ bounds i val
        (hpermA.mem_iff.mp hmA)
    · intro i val hm
      rw [← heResult, ← eqResult] at hm
      have Wcut : LctInvWith pathPayload (lctCutCost pathPayload st u v).1 bs (edge :: freeList) d := by
        rw [eqResult, heResult, ← heq]
        exact WB
      obtain ⟨t, ht, htPair⟩ := List.mem_flatMap.mp hm
      have htF := lct_tree_mem_of_same_pointers Wf Wcut rfl
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ht
      have hmF : (i, some val) ∈ forestPairs pathPayload (lctCutCost pathPayload st u v).1.splay tf :=
        List.mem_flatMap.mpr ⟨t, htF, htPair⟩
      exact pathForestAccounts_reroot_bound W htu hum hu WR bounds i val
        (hpermF.mem_iff.mp (List.mem_cons_of_mem (edge, released) hmF))

/-- After Cut the inactive records satisfy the previous bound when the
initial evaluated accounts satisfy that bound as well. -/
theorem lctCut_inactive_nodeBound
    {st next : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ} {edge : ℕ} {B : ℤ}
    (W : LctInvWith pathPayload st trees freeList depth)
    (W' : LctInvWith pathPayload next trees' (edge :: freeList) depth')
    (hn : next.n = st.n)
    (hframe : ∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z)
    (hedge : PathNodeBound B (next.splay.nodes edge))
    (hb : ∀ z ≤ 2 * st.n, z ∉ trees.flatMap AuxTree.toList → PathNodeBound B (st.splay.nodes z)) :
    ∀ z ≤ 2 * next.n, z ∉ trees'.flatMap AuxTree.toList → PathNodeBound B (next.splay.nodes z) := by
  intro z hsize hz
  by_cases he : z = edge
  · subst z
    exact hedge
  have old : z ∉ trees.flatMap AuxTree.toList := by
    intro ha
    have hva := W.activeValid z ha
    by_cases hv : z ≤ st.n
    · have h := W'.verticesActive (z - 1) (by rw [hn]; have := hva.1; omega)
      exact hz (by simpa [vid, Nat.sub_add_cancel hva.1] using h)
    · have hes : isEdgeSlot st.n z := ⟨by omega, hva.2⟩
      have hf := (W.partitionSlots z hes).mp ha
      exact hz ((W'.partitionSlots z (hn.symm ▸ hes)).mpr fun hm =>
        (List.mem_cons.mp hm).elim he hf)
  rw [hframe z old]
  exact hb z (by rwa [hn] at hsize) old

end MinCostFlow.MinRatio
