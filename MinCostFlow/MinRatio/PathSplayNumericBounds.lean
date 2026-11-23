module

public import MinCostFlow.MinRatio.PathTreeNumericBounds
public import MinCostFlow.LinkCut.ForestExposeOps
public import MinCostFlow.LinkCut.ForestModelOps
public import MinCostFlow.LinkCut.ForestModelSplice
import MinCostFlow.LinkCut.ForestReversals
import MinCostFlow.LinkCut.ForestSplices
import MinCostFlow.LinkCut.ForestCutLink
import MinCostFlow.LinkCut.ForestExposeSpec

/-!
# Cumulative tag bounds during splaying

The range proof for Section 6 (pages 29–30) follows the splay model's
ancestor pushes and rotations. A cleared rotation preserves every
route's tag charge, and the ancestor pushes can only lower it.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut

private theorem rotate_tag_bound
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {pivot x : ℕ} {B : ℤ}
    (ht : SplayState.TreeInv pathPayload s t) (hp : pivot ∈ t.toList)
    (hx : x ∈ t.toList) (ha : pivot ∈ t.pathTo x)
    (hclean : ∀ u ∈ t.pathTo x,
      (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hprefix : ∀ u ∈ t.pathTo pivot, u ∈ t.pathTo x)
    (hb : ∀ u ∈ t.toList, pathTagRouteMagnitude s (t.pathTo u) ≤ B) :
    let next := s.rotate pathPayload pivot
    let ts := t.rotateAt pivot
    SplayState.TreeInv pathPayload next ts ∧ ts.toList.Perm t.toList ∧ x ∈ ts.toList ∧
      (∀ u ∈ ts.pathTo x, (next.nodes u).rev = false ∧ (next.nodes u).tag = pathPayload.idTag) ∧
      (∀ u ∈ ts.toList, pathTagRouteMagnitude next (ts.pathTo u) ≤ B) := by
  dsimp only
  by_cases hr : pivot = t.rootId
  · have hp0 : (s.nodes pivot).par = 0 := by
      rw [SplayState.SubtreeInv_par_eq_parentIn ht.nodup ht.sub hp, hr]
      cases t with
      | leaf => rfl
      | node id l r => simp [AuxTree.parentIn, AuxTree.rootId]
    have htree : t.rotateAt pivot = t := by
      rw [hr]
      cases t <;> simp [AuxTree.rootId]
    simp only [htree, SplayState.rotate, hp0, ite_true, ite_self]
    exact ⟨ht, List.Perm.refl _, hx, hclean, hb⟩
  have hpclean u (hu : u ∈ t.pathTo pivot) := hclean u (hprefix u hu)
  obtain ⟨ht', hperm, _, _, _, htags⟩ :=
    SplayState.rotate_preserves pathPayload_laws ht hp hr hpclean
  refine ⟨ht', hperm, hperm.mem_iff.mpr hx, ?_, fun u hu => ?_⟩
  · intro u hu
    have h := AuxTree.rotateAt_pathTo_subset ht.nodup hx ha u hu
    obtain ⟨hrev, htag⟩ := htags u (AuxTree.mem_pathTo h)
    rw [hrev, htag]
    exact hclean u h
  · rw [pathTagRouteMagnitude_rotate_eq ht hp hr hpclean]
    exact hb u (hperm.mem_iff.mp hu)

private theorem splayStep_tag_bound
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {x : ℕ} {B : ℤ}
    (ht : SplayState.TreeInv pathPayload s t) (hx : x ∈ t.toList)
    (hpar : (s.nodes x).par ≠ 0)
    (hclean : ∀ u ∈ t.pathTo x,
      (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
    (hb : ∀ u ∈ t.toList, pathTagRouteMagnitude s (t.pathTo u) ≤ B) :
    let next := s.splayStep pathPayload x
    ∃ ts, SplayState.TreeInv pathPayload next ts ∧ ts.toList.Perm t.toList ∧ x ∈ ts.toList ∧
      (∀ u ∈ ts.pathTo x, (next.nodes u).rev = false ∧ (next.nodes u).tag = pathPayload.idTag) ∧
      (∀ u ∈ ts.toList, pathTagRouteMagnitude next (ts.pathTo u) ≤ B) := by
  dsimp only
  have hnz := SplayState.SubtreeInv_nonZero ht.sub hx
  have hparEq := SplayState.SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
  have hxr : x ≠ t.rootId := by
    intro he
    apply hpar
    rw [hparEq, he]
    cases t with
    | leaf => rfl
    | node id l r => simp [AuxTree.parentIn, AuxTree.rootId]
  obtain ⟨hp, _, hpath⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
  let parent := (s.nodes x).par
  have hp' : parent ∈ t.toList := by simpa only [parent, hparEq] using hp
  have hprefix u (hu : u ∈ t.pathTo parent) : u ∈ t.pathTo x := by
    rw [hpath]
    apply List.mem_append_left
    simpa only [parent, hparEq] using hu
  have hself := AuxTree.self_mem_pathTo hx
  have hsingle := rotate_tag_bound ht hx hx hself hclean (fun _ h => h) hb
  simp only [SplayState.splayStep, hnz, hpar, ite_false]
  split
  · exact ⟨t.rotateAt x, hsingle⟩
  split
  · obtain ⟨ht', hp₁, hx', hclean', hb'⟩ := rotate_tag_bound ht hp' hx
      (hprefix _ (AuxTree.self_mem_pathTo hp')) hclean hprefix hb
    obtain ⟨ht'', hp₂, hx'', hc'', hb''⟩ :=
      rotate_tag_bound ht' hx' hx' (AuxTree.self_mem_pathTo hx') hclean' (fun _ h => h) hb'
    exact ⟨_, ht'', hp₂.trans hp₁, hx'', hc'', hb''⟩
  · obtain ⟨ht', hp₁, hx', hclean', hb'⟩ := hsingle
    obtain ⟨ht'', hp₂, hx'', hc'', hb''⟩ :=
      rotate_tag_bound ht' hx' hx' (AuxTree.self_mem_pathTo hx') hclean' (fun _ h => h) hb'
    exact ⟨_, ht'', hp₂.trans hp₁, hx'', hc'', hb''⟩

/-- Splaying preserves a uniform route bound on its auxiliary tree. -/
theorem pathTagRouteMagnitude_splay_bound {fuel : ℕ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t : AuxTree} {x : ℕ} {B : ℤ}
    (ht : SplayState.TreeInv pathPayload s t) (hx : x ∈ t.toList) (hd : t.depthOf x < fuel)
    (hb : ∀ u ∈ t.toList, pathTagRouteMagnitude s (t.pathTo u) ≤ B) :
    let next := s.splay pathPayload fuel x
    ∃ ts, SplayState.TreeInv pathPayload next ts ∧ ts.toList.Perm t.toList ∧
      ∀ u ∈ ts.toList, pathTagRouteMagnitude next (ts.pathTo u) ≤ B := by
  have loop (k : ℕ) {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
      {t : AuxTree} (ht : SplayState.TreeInv pathPayload s t) (hx : x ∈ t.toList)
      (hclean : ∀ u ∈ t.pathTo x, (s.nodes u).rev = false ∧ (s.nodes u).tag = pathPayload.idTag)
      (hb : ∀ u ∈ t.toList, pathTagRouteMagnitude s (t.pathTo u) ≤ B) :
      ∃ ts, SplayState.TreeInv pathPayload (s.splayLoop pathPayload k x) ts ∧ ts.toList.Perm t.toList ∧
        ∀ u ∈ ts.toList, pathTagRouteMagnitude (s.splayLoop pathPayload k x) (ts.pathTo u) ≤ B := by
    induction k generalizing s t with
    | zero => exact ⟨t, ht, List.Perm.refl _, hb⟩
    | succ k ih =>
      have hnz := SplayState.SubtreeInv_nonZero ht.sub hx
      by_cases hpar : (s.nodes x).par = 0
      · simpa only [SplayState.splayLoop, hnz, ite_false, hpar, ite_true] using
          (show ∃ ts, SplayState.TreeInv pathPayload s ts ∧ ts.toList.Perm t.toList ∧
            ∀ u ∈ ts.toList, pathTagRouteMagnitude s (ts.pathTo u) ≤ B from ⟨t, ht, List.Perm.refl _, hb⟩)
      obtain ⟨ts, ht', hp₁, hx', hclean', hb'⟩ := splayStep_tag_bound ht hx hpar hclean hb
      obtain ⟨us, hu, hp₂, hb''⟩ := ih ht' hx' hclean' hb'
      exact ⟨us, by simpa only [SplayState.splayLoop, hnz, ite_false, hpar] using hu,
        hp₂.trans hp₁, by simpa only [SplayState.splayLoop, hnz, ite_false, hpar] using hb''⟩
  obtain ⟨ts, ht', hperm, _, _, hpath, _, hclean, _⟩ :=
    SplayState.pushPath_preserves pathPayload_laws ht hx hd
  have hb' u (hu : u ∈ ts.toList) :
      pathTagRouteMagnitude (s.pushPath pathPayload fuel x) (ts.pathTo u) ≤ B := by
    rw [hpath]
    exact (pathTagRouteMagnitude_pushPath_le ht hx hd (hperm.mem_iff.mp hu)).trans
      (hb u (hperm.mem_iff.mp hu))
  have hnz := SplayState.SubtreeInv_nonZero ht.sub hx
  obtain ⟨us, hu, hp, hb''⟩ := loop fuel ht' (hperm.mem_iff.mpr hx) hclean hb'
  exact ⟨us, by simpa only [SplayState.splay, hnz, ite_false] using hu, hp.trans hperm,
    by simpa only [SplayState.splay, hnz, ite_false] using hb''⟩

private theorem auxTree_eq_of_rootId
    {s s' : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t u : AuxTree} {parent : ℕ}
    (ht : SplayState.SubtreeInv pathPayload s parent t)
    (hu : SplayState.SubtreeInv pathPayload s' parent u)
    (hleft : ∀ z ∈ u.toList, (s.nodes z).left = (s'.nodes z).left)
    (hright : ∀ z ∈ u.toList, (s.nodes z).right = (s'.nodes z).right)
    (hr : t.rootId = u.rootId) : t = u := by
  induction t generalizing u parent with
  | leaf =>
    cases u with
    | leaf => rfl
    | node id l r =>
      rw [SplayState.SubtreeInv.eq_2] at hu
      exact (hu.1 hr.symm).elim
  | node id l r ihl ihr =>
    rw [SplayState.SubtreeInv.eq_2] at ht
    cases u with
    | leaf => exact (ht.1 hr).elim
    | node id' l' r' =>
      change id = id' at hr
      subst id'
      rw [SplayState.SubtreeInv.eq_2] at hu
      have hid : id ∈ (AuxTree.node id l' r').toList := by simp [AuxTree.toList]
      have inclL z (hz : z ∈ l'.toList) : z ∈ (AuxTree.node id l' r').toList := by
        simp [AuxTree.toList, hz]
      have inclR z (hz : z ∈ r'.toList) : z ∈ (AuxTree.node id l' r').toList := by
        simp [AuxTree.toList, hz]
      rw [ihl ht.2.2.2.2.2.2.2.1 hu.2.2.2.2.2.2.2.1
          (fun z hz => hleft z (inclL z hz)) (fun z hz => hright z (inclL z hz))
          (ht.2.1.symm.trans ((hleft id hid).trans hu.2.1)),
        ihr ht.2.2.2.2.2.2.2.2 hu.2.2.2.2.2.2.2.2
          (fun z hz => hleft z (inclR z hz)) (fun z hz => hright z (inclR z hz))
          (ht.2.2.1.symm.trans ((hright id hid).trans hu.2.2.1))]

/-- The route bound holds on the auxiliary tree rooted at the splayed node. -/
theorem pathTagRouteMagnitude_splay_bound_of_root {fuel : ℕ}
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {t u : AuxTree} {x : ℕ} {B : ℤ}
    (ht : SplayState.TreeInv pathPayload s t) (hx : x ∈ t.toList) (hd : t.depthOf x < fuel)
    (hb : ∀ y ∈ t.toList, pathTagRouteMagnitude s (t.pathTo y) ≤ B)
    (hu : SplayState.TreeInv pathPayload (s.splay pathPayload fuel x) u)
    (hr : u.rootId = x) :
    ∀ y ∈ u.toList, pathTagRouteMagnitude (s.splay pathPayload fuel x) (u.pathTo y) ≤ B := by
  obtain ⟨v, hv, hp, hbound⟩ := pathTagRouteMagnitude_splay_bound ht hx hd hb
  have hx₀ := SplayState.SubtreeInv_nonZero ht.sub hx
  have hpar : ((s.splay pathPayload fuel x).nodes x).par = 0 := by
    cases u with
    | leaf => exact (hx₀ hr.symm).elim
    | node id l r =>
      change id = x at hr
      subst id
      have hs := hu.sub
      rw [SplayState.SubtreeInv.eq_2] at hs
      exact hs.2.2.2.1
  have hxv := hp.mem_iff.mpr hx
  have hroot : v.rootId = x := by
    by_contra hn
    obtain ⟨hm, _, _⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) hv.nodup hxv (Ne.symm hn)
    have he := SplayState.SubtreeInv_par_eq_parentIn hv.nodup hv.sub hxv
    rw [← he, hpar] at hm
    exact SplayState.SubtreeInv_nonZero hv.sub hm rfl
  rw [← auxTree_eq_of_rootId hv.sub hu.sub (fun _ _ => rfl) (fun _ _ => rfl) (hroot.trans hr.symm)]
  exact hbound

/-- Splaying in a link-cut forest preserves the route bound on all auxiliary trees. -/
theorem lctSplayTree_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {x : ℕ} {B : ℤ} (ht : t ∈ trees) (hx : x ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let next := { st with splay := st.splay.splay pathPayload (2 * st.n + 1) x }
    ∃ u, u.rootId = x ∧
      (next.splay.nodes x).rev = false ∧ (next.splay.nodes x).tag = pathPayload.idTag ∧
      LctInvWith pathPayload next (u :: trees.erase t) freeList depth ∧
      (∀ z ∉ t.toList, next.splay.nodes z = st.splay.nodes z) ∧
      ∀ c ∈ u :: trees.erase t, ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B := by
  dsimp only
  obtain ⟨u, _, hr, _, _, hrev, htag, W', _, _, _, hout, _⟩ :=
    lctSplayTree_spec pathPayload_laws W ht hx
  refine ⟨u, hr, hrev, htag, W', hout, ?_⟩
  intro c hc y hy
  rcases List.mem_cons.mp hc with rfl | hc
  · have hd := SplayState.depthOf_lt_countNodes hx
    rw [← AuxTree.length_toList] at hd
    have hlen := tree_length_le_active ht
    have hactive := active_length_le_two_mul W.activeNodup W.activeValid
    exact pathTagRouteMagnitude_splay_bound_of_root (W.treesInv t ht) hx
      (by omega) (hb t ht) (W'.treesInv _ List.mem_cons_self) hr y hy
  · have hct : c ∈ trees := List.mem_of_mem_erase hc
    have he : pathTagRouteMagnitude (st.splay.splay pathPayload (2 * st.n + 1) x) (c.pathTo y) =
        pathTagRouteMagnitude st.splay (c.pathTo y) := by
      unfold pathTagRouteMagnitude
      congr 1
      apply List.map_congr_left
      intro z hz
      rw [hout z (erase_flatMap_disjoint_of_nodup ht W.activeNodup z
        (List.mem_flatMap.mpr ⟨c, hc, AuxTree.mem_pathTo hz⟩))]
    exact he.le.trans (hb c hct y hy)

/-- A right detach at a clean root preserves the route bound across the forest. -/
theorem lctDetachRight_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {x : ℕ} {left right : AuxTree} {B : ℤ}
    (ht : AuxTree.node x left right ∈ trees)
    (hrev : (st.splay.nodes x).rev = false)
    (htag : (st.splay.nodes x).tag = pathPayload.idTag)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let next := { st with splay := st.splay.detachRight pathPayload x }
    let trees' := if right = .leaf then trees else
      AuxTree.node x left .leaf :: right :: trees.erase (.node x left right)
    LctInvWith pathPayload next trees' freeList depth ∧
      ∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B := by
  dsimp only
  refine ⟨(detachRight_spec pathPayload_laws W ht hrev htag).1, ?_⟩
  have frame c (hc : c ∈ trees) y (hy : y ∈ c.toList) :
      pathTagRouteMagnitude (st.splay.detachRight pathPayload x) (c.pathTo y) ≤ B := by
    rw [pathTagRouteMagnitude_congr _ (detachRight_tag_eq st.splay x)]
    exact hb c hc y hy
  split
  · exact frame
  · intro c hc y hy
    rcases List.mem_cons.mp hc with rfl | hc
    · have hleft : y = x ∨ y ∈ left.toList := by
        simpa [AuxTree.toList, or_comm] using hy
      rw [(pathTagRouteMagnitude_rightSplice_retained (right := right) hleft).1]
      apply hb _ ht y
      rcases hleft with rfl | hy
      · simp [AuxTree.toList]
      · simp [AuxTree.toList, hy]
    · rcases List.mem_cons.mp hc with rfl | hc
      · rw [pathTagRouteMagnitude_detachRight (W.treesInv _ ht) htag hy]
        exact hb _ ht y (by simp [AuxTree.toList, hy])
      · exact frame c (List.mem_of_mem_erase hc) y hy

/-- Replacing two auxiliary trees by their clean right splice preserves every route bound. -/
theorem lctAttachRight_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {x : ℕ} {left right : AuxTree} {B : ℤ}
    (hl : AuxTree.node x left .leaf ∈ trees) (hr : right ∈ trees)
    (hnd : (AuxTree.node x left right).toList.Nodup)
    (htag : (st.splay.nodes x).tag = pathPayload.idTag)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∀ c ∈ AuxTree.node x left right :: (trees.erase (.node x left .leaf)).erase right,
      ∀ y ∈ c.toList,
        pathTagRouteMagnitude (st.splay.attachRight pathPayload x right.rootId) (c.pathTo y) ≤ B := by
  intro c hc y hy
  rcases List.mem_cons.mp hc with rfl | hc
  · by_cases hyr : y ∈ right.toList
    · rw [pathTagRouteMagnitude_attachRight hnd htag hyr]
      exact hb _ hr y hyr
    · have hleft : y = x ∨ y ∈ left.toList := by
        simpa [AuxTree.toList, hyr, or_comm] using hy
      rw [(pathTagRouteMagnitude_rightSplice_retained (right := right) hleft).2]
      exact hb _ hl y (by simpa [AuxTree.toList, or_comm] using hleft)
  · rw [pathTagRouteMagnitude_congr _ (attachRight_tag_eq st.splay x right.rootId)]
    exact hb c (List.mem_of_mem_erase (List.mem_of_mem_erase hc)) y hy

/-- The vertex count and free slots determine which node IDs are active. -/
theorem lct_active_mem_of_same_freeList
    {st st' : PathTreeState} {trees trees' : List AuxTree} {freeList : List ℕ}
    {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    (W' : LctInvWith pathPayload st' trees' freeList depth')
    (hn : st'.n = st.n) {x : ℕ} (hxr : x ∈ trees'.flatMap AuxTree.toList) :
    x ∈ trees.flatMap AuxTree.toList := by
  have hv := W'.activeValid x hxr
  rw [hn] at hv
  by_cases hvertex : x ≤ st.n
  · have hpos : 1 ≤ x := hv.1
    have h := W.verticesActive (x - 1) (by omega)
    have he : vid (x - 1) = x := by unfold vid; omega
    rwa [he] at h
  · have he : isEdgeSlot st.n x := ⟨by omega, hv.2⟩
    exact (W.partitionSlots x he).mpr ((W'.partitionSlots x (hn.symm ▸ he)).mp hxr)

/-- The first phase of Expose splays its vertex and detaches the right subtree. -/
theorem lctExposeInit_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {x : ℕ} {B : ℤ} (ht : t ∈ trees) (hx : x ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let splay := st.splay.splay pathPayload (2 * st.n + 1) x
    let next := { st with splay := splay.detachRight pathPayload x }
    ∃ trees' left, AuxTree.node x left .leaf ∈ trees' ∧
      LctInvWith pathPayload next trees' freeList depth ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) := by
  dsimp only
  obtain ⟨u, hr, hrev, htag, W', hout, hb'⟩ := lctSplayTree_route_bound W ht hx hb
  cases u with
  | leaf => exact (SplayState.SubtreeInv_nonZero (W.treesInv t ht).sub hx hr.symm).elim
  | node id left right =>
    change id = x at hr
    subst id
    let trees₀ := AuxTree.node x left right :: trees.erase t
    let trees' := if right = AuxTree.leaf then trees₀ else
      AuxTree.node x left .leaf :: right :: trees₀.erase (.node x left right)
    have h := lctDetachRight_route_bound (trees := trees₀) W' List.mem_cons_self hrev htag hb'
    have ht₀ : AuxTree.node x left right ∈ trees₀ := List.mem_cons_self
    refine ⟨trees', left, ?_, h.1, h.2, ?_⟩
    · by_cases hr : right = .leaf
      · subst right
        simp [trees', trees₀]
      · simp [trees', hr]
    · intro z hz
      have hz_t : z ∉ t.toList := fun hz' => hz (List.mem_flatMap.mpr ⟨t, ht, hz'⟩)
      have hz₀ : z ∉ (AuxTree.node x left right).toList := fun hz' =>
        hz (lct_active_mem_of_same_freeList W W' rfl (List.mem_flatMap.mpr ⟨_, ht₀, hz'⟩))
      have hd := SplayState.detachRight_preserves pathPayload_laws (W'.treesInv _ ht₀) hrev htag
      exact (hd.2.2.2.2.2.2.2 z hz₀).trans (hout z hz_t)

/-- After the path parent is splayed, an Expose splice preserves the route bound. -/
theorem lctExposeSplice_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {x : ℕ} {left right prev : AuxTree} {B : ℤ}
    (ht : AuxTree.node x left right ∈ trees) (hp : prev ∈ trees)
    (hne : AuxTree.node x left right ≠ prev)
    (hrev : (st.splay.nodes x).rev = false)
    (htag : (st.splay.nodes x).tag = pathPayload.idTag)
    (hpp : (st.splay.nodes prev.rootId).ppar = x)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let detached := { st with splay := st.splay.detachRight pathPayload x }
    let next := { detached with splay := detached.splay.attachRight pathPayload x prev.rootId }
    let base := if right = .leaf then trees else
      AuxTree.node x left .leaf :: right :: trees.erase (.node x left right)
    let trees' := AuxTree.node x left prev :: (base.erase (.node x left .leaf)).erase prev
    LctInvWith pathPayload next trees' freeList depth ∧
      ∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B := by
  intro detached next base trees'
  have W' : LctInvWith pathPayload next trees' freeList depth :=
    (exposeStep_heavy_light pathPayload_laws W ht hp hne hrev htag hpp).1
  have hl : AuxTree.node x left .leaf ∈ base := by
    by_cases hr : right = .leaf
    · subst right
      simpa [base] using ht
    · simp [base, hr]
  have hp' : prev ∈ base := by
    by_cases hr : right = .leaf
    · simpa [base, hr] using hp
    · have hm := (List.mem_erase_of_ne hne.symm).mpr hp
      simpa [base, hr] using
        (List.mem_cons_of_mem (AuxTree.node x left .leaf) (List.mem_cons_of_mem right hm))
  exact ⟨W', lctAttachRight_route_bound (st := detached) hl hp'
    (W'.treesInv _ List.mem_cons_self).nodup ((detachRight_tag_eq st.splay x x).trans htag)
    (lctDetachRight_route_bound W ht hrev htag hb).2⟩

/-- An Expose iteration preserves the route bound when the path parent lies in
a different auxiliary tree. -/
theorem lctExposeStep_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {parent prev : AuxTree} {last : ℕ} {B : ℤ}
    (hp : parent ∈ trees) (hprev : prev ∈ trees)
    (hne : parent ≠ prev) (hr : prev.rootId = last)
    (hparent : (st.splay.nodes last).ppar ∈ parent.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let next := (lctExposeStep pathPayload st last).1
    ∃ trees' left, AuxTree.node (st.splay.nodes last).ppar left prev ∈ trees' ∧
      LctInvWith pathPayload next trees' freeList depth ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) := by
  dsimp only
  let x := (st.splay.nodes last).ppar
  obtain ⟨u, hu, hrev, htag, W', hout, hb'⟩ := lctSplayTree_route_bound W hp hparent hb
  cases u with
  | leaf => exact (SplayState.SubtreeInv_nonZero (W.treesInv parent hp).sub hparent hu.symm).elim
  | node id left right =>
    change id = x at hu
    subst id
    let trees₀ := AuxTree.node x left right :: trees.erase parent
    have ht : AuxTree.node x left right ∈ trees₀ := List.mem_cons_self
    have hprev₀ : prev ∈ trees₀ := List.mem_cons_of_mem _ ((List.mem_erase_of_ne hne.symm).mpr hprev)
    have hdisj y (hy : y ∈ prev.toList) : y ∉ parent.toList := fun hm =>
      hne (flatMap_mem_unique W.activeNodup hp hprev hm hy)
    have hne₀ : AuxTree.node x left right ≠ prev := fun h =>
      hdisj x (h ▸ (by simp [AuxTree.toList])) hparent
    have hpp : ((st.splay.splay pathPayload (2 * st.n + 1) x).nodes prev.rootId).ppar = x := by
      rw [hout _ (hdisj _ (AuxTree.rootId_mem (W.treesNonEmpty _ hprev))), hr]
    have h := lctExposeSplice_route_bound (trees := trees₀) W' ht hprev₀ hne₀ hrev htag hpp hb'
    change ∃ ts l, AuxTree.node x l prev ∈ ts ∧ _
    have he : (lctExposeStep pathPayload st last).1 =
        { st with splay := ((st.splay.splay pathPayload (2 * st.n + 1) x).detachRight
            pathPayload x).attachRight pathPayload x prev.rootId } := by
      rw [hr]
      rfl
    rw [he]
    refine ⟨_, left, List.mem_cons_self, h.1, h.2, ?_⟩
    intro z hz
    let splay := st.splay.splay pathPayload (2 * st.n + 1) x
    let detached := splay.detachRight pathPayload x
    have hz₀ : z ∉ (AuxTree.node x left right).toList := fun hm =>
      hz (lct_active_mem_of_same_freeList W W' rfl (List.mem_flatMap.mpr ⟨_, ht, hm⟩))
    have hd := SplayState.detachRight_preserves pathPayload_laws (W'.treesInv _ ht) hrev htag
    have hdetach : detached.nodes z = splay.nodes z := hd.2.2.2.2.2.2.2 z hz₀
    have hzx : z ≠ x := fun h => hz (List.mem_flatMap.mpr ⟨parent, hp, h ▸ hparent⟩)
    have hzprev : z ≠ prev.rootId := fun h => hz (List.mem_flatMap.mpr
      ⟨prev, hprev, h ▸ AuxTree.rootId_mem (W.treesNonEmpty _ hprev)⟩)
    have hatt : (detached.attachRight pathPayload x prev.rootId).nodes z = detached.nodes z := by
      by_cases hx0 : x = 0
      · simp [SplayState.attachRight, hx0]
      by_cases hr0 : prev.rootId = 0
      · simp [SplayState.attachRight, SplayState.pull, SplayState.setRight, hx0, hr0, hzx]
      · simp [SplayState.attachRight, SplayState.pull, SplayState.setRight, SplayState.setPar,
          SplayState.setPpar, hx0, hr0, hzx, hzprev]
    exact hatt.trans (hdetach.trans (hout z (fun hm => hz (List.mem_flatMap.mpr ⟨_, hp, hm⟩))))

/-- Every iteration of the bottom-up Expose loop preserves the uniform route bound. -/
theorem lctExposeLoop_route_bound (fuel : ℕ)
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {prev : AuxTree} {last v : ℕ} {B : ℤ}
    (hprev : prev ∈ trees) (hr : prev.rootId = last) (hv : v ∈ prev.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let result := lctExposeLoop pathPayload st fuel last
    ∃ trees' prev', prev' ∈ trees' ∧ prev'.rootId = result.2.1 ∧ v ∈ prev'.toList ∧
      LctInvWith pathPayload result.1 trees' freeList depth ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude result.1.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, result.1.splay.nodes z = st.splay.nodes z) := by
  induction fuel generalizing st trees prev last with
  | zero => exact ⟨trees, prev, hprev, hr, hv, W, hb, fun _ _ => rfl⟩
  | succ fuel ih =>
    let x := (st.splay.nodes last).ppar
    by_cases hzero : x = 0
    · simpa only [lctExposeLoop, show (st.splay.nodes last).ppar = 0 from hzero,
        beq_self_eq_true, ite_true] using
        (show ∃ ts u, u ∈ ts ∧ u.rootId = last ∧ v ∈ u.toList ∧ LctInvWith pathPayload st ts freeList depth ∧
          (∀ c ∈ ts, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) ∧
          (∀ z ∉ trees.flatMap AuxTree.toList, st.splay.nodes z = st.splay.nodes z) from
          ⟨trees, prev, hprev, hr, hv, W, hb, fun _ _ => rfl⟩)
    have hx : x ∈ trees.flatMap AuxTree.toList := by
      have h := W.pparActive prev hprev
      rw [hr] at h
      exact h hzero
    obtain ⟨parent, hp, hparent⟩ := List.mem_flatMap.mp hx
    have hne : parent ≠ prev := by
      intro h
      have hxp : x ∈ prev.toList := h ▸ hparent
      let head := listHead0 (treeIds pathPayload st.splay prev)
      have hhead : head ∈ prev.toList :=
        listHead0_mem_of_ne_nil (W.treesNonEmpty prev hprev)
      have hheadActive := List.mem_flatMap.mpr ⟨prev, hprev, hhead⟩
      have hpar : inducedSubPar pathPayload st.splay trees head = x := by
        rw [inducedSubPar_eq_of_mem W.activeNodup hprev hhead]
        have hh := treeIds_ne_nil (P := pathPayload) (s := st.splay) (W.treesNonEmpty prev hprev)
        cases hids : treeIds pathPayload st.splay prev with
        | nil => exact (hh hids).elim
        | cons a rest => simp [head, listHead0, hids, chainPred, hr, x]
      have hreaches := tree_reaches_head W hprev hxp
      have hle := depth_le_of_reaches (fun _ hz hp => W.subPar_mem_active hz hp) W.acyclic
        (trees.flatMap AuxTree.toList).length head x hreaches hx
      have hlt := W.acyclic head hheadActive (by rw [hpar]; exact hzero)
      rw [hpar] at hlt
      omega
    obtain ⟨ts, left, ht, W', hb', frame⟩ := lctExposeStep_route_bound W hp hprev hne hr hparent hb
    have hroot : (AuxTree.node x left prev).rootId = (lctExposeStep pathPayload st last).2.1 := rfl
    obtain ⟨us, prev', hmem, hroot', hvm, W'', hb'', frame'⟩ :=
      ih W' ht hroot (show v ∈ (AuxTree.node x left prev).toList from
        by simp [AuxTree.toList, hv]) hb'
    simp only [lctExposeLoop, beq_false_of_ne (show (st.splay.nodes last).ppar ≠ 0 from hzero),
      Bool.false_eq_true, ite_false]
    refine ⟨us, prev', hmem, hroot', hvm, W'', hb'', ?_⟩
    intro z hz
    have hz' : z ∉ ts.flatMap AuxTree.toList := fun h =>
      hz (lct_active_mem_of_same_freeList W W' rfl h)
    exact (frame' z hz').trans (frame z hz)

/-- Expose preserves a uniform bound on all auxiliary path tag charges. -/
theorem lctExpose_route_bound_and_frame
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {v : ℕ} {B : ℤ} (ht : t ∈ trees) (hv : v ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∃ trees', LctInvWith pathPayload (lctExpose pathPayload st v) trees' freeList depth ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude (lctExpose pathPayload st v).splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, (lctExpose pathPayload st v).splay.nodes z = st.splay.nodes z) := by
  let first := { st with splay :=
    (st.splay.splay pathPayload (2 * st.n + 1) v).detachRight pathPayload v }
  obtain ⟨ts, left, hfirst, W₁, hb₁, frame₁⟩ := lctExposeInit_route_bound W ht hv hb
  obtain ⟨us, u, hu, _, hv₂, W₂, hb₂, frame₂⟩ :=
    lctExposeLoop_route_bound (2 * st.n + 1) (st := first) W₁ hfirst (last := v) rfl
      (show v ∈ (AuxTree.node v left .leaf).toList by simp [AuxTree.toList]) hb₁
  obtain ⟨q, _, _, _, W₃, frame₃, hb₃⟩ := lctSplayTree_route_bound W₂ hu hv₂ hb₂
  have hn := lctExposeLoop_n pathPayload (2 * st.n + 1) first v
  refine ⟨q :: us.erase u, by simpa only [hn, lctExpose, lctExposeCost, first] using W₃,
    by simpa only [hn, lctExpose, lctExposeCost, first] using hb₃, ?_⟩
  intro z hz
  have hz₁ : z ∉ ts.flatMap AuxTree.toList := fun hm =>
    hz (lct_active_mem_of_same_freeList W W₁ rfl hm)
  have hz₂ : z ∉ u.toList := fun hm => hz₁
    (lct_active_mem_of_same_freeList W₁ W₂ hn (List.mem_flatMap.mpr ⟨u, hu, hm⟩))
  have h := (frame₃ z hz₂).trans ((frame₂ z hz₁).trans (frame₁ z hz))
  simpa only [hn, lctExpose, lctExposeCost, first] using h

/-- Expose preserves a uniform route budget on the auxiliary trees. -/
theorem lctExpose_route_bound
    {st : PathTreeState} {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {v : ℕ} {B : ℤ} (ht : t ∈ trees) (hv : v ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∃ trees', LctInvWith pathPayload (lctExpose pathPayload st v) trees' freeList depth ∧
      ∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude (lctExpose pathPayload st v).splay (c.pathTo y) ≤ B := by
  obtain ⟨ts, W', hb', _⟩ := lctExpose_route_bound_and_frame W ht hv hb
  exact ⟨ts, W', hb'⟩

private theorem lct_tree_mem_of_pointers_on_tree
    {st st' : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees trees' : List AuxTree} {freeList freeList' : List ℕ} {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    (W' : LctInvWith pathPayload st' trees' freeList' depth')
    {c : AuxTree} (hc : c ∈ trees')
    (hx : c.rootId ∈ trees.flatMap AuxTree.toList)
    (hleft : ∀ z ∈ c.toList, (st.splay.nodes z).left = (st'.splay.nodes z).left)
    (hright : ∀ z ∈ c.toList, (st.splay.nodes z).right = (st'.splay.nodes z).right)
    (hparent : (st.splay.nodes c.rootId).par = (st'.splay.nodes c.rootId).par) :
    c ∈ trees := by
  let x := c.rootId
  have hxc := AuxTree.rootId_mem (W'.treesNonEmpty c hc)
  obtain ⟨a, ha, hxa⟩ := List.mem_flatMap.mp hx
  have hpar : (st.splay.nodes x).par = 0 := by
    rw [hparent]
    have h := SplayState.SubtreeInv_par_eq_parentIn
      (W'.treesInv c hc).nodup (W'.treesInv c hc).sub hxc
    cases c with
    | leaf => simp [AuxTree.toList] at hxc
    | node id l r => simpa [x, AuxTree.rootId, AuxTree.parentIn] using h
  have hr : a.rootId = x := by
    by_contra hn
    have h := W.treesInv a ha
    obtain ⟨hm, _, _⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) h.nodup hxa (Ne.symm hn)
    rw [← SplayState.SubtreeInv_par_eq_parentIn h.nodup h.sub hxa, hpar] at hm
    exact SplayState.SubtreeInv_nonZero h.sub hm rfl
  have he := auxTree_eq_of_rootId (W.treesInv a ha).sub (W'.treesInv c hc).sub hleft hright hr
  simpa only [he] using ha

/-- Forests with the same node pointers and free slots contain the same auxiliary trees. -/
theorem lct_tree_mem_of_same_pointers
    {st st' : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees trees' : List AuxTree} {freeList : List ℕ} {depth depth' : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    (W' : LctInvWith pathPayload st' trees' freeList depth')
    (hn : st'.n = st.n)
    (hleft : ∀ z, (st.splay.nodes z).left = (st'.splay.nodes z).left)
    (hright : ∀ z, (st.splay.nodes z).right = (st'.splay.nodes z).right)
    (hparent : ∀ z, (st.splay.nodes z).par = (st'.splay.nodes z).par)
    {c : AuxTree} (hc : c ∈ trees') : c ∈ trees := by
  let x := c.rootId
  have hxc := AuxTree.rootId_mem (W'.treesNonEmpty c hc)
  have hxr := List.mem_flatMap.mpr ⟨c, hc, hxc⟩
  have hx := lct_active_mem_of_same_freeList W W' hn hxr
  exact lct_tree_mem_of_pointers_on_tree W W' hc hx
    (fun z _ => hleft z) (fun z _ => hright z) (hparent _)

/-- The auxiliary-tree list presenting a physical forest is independent of its enumeration. -/
theorem lct_route_bound_of_same_state
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees trees' : List AuxTree} {freeList : List ℕ} {depth depth' : ℕ → ℕ} {B : ℤ}
    (W : LctInvWith pathPayload st trees freeList depth)
    (W' : LctInvWith pathPayload st trees' freeList depth')
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B :=
  fun c hc => hb c (lct_tree_mem_of_same_pointers W W' rfl
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) hc)

/-- Rerooting at a vertex preserves the route bound through Expose and reversal. -/
theorem lctReroot_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {v : ℕ} {B : ℤ} (ht : t ∈ trees) (hv : v ∈ t.toList)
    (hvertex : isVertex st.n v)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∃ trees' depth', LctInvWith pathPayload (lctReroot pathPayload st v) trees' freeList depth' ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude (lctReroot pathPayload st v).splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, (lctReroot pathPayload st v).splay.nodes z = st.splay.nodes z) := by
  obtain ⟨ts, W₁, hb₁, frame⟩ := lctExpose_route_bound_and_frame W ht hv hb
  obtain ⟨us, left, hmem, W₂, _, _, _, hpp, _, hrev, htag, _⟩ :=
    lctExpose_spec pathPayload_laws W ht hv
  let exposed := lctExpose pathPayload st v
  have hb₂ := lct_route_bound_of_same_state W₁ W₂ hb₁
  have hlast : isVertex exposed.n
      (listLast0 (treeIds pathPayload exposed.splay (.node v left .leaf))) := by
    change isVertex st.n (listLast0 (treeIds pathPayload (lctExposeCost pathPayload st v).1.splay (.node v left .leaf)))
    rw [listLast0_eq_root_of_right_leaf pathPayload_laws hrev htag]
    exact hvertex
  obtain ⟨depth', W₃, _, _, _, hout⟩ := revNode_spec pathPayload_laws W₂ hmem hpp hlast
  refine ⟨AuxTree.node v .leaf left :: us.erase (.node v left .leaf), depth', W₃, ?_, ?_⟩
  · intro c hc y hy
    change pathTagRouteMagnitude (exposed.splay.revNode pathPayload v) (c.pathTo y) ≤ B
    rw [pathTagRouteMagnitude_revNode]
    rcases List.mem_cons.mp hc with rfl | hc
    · have hn := (W₂.treesInv _ hmem).nodup
      rw [show AuxTree.node v .leaf left = (AuxTree.node v left .leaf).revRoot from rfl,
        SplayState.revRoot_pathTo hn]
      exact hb₂ _ hmem y ((SplayState.revRoot_toList_perm _).mem_iff.mp hy)
    · exact hb₂ c (List.mem_of_mem_erase hc) y hy
  · intro z hz
    have hzr : z ∉ (AuxTree.node v left .leaf).toList := fun hm =>
      hz (lct_active_mem_of_same_freeList W W₂ rfl (List.mem_flatMap.mpr ⟨_, hmem, hm⟩))
    exact (hout z hzr).trans (frame z hz)

/-- A path summary query preserves the tag budget for every auxiliary route. -/
theorem lctPathSummary_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {u v : ℕ} {B : ℤ} (ht : t ∈ trees) (hu : u ∈ t.toList)
    (huv : isVertex st.n u) (hvv : isVertex st.n v)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    ∃ trees' depth', LctInvWith pathPayload (lctPathSummary pathPayload st u v).1 trees' freeList depth' ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude (lctPathSummary pathPayload st u v).1.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, (lctPathSummary pathPayload st u v).1.splay.nodes z =
        st.splay.nodes z) := by
  obtain ⟨ts, d, W₁, hb₁, frame₁⟩ := lctReroot_route_bound W ht hu huv hb
  have ha : v ∈ ts.flatMap AuxTree.toList := by
    have hn : (lctReroot pathPayload st u).n = st.n := rfl
    have h := W₁.verticesActive (v - 1) (by rw [hn]; have := hvv.1; have := hvv.2; omega)
    have he : vid (v - 1) = v := by
      have hp := hvv.1
      unfold vid
      omega
    rwa [he] at h
  obtain ⟨t', ht', hv⟩ := List.mem_flatMap.mp ha
  obtain ⟨us, W₂, hb₂, frame₂⟩ := lctExpose_route_bound_and_frame W₁ ht' hv hb₁
  refine ⟨us, d, W₂, hb₂, ?_⟩
  intro z hz
  exact (frame₂ z (fun hm => hz (lct_active_mem_of_same_freeList W W₁ rfl hm))).trans (frame₁ z hz)

private theorem pathTo_nodup {t : AuxTree} (hn : t.toList.Nodup) (y : ℕ) :
    (t.pathTo y).Nodup := by
  induction t with
  | leaf => simp [AuxTree.pathTo]
  | node id left right ihl ihr =>
    obtain ⟨hl, hil, hr, hir, _⟩ := AuxTree.nodup_node_unfold hn
    by_cases hy : y = id
    · simp [AuxTree.pathTo, hy]
    · by_cases hyl : y ∈ left.toList
      · simpa [AuxTree.pathTo, hy, hyl] using
          List.nodup_cons.mpr ⟨fun h => hil (AuxTree.mem_pathTo h), ihl hl⟩
      · by_cases hyr : y ∈ right.toList
        · simpa [AuxTree.pathTo, hy, hyl, hyr] using
            List.nodup_cons.mpr ⟨fun h => hir (AuxTree.mem_pathTo h), ihr hr⟩
        · simp [AuxTree.pathTo, hy, hyl, hyr]

/-- Applying a path tag leaves all physical auxiliary tree pointers intact. -/
theorem pathApply_nodePointers
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (v : ℕ) (tag : PathTag) (z : ℕ) :
    ((s.applyTagNode pathPayload v tag).nodes z).left = (s.nodes z).left ∧
    ((s.applyTagNode pathPayload v tag).nodes z).right = (s.nodes z).right ∧
    ((s.applyTagNode pathPayload v tag).nodes z).par = (s.nodes z).par := by
  by_cases hv : v = 0
  · simp [SplayState.applyTagNode, hv]
  by_cases h : z = v
  · subst z
    rw [SplayState.applyTagNode, ite_eq_right hv, SplayState.nodes_updateNode_self]
    exact ⟨rfl, rfl, rfl⟩
  · rw [SplayState.applyTagNode, ite_eq_right hv, SplayState.nodes_updateNode_ne _ h]
    exact ⟨rfl, rfl, rfl⟩

/-- A path update increases the auxiliary route budget by at most its tag magnitude. -/
theorem lctPathApply_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {tu tv : AuxTree} {u v : ℕ} {B : ℤ}
    (htu : tu ∈ trees) (hu : u ∈ tu.toList) (huv : isVertex st.n u)
    (htv : tv ∈ trees) (hv : v ∈ tv.toList) (hvv : isVertex st.n v)
    (hconn : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u =
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B)
    (tag : PathTag) :
    let next := lctPathApply pathPayload st u v tag
    ∃ trees' depth', LctInvWith pathPayload next trees' freeList depth' ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList,
        pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B + pathTagMagnitude tag) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, next.splay.nodes z = st.splay.nodes z) := by
  dsimp only
  obtain ⟨ts, d, W₁, hb₁, frame⟩ := lctPathSummary_route_bound W htu hu huv hvv hb
  obtain ⟨us, _, depth', _, W₂, _⟩ := lctPathApply_spec pathPayload_laws W htu hu huv htv hv hconn tag
  refine ⟨us, depth', W₂, ?_, ?_⟩
  · intro c hc y hy
    let s := (lctPathSummary pathPayload st u v).1.splay
    have hv₀ : v ≠ 0 := Nat.ne_of_gt hvv.1
    have hptr z := pathApply_nodePointers s v tag z
    have hmem := lct_tree_mem_of_same_pointers W₁ W₂ rfl
      (fun z => (hptr z).1.symm) (fun z => (hptr z).2.1.symm) (fun z => (hptr z).2.2.symm) hc
    exact (pathTagRouteMagnitude_applyTagNode_le (s := s) hv₀ tag
      (pathTo_nodup (W₁.treesInv c hmem).nodup y)).trans (add_le_add_left (hb₁ c hmem y hy) _)

  · intro z hz
    have hne : z ≠ v := fun h => hz (List.mem_flatMap.mpr ⟨tv, htv, h ▸ hv⟩)
    change (((lctPathSummary pathPayload st u v).1.splay.applyTagNode pathPayload v tag).nodes z) =
      st.splay.nodes z
    rw [SplayState.applyTagNode, ite_eq_right (Nat.ne_of_gt hvv.1), SplayState.nodes_updateNode_ne _ hne]
    exact frame z hz

/-- Every represented vertex is active in the auxiliary forest. -/
theorem pathVertex_mem_active
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth) {v : ℕ} (hv : isVertex st.n v) :
    v ∈ trees.flatMap AuxTree.toList := by
  have h := W.verticesActive (v - 1) (by have := hv.1; have := hv.2; omega)
  simpa [vid, Nat.sub_add_cancel hv.1] using h

/-- Link preserves the route budget and inserts a singleton with no pending tag. -/
theorem lctLink_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {edge : ℕ} {freeRest : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees (edge :: freeRest) depth)
    {u v : ℕ} {B : ℤ} (hu : isVertex st.n u) (hv : isVertex st.n v)
    (hdisc : subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length u ≠
      subRoot (inducedSubPar pathPayload st.splay trees) (trees.flatMap AuxTree.toList).length v)
    (hB : 0 ≤ B)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B)
    (value : Option PathEdgeValue) :
    let next := lctLink pathPayload st u v value
    ∃ trees' depth', LctInvWith pathPayload next trees' freeRest depth' ∧
      (∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B) ∧
      (∀ z ∉ trees.flatMap AuxTree.toList, z ≠ edge → next.splay.nodes z = st.splay.nodes z) := by
  dsimp only
  let first := lctReroot pathPayload st v
  let second := lctReroot pathPayload first u
  obtain ⟨tv, htv, hv_mem⟩ := List.mem_flatMap.mp (pathVertex_mem_active W hv)
  obtain ⟨ts, d, W₁, hb₁, frame₁⟩ := lctReroot_route_bound W htv hv_mem hv hb
  have hu₁ : isVertex first.n u := hu
  obtain ⟨tu, htu, hu_mem⟩ := List.mem_flatMap.mp (pathVertex_mem_active W₁ hu₁)
  obtain ⟨us, d', W₂, hb₂, frame₂⟩ := lctReroot_route_bound W₁ htu hu_mem hu₁ hb₁
  obtain ⟨as, da, bs, db, W₂', W₃, _, hperm, _⟩ :=
    lctLink_spec pathPayload_laws W rfl hu hv hdisc value
  have hbound := lct_route_bound_of_same_state W₂ W₂' hb₂
  have hfh₀ := W.freeListInv.2.1
  have hfh₂ := W₂.freeListInv.2.1
  have hnz : edge ≠ 0 := hfh₀ ▸ W.freeListInv.1
  have huv : u ≠ v := fun h => hdisc (congrArg _ h)
  have hv₀ : v ≠ 0 := Nat.ne_of_gt hv.1
  have hu₀ : u ≠ 0 := Nat.ne_of_gt hu.1
  let s := second.splay
  let linked := (s.makeSingleton pathPayload edge value u).setPpar v edge
  have heq : (lctLinkCost pathPayload st u v value).1.splay = linked := by
    change (lctRerootCost pathPayload (lctRerootCost pathPayload st v).1 u).1.freeHead = edge at hfh₂
    have hstop : (u == 0 || v == 0 || u == v || st.freeHead == 0) = false := by
      simp [hu₀, hv₀, huv, hfh₀, hnz]
    simp [lctLinkCost, hstop, hfh₂, hnz, linked, s, second, first, lctReroot]
  have hptr z (hz : z ≠ edge) :
      (linked.nodes z).left = (s.nodes z).left ∧
      (linked.nodes z).right = (s.nodes z).right ∧
      (linked.nodes z).par = (s.nodes z).par := by
    by_cases h : z = v
    · subst z
      simp [linked, SplayState.setPpar, SplayState.makeSingleton, SplayState.setNode, hz]
    · simp [linked, SplayState.setPpar, SplayState.makeSingleton, SplayState.setNode, hz, h]
  have hve : edge ≠ v := by
    have h := W.freeValid edge List.mem_cons_self
    have hvn := hv.2
    intro he
    rw [he] at h
    exact (Nat.not_lt_of_ge hvn) h.1
  have hnode : linked.nodes edge =
      { left := 0, right := 0, par := 0, ppar := u, sz := 1, val := value,
        sum := pathPayload.single edge value, tag := pathPayload.idTag, rev := false } := by
    simp [linked, SplayState.setPpar, SplayState.makeSingleton, SplayState.setNode, hve]
  have charge := pathTagRouteMagnitude_linkSingleton s (edge := edge) (u := u) (v := v) value
  refine ⟨bs, db, W₃, ?_, ?_⟩
  · intro c hc y hy
    change pathTagRouteMagnitude (lctLinkCost pathPayload st u v value).1.splay (c.pathTo y) ≤ B
    rw [heq]
    by_cases hce : edge ∈ c.toList
    · have htree := W₃.treesInv c hc
      have hroot : c.rootId = edge := by
        by_contra h
        obtain ⟨hm, _, _⟩ := AuxTree.parentIn_mem_and_depth (p₀ := 0) htree.nodup hce (Ne.symm h)
        rw [← SplayState.SubtreeInv_par_eq_parentIn htree.nodup htree.sub hce, heq, hnode] at hm
        exact SplayState.SubtreeInv_nonZero htree.sub hm rfl
      cases c with
      | leaf => simp [AuxTree.toList] at hce
      | node id l r =>
        change id = edge at hroot
        subst id
        have hsub := htree.sub
        rw [SplayState.SubtreeInv.eq_2] at hsub
        rw [heq, hnode] at hsub
        have hl : l = .leaf := by
          cases l with
          | leaf => rfl
          | node id l r =>
            exact ((SplayState.SubtreeInv_nonZero hsub.2.2.2.2.2.2.2.1
              (by simp [AuxTree.toList] : id ∈ (AuxTree.node id l r).toList)) hsub.2.1.symm).elim
        have hr : r = .leaf := by
          cases r with
          | leaf => rfl
          | node id l r =>
            exact ((SplayState.SubtreeInv_nonZero hsub.2.2.2.2.2.2.2.2
              (by simp [AuxTree.toList] : id ∈ (AuxTree.node id l r).toList)) hsub.2.2.1.symm).elim
        subst l r
        have hy' : y = edge := by simpa [AuxTree.toList] using hy
        subst y
        simp only [AuxTree.pathTo, ite_true]
        exact charge.1.le.trans hB
    · have hcx := AuxTree.rootId_mem (W₃.treesNonEmpty c hc)
      have hxne : c.rootId ≠ edge := fun h => hce (h ▸ hcx)
      have hx := hperm.mem_iff.mp (List.mem_flatMap.mpr ⟨c, hc, hcx⟩)
      have hx₀ := (List.mem_cons.mp hx).resolve_left hxne
      have hc₀ := lct_tree_mem_of_pointers_on_tree W₂' W₃ hc hx₀
        (fun z hz => by rw [heq]; exact (hptr z (fun h => hce (h ▸ hz))).1.symm)
        (fun z hz => by rw [heq]; exact (hptr z (fun h => hce (h ▸ hz))).2.1.symm)
        (by rw [heq]; exact (hptr _ hxne).2.2.symm)
      rw [charge.2 _ (fun hm => hce (AuxTree.mem_pathTo hm))]
      exact hbound c hc₀ y hy

  · intro z hz hze
    have hzv : z ≠ v := fun h => hz (h ▸ pathVertex_mem_active W hv)
    change (lctLinkCost pathPayload st u v value).1.splay.nodes z = st.splay.nodes z
    rw [heq]
    have hm : linked.nodes z = s.nodes z := by
      simp [linked, SplayState.makeSingleton, SplayState.setNode, SplayState.setPpar, hze, hzv]
    exact hm.trans ((frame₂ z (fun h => hz (lct_active_mem_of_same_freeList W W₁ rfl h))).trans
      (frame₁ z hz))

/-- Pushing a node in the forest preserves the route budget in its tree and
leaves all other trees' tags intact. -/
theorem lctPushDown_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {t : AuxTree} {x : ℕ} {B : ℤ} (ht : t ∈ trees) (hx : x ∈ t.toList)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let next := { st with splay := st.splay.pushDown pathPayload x }
    let trees' := st.splay.pushDownTree x t :: trees.erase t
    LctInvWith pathPayload next trees' freeList depth ∧
    ∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B := by
  dsimp only
  have htree := W.treesInv t ht
  obtain ⟨hInv, hp, _, _, hpath, _, _, _, _, hpp, hout, hev⟩ :=
    SplayState.pushDown_preserves_TreeInv pathPayload_laws htree hx
  have hne : st.splay.pushDownTree x t ≠ .leaf := by
    intro he
    have hm := hp.mem_iff.mpr hx
    simp [he, AuxTree.toList] at hm
  refine ⟨(replaceSameIds_spec W ht hne hInv hp hev hpp hout).1, ?_⟩
  intro c hc y hy
  rcases List.mem_cons.mp hc with rfl | hc
  · have hy₀ := hp.mem_iff.mp hy
    rw [hpath]
    exact (pathTagRouteMagnitude_pushDown_le htree.nodup htree.sub hx hy₀).trans (hb t ht y hy₀)
  · have he : pathTagRouteMagnitude (st.splay.pushDown pathPayload x) (c.pathTo y) =
        pathTagRouteMagnitude st.splay (c.pathTo y) := by
      unfold pathTagRouteMagnitude
      congr 1
      apply List.map_congr_left
      intro z hz
      rw [hout z (erase_flatMap_disjoint_of_nodup ht W.activeNodup z
        (List.mem_flatMap.mpr ⟨c, hc, AuxTree.mem_pathTo hz⟩))]
    exact he.le.trans (hb c (List.mem_of_mem_erase hc) y hy)

/-- The final Cut splice frees the clean edge root and preserves both endpoint budgets. -/
theorem lctCutSplice_route_bound
    {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} {freeList : List ℕ} {depth : ℕ → ℕ}
    (W : LctInvWith pathPayload st trees freeList depth)
    {edge u v : ℕ} {B : ℤ}
    (ht : AuxTree.node edge (.node u .leaf .leaf) (.node v .leaf .leaf) ∈ trees)
    (hrev : (st.splay.nodes edge).rev = false)
    (htag : (st.splay.nodes edge).tag = pathPayload.idTag)
    (hpp : (st.splay.nodes edge).ppar = 0) (he : isEdgeSlot st.n edge)
    (hb : ∀ c ∈ trees, ∀ y ∈ c.toList, pathTagRouteMagnitude st.splay (c.pathTo y) ≤ B) :
    let detached := st.splay.detachRootChildren pathPayload edge
    let next : LctState _ _ _ := ⟨st.n, detached.setPar edge st.freeHead, edge⟩
    let trees' := AuxTree.node u .leaf .leaf :: AuxTree.node v .leaf .leaf ::
      trees.erase (.node edge (.node u .leaf .leaf) (.node v .leaf .leaf))
    LctInvWith pathPayload next trees' (edge :: freeList) depth ∧
      ∀ c ∈ trees', ∀ y ∈ c.toList, pathTagRouteMagnitude next.splay (c.pathTo y) ≤ B := by
  dsimp only
  refine ⟨(cut_splice_spec pathPayload_laws W ht hrev htag hpp he).1, ?_⟩
  have hn := (W.treesInv _ ht).nodup
  obtain ⟨_, hu₀, _, hv₀, huv₀⟩ := AuxTree.nodup_node_unfold hn
  have hu : u ≠ edge := fun h => hu₀ (by simp [AuxTree.toList, ← h])
  have hv : v ≠ edge := fun h => hv₀ (by simp [AuxTree.toList, ← h])
  have hvu : v ≠ u := fun h => huv₀ u (by simp [AuxTree.toList]) (by simp [AuxTree.toList, h])
  intro c hc y hy
  rw [pathTagRouteMagnitude_congr _ (setPar_tag_eq _ _ _),
    pathTagRouteMagnitude_detachRootChildren_frame]
  rcases List.mem_cons.mp hc with rfl | hc
  · have hyu : y = u := by simpa [AuxTree.toList] using hy
    subst y
    have h := hb _ ht u (by simp [AuxTree.toList])
    simpa [AuxTree.pathTo, AuxTree.toList, hu, pathTagRouteMagnitude, htag, pathTagMagnitude,
      pathPayload, PathTag.zero] using h
  · rcases List.mem_cons.mp hc with rfl | hc
    · have hyv : y = v := by simpa [AuxTree.toList] using hy
      subst y
      have h := hb _ ht v (by simp [AuxTree.toList])
      simpa [AuxTree.pathTo, AuxTree.toList, hv, hvu, pathTagRouteMagnitude, htag, pathTagMagnitude,
        pathPayload, PathTag.zero] using h
    · exact hb c (List.mem_of_mem_erase hc) y hy

/-- The forest of initially isolated vertices has zero raw numeric fields. -/
theorem lctInit_pathNodeBound (n i : ℕ) :
    PathNodeBound 0 ((lctInit pathPayload n none).splay.nodes i) := by
  simp only [lctInit, lctInitNodes]
  split
  · simp [PathNodeBound, pathPayload, PathSummary.single, PathSummary.empty, PathTag.zero]
  · split <;> simp [PathNodeBound, pathPayload, PathSummary.empty, PathTag.zero]

/-- Link-cut initialization starts the auxiliary route budget at zero. -/
theorem lctInit_route_bound (n : ℕ) :
    let trees := (List.range n).map (fun i => AuxTree.node (vid i) .leaf .leaf)
    let free := (List.range (n - 1)).map (fun i => n + 1 + i)
    let init := lctInit pathPayload n none
    LctInvWith pathPayload init trees free (fun _ => 1) ∧
      ∀ t ∈ trees, ∀ y ∈ t.toList, pathTagRouteMagnitude init.splay (t.pathTo y) ≤ 0 := by
  dsimp only
  refine ⟨(lctInit_spec pathPayload_laws n none).1, ?_⟩
  intro t ht y hy
  have htag i : pathTagMagnitude ((lctInit pathPayload n none).splay.nodes i).tag = 0 := by
    obtain ⟨_, _, _, _, hf, hd⟩ := lctInit_pathNodeBound n i
    unfold pathTagMagnitude
    have hf₀ := abs_nonneg ((lctInit pathPayload n none).splay.nodes i).tag.flow
    have hd₀ := abs_nonneg ((lctInit pathPayload n none).splay.nodes i).tag.detector
    omega
  unfold pathTagRouteMagnitude
  simp [htag]

end MinCostFlow.MinRatio
